(* cegqi.ml — see cegqi.mli. *)

open Ast

let rec head_spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> head_spine f (a :: acc) | _ -> (t, acc)

(* the symbol an application is headed by: a top-level name, or a local binder for a
   recursive self-call (inside a body the recursive reference is a [Tm_var]) *)
let head_name (h : term) : string option =
  match h with Tm_fvar l -> Some l.bname | Tm_var v -> Some v.vname | _ -> None

let ctor_names (m : modul) : (string, unit) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  List.iter
    (fun se ->
      match se.sig_el with
      | Sig_inductive ind ->
        List.iter (fun c -> Hashtbl.replace tbl c.dc_name.bname ()) ind.ind_ctors
      | _ -> ())
    m.mod_decls;
  tbl

(* a (possibly nullary) constructor application *)
let is_ctor_term (ctors : (string, unit) Hashtbl.t) (t : term) : bool =
  match fst (head_spine t []) with
  | Tm_fvar l -> Hashtbl.mem ctors l.bname
  | _ -> false

(* ===== the sort of a ground term ===== *)

let sort_of (vc : Vc.t) (ret_sort : (string, base_typ) Hashtbl.t) (t : term) :
    base_typ option =
  match head_spine t [] with
  | Tm_var v, [] ->
    List.find_map (fun (s, b) -> if s.vid = v.vid then Some b else None) vc.Vc.scope
  | Tm_fvar l, _ -> Hashtbl.find_opt ret_sort l.bname
  | _ -> None

(* ===== universal positions ===== *)

let universal_blocks (vc : Vc.t) : ((var * base_typ) list * term) list =
  let out = ref [] in
  (* the maximal run of [k]-quantifiers at the top of [t]: its binders with their sorts
     ([None] if one has no sort), and the body under them *)
  let rec prefix k t =
    match t with
    | Tm_quant { qk; qv; qty; qbody } when qk = k ->
      let bs, body = prefix k qbody in
      let b = match qty with Some (T_refine { rbase; _ }) -> Some (qv, rbase) | _ -> None in
      ((match b, bs with Some b, Some bs -> Some (b :: bs) | _ -> None), body)
    | _ -> (Some [], t)
  in
  (* [pos]: the formula is asserted as is ([true]) or negated ([false]) *)
  let rec go pos t =
    match t with
    | Tm_quant { qk; _ } when qk = (if pos then Forall else Exists) ->
      (match prefix qk t with Some bs, body -> out := (bs, body) :: !out | None, _ -> ())
    | Tm_ascribed (e, _) -> go pos e
    | Tm_app _ ->
      (match head_spine t [] with
       | Tm_fvar l, [ a; b ] when l.bname = "l_and" || l.bname = "l_or" -> go pos a; go pos b
       | Tm_fvar l, [ a; b ] when l.bname = "l_imp" -> go (not pos) a; go pos b
       | Tm_fvar l, [ a ] when l.bname = "l_not" -> go (not pos) a
       | _ -> ())
    | _ -> ()
  in
  List.iter (go true) (vc.Vc.hyps @ vc.Vc.axioms);
  go false vc.Vc.goal;
  List.rev !out

(* ===== instances of the universal blocks ===== *)

let inner_apps (t : term) : term list =
  let acc = ref [] in
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  let add a =
    let s = Ast.string_of_term a in
    if not (Hashtbl.mem seen s) then (Hashtbl.add seen s (); acc := a :: !acc)
  in
  (* [inside]: under the arguments of an uninterpreted application *)
  let rec go inside t =
    match t with
    | Tm_app _ ->
      let h, args = head_spine t [] in
      let uninterpreted =
        match h with
        | Tm_fvar l -> not (Smtlib.is_interpreted l.bname)
        | Tm_var _ -> true
        | _ -> false
      in
      if inside && uninterpreted then add t;
      List.iter (go (inside || uninterpreted)) args
    | Tm_quant q -> go inside q.qbody
    | Tm_ascribed (e, _) -> go inside e
    | _ -> ()
  in
  go false t;
  List.rev !acc

let self_feeding (ret_sort : (string, base_typ) Hashtbl.t)
    ((binders, body) : (var * base_typ) list * term) : (base_typ * string) list =
  let sorts = List.map snd binders in
  let mentions_binder a =
    List.exists (fun v -> List.exists (fun (b, _) -> b.vid = v.vid) binders)
      (Subst.free_vars_term a)
  in
  List.filter_map
    (fun a ->
      match head_spine a [] with
      | Tm_fvar l, _ when mentions_binder a ->
        (match Hashtbl.find_opt ret_sort l.bname with
         | Some s when List.mem s sorts -> Some (s, l.bname)
         | _ -> None)
      | _ -> None)
    (inner_apps body)

let instances ?(cap_block = 50) ?(cap_round = 200) ?fresh (vc : Vc.t)
    (ret_sort : (string, base_typ) Hashtbl.t) : (term list * term) list * bool =
  let fresh = Option.map (List.map Ast.string_of_term) fresh in
  (* the terms a binder can be instantiated at: the scope's variables, then the ledger's
     applications, each with its sort *)
  let terms =
    List.filter_map
      (fun t -> match sort_of vc ret_sort t with Some s -> Some (s, t) | None -> None)
      (List.map (fun (v, _) -> Tm_var v) vc.Vc.scope @ Smtlib.ledger_terms vc)
  in
  (* the applications the VC states itself, as opposed to those a round proposed *)
  let stated : (string, unit) Hashtbl.t = Hashtbl.create 32 in
  List.iter (fun a -> Hashtbl.replace stated (Ast.string_of_term a) ())
    (Smtlib.collect_apps (vc.Vc.goal :: vc.Vc.hyps));
  let capped = ref false in
  let rec take n = function
    | [] -> []
    | _ when n = 0 -> capped := true; []
    | x :: r -> x :: take (n - 1) r
  in
  let of_block ((binders, body) as block) =
    let feeding = self_feeding ret_sort block in
    (* a proposed term headed by a symbol through which the block feeds a binder of that
       sort is skipped: instantiating there would propose the next term of the same
       shape, without end. Terms the VC states itself are always allowed. *)
    let allowed (s : base_typ) (t : term) =
      match head_spine t [] with
      | Tm_fvar l, _ :: _ when List.mem (s, l.bname) feeding ->
        Hashtbl.mem stated (Ast.string_of_term t)
      | _ -> true
    in
    let per_binder =
      List.map
        (fun (_, s) -> List.filter_map (fun (s', t) -> if s' = s && allowed s t then Some t else None) terms)
        binders
    in
    let tuples =
      List.fold_right
        (fun choices acc -> List.concat_map (fun t -> List.map (fun rest -> t :: rest) acc) choices)
        per_binder [ [] ]
    in
    (* with [fresh], only the tuples that mention one of those terms: the others were
       enumerated by an earlier call *)
    let tuples =
      match fresh with
      | None -> tuples
      | Some fs ->
        List.filter (fun tu -> List.exists (fun t -> List.mem (Ast.string_of_term t) fs) tu) tuples
    in
    List.map
      (fun tuple ->
        (tuple, Subst.subst_term (List.combine (List.map fst binders) tuple) body))
      (take cap_block tuples)
  in
  let all = List.concat_map of_block (universal_blocks vc) in
  let kept = take cap_round all in
  (kept, !capped)

(* ===== shapes ===== *)

(* Hypotheses arrive as single propositions, but a branch can contribute a conjunction
   (a lemma call's postcondition alongside its binding), so flatten before scanning. *)
let rec conjuncts (t : term) : term list =
  match head_spine t [] with
  | Tm_fvar l, [ a; b ] when lid_eq l and_lid -> conjuncts a @ conjuncts b
  | _ -> [ t ]

(* The table is keyed by term, not by variable id, so that a shape can belong to an
   application as well as to a variable (a derived shape, [len t ↦ S (len t2)]); the
   first entry for a key wins. *)
let add_shape (sh : (term * term) list) (k : term) (s : term) : (term * term) list =
  if List.exists (fun (k', _) -> Subst.alpha_equal_term k' k) sh then sh else (k, s) :: sh

let shapes (m : modul) (vc : Vc.t) : (term * term) list =
  let ctors = ctor_names m in
  let acc = ref [] in
  let add (v : var) (t : term) = acc := add_shape !acc (Tm_var v) t in
  List.iter
    (fun h ->
      List.iter
        (fun c ->
          match head_spine c [] with
          | Tm_fvar l, [ lhs; rhs ] when lid_eq l eq_lid ->
            (match (lhs, rhs) with
             | Tm_var v, r when is_ctor_term ctors r -> add v r
             | r, Tm_var v when is_ctor_term ctors r -> add v r
             | _ -> ())
          | _ -> ())
        (conjuncts h))
    vc.Vc.hyps;
  List.rev !acc

(* Expand known shapes inside a term, so an equation's constructor patterns have something
   to match: [xs] with [xs = Cons h t] and [t = Nil] becomes [Cons h Nil]. Any subterm
   with an entry is rewritten, a variable or an application alike. Bounded, so a
   pathological cyclic shape cannot loop. *)
let rec apply_shapes (sh : (term * term) list) (fuel : int) (t : term) : term =
  if fuel <= 0 then t
  else
    match List.find_opt (fun (k, _) -> Subst.alpha_equal_term k t) sh with
    | Some (_, s) -> apply_shapes sh (fuel - 1) s
    | None ->
      (match t with
       | Tm_app (f, a) -> Tm_app (apply_shapes sh fuel f, apply_shapes sh fuel a)
       | _ -> t)

(* ===== evaluating a term in the counterexample ===== *)

let eval_in_cex (c : Cex.t) (t : term) : Cex.value option =
  let rec ev (t : term) : Cex.value option =
    match t with
    | Tm_const (C_bool b) -> Some (Cex.Scalar (if b then "true" else "false"))
    | Tm_const (C_int n) -> Some (Cex.Scalar (string_of_int n))
    | Tm_ascribed (e, _) -> ev e
    | Tm_var v ->
      (match List.assoc_opt v.vname c with Some (Cex.Scalar s) -> Some (Cex.Scalar s) | _ -> None)
    | Tm_fvar l ->
      (* a nullary constructor is rendered as its own name in the model *)
      (match List.assoc_opt l.bname c with
       | Some (Cex.Scalar s) -> Some (Cex.Scalar s)
       | _ -> Some (Cex.Scalar l.bname))
    | Tm_app _ ->
      let h, args = head_spine t [] in
      (match head_name h with
       | None -> None
       | Some f ->
         let argvs = List.map ev args in
         if List.exists (fun a -> a = None) argvs then None
         else
           let argvs = List.map (function Some v -> v | None -> assert false) argvs in
           (match List.assoc_opt f c with
            | Some (Cex.Entries es) ->
              (* absent from the map = the relation relates these args to nothing *)
              (match List.find_opt (fun (k, _) -> k = argvs) es with
               | Some (_, v) -> Some v
               | None -> None)
            | _ -> None))
    | _ -> None
  in
  ev t

(* ===== matching an equation's argument patterns ===== *)

(* One-way match of [pats] (containing the equation's binders) against [concrete].
   Non-linear patterns must agree. *)
let match_args (binders : (var * base_typ) list) (pats : term list) (concrete : term list)
  : (var * term) list option =
  let is_binder (v : var) = List.exists (fun (b, _) -> b.vid = v.vid) binders in
  let sub : (var * term) list ref = ref [] in
  let ok = ref true in
  let bind (v : var) (t : term) =
    match List.find_opt (fun (b, _) -> b.vid = v.vid) !sub with
    | Some (_, t') -> if not (Subst.alpha_equal_term t t') then ok := false
    | None -> sub := (v, t) :: !sub
  in
  let rec go (p : term) (c : term) =
    if !ok then
      match (p, c) with
      | Tm_var v, _ when is_binder v -> bind v c
      | Tm_var v, Tm_var w when var_eq v w -> ()
      | Tm_fvar l, Tm_fvar l' when lid_eq l l' -> ()
      | Tm_const a, Tm_const b when a = b -> ()
      | Tm_app (f, a), Tm_app (g, b) -> go f g; go a b
      | _ -> ok := false
  in
  (try List.iter2 go pats concrete with Invalid_argument _ -> ok := false);
  if !ok then Some !sub else None

(* ===== unrolling ===== *)

(* Split a guard equality [L = R] into its two sides, if it is one. *)
let eq_sides (g : term) : (term * term) option =
  match head_spine g [] with
  | Tm_fvar l, [ a; b ] when lid_eq l eq_lid -> Some (a, b)
  | _ -> None

(* [gen_equations] ANF-flattens a body, so a leaf's [de_guards] hold both the let-bindings
   that build its result and the conditions that select it. [resolve_guards] untangles the
   two:

   - σ, an inlining substitution over the leaf's *let-binders* — binders [g] that occur as a
     guard LHS [Tm_var g] and are not among [de_args] (so parameters matched on a literal,
     bound by [match_args], are excluded). Each binder's definition is its non-constant
     guard-RHS if it has one, else its constant one (so a tested predicate [let p = le x h]
     with a companion [p = true] takes [le x h], not [true]); [Tm_abs] defs are skipped
     (higher-order locals the backend rejects anyway). Folded in guard order (ANF emits them
     in dependency order), giving the transitive closure [p2 ↦ S (max x' y')].
   - the *conditions* that make this leaf conditional: a tested predicate's call ([le x h],
     when some [g = constant] pins [g]) and a datatype scrutinee's call ([lookup x en], when a
     guard reads [C(fields) = call]). Pure definitional lets are inlined via σ into the rhs
     and are not conditions; the [g = constant] tests themselves carry no call.

   Returns (σ, conditions). *)
let resolve_guards (ctors : (string, unit) Hashtbl.t) (de_args : term list)
    (guards : term list) : (var * term) list * term list =
  let arg_vars = List.concat_map Subst.free_vars_term de_args in
  let is_arg (v : var) = List.exists (fun a -> a.vid = v.vid) arg_vars in
  let is_const = function Tm_const _ -> true | _ -> false in
  (* a guard viewed as [Tm_var g = def], g a let-binder (not a [de_args] parameter) *)
  let as_let_def g =
    match eq_sides g with
    | Some (Tm_var v, r) when not (is_arg v) -> Some (v, r)
    | Some (r, Tm_var v) when not (is_arg v) -> Some (v, r)
    | _ -> None
  in
  (* binders pinned to a constant by a branch test *)
  let tested =
    List.filter_map
      (fun g -> match as_let_def g with Some (v, r) when is_const r -> Some v.vid | _ -> None)
      guards
  in
  (* σ: each let-binder to its definition, transitively closed. Folding in guard order, the
     first assignment wins — ANF emits a binder's real (non-constant) definition before any
     [if] branch test of it, so [p = le x h] is taken over the later [p = true]. [Tm_abs]
     definitions (higher-order locals the backend rejects) are skipped. *)
  let sigma = ref [] in
  List.iter
    (fun g ->
      match as_let_def g with
      | Some (v, r)
        when (not (List.mem_assoc v !sigma))
             && (match r with Tm_abs _ -> false | _ -> true) ->
        sigma := !sigma @ [ (v, Subst.subst_term !sigma r) ]
      | _ -> ())
    guards;
  let sigma = !sigma in
  (* constructor pattern C(x..): a constructor applied to variables only *)
  let is_pattern t =
    match head_spine t [] with
    | Tm_fvar l, args ->
      Hashtbl.mem ctors l.bname && List.for_all (function Tm_var _ -> true | _ -> false) args
    | _ -> false
  in
  (* conditions: tested-predicate calls + datatype-scrutinee calls, σ-resolved *)
  let conditions =
    List.filter_map
      (fun g ->
        match eq_sides g with
        | Some (l, r) ->
          let pick a b =            (* a is the pattern/binder side, b the def side *)
            if is_const b then None
            else
              match a with
              | Tm_var v when List.mem v.vid tested -> Some (Subst.subst_term sigma b)
              | _ when is_pattern a -> Some (Subst.subst_term sigma b)
              | _ -> None
          in
          (match pick l r with Some t -> Some t | None -> pick r l)
        | None -> None)
      guards
  in
  (sigma, conditions)

(* Inside a function body a recursive call is a [Tm_var] bound by the enclosing [let rec],
   whereas a VC refers to the same function as a top-level [Tm_fvar]. Rewrite unfolded
   right-hand sides accordingly, so a candidate is structurally what the VC would have
   written — otherwise the function's own name looks like a free variable and relabs has no
   [f_rel] to build. *)
let externalize (fns : (string, unit) Hashtbl.t) (t : term) : term =
  let rec go t =
    match t with
    | Tm_var v when Hashtbl.mem fns v.vname -> Tm_fvar (lid_of_str v.vname)
    | Tm_app (f, a) -> Tm_app (go f, go a)
    | Tm_ascribed (e, ty) -> Tm_ascribed (go e, ty)
    | _ -> t
  in
  go t

(* One matched equation, instantiated: its right-hand side and the guard calls on the
   path to that leaf. [guards = []] means the equation is unconditional — its result is
   what the application equals, not one alternative among several. *)
type unfolding = { rhs : term; guards : term list }

let unroll (m : modul) (eqs : Axioms.defeq list) (sh : (term * term) list) (t : term)
  : unfolding list =
  let h, args = head_spine t [] in
  if args = [] then []
  else
    match head_name h with
    | None -> []
    | Some f ->
      let ctors = ctor_names m in
      let fns = Hashtbl.create 16 in
      List.iter (fun (e : Axioms.defeq) -> Hashtbl.replace fns e.Axioms.de_fn ()) eqs;
      let args' = List.map (apply_shapes sh 8) args in
      List.filter_map
        (fun (e : Axioms.defeq) ->
          if e.Axioms.de_fn <> f then None
          else
            match match_args e.Axioms.de_binders e.Axioms.de_args args' with
            | None -> None
            | Some s ->
              (* resolve the ANF let-chain: σ inlines the let-definitions into the result,
                 leaving [conditions] = the genuine branch/scrutinee calls of this leaf *)
              let sigma, conditions = resolve_guards ctors e.Axioms.de_args e.Axioms.de_guards in
              let resolve t = Subst.subst_term s (Subst.subst_term sigma t) in
              Some
                { rhs = externalize fns (resolve e.Axioms.de_rhs);
                  guards = List.map (fun c -> externalize fns (Subst.subst_term s c)) conditions })
        eqs

(* The flat list of terms an unfolding needs: the right-hand side and the guard calls. *)
let unfolding_terms (u : unfolding) : term list = u.rhs :: u.guards

(* ===== candidate selection ===== *)

let candidates (m : modul) (vc : Vc.t) : term list =
  let eqs = Axioms.definitional_equations m in
  let ctors = ctor_names m in
  (* grows within the round with derived shapes (below) *)
  let sh = ref (shapes m vc) in
  let frontier = Smtlib.ledger_terms vc in
  (* What the query already materialises, by printed form — under both the term as written
     and its shape-expanded form, so an unfolding of a present term is recognised as present:
     [sorted (Cons h2 t2)] is [sorted t] under [t = Cons h2 t2], and the solver already
     relates the two through the hypothesis. The table is consulted as the round's shapes
     grow, so the expanded key follows the derived shapes too. *)
  let present : (string, unit) Hashtbl.t = Hashtbl.create 64 in
  let keys t =
    let w = Ast.string_of_term t and x = Ast.string_of_term (apply_shapes !sh 8 t) in
    if w = x then [ w ] else [ w; x ]
  in
  let is_present t = List.exists (Hashtbl.mem present) (keys t) in
  let mark t = List.iter (fun k -> Hashtbl.replace present k ()) (keys t) in
  List.iter mark frontier;
  (* a candidate must be writable from the VC's scope, else it would render as an unbound
     symbol; a witness that cannot be named here is exactly the lemma case *)
  let in_scope (v : var) = List.exists (fun (s, _) -> s.vid = v.vid) vc.Vc.scope in
  let closed t = List.for_all in_scope (Subst.free_vars_term t) in
  let out = ref [] in
  (* A candidate is only progress if it materialises an application that is not there yet.
     Unfolding a base case can yield a bare constructor ([count n Nil = Z]), which hoists to
     nothing: counting that as progress would keep the loop alive and burn fuel on a VC that
     has in fact saturated. *)
  let adds_something t =
    List.exists (fun sub -> not (is_present sub)) (Smtlib.collect_apps [ t ])
  in
  let add t =
    if (not (is_present t)) && closed t && adds_something t then begin
      mark t;
      (* the subterms it materialises are present from now on, too *)
      List.iter mark (Smtlib.collect_apps [ t ]);
      out := t :: !out
    end
  in
  (* [ledger_terms] is inner-first, so inner applications are unfolded before the outer
     ones that are stuck only because of them. An unfolding whose equation has no guard
     and whose result is a constructor term fixes the application's shape — a *derived*
     shape, [len t ↦ S (len t2)] — recorded at once so that an outer application matching
     on it ([double (len t)]) can unfold in the same round. A guarded result is one
     alternative among several and is not a shape. *)
  List.iter
    (fun app ->
      List.iter
        (fun (u : unfolding) ->
          List.iter add (unfolding_terms u);
          if u.guards = [] && is_ctor_term ctors u.rhs then sh := add_shape !sh app u.rhs)
        (unroll m eqs !sh app))
    frontier;
  (* Then the universal blocks, instantiated at the VC's own terms: an instance's inner
     applications are what the solver's instance of the block needs values for. They go
     through the same screen, so an application already materialised, or one the scope
     cannot name (a quantifier of the body's own), is not proposed. Unrolling comes
     first, so a witness that unfolding alone finds is never attributed to an instance. *)
  let ret_sort = Axioms.ret_sort_table m in
  (* To a fixpoint within the round: an instance's application is a ledger term for the
     next iteration ([key_def] at [key_of x], which [f4_def] at [x] just proposed), so a
     chain through the sorts closes here instead of costing one solver round per sort.
     Each iteration after the first looks only at tuples that mention a term the previous
     one added. The closure is finite when the sorts are layered; a cycle through several
     blocks is stopped by [instances]' caps and the iteration bound. *)
  let rec close fresh n =
    let added = ref [] in
    let add' t = let before = !out in add t; if !out != before then added := t :: !added in
    let vc' = { vc with Vc.instantiations = vc.Vc.instantiations @ List.rev !out } in
    let insts, _capped = instances ?fresh vc' ret_sort in
    List.iter (fun (_, body) -> List.iter add' (inner_apps body)) insts;
    if !added <> [] && n < 8 then close (Some !added) (n + 1)
  in
  close None 0;
  List.rev !out
