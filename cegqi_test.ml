(* cegqi_test.ml — unit tests for the CEGQI analysis (no solver involved).

   Each test drives the real pipeline (parse -> infer -> check) to obtain VCs, then asserts
   on [Cegqi.shapes] / [Cegqi.candidates] / [Cegqi.eval_in_cex]. Sources are the bundled
   Examples with their instantiate! hints stripped, so what we assert is exactly the hint a
   human would have had to write. *)

let failures = ref 0

let check (name : string) (ok : bool) (detail : string) =
  if ok then Printf.printf "  PASS  %s\n" name
  else begin
    incr failures;
    Printf.printf "  FAIL  %s\n        %s\n" name detail
  end

let vcs_of (src : string) : Ast.modul * Vc.t list =
  let m = Infer.infer_module (Parse.parse_string src) in
  (m, Check.check_module m)

(* every candidate CEGQI would add, across all VCs of a module, as printed terms *)
let all_candidates (src : string) : string list =
  let m, vcs = vcs_of src in
  List.concat_map (fun vc -> List.map Ast.string_of_term (Cegqi.candidates m vc)) vcs

let all_shapes (src : string) : string list =
  let m, vcs = vcs_of src in
  List.concat_map
    (fun vc ->
      List.map (fun (_, t) -> Ast.string_of_term t) (Cegqi.shapes m vc))
    vcs

(* ===== sources (Examples/*.cst, hints removed) ===== *)

let prop22 = {|
module Prop22
type nat = | Z : nat | S : nat -> nat
let rec max x y = match x with
  | Z -> y
  | S x' -> (match y with
             | Z -> x
             | S y' -> S (max x' y'))
val tip_22 : a:nat -> b:nat -> c:nat -> Lemma(ensures max (max a b) c = max a (max b c))
let rec tip_22 a b c = match a with
  | Z -> ()
  | S a' -> (match b with
             | Z -> ()
             | S b' -> (match c with
                        | Z -> ()
                        | S c' -> tip_22 a' b' c'))
|}

let prop77 = {|
module Prop77
type nat = | Z : nat | S : nat -> nat
type natlist = | Nil : natlist | Cons : nat -> natlist -> natlist
let rec le x y = match x with
  | Z -> true
  | S x' -> (match y with
             | Z -> false
             | S y' -> le x' y')
let rec insort x xs = match xs with
  | Nil -> Cons x Nil
  | Cons h t -> let p = le x h in if p then Cons x (Cons h t) else Cons h (insort x t)
let rec sorted xs = match xs with
  | Nil -> true
  | Cons h t -> (match t with
                 | Nil -> true
                 | Cons h2 t2 -> let p = le h h2 in if p then sorted (Cons h2 t2) else false)
val tip_77 : x:nat -> xs:natlist -> Lemma(ensures sorted xs ==> sorted (insort x xs))
let rec tip_77 x xs = match xs with
  | Nil -> ()
  | Cons h t -> (match t with
                 | Nil -> ()
                 | Cons h2 t2 -> tip_77 x t)
|}

(* prop04 without eq_refl: the obligation needs a lemma, so CEGQI must saturate *)
let prop04 = {|
module Prop04
type nat = | Z : nat | S : nat -> nat
type natlist = | Nil : natlist | Cons : nat -> natlist -> natlist
let rec eq_nat x y = match x with
  | Z -> (match y with
          | Z -> true
          | S y' -> false)
  | S x' -> (match y with
             | Z -> false
             | S y' -> eq_nat x' y')
let rec count x xs = match xs with
  | Nil -> Z
  | Cons h t -> let p = eq_nat x h in if p then S (count x t) else count x t
val tip_04 : n:nat -> xs:natlist -> Lemma(ensures S (count n xs) = count n (Cons n xs))
let tip_04 n xs = match xs with
  | Nil -> ()
  | Cons x xs' -> tip_04 n xs'
|}

(* A derived shape. [double (len xs)] matches on its argument; under [xs = Cons h t],
   [len xs] unfolds to the constructor term [S (len t)]. Only with that result recorded as
   the shape of [len xs] can [double]'s equation fire. The lemma is false; only candidates
   are computed here, never the solver. *)
let derived = {|
module Derived
type nat = | Z : nat | S : nat -> nat
type natlist = | Nil : natlist | Cons : nat -> natlist -> natlist
let rec len xs = match xs with
  | Nil -> Z
  | Cons h t -> S (len t)
let rec double x = match x with
  | Z -> Z
  | S x' -> S (S (double x'))
val tip : xs:natlist -> Lemma(ensures double (len xs) = len xs)
let rec tip xs = match xs with
  | Nil -> ()
  | Cons h t -> tip t
|}

(* A match on a call's result. [found] scrutinises [lookup x en]; in the [Found v] arm the
   equation's guard reads [Found v = lookup x en], and the engine must still propose the
   call at the arm's instance, [lookup x (ECons x v en)], or the goal saturates with one
   witness missing. *)
let through_call = {|
module ThroughCall
type nat = | Z : nat | S : nat -> nat
type look = | Found : nat -> look | Missing : look
type env = | ENil : env | ECons : nat -> nat -> env -> env
let rec lookup x en = match en with
  | ENil -> Missing
  | ECons y w r -> let p = (x = y) in if p then Found w else lookup x r
let found x en = let l = lookup x en in match l with
  | Found w -> true
  | Missing -> false
val t : x:nat -> v:nat -> en:env -> Lemma(ensures found x (ECons x v en) = true)
let t x v en = ()
|}

(* A nested let-chain in max's (S, S) arm: `let p1 = max x' y' in let p2 = S p1 in p2`.
   The witness `S (max a' b')` is only recovered by resolving the chain p2 -> S p1 ->
   S (max x' y'); emitting just the sub-call `max a' b'` (the pre-fix behaviour) leaves it
   stuck. The Z-arm VC needs `S (max a' b')`, which is absent from the goal. *)
let nested_max = {|
module NestedMax
type nat = | Z : nat | S : nat -> nat
let rec max x y = match x with
  | Z -> y
  | S x' -> (match y with
             | Z -> x
             | S y' -> let p1 = max x' y' in let p2 = S p1 in p2)
val tip_22 : a:nat -> b:nat -> c:nat -> Lemma(ensures max (max a b) c = max a (max b c))
let rec tip_22 a b c = match a with
  | Z -> ()
  | S a' -> (match b with
             | Z -> ()
             | S b' -> (match c with
                        | Z -> ()
                        | S c' -> tip_22 a' b' c'))
|}

(* [len] written with a let (`let r = len t in S r`) rather than the direct `S (len t)`.
   It is still *unconditional* and constructor-returning, so after let-chain resolution its
   result is `S (len t)` with no guards — a derivable shape. Only then does [double (len xs)]
   unfold. This guards against the second symptom of the let-chain bug (the let-def surfacing
   as a guard and suppressing shape derivation). *)
let derived_let = {|
module DerivedLet
type nat = | Z : nat | S : nat -> nat
type natlist = | Nil : natlist | Cons : nat -> natlist -> natlist
let rec len xs = match xs with
  | Nil -> Z
  | Cons h t -> let r = len t in S r
let rec double x = match x with
  | Z -> Z
  | S x' -> S (S (double x'))
val tip : xs:natlist -> Lemma(ensures double (len xs) = len xs)
let rec tip xs = match xs with
  | Nil -> ()
  | Cons h t -> tip t
|}

(* item 46, F2: sorts of the terms a quantifier's binders can be instantiated at *)
let sorts = {|
module Sorts
type nat = | Z : nat | S : nat -> nat
type nlist = | NNil : nlist | NCons : nat -> nlist -> nlist
type state = | St : nlist -> nat -> state
let items (s:state) = match s with | St l c -> l
let rec count (x:nat) (l:nlist) : nat = match l with
  | NNil -> Z
  | NCons y r -> if x = y then S (count x r) else count x r
let rec mem (x:nat) (l:nlist) = match l with
  | NNil -> false
  | NCons y r -> if x = y then true else mem x r
val t : s:state -> x:nat -> Lemma(ensures count x (items s) = count x (items s))
let t s x = ()
|}

(* item 46, F3: the quantifier blocks a query asserts universally *)
let blocks = {|
module Blocks
type nat = | Z : nat | S : nat -> nat
assume val f : nat -> nat
assume val k : nat -> nat
assume f_def : forall (x:nat). f x = k x
assume some_zero : exists (x:nat). f x = Z
assume total : forall (x:nat). exists (y:nat). f x = y
val t : u:nat -> Lemma(ensures (forall (a:nat) (b:nat). f a = f b) ==> (exists (z:nat). f z = Z))
let t u = ()
|}

(* item 46, F4: instances of the blocks at the terms the VC can name *)
let insts = {|
module Insts
type nat = | Z : nat | S : nat -> nat
type key = | K : nat -> key
assume val f2 : nat -> nat
assume val key_of : nat -> key
assume val val_k : key -> nat
assume val p : nat -> nat -> nat
assume val key_of2 : nat -> nat -> key
assume val fc : nat -> nat
assume val next : nat -> nat
assume f2_def : forall (x:nat). f2 x = val_k (key_of x)
assume p_def : forall (x:nat) (y:nat). p x y = val_k (key_of2 x y)
assume fc_def : forall (x:nat). fc x = fc (next x)
assume k_def : forall (y:key). val_k y = Z
val t : x:nat -> y:nat -> Lemma(ensures f2 x = Z)
let t x y = ()
|}

(* item 46, F6: only an instance with a present trigger is used *)
let connect = {|
module Connect
type nat = | Z : nat | S : nat -> nat
type key = | K : nat -> key
assume val f2 : nat -> nat
assume val key_of : nat -> key
assume val val_k : key -> nat
assume val fc : nat -> nat
assume val next : nat -> nat
assume f2_def : forall (x:nat). f2 x = val_k (key_of x)
assume fc_def : forall (x:nat). fc x = fc (next x)
val t : x:nat -> Lemma(ensures fc x = Z)
let t x = ()
|}

let () =
  print_endline "cegqi_test";

  (* --- shapes: the arm's discriminators are recovered from the hypotheses --- *)
  let sh22 = all_shapes prop22 in
  check "shapes/prop22 finds S-shapes" (List.exists (fun s -> s = "S a'") sh22)
    (String.concat ", " sh22);
  check "shapes/prop22 finds the nullary Z shape" (List.mem "Z" sh22)
    (String.concat ", " sh22);
  let sh77 = all_shapes prop77 in
  check "shapes/prop77 finds Cons and Nil"
    (List.exists (fun s -> s = "Cons h t") sh77 && List.mem "Nil" sh77)
    (String.concat ", " sh77);

  (* --- unroll/candidates: exactly the hints a human writes --- *)
  let c22 = all_candidates prop22 in
  check "prop22 proposes S (max a' b')" (List.mem "S (max a' b')" c22)
    (String.concat " | " c22);

  let c77 = all_candidates prop77 in
  (* the t = Nil arm: the hand-written hint is [Cons h (insort x t)]; shapes are expanded
     before matching, so the same instance comes out with [t] replaced by [Nil] *)
  check "prop77 proposes the else-branch list (t = Nil arm)"
    (List.mem "Cons h (insort x Nil)" c77) (String.concat " | " c77);
  check "prop77 proposes the then-branch list (t = Nil arm)"
    (List.mem "Cons x (Cons h Nil)" c77) (String.concat " | " c77);
  (* the deeper t = Cons h2 t2 arm reproduces the hand-written hint verbatim *)
  check "prop77 proposes Cons h2 (insort x t2) (deeper arm)"
    (List.mem "Cons h2 (insort x t2)" c77) (String.concat " | " c77);
  check "prop77 proposes the guard call le x h"
    (List.exists (fun s -> s = "le x h") c77) (String.concat " | " c77);
  (* [sorted (Cons h2 t2)] is [sorted t] under the arm's [t = Cons h2 t2]: present under
     its expanded form, so it is not proposed again (the solver relates the two through
     the hypothesis) *)
  check "prop77 does not re-propose sorted t under its expanded form"
    (not (List.mem "sorted (Cons h2 t2)" c77)) (String.concat " | " c77);

  (* --- derived shapes: an unguarded constructor result lets the outer application fire --- *)
  let cd = all_candidates derived in
  check "derived shape: len xs = S (len t) is proposed"
    (List.mem "S (len t)" cd) (String.concat " | " cd);
  check "derived shape: double (len xs) unfolds through it"
    (List.mem "S (S (double (len t)))" cd) (String.concat " | " cd);

  (* --- a match on a call's result: the scrutinee call is proposed at the arm's instance --- *)
  let ct = all_candidates through_call in
  check "match on a call's result proposes the scrutinee call"
    (List.mem "lookup x (ECons x v en)" ct) (String.concat " | " ct);

  (* --- Change 1: let-chain resolution --- *)
  (* nested-let max must yield the full witness S (max a' b'), not just the sub-call max a' b' *)
  let cn = all_candidates nested_max in
  check "nested-let max proposes the full witness S (max a' b')"
    (List.mem "S (max a' b')" cn) (String.concat " | " cn);
  check "nested-let max resolves the recursive arm's witness S (max b' c') too"
    (List.mem "S (max b' c')" cn) (String.concat " | " cn);
  (* let-style unconditional len still derives its shape, so double (len xs) unfolds *)
  let cdl = all_candidates derived_let in
  check "let-style len: its result S (len t) is proposed"
    (List.mem "S (len t)" cdl) (String.concat " | " cdl);
  check "let-style len: shape still derived, double (len xs) unfolds"
    (List.mem "S (S (double (len t)))" cdl) (String.concat " | " cdl);

  (* --- saturation: nothing to instantiate when the gap is a lemma --- *)
  let c04 = all_candidates prop04 in
  check "prop04 saturates on the opaque-guard arm"
    (not (List.mem "S (count n (Cons n xs))" c04))
    (String.concat " | " c04);

  (* --- eval_in_cex: a tuple absent from a function's map is undefined --- *)
  let a = Ast.fresh_var "a" and b = Ast.fresh_var "b" in
  let app f args = Ast.mk_app (Ast.Tm_fvar (Ast.lid_of_str f)) args in
  let cex : Cex.t =
    [ ("a", Cex.Scalar "nat!1");
      ("b", Cex.Scalar "nat!3");
      ("max", Cex.Entries [ ([ Cex.Scalar "nat!1"; Cex.Scalar "nat!3" ], Cex.Scalar "nat!6") ]);
      ("le", Cex.Entries [ ([ Cex.Scalar "nat!1"; Cex.Scalar "nat!3" ], Cex.Scalar "false") ]) ]
  in
  check "eval_in_cex reads a defined application"
    (Cegqi.eval_in_cex cex (app "max" [ Ast.Tm_var a; Ast.Tm_var b ]) = Some (Cex.Scalar "nat!6"))
    "expected nat!6";
  check "eval_in_cex reports an absent tuple as undefined"
    (Cegqi.eval_in_cex cex (app "max" [ Ast.Tm_var b; Ast.Tm_var a ]) = None)
    "expected None for (nat!3, nat!1)";
  check "eval_in_cex reads a bool predicate (always total)"
    (Cegqi.eval_in_cex cex (app "le" [ Ast.Tm_var a; Ast.Tm_var b ]) = Some (Cex.Scalar "false"))
    "expected false";
  check "eval_in_cex renders a nullary constructor as itself"
    (Cegqi.eval_in_cex cex (Ast.Tm_fvar (Ast.lid_of_str "Z")) = Some (Cex.Scalar "Z"))
    "expected Z";

  (* --- ground_apps_under_quantifiers (item 46, gap A) --- *)
  let s = Ast.Tm_var (Ast.fresh_var "s") in
  let c n = Ast.Tm_fvar (Ast.lid_of_str n) in
  let y = Ast.fresh_var "y" in
  let yv = Ast.Tm_var y in
  let forall_y body =
    Ast.Tm_quant { Ast.qk = Ast.Forall; qv = y; qty = None; qbody = body } in
  let eq a b = app "eq" [ a; b ] in
  let under ts = List.map Ast.string_of_term (Smtlib.ground_apps_under_quantifiers ts) in
  let h1 = forall_y (eq (app "count" [ yv; app "items" [ s ] ]) (c "Z")) in
  check "under-quantifier: the ground items s is listed"
    (under [ h1 ] = [ "items s" ]) (String.concat " | " (under [ h1 ]));
  check "under-quantifier: an application over the bound y is not"
    (not (List.mem "count y (items s)" (under [ h1 ]))) (String.concat " | " (under [ h1 ]));
  let goal = eq (app "items" [ s ]) (c "NNil") in
  check "under-quantifier: a term that also occurs outside a quantifier is not listed"
    (under [ h1; goal ] = []) (String.concat " | " (under [ h1; goal ]));
  check "under-quantifier: a formula with no quantifier gives nothing"
    (under [ goal ] = []) (String.concat " | " (under [ goal ]));

  (* --- sort_of (item 46, F2): the sort of a term the ledger can name --- *)
  let m, vcs = vcs_of sorts in
  let vc = List.hd vcs in
  let rs = Axioms.ret_sort_table m in
  let scope_var n = Ast.Tm_var (fst (List.find (fun (v, _) -> v.Ast.vname = n) vc.Vc.scope)) in
  let s = scope_var "s" and x = scope_var "x" in
  let sort t =
    match Cegqi.sort_of vc rs t with Some b -> Smtlib.sort_of_base b | None -> "None" in
  let expect name t want =
    let got = sort t in
    check ("sort_of " ^ name ^ " is " ^ want) (got = want) ("got " ^ got)
  in
  expect "a scope variable (x)" x "UI_nat";
  expect "a scope variable of a datatype (s)" s "UI_state";
  expect "an application (items s)" (app "items" [ s ]) "UI_nlist";
  expect "a nested application (count x (items s))"
    (app "count" [ x; app "items" [ s ] ]) "UI_nat";
  expect "a bool predicate's application (mem x (items s))"
    (app "mem" [ x; app "items" [ s ] ]) "Bool";
  expect "a nullary constructor (Z)" (c "Z") "UI_nat";
  expect "a constructor application (NCons Z NNil)" (app "NCons" [ c "Z"; c "NNil" ]) "UI_nlist";
  expect "a variable not in scope (bound by a quantifier)" (Ast.Tm_var (Ast.fresh_var "y")) "None";
  expect "a literal" (Ast.Tm_const (Ast.C_bool true)) "None";
  expect "an unknown head" (app "nosuch" [ x ]) "None";

  (* --- universal_blocks (item 46, F3) --- *)
  let _, bvcs = vcs_of blocks in
  let bvc = List.hd bvcs in
  let show (bs, body) =
    String.concat " " (List.map (fun (v, _) -> v.Ast.vname) bs) ^ ". " ^ Ast.string_of_term body in
  let blks vc = List.map show (Cegqi.universal_blocks vc) in
  let got = blks bvc in
  let has prefix = List.exists (fun b -> String.length b >= String.length prefix
                                         && String.sub b 0 (String.length prefix) = prefix) got in
  let detail = String.concat " | " got in
  check "blocks: an axiom's forall is a block" (has "x. (f x) = (k x)") detail;
  check "blocks: an existential axiom is not" (not (has "x. (f x) = Z")) detail;
  check "blocks: forall-exists gives the forall, its body keeps the exists"
    (has "x. exists") detail;
  check "blocks: a goal's premise forall, two binders merged" (has "a b. ") detail;
  check "blocks: a goal's exists (negated: universal)" (has "z. ") detail;
  check "blocks: exactly these four" (List.length got = 4) detail;
  let y = Ast.fresh_var "y" in
  let q k ty body = Ast.Tm_quant { Ast.qk = k; qv = y; qty = ty; qbody = body } in
  let nat_ty = Some (Ast.T_refine { Ast.rbase = Ast.B_app (Ast.lid_of_str "nat", []);
                                    rv = y; rphi = Ast.mk_true }) in
  let atom = app "eq" [ app "f" [ Ast.Tm_var y ]; c "Z" ] in
  let only h = blks { bvc with Vc.hyps = [ h ]; axioms = []; goal = Ast.mk_true } in
  check "blocks: not (exists y. ...) in a hypothesis is universal"
    (only (app "l_not" [ q Ast.Exists nat_ty atom ]) = [ "y. " ^ Ast.string_of_term atom ])
    (String.concat " | " (only (app "l_not" [ q Ast.Exists nat_ty atom ])));
  check "blocks: a forall under <==> is not a block"
    (only (app "l_iff" [ q Ast.Forall nat_ty atom; Ast.mk_true ]) = []) "";
  check "blocks: a binder with no sort is skipped"
    (only (q Ast.Forall None atom) = []) "";
  let w = Ast.fresh_var "w" in
  let qw body = Ast.Tm_quant { Ast.qk = Ast.Exists; qv = w; qty = nat_ty; qbody = body } in
  check "blocks: a forall under a hypothesis' exists (a Skolem constant) is a block"
    (only (qw (q Ast.Forall nat_ty atom)) = [ "y. " ^ Ast.string_of_term atom ])
    (String.concat " | " (only (qw (q Ast.Forall nat_ty atom))));

  (* --- inner_apps, self_feeding, instances (item 46, F4) --- *)
  let im, ivcs = vcs_of insts in
  let ivc = List.hd ivcs in
  let irs = Axioms.ret_sort_table im in
  let strs ts = List.map Ast.string_of_term ts in
  let iblocks = Cegqi.universal_blocks ivc in
  let block_with s =
    List.find (fun (_, body) ->
        let b = Ast.string_of_term body in
        let n = String.length s in
        let rec has i = i + n <= String.length b && (String.sub b i n = s || has (i + 1)) in
        has 0)
      iblocks
  in
  let f2_blk = block_with "key_of" and fc_blk = block_with "next" in
  let sf blk = List.map (fun (b, h) -> Smtlib.sort_of_base b ^ ":" ^ h) (Cegqi.self_feeding irs blk) in
  check "self_feeding: fc x = fc (next x) feeds nat through fc and next"
    (sf fc_blk = [ "UI_nat:fc"; "UI_nat:next" ]) (String.concat " | " (sf fc_blk));
  check "self_feeding: f2 x = val_k (key_of x) feeds nat through f2 and val_k, not key_of"
    (sf f2_blk = [ "UI_nat:f2"; "UI_nat:val_k" ]) (String.concat " | " (sf f2_blk));
  let bodies vc = List.map (fun i -> Ast.string_of_term i.Cegqi.body) (fst (Cegqi.instances vc irs)) in
  let got = bodies ivc in
  let detail = String.concat " | " got in
  check "instances: f2_def at the scope variable x" (List.mem "(f2 x) = (val_k (key_of x))" got) detail;
  check "instances: f2_def at the other scope variable y too" (List.mem "(f2 y) = (val_k (key_of y))" got) detail;
  check "instances: f2_def at the ledger term f2 x" (List.mem "(f2 (f2 x)) = (val_k (key_of (f2 x)))" got) detail;
  check "instances: p_def gets every tuple, (x, y) included"
    (List.mem "(p x y) = (val_k (key_of2 x y))" got && List.mem "(p y x) = (val_k (key_of2 y x))" got) detail;
  check "instances: k_def has no key term to instantiate at"
    (not (List.exists (fun b -> String.length b >= 6 && String.sub b 0 6 = "(val_k") got)) detail;
  check "instances: 3 + 9 + 3 + 0 = 15, no cap hit"
    (List.length got = 15 && not (snd (Cegqi.instances ivc irs))) (string_of_int (List.length got));
  let x = List.find (fun (v, _) -> v.Ast.vname = "x") ivc.Vc.scope |> fst |> fun v -> Ast.Tm_var v in
  let proposed = { ivc with Vc.instantiations = [ app "next" [ x ] ] } in
  let gp = bodies proposed in
  check "instances: a proposed next x is refused for fc_def (rule 3')"
    (not (List.mem "(fc (next x)) = (fc (next (next x)))" gp)) (String.concat " | " gp);
  check "instances: the same next x is allowed for f2_def"
    (List.mem "(f2 (next x)) = (val_k (key_of (next x)))" gp) (String.concat " | " gp);
  let stated = { ivc with Vc.goal = app "eq" [ app "fc" [ app "next" [ x ] ]; c "Z" ] } in
  let gs = bodies stated in
  check "instances: next x stated in the goal is allowed for fc_def"
    (List.mem "(fc (next x)) = (fc (next (next x)))" gs) (String.concat " | " gs);
  let few, capped = Cegqi.instances ~cap_block:2 ivc irs in
  check "instances: cap_block 2 gives 2 per block and reports the cap"
    (List.length few = 6 && capped) (string_of_int (List.length few));
  let one, capped1 = Cegqi.instances ~cap_round:4 ivc irs in
  check "instances: cap_round 4 gives 4 in all and reports the cap"
    (List.length one = 4 && capped1) (string_of_int (List.length one));
  let at_x =
    List.find (fun i -> strs i.Cegqi.at = [ "x" ] && Ast.string_of_term i.Cegqi.body = "(f2 x) = (val_k (key_of x))")
      (fst (Cegqi.instances ivc irs))
  in
  check "instances: f2_def at x has, for its one binder, triggers f2 x, key_of x, val_k (key_of x)"
    (List.map strs at_x.Cegqi.triggers = [ [ "f2 x"; "key_of x"; "val_k (key_of x)" ] ])
    (String.concat " | " (List.concat_map strs at_x.Cegqi.triggers));
  let at_xy =
    List.find (fun i -> strs i.Cegqi.at = [ "x"; "y" ] && Ast.string_of_term i.Cegqi.body = "(p x y) = (val_k (key_of2 x y))")
      (fst (Cegqi.instances ivc irs))
  in
  check "instances: p_def at (x, y) has one trigger list, its applications over both binders"
    (List.map strs at_xy.Cegqi.triggers = [ [ "p x y"; "key_of2 x y"; "val_k (key_of2 x y)" ] ])
    (String.concat " | " (List.concat_map strs at_xy.Cegqi.triggers));
  let two = {|
module Two
type nat = | Z : nat | S : nat -> nat
assume val g : nat -> nat
assume val h : nat -> nat
assume two_def : forall (x:nat) (y:nat). g x = h y
val t : x:nat -> y:nat -> Lemma(ensures g x = Z)
let t x y = ()
|} in
  let tm, tvcs = vcs_of two in
  let tvc = List.hd tvcs in
  let at_xy2 =
    List.find (fun i -> strs i.Cegqi.at = [ "x"; "y" ]) (fst (Cegqi.instances tvc (Axioms.ret_sort_table tm)))
  in
  check "instances: with no application over both binders, one trigger list per binder"
    (List.map strs at_xy2.Cegqi.triggers = [ [ "g x" ]; [ "h y" ] ])
    (String.concat " | " (List.concat_map strs at_xy2.Cegqi.triggers));

  (* --- projections are no triggers --- *)
  let pm, pvcs = vcs_of sorts in
  let pj = Cegqi.projections (Axioms.definitional_equations pm) in
  check "projections: items (a field accessor) is one, count and mem are not"
    (pj = [ "items" ]) (String.concat " | " pj);
  let spec = {|
module Spec
type nat = | Z : nat | S : nat -> nat
type nlist = | NNil : nlist | NCons : nat -> nlist -> nlist
type state = | St : nlist -> nat -> state
let items (s:state) = match s with | St l c -> l
assume val step : state -> state
assume val size : nlist -> nat
assume step_spec : forall (s:state). size (items (step s)) = size (items s)
val t : s:state -> Lemma(ensures size (items (step s)) = Z)
let t s = ()
|} in
  let sm, svcs = vcs_of spec in
  let svc = List.hd svcs in
  let srs = Axioms.ret_sort_table sm in
  let at_s skip =
    List.find (fun i -> strs i.Cegqi.at = [ "s" ]) (fst (Cegqi.instances ~skip_heads:skip svc srs)) in
  check "instances: without skip_heads, items s is a trigger of step_spec at s"
    (List.mem "items s" (List.concat_map strs (at_s []).Cegqi.triggers))
    (String.concat " | " (List.concat_map strs (at_s []).Cegqi.triggers));
  check "instances: with projections skipped, the triggers are step s, items (step s) is gone too, size (…) stay"
    (List.map strs (at_s [ "items" ]).Cegqi.triggers
     = [ [ "step s"; "size (items (step s))"; "size (items s)" ] ])
    (String.concat " | " (List.concat_map strs (at_s [ "items" ]).Cegqi.triggers));
  ignore pvcs;

  (* --- candidates: an instance is used only when a trigger is present (F6) --- *)
  let cc = all_candidates connect in
  let dc = String.concat " | " cc in
  check "connected: fc_def at x (fc x is the goal's) proposes next x and fc (next x)"
    (List.mem "next x" cc && List.mem "fc (next x)" cc) dc;
  check "connected: f2_def is not instantiated, no application of it is present"
    (not (List.exists (fun c -> String.length c >= 6 && String.sub c 0 6 = "key_of") cc)) dc;
  check "connected: fc_def is not re-instantiated at next x (self-feeding), so no next (next x)"
    (not (List.mem "next (next x)" cc)) dc;

  if !failures = 0 then print_endline "all cegqi tests passed"
  else (Printf.printf "%d failure(s)\n" !failures; exit 1)
