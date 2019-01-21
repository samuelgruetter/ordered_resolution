Require Import Coq.Lists.List. Import ListNotations.

Definition funname := nat.
Definition varname := nat.

Inductive term: Type :=
| Var: varname -> term
| Fun: funname -> list term -> term.

(* clauses consist of positive or negated literals *)
Inductive literal: Type :=
| Pos: term -> literal
| Neg: term -> literal.

Definition atm_of(l: literal): term := match l with Pos t | Neg t => t end.

(* clauses are disjunctions of literals *)
Definition clause := list literal.

(* a goal is a list of clauses implying False *)
Definition goal := list clause.

Definition set(T: Type) := T -> Prop.

(* A Herbrand interpretation ("model") is a set of ground terms considered true *)
Definition model := set term.

Definition satisfies_literal(m: model)(l: literal): Prop :=
  match l with
  | Pos t => m t
  | Neg t => ~ m t
  end.

Definition satisfies_clause(m: model)(c: clause): Prop :=
  fold_right (fun l acc => satisfies_literal m l \/ acc) False c.

Definition satisfies_clauses_listbased(m: model)(cs: list clause): Prop :=
  fold_right (fun c acc => satisfies_clause m c /\ acc) True cs.

Definition satisfiable_listbased(cs: list clause): Prop :=
  exists (m: model), satisfies_clauses_listbased m cs.

Definition satisfies_clauses(m: model)(cs: set clause): Prop :=
  forall c, cs c -> satisfies_clause m c.

Definition satisfiable(cs: set clause): Prop :=
  exists (m: model), satisfies_clauses m cs.

Definition substitution := varname -> option term.

Definition apply_subst_in_term(s: substitution): term -> term :=
  fix rec t :=
    match t with
    | Var x =>
      match s x with
      | Some u => u
      | None => Var x
      end
    | Fun name args => Fun name (map rec args)
    end.

Definition apply_subst_in_literal(s: substitution)(l: literal): literal :=
  match l with
  | Pos t => Pos (apply_subst_in_term s t)
  | Neg t => Neg (apply_subst_in_term s t)
  end.

Definition apply_subst_in_clause(s: substitution)(cl: clause): clause :=
  map (apply_subst_in_literal s) cl.

Definition is_ground_term(t: term): Prop := forall s, apply_subst_in_term s t = t.

Definition is_ground_literal(l: literal): Prop := is_ground_term (atm_of l).

Definition is_ground_clause(c: clause): Prop := Forall is_ground_literal c.

Definition grounding_of_clause(c: clause): set clause :=
  fun c' => is_ground_clause c' /\ exists s, c' = apply_subst_in_clause s c.

(* closer to IsaFOL:
Definition is_ground_subst(s: substitution): Prop :=
  forall (t: term), is_ground_term (apply_subst_in_term s t).

Definition grounding_of_clause(c: clause): set clause :=
  fun c' => exists s, is_ground_subst s /\ c' = apply_subst_in_clause s c.
*)

Definition union{T: Type}(A B: set T): set T :=
  fun x => A x \/ B x.

Definition empty{T: Type}: set T := fun x => False.

Definition grounding_of_clauses(cs: list clause): set clause :=
  fold_right (fun c acc => union (grounding_of_clause c) acc) empty cs.

Definition goal_unsatisfiable(g: goal): Prop := ~ satisfiable (grounding_of_clauses g).

Definition fun_ctx := funname -> forall (T: Type), T -> Prop.
Definition var_ctx := varname -> forall (T: Type), T -> Prop.

Inductive interp_term: fun_ctx -> var_ctx -> term -> forall {T: Type}, T -> Prop :=
| interp_var: forall (Gf: fun_ctx) (Gv: var_ctx) x T v,
    Gv x T v ->
    interp_term Gf Gv (Var x) v
| interp_fun: forall (Gf: fun_ctx) (Gv: var_ctx) name args (VS: Type) (vs: VS) (R: Type) f,
    Gf name (VS -> R) f ->
    interp_terms Gf Gv args vs ->
    interp_term Gf Gv (Fun name args) (f vs)
with interp_terms: fun_ctx -> var_ctx -> list term -> forall {T: Type}, T -> Prop :=
| interp_nil: forall (Gf: fun_ctx) (Gv: var_ctx),
    interp_terms Gf Gv nil tt
| interp_cons: forall (Gf: fun_ctx) (Gv: var_ctx) t ts (V VS: Type) (v: V) (vs: VS),
    interp_term Gf Gv t v ->
    interp_terms Gf Gv ts vs ->
    interp_terms Gf Gv (t :: ts) (v, vs).

Inductive interp_lit: fun_ctx -> var_ctx -> literal -> Prop -> Prop :=
| interp_Pos: forall Gf Gv t P,
    interp_term Gf Gv t P ->
    interp_lit Gf Gv (Pos t) P
| interp_Neg: forall Gf Gv t P,
    interp_term Gf Gv t P ->
    interp_lit Gf Gv (Neg t) (~ P).

Inductive interp_clause'': fun_ctx -> var_ctx -> clause -> Prop -> Prop :=
| interp_False: forall Gf Gv,
    interp_clause'' Gf Gv nil False
| interp_or: forall Gf Gv c cs P Ps,
    interp_lit Gf Gv c P ->
    interp_clause'' Gf Gv cs Ps ->
    interp_clause'' Gf Gv (c :: cs) (P \/ Ps).

Inductive Eq: forall (T: Type) (x: T) (T': Type) (x': T'), Prop :=
| Refl: forall (T: Type) (x: T), Eq T x T x.
(*
Inductive Wrap: Prop :=
| wrap(T: Type)(x: T): Wrap.
*)

Definition empty_ctx: nat -> forall (T: Type), T -> Prop :=
  fun n T v => False.

Definition cons_ctx(ctx: nat -> forall (T: Type), T -> Prop)
   (newName: nat)(newT: Type)(newV: newT): nat -> forall (T: Type), T -> Prop :=
  fun n => if PeanoNat.Nat.eq_dec n newName then Eq newT newV else ctx n.

Definition singleton_ctx(n: nat)(T: Type)(v: T) := cons_ctx empty_ctx n T v.

Inductive interp_clause': fun_ctx -> var_ctx -> clause -> Prop -> Prop :=
| interp_done: forall Gf Gv c P,
    interp_clause'' Gf Gv c P ->
    interp_clause' Gf Gv c P
| interp_forall: forall Gf Gv c U (P: U -> Prop) fresh,
    (forall T v, ~ Gv fresh T v) ->
    (forall (u: U), interp_clause' Gf (cons_ctx Gv fresh U u) c (P u)) ->
    interp_clause' Gf Gv c (forall (u: U), P u).

Definition interp_clause(Gf: fun_ctx): clause -> Prop -> Prop :=
  interp_clause' Gf empty_ctx.

Inductive interp_goal'': fun_ctx -> list clause -> Prop -> Prop :=
| interp_goal_nil: forall Gf,
    interp_goal'' Gf nil False
| interp_goal_cons: forall Gf c cs P Ps,
    interp_clause Gf c P ->
    interp_goal'' Gf cs Ps ->
    interp_goal'' Gf (c :: cs) (P -> Ps).

Inductive interp_goal': fun_ctx -> list clause -> Prop -> Prop :=
| interp_goal_done: forall Gf c P,
    interp_goal'' Gf c P ->
    interp_goal' Gf c P
| interp_forall_fun: forall Gf c (A B: Type) (P: (A -> B) -> Prop) fresh,
    (forall T v, ~ Gf fresh T v) ->
    (forall (f: A -> B), interp_goal' (cons_ctx Gf fresh (A -> B) f) c (P f)) ->
    interp_goal' Gf c (forall (f: A -> B), P f).

Definition interp_goal: list clause -> Prop -> Prop := interp_goal' empty_ctx.


Lemma interp_goal_herbrand_sound: forall g P,
    interp_goal g P ->
    goal_unsatisfiable g ->
    P.
Admitted.

(* tells if goal is satisfiable *)
Definition prover(g: goal): bool. Admitted.

Theorem prover_sound: forall g, prover g = false -> goal_unsatisfiable g.
Admitted.

(* this goal does not hold, but that's how we'd prove goals *)
Lemma test2: forall (P: (nat * (nat * unit)) -> Prop),
    (forall a b c, ~ P (a, (b, tt)) \/ ~ P (b, (c, tt)) \/ P (a, (c, tt)) \/ False) ->
    False.
Proof.
  eapply interp_goal_herbrand_sound.

  (* Reification: TODO automate *)
  { eapply interp_forall_fun with (fresh := 0). { cbv. auto. }
    intros.
    eapply interp_goal_done.
    eapply interp_goal_cons; [|eapply interp_goal_nil].
  eapply interp_forall with (fresh := 0). { cbv. auto. }
  intros.
  eapply interp_forall with (fresh := 1). { cbv. auto. }
  intros.
  eapply interp_forall with (fresh := 2). { cbv. auto. }
  intros.
  eapply interp_done.
  repeat eapply interp_or.
  { eapply interp_Neg.
    eapply interp_fun with (name := 0); cycle 1.
    - eapply interp_cons.
      + eapply interp_var with (x := 0). cbv. apply Refl.
      + eapply interp_cons.
        * eapply interp_var with (x := 1). cbv. apply Refl.
        * eapply interp_nil.
    - cbv. apply Refl. }
  { eapply interp_Neg.
    eapply interp_fun with (name := 0); cycle 1.
    - eapply interp_cons.
      + eapply interp_var with (x := 1). cbv. apply Refl.
      + eapply interp_cons.
        * eapply interp_var with (x := 2). cbv. apply Refl.
        * eapply interp_nil.
    - cbv. apply Refl. }
  { eapply interp_Pos.
    eapply interp_fun with (name := 0); cycle 1.
    - eapply interp_cons.
      + eapply interp_var with (x := 0). cbv. apply Refl.
      + eapply interp_cons.
        * eapply interp_var with (x := 2). cbv. apply Refl.
        * eapply interp_nil.
    - cbv. apply Refl. }
  { eapply interp_False. } }

  apply prover_sound.

  (* now if "prover" was implemented, we could just run "vm_compute", which would
     reduce the goal to "false = false", and then apply "reflexivity" *)

Admitted.
