Require Import ZArith.Znat ZArith.BinInt Lists.List.
Require Import Autosubst.Autosubst.

(** * PCF *)

(**
  In this section we introduce the language PCF. We define its syntax, its
  type-system, and its operational semantics.

  In order to not have to worry about substitution and alpha-equivalence we use
  de Bruijn indices. This means that lambda's do not include a variable name. To
  manage the de Bruijn indices we use the autosubst library. This library gives
  us a lot of things for free.
*)

(** We first define the syntax of the types of the programming language. *)
Inductive type :=
| TNat
| TFun (a b : type).

(** We define some handy notation for the types. *)

Declare Scope pcf_type_scope.
Delimit Scope pcf_type_scope with T.
Bind Scope pcf_type_scope with type.

Notation "'N'" := (TNat) : pcf_type_scope.
Notation "A -> B" := (TFun A B) (at level 99, B at level 200, right associativity) : pcf_type_scope.

(** The syntax of PCF. Note the curly braces in the [Lam], these create a binder
    through the autosubst library. *)
Inductive term :=
| Var (x : var)                            (* variables *)
| App (e1 e2 : term)                       (* lambda abstraction *)
| Lam (t: type) (s : {bind term})          (* application *)
| Y (x : term)                             (* the Y-combinator *)
| Zero                                     (* zero *)
| Succ (x : term)                          (* succ *)
| Pred (x : term)                          (* pred *)
| Ifz (ec et el : term).                   (* if zero *)

(** Next we must write a bit of boilerplate for autosubst. *)
Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** We want a nice way to write PCF terms in Coq so we declare a notation scope. *)

Declare Scope term_scope.
Delimit Scope term_scope with E.
Bind Scope term_scope with term.

(** Converts a nat into a term. This function is the same as the underline
    notation that Streicher uses. *)
Fixpoint of_nat (n : nat) : term :=
  match n with
  | O => Zero
  | S n => Succ (of_nat n)
  end.

(** We now introduce notation for the PCF term. Note that in the notation for
    lambda the thing proceeding the [λ] is a type and not a variable name. *)
Notation "#v x" := (Var x) (at level 80) : term_scope.
Notation "# n" := (of_nat n) (at level 8) : term_scope.
Notation "'λ' t ',' e" := (Lam t e) (at level 80) : term_scope.
Notation "'ifz' cond 'then' e1 'else' e2" := (Ifz cond e1 e2) (at level 70) : term_scope.
Notation "e1 $ e2" := (App e1 e2) (at level 80) : term_scope.

(** Converts a term into a Z. *)
Fixpoint to_Z (e : term) : option Z :=
  match e with
  | Zero => Some 0%Z
  | Succ e' =>
    match to_Z e' with | None => None | Some n => Some (1 + n)%Z end
  | _ => None
  end.

Definition of_Z (z : Z) : term := of_nat (Z.to_nat z).

(** By creating a numberal notation we can write numerals/literals to denote
    terms. Note that this only lets us write constants, e.g., [3], for a term,
    not [n] for any natural number. For that we use [#n]. *)
Numeral Notation term of_Z to_Z : term_scope.

(** We now define the small-steps operational semantics of the programming
    language. *)

(** ** Big step semantics. *)

Reserved Notation "e1 ⇓ e2" (at level 50).

Inductive step : term -> term -> Prop :=
(** Base cases *)
| Step_var x : Var x ⇓ Var x
| Step_lam t e : (λ t, e) ⇓ λ t, e
| Step_zero : 0 ⇓ 0
(** Inductive cases. *)
| Step_app f e v : f.[e/] ⇓ v -> (f $ e) ⇓ v
| Step_y f e : (f $ Y f) ⇓ e -> Y f ⇓ e
| Step_succ e (n : nat) : e ⇓ #n -> Succ e ⇓ #(n + 1)
| Step_pred_zero e : e ⇓ #0 -> Pred e ⇓ #0
| Step_pred_succ e n : e ⇓ #(n + 1) -> Pred e ⇓ #n 
| Step_ifz_zero e1 e2 e3 : e1 ⇓ 0 -> (ifz e1 then e2 else e3) ⇓ e1
| Step_ifz_succ e1 n e2 e3 : e1 ⇓ #(n + 1) -> (ifz e1 then e2 else e3) ⇓ e2
where "e1 ⇓ e2" := (step e1 e2).

(** We can now do our first proof: Show that the operational semantics are
    deterministic. *)
Lemma operational_semantics_deterministic e v v' :
  e ⇓ v -> e ⇓ v' -> v = v'.
Proof.
  intros Hv Hv'.
  (** We do induction in the first evaluation derivation. *)
  induction Hv.
  (** The base cases are fairly trivial. By inversion we can conclude that the
    evaluation derivation for [v'] must have been constructed using the same
    rule. *)
  - inversion Hv'. reflexivity.
  - inversion Hv'. reflexivity.
  - inversion Hv'. reflexivity.
  - (** If the evaluation is that for an application ... *)
    inversion Hv'. apply IHHv. assumption.
  - inversion Hv'. apply IHHv. assumption.
  - inversion Hv'. subst. admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(* Since we use de Bruijn indices a context is just a list. *)
Definition context := list type.

Implicit Type Γ : context.

Reserved Notation "g '⊢' e ':' t" (at level 40, e at next level, t at level 0).

Inductive ty (Γ : context) : term -> type -> Prop :=
| Ty_Var x A : (nth_error Γ x = Some A) -> Γ ⊢ Var x : A
| Ty_App f a A B : (Γ ⊢ f : (A -> B)) -> (Γ ⊢ a : A) -> Γ ⊢ (f $ a) : B
| Ty_Lam e A B : (A :: Γ) ⊢ e : B -> Γ ⊢ (λ A, e) : (A -> B)
| Ty_Y e A : Γ ⊢ e : (A -> A) -> Γ ⊢ Y e : A
| Ty_Zero : Γ ⊢ 0 : N
| Ty_Succ n : (Γ ⊢ n : N) -> Γ ⊢ Succ n : N
| Ty_Pred n : (Γ ⊢ n : N) -> Γ ⊢ Succ n : N
| Ty_Ifz e1 e2 e3 A :
    (ty Γ e1 N) -> (ty Γ e2 A) -> (ty Γ e2 A) -> ty Γ (ifz e1 then e2 else e3) A
where "g '⊢' e ':' t" := (ty g e t).

(** * The Scott Model of PCF *)

