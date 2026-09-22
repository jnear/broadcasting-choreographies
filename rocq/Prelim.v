(** * Preliminaries (Section 1.1 of the paper)

    The paper fixes a set of process names, a set of variables, a set of
    values and a language of local expressions with total, deterministic
    evaluation (Assumption 1.1).  We bundle all of these parameters in a
    single record [lang].  Guards of conditionals form a separate syntactic
    class [BExpr] whose evaluation returns a boolean; this realises the second
    half of Assumption 1.1 (guards always evaluate to booleans). *)

From Stdlib Require Import List Bool.
Import ListNotations.

Record lang := {
  P : Type;
  P_eq_dec : forall p q : P, {p = q} + {p <> q};
  Var : Type;
  Var_eq_dec : forall x y : Var, {x = y} + {x <> y};
  Val : Type;
  Expr : Type;
  eval : Expr -> (Var -> Val) -> Val;
  BExpr : Type;
  beval : BExpr -> (Var -> Val) -> bool
}.

(** [sel v a1 a2] is the paper's [a_v]: [a1] if [v = true], [a2] otherwise. *)
Definition sel {A : Type} (v : bool) (a1 a2 : A) : A :=
  if v then a1 else a2.

Section Prelim.
Context {L : lang}.

(** ** Decidable equality on process names, as a boolean *)

Definition P_eqb (p q : P L) : bool :=
  if P_eq_dec L p q then true else false.

Lemma P_eqb_spec p q : reflect (p = q) (P_eqb p q).
Proof.
  unfold P_eqb; destruct (P_eq_dec L p q); constructor; auto.
Qed.

Lemma P_eqb_refl p : P_eqb p p = true.
Proof. destruct (P_eqb_spec p p); congruence. Qed.

Lemma P_eqb_neq p q : p <> q -> P_eqb p q = false.
Proof. intros H; destruct (P_eqb_spec p q); congruence. Qed.

(** Boolean list membership. *)
Definition inb (p : P L) (l : list (P L)) : bool :=
  existsb (P_eqb p) l.

Lemma inb_spec p l : reflect (In p l) (inb p l).
Proof.
  unfold inb.
  destruct (existsb (P_eqb p) l) eqn:E; constructor.
  - apply existsb_exists in E as [q [Hq Heq]].
    destruct (P_eqb_spec p q); subst; auto; discriminate.
  - intros Hin.
    assert (existsb (P_eqb p) l = true) as E'.
    { apply existsb_exists; exists p; split; auto using P_eqb_refl. }
    congruence.
Qed.

Lemma inb_true p l : In p l -> inb p l = true.
Proof. intros H; destruct (inb_spec p l); tauto. Qed.

Lemma inb_false p l : ~ In p l -> inb p l = false.
Proof. intros H; destruct (inb_spec p l); tauto. Qed.

(** ** Stores *)

(** A local store maps variables to values; a (global) store maps each
    process to its local store. *)
Definition lstore := Var L -> Val L.
Definition store := P L -> lstore.

(** [upd s p x v] is the paper's [s[p.x |-> v]]. *)
Definition upd (s : store) (p : P L) (x : Var L) (v : Val L) : store :=
  fun r =>
    if P_eq_dec L r p
    then (fun y => if Var_eq_dec L y x then v else s r y)
    else s r.

Lemma upd_other s p x v r : r <> p -> upd s p x v r = s r.
Proof.
  intros H; unfold upd; destruct (P_eq_dec L r p); congruence.
Qed.

Lemma upd_same s p x v : upd s p x v p = fun y => if Var_eq_dec L y x then v else s p y.
Proof.
  unfold upd; destruct (P_eq_dec L p p); congruence.
Qed.

End Prelim.
