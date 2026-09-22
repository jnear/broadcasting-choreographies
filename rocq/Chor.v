(** * Choreographies (Section 1 of the paper) *)

From Stdlib Require Import List Bool.
Import ListNotations.
From Choreasy Require Import Prelim.

Section Chor.
Context {L : lang}.

(** ** Syntax (Definition 1.2) *)

Inductive action : Type :=
| ALocal (p : P L) (x : Var L) (e : Expr L)          (* p.x := e *)
| ACom   (p : P L) (e : Expr L) (q : P L) (x : Var L). (* p.e -> q.x *)

Inductive chor : Type :=
| CNil                                                   (* 0 *)
| CAct (eta : action) (C : chor)                          (* eta ; C *)
| CIf  (p : P L) (e : BExpr L) (C1 C2 : chor).            (* if p.e then C1 else C2 *)

(** The grammar requires [p <> q] in a communication.  We record this side
    condition as a well-formedness predicate. *)
Definition wf_act (eta : action) : Prop :=
  match eta with
  | ALocal _ _ _ => True
  | ACom p _ q _ => p <> q
  end.

Fixpoint wf (C : chor) : Prop :=
  match C with
  | CNil => True
  | CAct eta C => wf_act eta /\ wf C
  | CIf _ _ C1 C2 => wf C1 /\ wf C2
  end.

(** ** Process names (Definition 1.4) *)

Definition pn_act (eta : action) : list (P L) :=
  match eta with
  | ALocal p _ _ => [p]
  | ACom p _ q _ => [p; q]
  end.

Fixpoint pn (C : chor) : list (P L) :=
  match C with
  | CNil => []
  | CAct eta C => pn_act eta ++ pn C
  | CIf p _ C1 C2 => p :: pn C1 ++ pn C2
  end.

(** The receivers of a conditional at [p] with branches [C1], [C2]:
    [(pn C1 U pn C2) \ {p}]. *)
Definition receivers (p : P L) (C1 C2 : chor) : list (P L) :=
  nodup (P_eq_dec L) (filter (fun q => negb (P_eqb q p)) (pn C1 ++ pn C2)).

Lemma receivers_spec p C1 C2 q :
  In q (receivers p C1 C2) <-> (In q (pn C1) \/ In q (pn C2)) /\ q <> p.
Proof.
  unfold receivers. rewrite nodup_In, filter_In, in_app_iff.
  split.
  - intros [Hin Hneq]. split; auto.
    destruct (P_eqb_spec q p); simpl in Hneq; congruence.
  - intros [Hin Hneq]. split; auto.
    rewrite P_eqb_neq; auto.
Qed.

Lemma pn_if_iff p e C1 C2 r :
  In r (pn (CIf p e C1 C2)) <-> r = p \/ In r (receivers p C1 C2).
Proof.
  simpl. rewrite in_app_iff, receivers_spec.
  destruct (P_eq_dec L r p); subst; [ tauto | ].
  split.
  - intros [Heq | Hin]; [ congruence | tauto ].
  - intros [Heq | [Hin _]]; [ congruence | tauto ].
Qed.

(** ** Labels (Definition 1.5) *)

Inductive label : Type :=
| LTau  (p : P L)                 (* tau@p *)
| LCom  (p q : P L)               (* p -> q *)
| LCast (p : P L) (Q : list (P L)). (* p ~> Q *)

Definition pn_lbl (mu : label) : list (P L) :=
  match mu with
  | LTau p => [p]
  | LCom p q => [p; q]
  | LCast p Q => p :: Q
  end.

(** ** Semantics (Definition 1.6, Figure 1) *)

Inductive cstep : chor -> store -> label -> chor -> store -> Prop :=
| CLocal p x e C s :
    cstep (CAct (ALocal p x e) C) s (LTau p)
          C (upd s p x (eval L e (s p)))
| CCom p e q x C s :
    cstep (CAct (ACom p e q x) C) s (LCom p q)
          C (upd s q x (eval L e (s p)))
| CCast p e C1 C2 s :
    cstep (CIf p e C1 C2) s (LCast p (receivers p C1 C2))
          (sel (beval L e (s p)) C1 C2) s
| CDelay eta C s mu C' s' :
    cstep C s mu C' s' ->
    (forall r, In r (pn_act eta) -> ~ In r (pn_lbl mu)) ->
    cstep (CAct eta C) s mu (CAct eta C') s'.

(** ** Lemma 1.7 (Store locality) *)

Lemma cstep_store_locality C s mu C' s' :
  cstep C s mu C' s' ->
  forall r, ~ In r (pn_lbl mu) -> s' r = s r.
Proof.
  induction 1; intros r Hr; simpl in *.
  - apply upd_other; intuition.
  - apply upd_other; intuition.
  - reflexivity.
  - auto.
Qed.

(** ** Remark 1.5 (No delay through a conditional)

    The only step a conditional can take is [CCast]. *)
Lemma cstep_if_inv p e C1 C2 s mu C' s' :
  cstep (CIf p e C1 C2) s mu C' s' ->
  mu = LCast p (receivers p C1 C2) /\
  C' = sel (beval L e (s p)) C1 C2 /\
  s' = s.
Proof.
  intros H; inversion H; subst; auto.
Qed.

(** Well-formedness is preserved by steps. *)
Lemma cstep_wf C s mu C' s' :
  cstep C s mu C' s' -> wf C -> wf C'.
Proof.
  induction 1; simpl; intros; try tauto.
  destruct (beval L e (s p)); simpl; tauto.
Qed.

(** Every label involves at least one process. *)
Lemma pn_lbl_nonempty mu : exists r, In r (pn_lbl mu).
Proof.
  destruct mu; simpl; eexists; left; reflexivity.
Qed.

End Chor.

(** Bidirectionality hints: when the expected type is known, use it to
    determine the language parameter before elaborating the arguments. *)
Arguments ALocal {L} & _ _ _.
Arguments ACom {L} & _ _ _ _.
Arguments CNil {L}.
Arguments CAct {L} & _ _.
Arguments CIf {L} & _ _ _ _.
Arguments LTau {L} & _.
Arguments LCom {L} & _ _.
Arguments LCast {L} & _ _.
