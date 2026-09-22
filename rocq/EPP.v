(** * Endpoint projection (Section 3 of the paper) *)

From Stdlib Require Import List Bool.
Import ListNotations.
From Choreasy Require Import Prelim Chor Net.

Section EPP.
Context {L : lang}.

(** ** Definition 3.1 (Endpoint projection) *)

Fixpoint proj (C : chor) (r : P L) : behaviour :=
  match C with
  | CNil => BNil
  | CAct (ALocal p x e) C =>
      if P_eq_dec L r p then BLocal x e (proj C r) else proj C r
  | CAct (ACom p e q x) C =>
      if P_eq_dec L r p then BSend q e (proj C r)
      else if P_eq_dec L r q then BRecv p x (proj C r)
      else proj C r
  | CIf p e C1 C2 =>
      if P_eq_dec L r p then BSendBr (receivers p C1 C2) e (proj C1 p) (proj C2 p)
      else if inb r (receivers p C1 C2) then BRecvBr p (proj C1 r) (proj C2 r)
      else BNil
  end.

(** The projection of a choreography is the network of its projections. *)
Definition projn (C : chor) : network := fun r => proj C r.

(** ** Unfolding lemmas for the projection of a prefix *)

Lemma proj_local_same p x e C :
  proj (CAct (ALocal p x e) C) p = BLocal x e (proj C p).
Proof. simpl; destruct (P_eq_dec L p p); congruence. Qed.

Lemma proj_com_sender p e q x C :
  proj (CAct (ACom p e q x) C) p = BSend q e (proj C p).
Proof. simpl; destruct (P_eq_dec L p p); congruence. Qed.

Lemma proj_com_receiver p e q x C :
  q <> p -> proj (CAct (ACom p e q x) C) q = BRecv p x (proj C q).
Proof.
  intros Hqp; simpl.
  destruct (P_eq_dec L q p); [ congruence | ].
  destruct (P_eq_dec L q q); congruence.
Qed.

Lemma proj_if_sender p e C1 C2 :
  proj (CIf p e C1 C2) p = BSendBr (receivers p C1 C2) e (proj C1 p) (proj C2 p).
Proof. simpl; destruct (P_eq_dec L p p); congruence. Qed.

Lemma proj_if_receiver p e C1 C2 q :
  In q (receivers p C1 C2) ->
  proj (CIf p e C1 C2) q = BRecvBr p (proj C1 q) (proj C2 q).
Proof.
  intros Hq; simpl.
  assert (q <> p) by (apply receivers_spec in Hq; tauto).
  destruct (P_eq_dec L q p); [ congruence | ].
  rewrite inb_true by assumption. reflexivity.
Qed.

Lemma proj_if_other p e C1 C2 r :
  r <> p -> ~ In r (receivers p C1 C2) ->
  proj (CIf p e C1 C2) r = BNil.
Proof.
  intros Hrp Hr; simpl.
  destruct (P_eq_dec L r p); [ congruence | ].
  rewrite inb_false by assumption. reflexivity.
Qed.

(** ** Lemma 4.3 (Projection of prefixes) *)

(** (i) A process not involved in [eta] does not see it. *)
Lemma proj_act_skip eta C r :
  ~ In r (pn_act eta) -> proj (CAct eta C) r = proj C r.
Proof.
  destruct eta as [p x e | p e q x]; simpl; intros Hr.
  - destruct (P_eq_dec L r p); [ subst; tauto | reflexivity ].
  - destruct (P_eq_dec L r p); [ subst; tauto | ].
    destruct (P_eq_dec L r q); [ subst; tauto | reflexivity ].
Qed.

(** (ii) A process not occurring in [C] projects to [BNil]. *)
Lemma proj_nil_of_not_pn C r :
  ~ In r (pn C) -> proj C r = BNil.
Proof.
  induction C as [ | eta C IH | p e C1 IH1 C2 IH2 ]; intros Hr; simpl in Hr.
  - reflexivity.
  - rewrite in_app_iff in Hr.
    rewrite proj_act_skip by tauto. apply IH; tauto.
  - apply proj_if_other.
    + intros ->; apply Hr; left; reflexivity.
    + intros Hin. apply receivers_spec in Hin.
      rewrite in_app_iff in Hr. tauto.
Qed.

(** If [r] is involved in [eta], the projections of [eta ; C] and [eta ; C']
    onto [r] have the same prefix, so they are equal whenever the projections
    of [C] and [C'] are. *)
Lemma proj_act_congr eta C C' r :
  proj C r = proj C' r -> proj (CAct eta C) r = proj (CAct eta C') r.
Proof.
  intros Heq; destruct eta as [p x e | p e q x]; simpl.
  - destruct (P_eq_dec L r p); congruence.
  - destruct (P_eq_dec L r p); [ congruence | ].
    destruct (P_eq_dec L r q); congruence.
Qed.

(** ** Lemma 4.4 (Projection invariance) *)

Lemma proj_invariance C s mu C' s' :
  cstep C s mu C' s' ->
  forall r, ~ In r (pn_lbl mu) -> proj C' r = proj C r.
Proof.
  induction 1 as [ p x e C s | p e q x C s | p e C1 C2 s | eta C s mu C' s' Hstep IH Hdisj ];
    intros r Hr; simpl in Hr.
  - rewrite proj_act_skip; [ reflexivity | simpl; tauto ].
  - rewrite proj_act_skip; [ reflexivity | simpl; tauto ].
  - assert (Hnot : ~ In r (pn (CIf p e C1 C2))).
    { rewrite pn_if_iff. intros [-> | Hin]; apply Hr; [ left; reflexivity | right; assumption ]. }
    rewrite (proj_nil_of_not_pn (CIf p e C1 C2) r Hnot).
    apply proj_nil_of_not_pn.
    intros Hin; apply Hnot; simpl; right; rewrite in_app_iff.
    destruct (beval L e (s p)); simpl in Hin; tauto.
  - apply proj_act_congr. apply IH; assumption.
Qed.

End EPP.
