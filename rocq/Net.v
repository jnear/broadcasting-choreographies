(** * Network processes (Section 2 of the paper) *)

From Stdlib Require Import List Bool.
Import ListNotations.
From Choreasy Require Import Prelim Chor.

Section Net.
Context {L : lang}.

(** ** Syntax (Definition 2.1) *)

Inductive behaviour : Type :=
| BNil                                                        (* 0 *)
| BLocal  (x : Var L) (e : Expr L) (B : behaviour)             (* x := e ; B *)
| BSend   (q : P L) (e : Expr L) (B : behaviour)               (* q!e ; B *)
| BRecv   (p : P L) (x : Var L) (B : behaviour)                (* p?x ; B *)
| BSendBr (Q : list (P L)) (e : BExpr L) (B1 B2 : behaviour)   (* Q!e |> (B1, B2) *)
| BRecvBr (p : P L) (B1 B2 : behaviour).                       (* p?(B1, B2) *)

(** A network is a total function from process names to behaviours. *)
Definition network : Type := P L -> behaviour.

Definition terminated (N : network) : Prop := forall r, N r = BNil.

(** [N] and [M] agree on every process in [S]. *)
Definition agree_on (S : list (P L)) (N M : network) : Prop :=
  forall r, In r S -> N r = M r.

(** ** Semantics (Definition 2.2, Figure 2)

    Since networks are functions, each rule characterises the target network
    pointwise: it fixes the behaviours of the processes involved in the label
    and requires every other process to be unchanged. *)

Inductive nstep : network -> store -> label -> network -> store -> Prop :=
| NLocal N N' s p x e B :
    N p = BLocal x e B ->
    N' p = B ->
    (forall r, r <> p -> N' r = N r) ->
    nstep N s (LTau p) N' (upd s p x (eval L e (s p)))
| NCom N N' s p q e B x B' :
    p <> q ->
    N p = BSend q e B ->
    N q = BRecv p x B' ->
    N' p = B ->
    N' q = B' ->
    (forall r, r <> p -> r <> q -> N' r = N r) ->
    nstep N s (LCom p q) N' (upd s q x (eval L e (s p)))
| NCast N N' s p Q e B1 B2 :
    N p = BSendBr Q e B1 B2 ->
    (forall q, In q Q ->
       exists B1' B2', N q = BRecvBr p B1' B2' /\
                       N' q = sel (beval L e (s p)) B1' B2') ->
    N' p = sel (beval L e (s p)) B1 B2 ->
    (forall r, r <> p -> ~ In r Q -> N' r = N r) ->
    nstep N s (LCast p Q) N' s.

(** Inversion on [nstep] with fixed hypothesis names:
    - [HNp] : behaviour of the sender/subject in [N];
    - [HNq] : behaviour of the receiver in [N] (communication only);
    - [HN'p], [HN'q] : behaviours afterwards;
    - [Hrecv] : receivers of a multicast;
    - [Hoth] : all other processes unchanged. *)
Ltac inv_nstep H :=
  inversion H as
    [ N0 N'0 s0 p0 x0 e0 B0 HNp HN'p Hoth
    | N0 N'0 s0 p0 q0 e0 B0 x0 B'0 Hpq HNp HNq HN'p HN'q Hoth
    | N0 N'0 s0 p0 Q0 e0 B10 B20 HNp Hrecv HN'p Hoth ];
  subst; clear H.

(** In a multicast the sender is not among the receivers (it cannot have two
    different behaviours), so the side condition [p notin Q] of Definition 1.5
    is derivable. *)
Lemma nstep_cast_sender_not_receiver N s p Q N' s' :
  nstep N s (LCast p Q) N' s' -> ~ In p Q.
Proof.
  intros H; inv_nstep H.
  intros Hin. destruct (Hrecv p Hin) as [B1' [B2' [Heq _]]]. congruence.
Qed.

(** ** Lemma 4.1 (Network locality and framing) *)

Lemma nstep_locality N s mu N' s' :
  nstep N s mu N' s' ->
  forall r, ~ In r (pn_lbl mu) -> N' r = N r /\ s' r = s r.
Proof.
  intros H r Hr; inv_nstep H; simpl in Hr.
  - split; [ apply Hoth | apply upd_other ]; intuition.
  - split; [ apply Hoth | apply upd_other ]; intuition.
  - split; [ apply Hoth | reflexivity ]; intuition.
Qed.

(** Framing, general form: a step is determined by the behaviours of the
    processes in its label.  Any network [M] that agrees with [N] on
    [pn mu] can take the same step, to any [M'] that agrees with [N'] on
    [pn mu] and with [M] elsewhere. *)
Lemma nstep_frame_gen N s mu N' s' M M' :
  nstep N s mu N' s' ->
  agree_on (pn_lbl mu) M N ->
  agree_on (pn_lbl mu) M' N' ->
  (forall r, ~ In r (pn_lbl mu) -> M' r = M r) ->
  nstep M s mu M' s'.
Proof.
  intros H HM HM' Hoth'.
  inv_nstep H; simpl in *.
  - eapply NLocal.
    + rewrite HM; [ eassumption | simpl; auto ].
    + rewrite HM' by (simpl; auto). congruence.
    + intros r Hr. apply Hoth'; simpl; intuition.
  - eapply NCom; try eassumption.
    + rewrite HM; [ eassumption | simpl; auto ].
    + rewrite HM; [ eassumption | simpl; auto ].
    + rewrite HM' by (simpl; auto). congruence.
    + rewrite HM' by (simpl; auto). congruence.
    + intros r Hr1 Hr2. apply Hoth'; simpl; intuition.
  - eapply NCast.
    + rewrite HM; [ eassumption | simpl; auto ].
    + intros q Hq. destruct (Hrecv q Hq) as [B1' [B2' [HNq HN'q]]].
      exists B1', B2'. split.
      * rewrite HM by (simpl; auto). assumption.
      * rewrite HM' by (simpl; auto). assumption.
    + rewrite HM' by (simpl; auto). congruence.
    + intros r Hr1 Hr2. apply Hoth'; simpl; intuition.
Qed.

(** Lemma 4.1 (ii) as stated in the paper. *)
Lemma nstep_frame N s mu N' s' M :
  nstep N s mu N' s' ->
  agree_on (pn_lbl mu) M N ->
  exists M',
    nstep M s mu M' s' /\
    agree_on (pn_lbl mu) M' N' /\
    (forall r, ~ In r (pn_lbl mu) -> M' r = M r).
Proof.
  intros H Hag.
  exists (fun r => if inb r (pn_lbl mu) then N' r else M r).
  split; [ | split ].
  - eapply nstep_frame_gen; try eassumption.
    + intros r Hr. cbv beta. rewrite inb_true by assumption. reflexivity.
    + intros r Hr. cbv beta. rewrite inb_false by assumption. reflexivity.
  - intros r Hr. cbv beta. rewrite inb_true by assumption. reflexivity.
  - intros r Hr. cbv beta. rewrite inb_false by assumption. reflexivity.
Qed.

(** ** Lemma 4.2 (Inversion for networks)

    Given a step and a process [r] involved in its label, the shape of [N r]
    determines the rule, the label, the behaviour of [r] afterwards and the
    store change. *)

Lemma nstep_inv_nonnil N s mu N' s' r :
  nstep N s mu N' s' -> In r (pn_lbl mu) -> N r <> BNil.
Proof.
  intros H Hr; inv_nstep H; simpl in Hr.
  - destruct Hr as [-> | []]. congruence.
  - destruct Hr as [-> | [-> | []]]; congruence.
  - destruct Hr as [-> | Hr]; [ congruence | ].
    destruct (Hrecv r Hr) as [B1' [B2' [-> _]]]. discriminate.
Qed.

Lemma nstep_inv_local N s mu N' s' r x e B :
  nstep N s mu N' s' -> In r (pn_lbl mu) ->
  N r = BLocal x e B ->
  mu = LTau r /\ N' r = B /\ s' = upd s r x (eval L e (s r)).
Proof.
  intros H Hr HN; inv_nstep H; simpl in Hr.
  - destruct Hr as [-> | []]. rewrite HN in HNp; inversion HNp; subst; auto.
  - destruct Hr as [-> | [-> | []]]; congruence.
  - destruct Hr as [-> | Hr]; [ congruence | ].
    destruct (Hrecv r Hr) as [B1' [B2' [Heq _]]]; congruence.
Qed.

Lemma nstep_inv_send N s mu N' s' r q e B :
  nstep N s mu N' s' -> In r (pn_lbl mu) ->
  N r = BSend q e B ->
  mu = LCom r q /\ r <> q /\
  exists x B', N q = BRecv r x B' /\ N' r = B /\ N' q = B' /\
               s' = upd s q x (eval L e (s r)).
Proof.
  intros H Hr HN; inv_nstep H; simpl in Hr.
  - destruct Hr as [-> | []]; congruence.
  - destruct Hr as [-> | [-> | []]]; [ | congruence ].
    rewrite HN in HNp; inversion HNp; subst.
    split; [ reflexivity | split; [ assumption | ] ].
    do 2 eexists; repeat split; eauto.
  - destruct Hr as [-> | Hr]; [ congruence | ].
    destruct (Hrecv r Hr) as [B1' [B2' [Heq _]]]; congruence.
Qed.

Lemma nstep_inv_recv N s mu N' s' r p x B :
  nstep N s mu N' s' -> In r (pn_lbl mu) ->
  N r = BRecv p x B ->
  mu = LCom p r /\ p <> r /\
  exists e B', N p = BSend r e B' /\ N' r = B /\ N' p = B' /\
               s' = upd s r x (eval L e (s p)).
Proof.
  intros H Hr HN; inv_nstep H; simpl in Hr.
  - destruct Hr as [-> | []]; congruence.
  - destruct Hr as [-> | [-> | []]]; [ congruence | ].
    rewrite HN in HNq; inversion HNq; subst.
    split; [ reflexivity | split; [ assumption | ] ].
    do 2 eexists; repeat split; eauto.
  - destruct Hr as [-> | Hr]; [ congruence | ].
    destruct (Hrecv r Hr) as [B1' [B2' [Heq _]]]; congruence.
Qed.

Lemma nstep_inv_sendbr N s mu N' s' r Q e B1 B2 :
  nstep N s mu N' s' -> In r (pn_lbl mu) ->
  N r = BSendBr Q e B1 B2 ->
  mu = LCast r Q /\ s' = s /\
  N' r = sel (beval L e (s r)) B1 B2 /\
  (forall q, In q Q ->
     exists B1' B2', N q = BRecvBr r B1' B2' /\
                     N' q = sel (beval L e (s r)) B1' B2').
Proof.
  intros H Hr HN; inv_nstep H; simpl in Hr.
  - destruct Hr as [-> | []]; congruence.
  - destruct Hr as [-> | [-> | []]]; congruence.
  - destruct Hr as [-> | Hr].
    + rewrite HN in HNp; inversion HNp; subst. auto.
    + destruct (Hrecv r Hr) as [B1' [B2' [Heq _]]]; congruence.
Qed.

Lemma nstep_inv_recvbr N s mu N' s' r p B1 B2 :
  nstep N s mu N' s' -> In r (pn_lbl mu) ->
  N r = BRecvBr p B1 B2 ->
  exists Q e B1' B2',
    mu = LCast p Q /\ In r Q /\ s' = s /\
    N p = BSendBr Q e B1' B2' /\
    N' r = sel (beval L e (s p)) B1 B2.
Proof.
  intros H Hr HN; inv_nstep H; simpl in Hr.
  - destruct Hr as [-> | []]; congruence.
  - destruct Hr as [-> | [-> | []]]; congruence.
  - destruct Hr as [-> | Hr]; [ congruence | ].
    destruct (Hrecv r Hr) as [B1' [B2' [Heq HN'r]]].
    rewrite HN in Heq; inversion Heq; subst.
    do 4 eexists; repeat split; eauto.
Qed.

End Net.

Arguments BNil {L}.
Arguments BLocal {L} & _ _ _.
Arguments BSend {L} & _ _ _.
Arguments BRecv {L} & _ _ _.
Arguments BSendBr {L} & _ _ _ _.
Arguments BRecvBr {L} & _ _ _.
