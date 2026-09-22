(** * Correctness of endpoint projection (Section 4 of the paper) *)

From Stdlib Require Import List Bool FunctionalExtensionality Relations.
Import ListNotations.
From Choreasy Require Import Prelim Chor Net EPP.

Section Correctness.
Context {L : lang}.

(** Fix the language parameter in the types of all binders below. *)
Local Notation chor := (@chor L).
Local Notation store := (@store L).
Local Notation label := (@label L).
Local Notation network := (@network L).
Local Notation action := (@action L).

(** Projection commutes with branch selection. *)
Lemma proj_sel (v : bool) (C1 C2 : chor) (r : P L) :
  proj (sel v C1 C2) r = sel v (proj C1 r) (proj C2 r).
Proof. destruct v; reflexivity. Qed.

(** A process outside [{p} U receivers] does not occur in the selected
    branch. *)
Lemma not_in_sel_branch (p : P L) (C1 C2 : chor) (v : bool) (r : P L) :
  r <> p -> ~ In r (receivers p C1 C2) -> ~ In r (pn (sel v C1 C2)).
Proof.
  intros Hrp Hr Hin. apply Hr. apply receivers_spec. split; auto.
  destruct v; simpl in Hin; tauto.
Qed.

(** ** Theorem 4.5 (Completeness) *)

Theorem completeness (C : chor) (s : store) (mu : label) (C' : chor) (s' : store) :
  wf C ->
  cstep C s mu C' s' ->
  nstep (projn C) s mu (projn C') s'.
Proof.
  intros Hwf H; revert Hwf.
  induction H as [ p x e C s | p e q x C s | p e C1 C2 s
                 | eta C s mu C' s' Hstep IH Hdisj ];
    intros Hwf; simpl in Hwf; unfold projn.
  - (* C|Local *)
    eapply NLocal.
    + apply proj_local_same.
    + reflexivity.
    + intros r Hr. symmetry. apply proj_act_skip. simpl; intuition.
  - (* C|Com *)
    destruct Hwf as [Hpq _].
    eapply NCom; try eassumption.
    + apply proj_com_sender.
    + apply proj_com_receiver; auto.
    + reflexivity.
    + reflexivity.
    + intros r Hr1 Hr2. symmetry. apply proj_act_skip. simpl; intuition.
  - (* C|Cast *)
    eapply NCast.
    + apply proj_if_sender.
    + intros q Hq. exists (proj C1 q), (proj C2 q). split.
      * apply proj_if_receiver; assumption.
      * apply proj_sel.
    + apply proj_sel.
    + intros r Hr1 Hr2.
      rewrite proj_if_other by assumption.
      apply proj_nil_of_not_pn.
      apply (not_in_sel_branch p C1 C2); assumption.
  - (* C|Delay *)
    destruct Hwf as [_ HwfC].
    specialize (IH HwfC).
    eapply nstep_frame_gen; [ exact IH | | | ].
    + (* projn (eta ; C) agrees with projn C on pn mu *)
      intros r Hr. apply proj_act_skip.
      intros Hin. apply (Hdisj r Hin Hr).
    + (* projn (eta ; C') agrees with projn C' on pn mu *)
      intros r Hr. apply proj_act_skip.
      intros Hin. apply (Hdisj r Hin Hr).
    + (* off pn mu, projections of eta ; C' and eta ; C agree *)
      intros r Hr. apply proj_act_congr.
      apply (proj_invariance _ _ _ _ _ Hstep); assumption.
Qed.

(** ** Theorem 4.6 (Soundness) *)

(** The sub-case of an action prefix whose processes are not involved in
    the step, handled by [C|Delay] and the induction hypothesis. *)
Lemma soundness_delay (eta : action) (C : chor) (s : store) (mu : label) (N' : network) (s' : store) :
  (forall (s : store) (mu : label) (N' : network) (s' : store),
      nstep (projn C) s mu N' s' ->
      exists C', cstep C s mu C' s' /\ N' = projn C') ->
  nstep (projn (CAct eta C)) s mu N' s' ->
  (forall r, In r (pn_act eta) -> ~ In r (pn_lbl mu)) ->
  exists C', cstep (CAct eta C) s mu C' s' /\ N' = projn C'.
Proof.
  intros IH H Hdisj.
  assert (Hag : agree_on (pn_lbl mu) (projn C) (projn (CAct eta C))).
  { intros r Hr. unfold projn. symmetry. apply proj_act_skip.
    intros Hin. apply (Hdisj r Hin Hr). }
  destruct (nstep_frame _ _ _ _ _ _ H Hag) as [N'' [H'' [Hag1 Hag2]]].
  destruct (IH _ _ _ _ H'') as [C0' [Hstep HN'']].
  exists (CAct eta C0'). split.
  - apply CDelay; assumption.
  - apply functional_extensionality; intros r. unfold projn.
    destruct (in_dec (P_eq_dec L) r (pn_lbl mu)) as [Hin | Hnin].
    + rewrite <- (Hag1 r Hin), HN''. unfold projn.
      symmetry. apply proj_act_skip.
      intros Hin'. apply (Hdisj r Hin' Hin).
    + destruct (nstep_locality _ _ _ _ _ H r Hnin) as [HN'r _].
      rewrite HN'r. unfold projn.
      apply proj_act_congr. symmetry.
      apply (proj_invariance _ _ _ _ _ Hstep); assumption.
Qed.

Theorem soundness (C : chor) (s : store) (mu : label) (N' : network) (s' : store) :
  nstep (projn C) s mu N' s' ->
  exists C', cstep C s mu C' s' /\ N' = projn C'.
Proof.
  revert s mu N' s'.
  induction C as [ | eta C IH | p e C1 IH1 C2 IH2 ]; intros s mu N' s' H.
  - (* C = 0: no transition is possible *)
    exfalso.
    destruct (pn_lbl_nonempty mu) as [r Hr].
    apply (nstep_inv_nonnil _ _ _ _ _ r H Hr). reflexivity.
  - (* C = eta ; C0 *)
    destruct eta as [ p x e | p e q x ].
    + (* eta = p.x := e *)
      destruct (in_dec (P_eq_dec L) p (pn_lbl mu)) as [Hp | Hp].
      * (* p is involved: the step is C|Local *)
        destruct (nstep_inv_local _ _ _ _ _ p x e (proj C p) H Hp
                    (proj_local_same p x e C)) as [-> [HN'p ->]].
        exists C. split; [ constructor | ].
        apply functional_extensionality; intros r. unfold projn.
        destruct (P_eq_dec L r p) as [-> | Hrp]; [ congruence | ].
        destruct (nstep_locality _ _ _ _ _ H r) as [HN'r _];
          [ simpl; intuition | ].
        rewrite HN'r. unfold projn. apply proj_act_skip. simpl; intuition.
      * (* p is not involved: delay *)
        apply soundness_delay; [ assumption | assumption | ].
        intros r Hr; simpl in Hr; destruct Hr as [-> | []]; assumption.
    + (* eta = p.e -> q.x *)
      destruct (in_dec (P_eq_dec L) p (pn_lbl mu)) as [Hp | Hp].
      * (* the sender is involved: the step is C|Com *)
        destruct (nstep_inv_send _ _ _ _ _ p q e (proj C p) H Hp
                    (proj_com_sender p e q x C))
          as [-> [Hpq [x' [B' [HNq [HN'p [HN'q ->]]]]]]].
        unfold projn in HNq.
        rewrite proj_com_receiver in HNq by auto.
        inversion HNq; subst; clear HNq.
        exists C. split; [ constructor | ].
        apply functional_extensionality; intros r. unfold projn.
        destruct (P_eq_dec L r p) as [-> | Hrp]; [ congruence | ].
        destruct (P_eq_dec L r q) as [-> | Hrq]; [ congruence | ].
        destruct (nstep_locality _ _ _ _ _ H r) as [HN'r _];
          [ simpl; intuition | ].
        rewrite HN'r. unfold projn. apply proj_act_skip. simpl; intuition.
      * destruct (in_dec (P_eq_dec L) q (pn_lbl mu)) as [Hq | Hq].
        -- (* the receiver is involved: the step is C|Com *)
           assert (Hqp : q <> p) by (intros ->; contradiction).
           destruct (nstep_inv_recv _ _ _ _ _ q p x (proj C q) H Hq
                       (proj_com_receiver p e q x C Hqp))
             as [-> [_ [e' [B' [HNp [HN'q [HN'p ->]]]]]]].
           unfold projn in HNp.
           rewrite proj_com_sender in HNp.
           inversion HNp; subst; clear HNp.
           exists C. split; [ constructor | ].
           apply functional_extensionality; intros r. unfold projn.
           destruct (P_eq_dec L r p) as [-> | Hrp]; [ congruence | ].
           destruct (P_eq_dec L r q) as [-> | Hrq]; [ congruence | ].
           destruct (nstep_locality _ _ _ _ _ H r) as [HN'r _];
             [ simpl; intuition | ].
           rewrite HN'r. unfold projn. apply proj_act_skip. simpl; intuition.
        -- (* neither is involved: delay *)
           apply soundness_delay; [ assumption | assumption | ].
           intros r Hr; simpl in Hr.
           destruct Hr as [-> | [-> | []]]; assumption.
  - (* C = if p.e then C1 else C2 *)
    set (Q := receivers p C1 C2) in *.
    (* Every involved process is p or a receiver. *)
    assert (Hinv : forall r, In r (pn_lbl mu) -> r = p \/ In r Q).
    { intros r Hr.
      destruct (P_eq_dec L r p) as [-> | Hrp]; [ left; reflexivity | right ].
      destruct (in_dec (P_eq_dec L) r Q) as [HrQ | HrQ]; [ assumption | ].
      exfalso. apply (nstep_inv_nonnil _ _ _ _ _ r H Hr).
      apply proj_if_other; assumption. }
    (* p is involved. *)
    assert (Hp : In p (pn_lbl mu)).
    { destruct (pn_lbl_nonempty mu) as [r Hr].
      destruct (Hinv r Hr) as [-> | HrQ]; [ assumption | ].
      destruct (nstep_inv_recvbr _ _ _ _ _ r p (proj C1 r) (proj C2 r) H Hr
                  (proj_if_receiver p e C1 C2 r HrQ))
        as [Q' [e' [B1' [B2' [-> _]]]]].
      simpl; left; reflexivity. }
    destruct (nstep_inv_sendbr _ _ _ _ _ p Q e (proj C1 p) (proj C2 p) H Hp
                (proj_if_sender p e C1 C2))
      as [-> [-> [HN'p Hrecv]]].
    exists (sel (beval L e (s p)) C1 C2). split; [ constructor | ].
    apply functional_extensionality; intros r. unfold projn.
    rewrite proj_sel.
    destruct (P_eq_dec L r p) as [-> | Hrp]; [ congruence | ].
    destruct (in_dec (P_eq_dec L) r Q) as [HrQ | HrQ].
    + destruct (Hrecv r HrQ) as [B1' [B2' [HNr HN'r]]].
      unfold projn in HNr. rewrite proj_if_receiver in HNr by assumption.
      inversion HNr; subst. congruence.
    + destruct (nstep_locality _ _ _ _ _ H r) as [HN'r _].
      { simpl. intros [Heq | Hin]; [ congruence | contradiction ]. }
      rewrite HN'r. unfold projn. rewrite proj_if_other by assumption.
      rewrite <- proj_sel. symmetry. apply proj_nil_of_not_pn.
      apply (not_in_sel_branch p C1 C2); assumption.
Qed.

(** ** Corollary 4.7 (Bisimulation) *)

(** The relation [B] of the paper: a choreographic configuration is related
    to its projection (with the same store).  Well-formedness records the
    grammar's side condition [p <> q] on communications. *)
Definition bisim_rel (c : chor * store) (n : network * store) : Prop :=
  wf (fst c) /\ n = (projn (fst c), snd c).

Corollary bisimulation_forward (C : chor) (s : store) (N : network) (mu : label) (C' : chor) (s' : store) :
  bisim_rel (C, s) (N, s) ->
  cstep C s mu C' s' ->
  exists N', nstep N s mu N' s' /\ bisim_rel (C', s') (N', s').
Proof.
  intros [Hwf Heq] Hstep; simpl in *.
  inversion Heq; subst N; clear Heq.
  exists (projn C'). split.
  - apply completeness; assumption.
  - split; [ eapply cstep_wf; eassumption | reflexivity ].
Qed.

Corollary bisimulation_backward (C : chor) (s : store) (N : network) (mu : label) (N' : network) (s' : store) :
  bisim_rel (C, s) (N, s) ->
  nstep N s mu N' s' ->
  exists C', cstep C s mu C' s' /\ bisim_rel (C', s') (N', s').
Proof.
  intros [Hwf Heq] Hstep; simpl in *.
  inversion Heq; subst N; clear Heq.
  destruct (soundness _ _ _ _ _ Hstep) as [C' [Hcstep ->]].
  exists C'. split; [ assumption | ].
  split; [ eapply cstep_wf; eassumption | reflexivity ].
Qed.

(** ** Lemma 4.8 (Progress) *)

Lemma progress (C : chor) (s : store) :
  C <> CNil -> exists mu C' s', cstep C s mu C' s'.
Proof.
  destruct C as [ | [ p x e | p e q x ] C | p e C1 C2 ]; intros Hne.
  - congruence.
  - do 3 eexists. apply CLocal.
  - do 3 eexists. apply CCom.
  - do 3 eexists. apply CCast.
Qed.

(** ** Corollary 4.9 (Deadlock-freedom by construction) *)

Definition stuck (N : network) (s : store) : Prop :=
  forall mu N' s', ~ nstep N s mu N' s'.

Lemma projn_terminated_iff (C : chor) :
  terminated (projn C) <-> C = CNil.
Proof.
  split.
  - intros Hterm.
    destruct C as [ | [ p x e | p e q x ] C | p e C1 C2 ]; [ reflexivity | .. ];
      exfalso; unfold terminated, projn in Hterm; specialize (Hterm p).
    + rewrite proj_local_same in Hterm; discriminate.
    + rewrite proj_com_sender in Hterm; discriminate.
    + rewrite proj_if_sender in Hterm; discriminate.
  - intros ->. intros r. reflexivity.
Qed.

Lemma terminated_stuck (N : network) (s : store) :
  terminated N -> stuck N s.
Proof.
  intros Hterm mu N' s' H.
  destruct (pn_lbl_nonempty mu) as [r Hr].
  apply (nstep_inv_nonnil _ _ _ _ _ r H Hr). apply Hterm.
Qed.

Lemma projn_stuck_iff_terminated (C : chor) (s : store) :
  wf C -> (stuck (projn C) s <-> terminated (projn C)).
Proof.
  intros Hwf. split.
  - intros Hstuck.
    apply projn_terminated_iff.
    destruct C as [ | eta C | p e C1 C2 ]; [ reflexivity | exfalso | exfalso ].
    + destruct (progress (CAct eta C) s) as [mu [C' [s' Hstep]]];
        [ discriminate | ].
      exact (Hstuck _ _ _ (completeness _ _ _ _ _ Hwf Hstep)).
    + destruct (progress (CIf p e C1 C2) s) as [mu [C' [s' Hstep]]];
        [ discriminate | ].
      exact (Hstuck _ _ _ (completeness _ _ _ _ _ Hwf Hstep)).
  - apply terminated_stuck.
Qed.

(** Reachability in the network transition system, forgetting labels. *)
Definition nconfig : Type := (network * store)%type.

Definition nstep_any (c c' : nconfig) : Prop :=
  exists mu, nstep (fst c) (snd c) mu (fst c') (snd c').

Definition reach : nconfig -> nconfig -> Prop :=
  clos_refl_trans nconfig nstep_any.

(** Every configuration reachable from the projection of a well-formed
    choreography is the projection of a well-formed choreography. *)
Lemma reach_proj (c c' : nconfig) :
  reach c c' ->
  forall C : chor, wf C -> fst c = projn C ->
  exists C', wf C' /\ fst c' = projn C'.
Proof.
  induction 1 as [ c c' [mu Hstep] | c | c c' c'' _ IH1 _ IH2 ];
    intros C Hwf Hc.
  - rewrite Hc in Hstep.
    destruct (soundness _ _ _ _ _ Hstep) as [C' [Hcstep ->]].
    exists C'. split; [ eapply cstep_wf; eassumption | reflexivity ].
  - exists C; auto.
  - destruct (IH1 C Hwf Hc) as [C' [Hwf' Hc']].
    apply (IH2 C' Hwf' Hc').
Qed.

Corollary deadlock_freedom (C : chor) (s : store) :
  wf C ->
  (stuck (projn C) s <-> terminated (projn C)) /\
  (terminated (projn C) <-> C = CNil) /\
  (forall N' s',
      reach (projn C, s) (N', s') ->
      terminated N' \/ exists mu N'' s'', nstep N' s' mu N'' s'').
Proof.
  intros Hwf.
  split; [ apply projn_stuck_iff_terminated; assumption | ].
  split; [ apply projn_terminated_iff | ].
  intros N' s' Hreach.
  destruct (reach_proj _ _ Hreach C Hwf eq_refl) as [C' [Hwf' HN']].
  simpl in HN'; subst N'.
  destruct C' as [ | eta C' | p e C1 C2 ].
  - left. apply projn_terminated_iff. reflexivity.
  - right. destruct (progress (CAct eta C') s') as [mu [C'' [s'' Hstep]]];
      [ discriminate | ].
    do 3 eexists. apply completeness; eassumption.
  - right. destruct (progress (CIf p e C1 C2) s') as [mu [C'' [s'' Hstep]]];
      [ discriminate | ].
    do 3 eexists. apply completeness; eassumption.
Qed.

End Correctness.

(** The only axiom used is functional extensionality (for equality of
    networks, which are functions). *)
Print Assumptions completeness.
Print Assumptions soundness.
Print Assumptions deadlock_freedom.
