(** * Correctness of endpoint projection (Section 4 of the paper) *)

From Stdlib Require Import List Bool FunctionalExtensionality Relations.
Import ListNotations.
From ChoreasyFun Require Import Prelim Chor Net EPP.

Section Correctness.
Context {L : lang} {D : @defs L}.

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

(** ** Definition 4.5 (Well-formedness)

    Every process that has not yet entered a call [Ps : X . C] must still be
    expected to behave as its local body of [X].  We call this [wf_rt], to
    distinguish it from [wf], which records the side conditions of the
    grammar. *)
Fixpoint wf_rt (C : chor) : Prop :=
  match C with
  | CNil => True
  | CAct _ C => wf_rt C
  | CIf _ _ C1 C2 => wf_rt C1 /\ wf_rt C2
  | CProc _ => True
  | CRT Ps X C => wf_rt C /\ forall r, In r Ps -> proj C r = proj (body X) r
  end.

(** Every source choreography is well-formed. *)
Lemma source_wf_rt (C : chor) : source C -> wf_rt C.
Proof. induction C; simpl; tauto. Qed.

(** The clause for runtime terms also holds for an empty set of processes,
    under the convention implemented by [rt]. *)
Lemma rt_wf_rt (Ps : list (P L)) (X : PName L) (C : chor) :
  wf_rt C ->
  (forall r, In r Ps -> proj C r = proj (body X) r) ->
  wf_rt (rt Ps X C).
Proof. intros H1 H2; destruct Ps; simpl; [ assumption | split; assumption ]. Qed.

(** ** Lemma 4.7 (Preservation of well-formedness) *)

Lemma cstep_wf_rt (C : chor) (s : store) (mu : label) (C' : chor) (s' : store) :
  cstep C s mu C' s' -> wf_rt C -> wf_rt C'.
Proof.
  induction 1 as [ p x e C s | p e q x C s | p e C1 C2 s
                 | eta C s mu C' s' Hstep IH Hdisj
                 | X p s Hp | Ps X C p s Hp
                 | Ps X C s mu C' s' Hstep IH Hdisj ];
    simpl; intros Hwf.
  - assumption.
  - assumption.
  - destruct (beval L e (s p)); simpl; tauto.
  - auto.
  - (* C|Call: the body is a source choreography *)
    apply rt_wf_rt; [ apply source_wf_rt, body_source | reflexivity ].
  - (* C|Enter *)
    destruct Hwf as [HC HPs]. apply rt_wf_rt; [ assumption | ].
    intros r Hr. apply in_remove in Hr. apply HPs; tauto.
  - (* C|Inside: the processes that have not entered are not involved *)
    destruct Hwf as [HC HPs]. split; [ auto | ].
    intros r Hr. rewrite <- (HPs r Hr).
    apply (proj_invariance _ _ _ _ _ Hstep).
    intros Hin. apply (Hdisj r Hr Hin).
Qed.

(** ** Theorem 4.8 (Completeness) *)

Theorem completeness (C : chor) (s : store) (mu : label) (C' : chor) (s' : store) :
  wf C ->
  wf_rt C ->
  cstep C s mu C' s' ->
  nstep (projn C) s mu (projn C') s'.
Proof.
  intros Hwf Hwfrt H; revert Hwf Hwfrt.
  induction H as [ p x e C s | p e q x C s | p e C1 C2 s
                 | eta C s mu C' s' Hstep IH Hdisj
                 | X p s Hp | Ps X C p s Hp
                 | Ps X C s mu C' s' Hstep IH Hdisj ];
    intros Hwf Hwfrt; simpl in Hwf, Hwfrt; unfold projn.
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
    specialize (IH HwfC Hwfrt).
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
  - (* C|Call *)
    eapply NCall.
    + apply proj_call_in; assumption.
    + rewrite proj_rt_out; [ reflexivity | ].
      intros Hin. apply in_remove in Hin. tauto.
    + intros r Hr.
      apply (proj_invariance _ _ _ _ _ (CCall X p s Hp)).
      simpl; intuition.
  - (* C|Enter: by well-formedness, p's local body is the projection of
       the current state of the body *)
    destruct Hwfrt as [_ HPs].
    eapply NCall.
    + apply proj_crt_in; assumption.
    + rewrite proj_rt_out.
      * exact (HPs p Hp).
      * intros Hin. apply in_remove in Hin. tauto.
    + intros r Hr.
      apply (proj_invariance _ _ _ _ _ (CEnter Ps X C p s Hp)).
      simpl; intuition.
  - (* C|Inside *)
    destruct Hwf as [_ HwfC]. destruct Hwfrt as [HwfrtC _].
    specialize (IH HwfC HwfrtC).
    eapply nstep_frame_gen; [ exact IH | | | ].
    + (* projn (Ps : X . C) agrees with projn C on pn mu *)
      intros r Hr. apply proj_crt_out.
      intros Hin. apply (Hdisj r Hin Hr).
    + (* projn (Ps : X . C') agrees with projn C' on pn mu *)
      intros r Hr. apply proj_crt_out.
      intros Hin. apply (Hdisj r Hin Hr).
    + (* off pn mu, projections of Ps : X . C' and Ps : X . C agree *)
      intros r Hr. apply proj_crt_congr.
      apply (proj_invariance _ _ _ _ _ Hstep); assumption.
Qed.

(** ** Theorem 4.9 (Soundness) *)

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

(** The sub-case of a runtime term whose waiting processes are not involved
    in the step, handled by [C|Inside] and the induction hypothesis. *)
Lemma soundness_inside (Ps : list (P L)) (X : PName L) (C : chor) (s : store) (mu : label) (N' : network) (s' : store) :
  (forall (s : store) (mu : label) (N' : network) (s' : store),
      nstep (projn C) s mu N' s' ->
      exists C', cstep C s mu C' s' /\ N' = projn C') ->
  nstep (projn (CRT Ps X C)) s mu N' s' ->
  (forall r, In r Ps -> ~ In r (pn_lbl mu)) ->
  exists C', cstep (CRT Ps X C) s mu C' s' /\ N' = projn C'.
Proof.
  intros IH H Hdisj.
  assert (Hag : agree_on (pn_lbl mu) (projn C) (projn (CRT Ps X C))).
  { intros r Hr. unfold projn. symmetry. apply proj_crt_out.
    intros Hin. apply (Hdisj r Hin Hr). }
  destruct (nstep_frame _ _ _ _ _ _ H Hag) as [N'' [H'' [Hag1 Hag2]]].
  destruct (IH _ _ _ _ H'') as [C0' [Hstep HN'']].
  exists (CRT Ps X C0'). split.
  - apply CInside; assumption.
  - apply functional_extensionality; intros r. unfold projn.
    destruct (in_dec (P_eq_dec L) r (pn_lbl mu)) as [Hin | Hnin].
    + rewrite <- (Hag1 r Hin), HN''. unfold projn.
      symmetry. apply proj_crt_out.
      intros Hin'. apply (Hdisj r Hin' Hin).
    + destruct (nstep_locality _ _ _ _ _ H r Hnin) as [HN'r _].
      rewrite HN'r. unfold projn.
      apply proj_crt_congr. symmetry.
      apply (proj_invariance _ _ _ _ _ Hstep); assumption.
Qed.

Theorem soundness (C : chor) (s : store) (mu : label) (N' : network) (s' : store) :
  wf_rt C ->
  nstep (projn C) s mu N' s' ->
  exists C', cstep C s mu C' s' /\ N' = projn C'.
Proof.
  revert s mu N' s'.
  induction C as [ | eta C IH | p e C1 IH1 C2 IH2 | X | Ps X C IH ];
    intros s mu N' s' Hwfrt H; simpl in Hwfrt.
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
        apply soundness_delay; [ intros; apply IH; assumption | assumption | ].
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
           apply soundness_delay; [ intros; apply IH; assumption | assumption | ].
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
  - (* C = X: some participant enters the call *)
    destruct (pn_lbl_nonempty mu) as [r Hr].
    assert (HrX : In r (procs X)).
    { destruct (in_dec (P_eq_dec L) r (procs X)) as [Hin | Hnin]; [ assumption | ].
      exfalso. apply (nstep_inv_nonnil _ _ _ _ _ r H Hr).
      apply proj_call_out; assumption. }
    destruct (nstep_inv_call _ _ _ _ _ r X H Hr (proj_call_in X r HrX))
      as [-> [HN'r ->]].
    exists (rt (remove (P_eq_dec L) r (procs X)) X (body X)).
    split; [ apply CCall; assumption | ].
    apply functional_extensionality; intros q. unfold projn.
    destruct (P_eq_dec L q r) as [-> | Hqr].
    + rewrite HN'r, proj_rt_out; [ reflexivity | ].
      intros Hin. apply in_remove in Hin. tauto.
    + destruct (nstep_locality _ _ _ _ _ H q) as [HN'q _];
        [ simpl; intuition | ].
      rewrite HN'q. unfold projn. symmetry.
      apply (proj_invariance _ _ _ _ _ (CCall X r s HrX)).
      simpl; intuition.
  - (* C = Ps : X . C0 *)
    destruct Hwfrt as [HwfrtC HPs].
    destruct (existsb (fun r => inb r (pn_lbl mu)) Ps) eqn:E.
    + (* a process that has not entered is involved: the step is C|Enter *)
      apply existsb_exists in E as [r [HrPs Hrmu]].
      destruct (inb_spec r (pn_lbl mu)) as [Hr | ]; [ | discriminate ].
      destruct (nstep_inv_call _ _ _ _ _ r X H Hr (proj_crt_in Ps X C r HrPs))
        as [-> [HN'r ->]].
      exists (rt (remove (P_eq_dec L) r Ps) X C).
      split; [ apply CEnter; assumption | ].
      apply functional_extensionality; intros q. unfold projn.
      destruct (P_eq_dec L q r) as [-> | Hqr].
      * rewrite HN'r, proj_rt_out.
        -- symmetry. exact (HPs r HrPs).
        -- intros Hin. apply in_remove in Hin. tauto.
      * destruct (nstep_locality _ _ _ _ _ H q) as [HN'q _];
          [ simpl; intuition | ].
        rewrite HN'q. unfold projn. symmetry.
        apply (proj_invariance _ _ _ _ _ (CEnter Ps X C r s HrPs)).
        simpl; intuition.
    + (* no such process: the step happens inside the body *)
      apply soundness_inside; [ intros; apply IH; assumption | assumption | ].
      intros r HrPs Hrmu.
      assert (existsb (fun r => inb r (pn_lbl mu)) Ps = true) as E'.
      { apply existsb_exists. exists r. split; [ assumption | ].
        apply inb_true; assumption. }
      congruence.
Qed.

(** ** Corollary 4.10 (Bisimulation) *)

(** The relation [B] of the paper: a well-formed choreographic configuration
    is related to its projection (with the same store).  In addition to
    [wf_rt], [wf] records the grammar's side conditions. *)
Definition bisim_rel (c : chor * store) (n : network * store) : Prop :=
  wf (fst c) /\ wf_rt (fst c) /\ n = (projn (fst c), snd c).

Corollary bisimulation_forward (C : chor) (s : store) (N : network) (mu : label) (C' : chor) (s' : store) :
  bisim_rel (C, s) (N, s) ->
  cstep C s mu C' s' ->
  exists N', nstep N s mu N' s' /\ bisim_rel (C', s') (N', s').
Proof.
  intros [Hwf [Hwfrt Heq]] Hstep; simpl in *.
  inversion Heq; subst N; clear Heq.
  exists (projn C'). split.
  - apply completeness; assumption.
  - split; [ eapply cstep_wf; eassumption | ].
    split; [ eapply cstep_wf_rt; eassumption | reflexivity ].
Qed.

Corollary bisimulation_backward (C : chor) (s : store) (N : network) (mu : label) (N' : network) (s' : store) :
  bisim_rel (C, s) (N, s) ->
  nstep N s mu N' s' ->
  exists C', cstep C s mu C' s' /\ bisim_rel (C', s') (N', s').
Proof.
  intros [Hwf [Hwfrt Heq]] Hstep; simpl in *.
  inversion Heq; subst N; clear Heq.
  destruct (soundness _ _ _ _ _ Hwfrt Hstep) as [C' [Hcstep ->]].
  exists C'. split; [ assumption | ].
  split; [ eapply cstep_wf; eassumption | ].
  split; [ eapply cstep_wf_rt; eassumption | reflexivity ].
Qed.

(** ** Lemma 4.11 (Progress) *)

Lemma progress (C : chor) (s : store) :
  pn C <> [] -> exists mu C' s', cstep C s mu C' s'.
Proof.
  induction C as [ | [ p x e | p e q x ] C _ | p e C1 _ C2 _ | X | Ps X C IH ];
    intros Hne.
  - simpl in Hne; congruence.
  - do 3 eexists. apply CLocal.
  - do 3 eexists. apply CCom.
  - do 3 eexists. apply CCast.
  - simpl in Hne. destruct (procs X) as [ | p Ps ] eqn:E; [ congruence | ].
    do 3 eexists. apply CCall. rewrite E. left; reflexivity.
  - destruct Ps as [ | p Ps ].
    + (* not possible for a choreography satisfying [wf], but harmless *)
      simpl in Hne. destruct (IH Hne) as [mu [C' [s' Hstep]]].
      do 3 eexists. apply CInside; [ eassumption | intros r [] ].
    + do 3 eexists. apply CEnter. left; reflexivity.
Qed.

(** ** Corollary 4.12 (Deadlock-freedom by construction) *)

Definition stuck (N : network) (s : store) : Prop :=
  forall mu N' s', ~ nstep N s mu N' s'.

Lemma projn_terminated_iff (C : chor) :
  terminated (projn C) <-> pn C = [].
Proof.
  split.
  - intros Hterm.
    destruct (pn C) as [ | r rs ] eqn:E; [ reflexivity | exfalso ].
    apply (proj_nonnil_of_pn C r); [ rewrite E; left; reflexivity | apply Hterm ].
  - intros Hnil r. unfold projn. apply proj_nil_of_not_pn.
    rewrite Hnil. intros [].
Qed.

Lemma terminated_stuck (N : network) (s : store) :
  terminated N -> stuck N s.
Proof.
  intros Hterm mu N' s' H.
  destruct (pn_lbl_nonempty mu) as [r Hr].
  apply (nstep_inv_nonnil _ _ _ _ _ r H Hr). apply Hterm.
Qed.

Lemma projn_stuck_iff_terminated (C : chor) (s : store) :
  wf C -> wf_rt C -> (stuck (projn C) s <-> terminated (projn C)).
Proof.
  intros Hwf Hwfrt. split.
  - intros Hstuck.
    apply projn_terminated_iff.
    destruct (pn C) as [ | r rs ] eqn:E; [ reflexivity | exfalso ].
    destruct (progress C s) as [mu [C' [s' Hstep]]]; [ congruence | ].
    exact (Hstuck _ _ _ (completeness _ _ _ _ _ Hwf Hwfrt Hstep)).
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
  forall C : chor, wf C -> wf_rt C -> fst c = projn C ->
  exists C', wf C' /\ wf_rt C' /\ fst c' = projn C'.
Proof.
  induction 1 as [ c c' [mu Hstep] | c | c c' c'' _ IH1 _ IH2 ];
    intros C Hwf Hwfrt Hc.
  - rewrite Hc in Hstep.
    destruct (soundness _ _ _ _ _ Hwfrt Hstep) as [C' [Hcstep ->]].
    exists C'. split; [ eapply cstep_wf; eassumption | ].
    split; [ eapply cstep_wf_rt; eassumption | reflexivity ].
  - exists C; auto.
  - destruct (IH1 C Hwf Hwfrt Hc) as [C' [Hwf' [Hwfrt' Hc']]].
    apply (IH2 C' Hwf' Hwfrt' Hc').
Qed.

Corollary deadlock_freedom (C : chor) (s : store) :
  wf C ->
  wf_rt C ->
  (stuck (projn C) s <-> terminated (projn C)) /\
  (terminated (projn C) <-> pn C = []) /\
  (forall N' s',
      reach (projn C, s) (N', s') ->
      terminated N' \/ exists mu N'' s'', nstep N' s' mu N'' s'').
Proof.
  intros Hwf Hwfrt.
  split; [ apply projn_stuck_iff_terminated; assumption | ].
  split; [ apply projn_terminated_iff | ].
  intros N' s' Hreach.
  destruct (reach_proj _ _ Hreach C Hwf Hwfrt eq_refl) as [C' [Hwf' [Hwfrt' HN']]].
  simpl in HN'; subst N'.
  destruct (pn C') as [ | r rs ] eqn:E.
  - left. apply projn_terminated_iff. assumption.
  - right. destruct (progress C' s') as [mu [C'' [s'' Hstep]]]; [ congruence | ].
    do 3 eexists. apply completeness; eassumption.
Qed.

(** ** Remark 4.13 (Procedures without participants)

    If every procedure has a participant, a choreography satisfying the
    side conditions of the grammar has no process names exactly when it is
    [CNil], and Corollary 4.12 takes the form of the language without
    procedures. *)
Lemma pn_nil_iff_nil (C : chor) :
  (forall X, procs X <> []) -> wf C -> (pn C = [] <-> C = CNil).
Proof.
  intros Hprocs Hwf. split; [ | intros ->; reflexivity ].
  destruct C as [ | [ p x e | p e q x ] C | p e C1 C2 | X | Ps X C ];
    simpl in *; intros H; try discriminate; try reflexivity.
  - exfalso; apply (Hprocs X); assumption.
  - destruct Ps; [ tauto | discriminate ].
Qed.

End Correctness.

(** The only axiom used is functional extensionality (for equality of
    networks, which are functions). *)
Print Assumptions completeness.
Print Assumptions soundness.
Print Assumptions deadlock_freedom.
