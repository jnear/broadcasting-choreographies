(** * The running example of the paper (Examples 1.6, 1.11, 3.3 and 4.6)

    We instantiate the development with three processes [pp], [qq], [rr],
    five variables, natural-number values, a tiny expression language and
    two procedures: [Loop], the running example, and [Ping], used for
    Example 4.6.  We check by computation the participants and receivers of
    Example 1.6 and the projected definitions of Example 3.3, derive the
    execution of Example 1.11, and check that the network of Example 4.6
    deadlocks. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
From ChoreasyFun Require Import Prelim Chor Net EPP Correctness.

(** ** A concrete language *)

Inductive proc := pp | qq | rr.
Inductive var := vx | vy | vz | vn | vk.
Inductive pname := Loop | Ping.

Inductive expr :=
| EConst (k : nat)        (* k *)
| EVar (v : var)          (* v *)
| EDouble (v : var)       (* 2 * v *)
| ESucc (v : var).        (* v + 1 *)

Inductive bexpr :=
| BGt (v : var) (k : nat). (* v > k *)

Definition proc_eq_dec : forall a b : proc, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition var_eq_dec : forall a b : var, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma pname_all_spec : forall X : pname, In X [Loop; Ping].
Proof. intros []; simpl; auto. Qed.

Definition eval_ex (e : expr) (s : var -> nat) : nat :=
  match e with
  | EConst k => k
  | EVar v => s v
  | EDouble v => 2 * s v
  | ESucc v => S (s v)
  end.

Definition beval_ex (b : bexpr) (s : var -> nat) : bool :=
  match b with
  | BGt v k => k <? s v
  end.

Definition L_ex : lang := {|
  P := proc; P_eq_dec := proc_eq_dec;
  Var := var; Var_eq_dec := var_eq_dec;
  Val := nat;
  Expr := expr; eval := eval_ex;
  BExpr := bexpr; beval := beval_ex;
  PName := pname; PName_all := [Loop; Ping]; PName_all_spec := pname_all_spec
|}.

(** ** Example 1.6: the procedure [Loop] *)

(* C1' = p.x -> q.y ; q.y -> r.z ; 0 *)
Definition C1' : @chor L_ex :=
  CAct (ACom pp (EVar vx) qq vy) (CAct (ACom qq (EVar vy) rr vz) CNil).
(* C_last = q.y -> r.z ; 0 *)
Definition C_last : @chor L_ex := CAct (ACom qq (EVar vy) rr vz) CNil.
(* C1 = r.n := n + 1 ; C1' *)
Definition C1 : @chor L_ex := CAct (ALocal rr vn (ESucc vn)) C1'.
(* C2 = q.k := k + 1 ; Loop *)
Definition C2 : @chor L_ex := CAct (ALocal qq vk (ESucc vk)) (CProc Loop).
(* C_if = if p.(x > 10) then C1 else C2 *)
Definition C_if : @chor L_ex := CIf pp (BGt vx 10) C1 C2.

(* Loop = p.x := 2 * x ; C_if *)
Definition C_Loop : @chor L_ex := CAct (ALocal pp vx (EDouble vx)) C_if.

(* Ping = p.x -> q.x ; Ping  (Example 4.6) *)
Definition C_Ping : @chor L_ex := CAct (ACom pp (EVar vx) qq vx) (CProc Ping).

Definition body_ex (X : PName L_ex) : @chor L_ex :=
  match X with
  | Loop => C_Loop
  | Ping => C_Ping
  end.

Lemma body_ex_wf (X : PName L_ex) : wf (body_ex X).
Proof. destruct X; simpl; repeat split; discriminate. Qed.

Lemma body_ex_source (X : PName L_ex) : source (body_ex X).
Proof. destruct X; simpl; tauto. Qed.

(** The procedure definitions. *)
#[export] Instance defs_ex : @defs L_ex :=
  @Build_defs L_ex body_ex body_ex_wf body_ex_source.

(** The participants of [Loop] are all three processes, computed as a least
    fixed point. *)
Lemma procs_Loop : procs Loop = [pp; rr; qq].
Proof. reflexivity. Qed.

(** The receivers of the conditional are [q] and [r]. *)
Lemma receivers_ex : @receivers L_ex _ pp C1 C2 = [rr; qq].
Proof. reflexivity. Qed.

(** ** Example 3.3: the projection of [Loop] *)

(** The program [Loop] projects to a call at every process. *)
Lemma proj_Loop (r : proc) : proj (CProc Loop) r = BCall Loop.
Proof. destruct r; reflexivity. Qed.

(** The projected local procedure definitions. *)
Lemma lbody_p :
  lbody pp Loop =
  BLocal vx (EDouble vx)
    (BSendBr [rr; qq] (BGt vx 10) (BSend qq (EVar vx) BNil) (BCall Loop)).
Proof. reflexivity. Qed.

Lemma lbody_q :
  lbody qq Loop =
  BRecvBr pp (BRecv pp vy (BSend rr (EVar vy) BNil)) (BLocal vk (ESucc vk) (BCall Loop)).
Proof. reflexivity. Qed.

Lemma lbody_r :
  lbody rr Loop =
  BRecvBr pp (BLocal vn (ESucc vn) (BRecv qq vz BNil)) (BCall Loop).
Proof. reflexivity. Qed.

(** ** Example 1.11: an execution of [Loop] *)

(** The initial store: [x = 3] at [p], everything else [0]. *)
Definition s0 : @store L_ex := fun _ _ => 0.
Definition s_init : @store L_ex := upd s0 pp vx 3.

(** [k_inc C] is [q.k := k + 1 ; C]. *)
Definition k_inc (C : @chor L_ex) : @chor L_ex := CAct (ALocal qq vk (ESucc vk)) C.

(** The targets of [C|Call] and [C|Enter] are given by [rt]; we compute
    them to concrete runtime terms. *)
Lemma cstep_conv (C : @chor L_ex) s mu C1 C2 s' :
  cstep C s mu C1 s' -> C1 = C2 -> cstep C s mu C2 s'.
Proof. intros H <-; exact H. Qed.

Ltac conv_step tac := eapply cstep_conv; [ tac | reflexivity ].

(** Side conditions of [C|Delay] and [C|Inside] on concrete lists. *)
Ltac disjoint :=
  let r := fresh "r" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  intros r H1 H2; simpl in H1, H2;
  repeat match goal with
         | H : _ \/ _ |- _ => destruct H
         | H : False |- _ => destruct H
         end;
  subst; discriminate.

(** The run of Example 1.11.  The runtime term [{q,r} : Loop . C] is
    [CRT [rr; qq] Loop C]. *)
Lemma run_ex :
  exists s1 s2 s3 s4 s5 s6 : @store L_ex,
    cstep (CProc Loop) s_init (LTau pp) (CRT [rr; qq] Loop C_Loop) s_init /\
    cstep (CRT [rr; qq] Loop C_Loop) s_init (LTau pp) (CRT [rr; qq] Loop C_if) s1 /\
    cstep (CRT [rr; qq] Loop C_if) s1 (LTau qq) (CRT [rr] Loop C_if) s1 /\
    cstep (CRT [rr] Loop C_if) s1 (LTau rr) C_if s1 /\
    cstep C_if s1 (LCast pp [rr; qq]) C2 s1 /\
    cstep C2 s1 (LTau pp) (k_inc (CRT [rr; qq] Loop C_Loop)) s1 /\
    cstep (k_inc (CRT [rr; qq] Loop C_Loop)) s1 (LTau pp)
          (k_inc (CRT [rr; qq] Loop C_if)) s2 /\
    cstep (k_inc (CRT [rr; qq] Loop C_if)) s2 (LTau rr)
          (k_inc (CRT [qq] Loop C_if)) s2 /\
    cstep (k_inc (CRT [qq] Loop C_if)) s2 (LTau qq) (CRT [qq] Loop C_if) s3 /\
    cstep (CRT [qq] Loop C_if) s3 (LTau qq) C_if s3 /\
    cstep C_if s3 (LCast pp [rr; qq]) C1 s3 /\
    cstep C1 s3 (LTau rr) C1' s4 /\
    cstep C1' s4 (LCom pp qq) C_last s5 /\
    cstep C_last s5 (LCom qq rr) CNil s6 /\
    s1 pp vx = 6 /\ s2 pp vx = 12 /\ s3 qq vk = 1 /\
    s6 rr vn = 1 /\ s6 qq vy = 12 /\ s6 rr vz = 12.
Proof.
  do 6 eexists. repeat split.
  - (* p calls Loop *)
    conv_step ltac:(apply CCall; rewrite procs_Loop; left; reflexivity).
  - (* p doubles x before q and r have entered *)
    apply CInside; [ apply CLocal | disjoint ].
  - (* q enters *)
    conv_step ltac:(apply CEnter; right; left; reflexivity).
  - (* r enters *)
    conv_step ltac:(apply CEnter; left; reflexivity).
  - (* first multicast: 6 > 10 is false *)
    exact (@CCast L_ex _ pp (BGt vx 10) C1 C2 _).
  - (* p calls Loop again while q still has to increment k *)
    apply CDelay; [ | disjoint ].
    conv_step ltac:(apply CCall; rewrite procs_Loop; left; reflexivity).
  - (* p doubles x again *)
    apply CDelay; [ | disjoint ].
    apply CInside; [ apply CLocal | disjoint ].
  - (* r enters *)
    apply CDelay; [ | disjoint ].
    conv_step ltac:(apply CEnter; left; reflexivity).
  - (* q increments k *)
    apply CLocal.
  - (* q enters, enabling the second multicast *)
    conv_step ltac:(apply CEnter; left; reflexivity).
  - (* second multicast: 12 > 10 is true *)
    exact (@CCast L_ex _ pp (BGt vx 10) C1 C2 _).
  - apply CLocal.
  - apply CCom.
  - apply CCom.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Read through the projection (Theorem 4.8), the first multicast takes
    the network to the projection of [C2], in the store [s1] reached after
    [p] doubles [x] (where [x = 6] at [p]). *)
Definition s1 : @store L_ex := upd s_init pp vx 6.

Lemma C_if_wf : wf C_if /\ wf_rt C_if.
Proof.
  split.
  - simpl; repeat split; discriminate.
  - apply source_wf_rt. simpl; tauto.
Qed.

Lemma run_ex_net :
  nstep (projn C_if) s1 (LCast pp [rr; qq]) (projn C2) s1.
Proof.
  apply (completeness C_if s1 (LCast pp [rr; qq]) C2 s1);
    [ apply C_if_wf | apply C_if_wf | ].
  exact (@CCast L_ex _ pp (BGt vx 10) C1 C2 s1).
Qed.

(** After [p] has re-entered [Loop] and doubled [x], and [r] has entered,
    the second multicast is not enabled in the network: [q] is still at
    [k := k + 1 ; Loop]. *)
Lemma blocked_no_cast (s : @store L_ex) (Q : list proc) (N' : @network L_ex) (s' : @store L_ex) :
  ~ nstep (projn (k_inc (CRT [qq] Loop C_if))) s (LCast pp Q) N' s'.
Proof.
  intros H.
  destruct (nstep_inv_sendbr (L := L_ex) _ _ _ _ _ pp [rr; qq] (BGt vx 10)
              (BSend qq (EVar vx) BNil) (BCall Loop) H (or_introl eq_refl) eq_refl)
    as [Hmu _].
  injection Hmu as ->.
  destruct (nstep_inv_local (L := L_ex) _ _ _ _ _ qq vk (ESucc vk) (BCall Loop) H
              (or_intror (or_intror (or_introl eq_refl))) eq_refl)
    as [Hmu _].
  discriminate.
Qed.

(** ** Example 4.6: well-formedness is needed *)

(* {q} : Ping . 0 *)
Definition C_bad : @chor L_ex := CRT [qq] Ping CNil.

Lemma C_bad_not_wf_rt : ~ wf_rt C_bad.
Proof.
  simpl. intros [_ H]. specialize (H qq (or_introl eq_refl)).
  discriminate H.
Qed.

(** The choreography terminates in one step... *)
Lemma C_bad_step (s : @store L_ex) : cstep C_bad s (LTau qq) CNil s.
Proof. conv_step ltac:(apply CEnter; left; reflexivity). Qed.

(** ...but its projection cannot follow: the only step of the network
    unfolds [q]'s call, after which [q] waits for [p] forever. *)
Lemma C_bad_net_not_complete (s : @store L_ex) :
  ~ nstep (projn C_bad) s (LTau qq) (projn CNil) s.
Proof.
  intros H.
  destruct (nstep_inv_call (L := L_ex) _ _ _ _ _ qq Ping H (or_introl eq_refl) eq_refl)
    as [_ [HN' _]].
  discriminate HN'.
Qed.

Definition N_bad : @network L_ex :=
  fun r => match r with qq => BRecv pp vx (BCall Ping) | _ => BNil end.

Lemma C_bad_net_step (s : @store L_ex) : nstep (projn C_bad) s (LTau qq) N_bad s.
Proof.
  eapply NCall; [ reflexivity | reflexivity | ].
  intros [] Hr; reflexivity || congruence.
Qed.

Lemma N_bad_deadlock (s : @store L_ex) : stuck N_bad s /\ ~ terminated N_bad.
Proof.
  split.
  - intros mu N' s' H.
    destruct (pn_lbl_nonempty mu) as [r Hr].
    assert (r = qq) as ->.
    { destruct r; [ | reflexivity | ];
        exfalso; exact (nstep_inv_nonnil _ _ _ _ _ _ H Hr eq_refl). }
    destruct (nstep_inv_recv (L := L_ex) _ _ _ _ _ qq pp vx (BCall Ping) H Hr eq_refl)
      as [_ [_ [e [B' [HNp _]]]]].
    discriminate HNp.
  - intros Hterm. specialize (Hterm qq). discriminate Hterm.
Qed.
