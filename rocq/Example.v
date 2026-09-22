(** * The running example of the paper (Examples 1.3, 1.6 and 3.3)

    We instantiate the development with three processes [pp], [qq], [rr],
    four variables, natural-number values and a tiny expression language,
    and check by computation that the projection of the example
    choreography is the network given in Example 3.3, and that the
    execution of Example 1.6 is derivable. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
From Choreasy Require Import Prelim Chor Net EPP Correctness.

(** ** A concrete language *)

Inductive proc := pp | qq | rr.
Inductive var := vx | vy | vz | vn.

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
  BExpr := bexpr; beval := beval_ex
|}.

(** ** Example 1.3: the choreography [C_ex] *)

(* C1' = p.x -> q.y ; q.y -> r.z ; 0 *)
Definition C1' : @chor L_ex :=
  CAct (ACom pp (EVar vx) qq vy) (CAct (ACom qq (EVar vy) rr vz) CNil).

(* C_last = q.y -> r.z ; 0 *)
Definition C_last : @chor L_ex := CAct (ACom qq (EVar vy) rr vz) CNil.

(* C1 = r.n := n + 1 ; C1' *)
Definition C1 : @chor L_ex := CAct (ALocal rr vn (ESucc vn)) C1'.

(* C2 = q.y := 0 ; 0 *)
Definition C2 : @chor L_ex := CAct (ALocal qq vy (EConst 0)) CNil.

(* C_ex = p.x := 2 * x ; if p.(x > 10) then C1 else C2 *)
Definition C_if : @chor L_ex := CIf pp (BGt vx 10) C1 C2.
Definition C_ex : @chor L_ex := CAct (ALocal pp vx (EDouble vx)) C_if.

Lemma C_ex_wf : wf C_ex.
Proof. simpl; repeat split; discriminate. Qed.

(** The receivers of the conditional are [q] and [r]. *)
Lemma receivers_ex : @receivers L_ex pp C1 C2 = [rr; qq].
Proof. reflexivity. Qed.

(** ** Example 3.3: the projection of [C_ex] *)

Lemma proj_C_ex_p :
  proj C_ex pp =
  BLocal vx (EDouble vx)
    (BSendBr [rr; qq] (BGt vx 10) (BSend qq (EVar vx) BNil) BNil).
Proof. reflexivity. Qed.

Lemma proj_C_ex_q :
  proj C_ex qq =
  BRecvBr pp (BRecv pp vy (BSend rr (EVar vy) BNil)) (BLocal vy (EConst 0) BNil).
Proof. reflexivity. Qed.

Lemma proj_C_ex_r :
  proj C_ex rr =
  BRecvBr pp (BLocal vn (ESucc vn) (BRecv qq vz BNil)) BNil.
Proof. reflexivity. Qed.

(** ** Example 1.6: an execution of [C_ex] *)

(** The initial store: [x = 7] at [p], everything else [0]. *)
Definition s0 : @store L_ex := fun _ _ => 0.
Definition s_init : @store L_ex := upd s0 pp vx 7.

Lemma run_ex :
  exists s1 s2 s3 s4 : @store L_ex,
    cstep C_ex s_init (LTau pp) C_if s1 /\
    cstep C_if s1 (LCast pp [rr; qq]) C1 s1 /\
    cstep C1 s1 (LTau rr) C1' s2 /\
    cstep C1' s2 (LCom pp qq) C_last s3 /\
    cstep C_last s3 (LCom qq rr) CNil s4 /\
    s4 pp vx = 14 /\ s4 rr vn = 1 /\ s4 qq vy = 14 /\ s4 rr vz = 14.
Proof.
  do 4 eexists. repeat split.
  - apply CLocal.
  - exact (@CCast L_ex pp (BGt vx 10) C1 C2 _).
  - apply CLocal.
  - apply CCom.
  - apply CCom.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The third and fourth steps can be taken in the other order, using
    [C|Delay] to let [p] and [q] communicate before [r] increments its
    counter. *)
Lemma run_ex_delay (s : @store L_ex) :
  cstep C1 s (LCom pp qq)
        (CAct (ALocal rr vn (ESucc vn)) C_last)
        (upd s qq vy (eval L_ex (EVar vx) (s pp))).
Proof.
  apply CDelay.
  - apply CCom.
  - intros r0 Hr Hin; simpl in *.
    destruct Hr as [<- | []]; destruct Hin as [H | [H | []]]; discriminate.
Qed.

(** Read through the projection (Theorem 4.5), the multicast step takes the
    network of Example 3.3 to the projection of [C1], in the store [s1]
    reached after the first step (where [x = 14] at [p]). *)
Definition s1 : @store L_ex := upd s_init pp vx 14.

Lemma run_ex_net :
  nstep (projn C_if) s1 (LCast pp [rr; qq]) (projn C1) s1.
Proof.
  apply (completeness C_if s1 (LCast pp [rr; qq]) C1 s1).
  - simpl; repeat split; discriminate.
  - exact (@CCast L_ex pp (BGt vx 10) C1 C2 s1).
Qed.
