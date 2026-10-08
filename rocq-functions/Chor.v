(** * Choreographies (Section 1 of the paper) *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From ChoreasyFun Require Import Prelim.

Section Chor.
Context {L : lang}.

(** ** Syntax (Definition 1.2) *)

Inductive action : Type :=
| ALocal (p : P L) (x : Var L) (e : Expr L)          (* p.x := e *)
| ACom   (p : P L) (e : Expr L) (q : P L) (x : Var L). (* p.e -> q.x *)

Inductive chor : Type :=
| CNil                                                   (* 0 *)
| CAct (eta : action) (C : chor)                          (* eta ; C *)
| CIf  (p : P L) (e : BExpr L) (C1 C2 : chor)             (* if p.e then C1 else C2 *)
| CProc (X : PName L)                                     (* X *)
| CRT  (Ps : list (P L)) (X : PName L) (C : chor).        (* Ps : X . C (runtime term) *)

(** The grammar requires [p <> q] in a communication and a nonempty set of
    processes in a runtime term.  We record these side conditions as a
    well-formedness predicate. *)
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
  | CProc _ => True
  | CRT Ps _ C => Ps <> [] /\ wf C
  end.

(** A source choreography contains no runtime term. *)
Fixpoint source (C : chor) : Prop :=
  match C with
  | CNil => True
  | CAct _ C => source C
  | CIf _ _ C1 C2 => source C1 /\ source C2
  | CProc _ => True
  | CRT _ _ _ => False
  end.

(** ** Procedure definitions (Definition 1.3)

    A set of procedure definitions assigns a source choreography to every
    procedure name.  The bodies also satisfy the side conditions of the
    grammar.  The set of definitions is fixed throughout, so we make it a
    class: every later definition and lemma is parameterised by it, and the
    instance is found automatically. *)

Class defs := {
  body : PName L -> chor;
  body_wf : forall X, wf (body X);
  body_source : forall X, source (body X)
}.

Context {D : defs}.

(** ** Process names (Definition 1.4) *)

Definition pn_act (eta : action) : list (P L) :=
  match eta with
  | ALocal p _ _ => [p]
  | ACom p _ q _ => [p; q]
  end.

(** [pn_with rho C] is the paper's [pn_rho(C)]: the process names of [C],
    where [rho X] is taken as the process names of a call to [X]. *)
Fixpoint pn_with (rho : PName L -> list (P L)) (C : chor) : list (P L) :=
  match C with
  | CNil => []
  | CAct eta C => pn_act eta ++ pn_with rho C
  | CIf p _ C1 C2 => p :: pn_with rho C1 ++ pn_with rho C2
  | CProc X => rho X
  | CRT Ps _ C => Ps ++ pn_with rho C
  end.

(** The participants of the procedures are the least function [pi] with
    [pi X = pn_pi (body X)] for every [X].  We compute it by iterating
    [rho |-> (X |-> pn_rho (body X))] from the everywhere-empty function,
    removing duplicates at each step. *)
Fixpoint procs_iter (k : nat) (X : PName L) : list (P L) :=
  match k with
  | 0 => []
  | S k => nodup (P_eq_dec L) (pn_with (procs_iter k) (body X))
  end.

(** Every iterate is contained in the processes occurring in the bodies,
    ignoring calls.  The iteration therefore stabilises after at most
    [procs_bound] steps. *)
Definition pn_universe : list (P L) :=
  flat_map (fun Y => pn_with (fun _ => []) (body Y)) (PName_all L).

Definition procs_bound : nat :=
  length (PName_all L) * length (nodup (P_eq_dec L) pn_universe).

(** The participants [pn(X)] of a procedure. *)
Definition procs : PName L -> list (P L) := procs_iter procs_bound.

Arguments procs : simpl never.

(** [pn C] is [pn_pi C].  It is defined by its own fixpoint, so that it
    unfolds as in the language without procedures. *)
Fixpoint pn (C : chor) : list (P L) :=
  match C with
  | CNil => []
  | CAct eta C => pn_act eta ++ pn C
  | CIf p _ C1 C2 => p :: pn C1 ++ pn C2
  | CProc X => procs X
  | CRT Ps _ C => Ps ++ pn C
  end.

Lemma pn_pn_with C : pn C = pn_with procs C.
Proof. induction C; simpl; congruence. Qed.

(** *** Convergence of the iteration *)

(** Pointwise inclusion of functions from procedure names to sets. *)
Definition sub (rho rho' : PName L -> list (P L)) : Prop :=
  forall X, incl (rho X) (rho' X).

Lemma pn_with_mono rho rho' C :
  sub rho rho' -> incl (pn_with rho C) (pn_with rho' C).
Proof.
  intros Hsub; unfold sub, incl in *.
  induction C; intros r; simpl; rewrite ?in_app_iff; firstorder.
Qed.

Lemma procs_iter_S k X r :
  In r (procs_iter (S k) X) <-> In r (pn_with (procs_iter k) (body X)).
Proof. apply nodup_In. Qed.

Lemma procs_iter_mono k : sub (procs_iter k) (procs_iter (S k)).
Proof.
  induction k as [ | k IH ]; intros X r Hr; [ destruct Hr | ].
  apply procs_iter_S. apply procs_iter_S in Hr.
  exact (pn_with_mono _ _ (body X) IH r Hr).
Qed.

Lemma pn_with_split rho C r :
  In r (pn_with rho C) ->
  In r (pn_with (fun _ => []) C) \/ exists Y, In r (rho Y).
Proof.
  induction C; simpl; rewrite ?in_app_iff; firstorder.
Qed.

Lemma procs_iter_universe k X : incl (procs_iter k X) pn_universe.
Proof.
  revert X; induction k as [ | k IH ]; intros X r Hr; [ destruct Hr | ].
  rewrite procs_iter_S in Hr.
  destruct (pn_with_split _ _ _ Hr) as [Hr' | [Y HY]].
  - unfold pn_universe. apply in_flat_map.
    exists X. split; [ apply PName_all_spec | assumption ].
  - apply (IH Y r HY).
Qed.

(** The iteration is stable at [k] if it gains nothing at step [k + 1]. *)
Definition stable (k : nat) : Prop := sub (procs_iter (S k)) (procs_iter k).

Lemma stable_S k : stable k -> stable (S k).
Proof.
  intros H X r Hr. apply procs_iter_S. apply procs_iter_S in Hr.
  exact (pn_with_mono _ _ (body X) H r Hr).
Qed.

Lemma stable_le j k : j <= k -> stable j -> stable k.
Proof. induction 1; auto using stable_S. Qed.

(** Stability is decidable. *)
Definition inclb (l l' : list (P L)) : bool := forallb (fun r => inb r l') l.

Lemma inclb_spec l l' : reflect (incl l l') (inclb l l').
Proof.
  unfold inclb.
  destruct (forallb (fun r => inb r l') l) eqn:E; constructor.
  - rewrite forallb_forall in E. intros r Hr.
    specialize (E r Hr). destruct (inb_spec r l'); [ assumption | discriminate ].
  - intros H. rewrite <- not_true_iff_false in E. apply E.
    apply forallb_forall. intros r Hr. apply inb_true, H, Hr.
Qed.

Lemma forallb_false_exists {A : Type} (f : A -> bool) l :
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  induction l as [ | a l IH ]; simpl; [ discriminate | ].
  destruct (f a) eqn:Ea; simpl; intros H.
  - destruct (IH H) as [x [Hx Hfx]]. eauto.
  - eauto.
Qed.

Definition stableb (k : nat) : bool :=
  forallb (fun X => inclb (procs_iter (S k) X) (procs_iter k X)) (PName_all L).

Lemma stableb_true k : stableb k = true -> stable k.
Proof.
  unfold stableb; rewrite forallb_forall; intros H X.
  specialize (H X (PName_all_spec L X)).
  destruct (inclb_spec (procs_iter (S k) X) (procs_iter k X)); [ assumption | discriminate ].
Qed.

Lemma stableb_false k :
  stableb k = false ->
  exists X r, In r (procs_iter (S k) X) /\ ~ In r (procs_iter k X).
Proof.
  unfold stableb; intros H.
  destruct (forallb_false_exists _ _ H) as [X [_ HX]].
  unfold inclb in HX.
  destruct (forallb_false_exists _ _ HX) as [r [Hr Hnr]].
  exists X, r. split; [ assumption | ].
  destruct (inb_spec r (procs_iter k X)); [ discriminate | assumption ].
Qed.

(** The measure: the total number of distinct participants found so far. *)
Definition procs_measure (k : nat) : nat :=
  list_sum (map (fun X => length (nodup (P_eq_dec L) (procs_iter k X))) (PName_all L)).

Lemma list_sum_map_le {A : Type} (f g : A -> nat) l :
  (forall x, In x l -> f x <= g x) ->
  list_sum (map f l) <= list_sum (map g l).
Proof.
  induction l as [ | a l IH ]; simpl; intros H; [ lia | ].
  pose proof (H a (or_introl eq_refl)).
  assert (list_sum (map f l) <= list_sum (map g l)) by (apply IH; auto).
  lia.
Qed.

Lemma list_sum_map_lt {A : Type} (f g : A -> nat) l :
  (forall x, In x l -> f x <= g x) ->
  (exists x, In x l /\ f x < g x) ->
  list_sum (map f l) < list_sum (map g l).
Proof.
  induction l as [ | a l IH ]; simpl; intros Hle [x [Hx Hlt]]; [ destruct Hx | ].
  destruct Hx as [-> | Hx].
  - assert (list_sum (map f l) <= list_sum (map g l))
      by (apply list_sum_map_le; auto).
    lia.
  - assert (list_sum (map f l) < list_sum (map g l))
      by (apply IH; eauto).
    specialize (Hle a (or_introl eq_refl)). lia.
Qed.

Lemma list_sum_map_bound {A : Type} (f : A -> nat) l b :
  (forall x, In x l -> f x <= b) ->
  list_sum (map f l) <= length l * b.
Proof.
  induction l as [ | a l IH ]; simpl; intros H; [ lia | ].
  pose proof (H a (or_introl eq_refl)).
  assert (list_sum (map f l) <= length l * b) by (apply IH; auto).
  lia.
Qed.

Lemma length_nodup_le l l' :
  incl l l' -> length (nodup (P_eq_dec L) l) <= length (nodup (P_eq_dec L) l').
Proof.
  intros H. apply NoDup_incl_length; [ apply NoDup_nodup | ].
  intros r. rewrite !nodup_In. apply H.
Qed.

Lemma length_nodup_lt l l' r :
  incl l l' -> In r l' -> ~ In r l ->
  length (nodup (P_eq_dec L) l) < length (nodup (P_eq_dec L) l').
Proof.
  intros H Hr Hnr.
  destruct (Nat.lt_ge_cases (length (nodup (P_eq_dec L) l))
                            (length (nodup (P_eq_dec L) l'))) as [Hlt | Hge];
    [ assumption | exfalso ].
  apply Hnr. apply (nodup_In (P_eq_dec L)).
  apply (NoDup_length_incl (NoDup_nodup (P_eq_dec L) l) Hge).
  - intros q. rewrite !nodup_In. apply H.
  - apply nodup_In. assumption.
Qed.

Lemma procs_measure_lt k : stableb k = false -> procs_measure k < procs_measure (S k).
Proof.
  intros H. unfold procs_measure. apply list_sum_map_lt.
  - intros X _. apply length_nodup_le, procs_iter_mono.
  - destruct (stableb_false k H) as [X [r [Hr Hnr]]].
    exists X. split; [ apply PName_all_spec | ].
    apply (length_nodup_lt _ _ r); [ apply procs_iter_mono | assumption | assumption ].
Qed.

Lemma procs_measure_bound k : procs_measure k <= procs_bound.
Proof.
  unfold procs_measure, procs_bound. apply list_sum_map_bound.
  intros X _. apply length_nodup_le, procs_iter_universe.
Qed.

Lemma stable_or_grow n : (exists k, k < n /\ stable k) \/ n <= procs_measure n.
Proof.
  induction n as [ | n IH ]; [ right; lia | ].
  destruct IH as [[k [Hk Hst]] | Hle].
  - left. exists k. split; [ lia | assumption ].
  - destruct (stableb n) eqn:E.
    + left. exists n. split; [ lia | apply stableb_true; assumption ].
    + right. pose proof (procs_measure_lt n E). lia.
Qed.

Lemma procs_stable : stable procs_bound.
Proof.
  destruct (stable_or_grow (S procs_bound)) as [[k [Hk Hst]] | Hle].
  - apply (stable_le k); [ lia | assumption ].
  - pose proof (procs_measure_bound (S procs_bound)). lia.
Qed.

(** ** Lemma 1.5 (Participants of a procedure) *)

Lemma procs_fix X r : In r (pn (body X)) <-> In r (procs X).
Proof.
  rewrite pn_pn_with. split; intros H.
  - exact (procs_stable X r (proj2 (procs_iter_S procs_bound X r) H)).
  - exact (proj1 (procs_iter_S procs_bound X r) (procs_iter_mono procs_bound X r H)).
Qed.

(** [procs] is the least such function: it is included in every [rho] with
    [pn_rho (body X)] included in [rho X] for every [X]. *)
Lemma procs_least rho :
  (forall X, incl (pn_with rho (body X)) (rho X)) -> sub procs rho.
Proof.
  intros Hpre. unfold procs. generalize procs_bound as k.
  induction k as [ | k IH ]; intros X r Hr; [ destruct Hr | ].
  apply procs_iter_S in Hr.
  apply Hpre. exact (pn_with_mono _ _ (body X) IH r Hr).
Qed.

(** ** Receivers *)

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

(** ** Runtime terms with a possibly empty set

    By the paper's convention, [Ps : X . C] stands for [C] when [Ps] is
    empty.  [rt] implements this convention. *)
Definition rt (Ps : list (P L)) (X : PName L) (C : chor) : chor :=
  match Ps with
  | [] => C
  | _ :: _ => CRT Ps X C
  end.

Lemma pn_rt Ps X C r : In r (pn (rt Ps X C)) <-> In r Ps \/ In r (pn C).
Proof. destruct Ps; simpl; rewrite ?in_app_iff; tauto. Qed.

Lemma rt_wf Ps X C : wf C -> wf (rt Ps X C).
Proof. destruct Ps; simpl; [ auto | split; [ discriminate | assumption ] ]. Qed.

(** ** Labels (Definition 1.7) *)

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

(** ** Semantics (Definition 1.8, Figure 1) *)

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
    cstep (CAct eta C) s mu (CAct eta C') s'
| CCall X p s :
    In p (procs X) ->
    cstep (CProc X) s (LTau p)
          (rt (remove (P_eq_dec L) p (procs X)) X (body X)) s
| CEnter Ps X C p s :
    In p Ps ->
    cstep (CRT Ps X C) s (LTau p)
          (rt (remove (P_eq_dec L) p Ps) X C) s
| CInside Ps X C s mu C' s' :
    cstep C s mu C' s' ->
    (forall r, In r Ps -> ~ In r (pn_lbl mu)) ->
    cstep (CRT Ps X C) s mu (CRT Ps X C') s'.

(** ** Lemma 1.13 (Store locality) *)

Lemma cstep_store_locality C s mu C' s' :
  cstep C s mu C' s' ->
  forall r, ~ In r (pn_lbl mu) -> s' r = s r.
Proof.
  induction 1; intros r Hr; simpl in *.
  - apply upd_other; intuition.
  - apply upd_other; intuition.
  - reflexivity.
  - auto.
  - reflexivity.
  - reflexivity.
  - auto.
Qed.

(** ** Remark 1.9 (No delay through a conditional)

    The only step a conditional can take is [CCast]. *)
Lemma cstep_if_inv p e C1 C2 s mu C' s' :
  cstep (CIf p e C1 C2) s mu C' s' ->
  mu = LCast p (receivers p C1 C2) /\
  C' = sel (beval L e (s p)) C1 C2 /\
  s' = s.
Proof.
  intros H; inversion H; subst; auto.
Qed.

(** The side conditions of the grammar are preserved by steps. *)
Lemma cstep_wf C s mu C' s' :
  cstep C s mu C' s' -> wf C -> wf C'.
Proof.
  induction 1; simpl; intros; try tauto.
  - destruct (beval L e (s p)); simpl; tauto.
  - apply rt_wf, body_wf.
  - apply rt_wf; tauto.
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
Arguments CProc {L} & _.
Arguments CRT {L} & _ _ _.
Arguments LTau {L} & _.
Arguments LCom {L} & _ _.
Arguments LCast {L} & _ _.
