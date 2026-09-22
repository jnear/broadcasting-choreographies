# Rocq formalization of *A Core Choreographic Language with Multicast Knowledge of Choice*

This directory mechanizes the definitions and results of `../tex/main.tex`
in the Rocq Prover (tested with Rocq 9.1.1 and its standard library).

## Building

```
make          # generates Makefile.coq from _CoqProject and builds everything
make clean
```

## Files

| File | Paper | Contents |
|------|-------|----------|
| `Prelim.v` | §1.1 | The `lang` record of parameters (process names, variables, values, expressions, evaluation), stores and the update `upd`, the selector `sel`, boolean membership helpers. |
| `Chor.v` | §1.2–1.3 | Actions and choreographies (Def. 1.2), `pn` and `receivers` (Def. 1.4), labels (Def. 1.5), the semantics `cstep` (Def. 1.6, Fig. 1), store locality (Lemma 1.7), Remark 1.5 as `cstep_if_inv`, well-formedness `wf`. |
| `Net.v` | §2 | Behaviours and networks (Def. 2.1), the semantics `nstep` (Def. 2.2, Fig. 2), locality and framing (Lemma 4.1), inversion (Lemma 4.2). |
| `EPP.v` | §3 | Endpoint projection `proj` / `projn` (Def. 3.1), projection of prefixes (Lemma 4.3), projection invariance (Lemma 4.4). |
| `Correctness.v` | §4 | Completeness (Thm. 4.5), soundness (Thm. 4.6), bisimulation (Cor. 4.7), progress (Lemma 4.8), deadlock-freedom (Cor. 4.9). |
| `Example.v` | Ex. 1.3, 1.6, 3.3 | A concrete instantiation with three processes; the projection of the running example and its execution are checked by computation. |

## Correspondence with the paper

| Paper | Rocq |
|-------|------|
| Assumption 1.1 | `eval`, `beval` are functions (total and deterministic); guards are a separate class `BExpr` evaluating to `bool` |
| Def. 1.2 | `action`, `chor` |
| Def. 1.4 | `pn_act`, `pn`, `receivers` (with `receivers_spec`) |
| Def. 1.5 | `label`, `pn_lbl` |
| Def. 1.6 | `cstep` with constructors `CLocal`, `CCom`, `CCast`, `CDelay` |
| Lemma 1.7 | `cstep_store_locality` |
| Remark 1.5 | `cstep_if_inv` |
| Def. 2.1 | `behaviour`, `network`, `terminated`, `agree_on` |
| Def. 2.2 | `nstep` with constructors `NLocal`, `NCom`, `NCast` |
| Def. 3.1 | `proj`, `projn` |
| Lemma 4.1 (i) | `nstep_locality` |
| Lemma 4.1 (ii) | `nstep_frame` (and the more general `nstep_frame_gen`) |
| Lemma 4.2 | `nstep_inv_nonnil`, `nstep_inv_local`, `nstep_inv_send`, `nstep_inv_recv`, `nstep_inv_sendbr`, `nstep_inv_recvbr` |
| Lemma 4.3 (i), (ii) | `proj_act_skip`, `proj_nil_of_not_pn` |
| Lemma 4.4 | `proj_invariance` |
| Theorem 4.5 | `completeness` |
| Theorem 4.6 | `soundness` |
| Corollary 4.7 | `bisim_rel`, `bisimulation_forward`, `bisimulation_backward` |
| Lemma 4.8 | `progress` |
| Corollary 4.9 | `deadlock_freedom` (using `reach`, `stuck`, `reach_proj`) |

## Design choices

* **Parameters.** The paper fixes sets of process names, variables and
  values and a local expression language.  These are bundled in the record
  `lang` (`Prelim.v`); every file opens a section with `Context {L : lang}`.
  Finiteness of the set of process names is never needed and is not assumed.
  Decidable equality on process names and variables is assumed.

* **Guards.** Assumption 1.1 requires guards to evaluate to booleans.  Guards
  are given their own syntactic class `BExpr` with `beval : BExpr -> lstore -> bool`,
  so no typing hypothesis is needed anywhere (in particular in `progress`).

* **Sets of process names** are lists with membership `In`.  The receiver
  set of a conditional is computed by the function `receivers`, which is used
  both in the rule `CCast` and in the projection, so the labels of a
  choreography and of its projection agree syntactically.

* **The side condition `p <> q`** on communications (part of the grammar in
  the paper) is the predicate `wf`.  It is a hypothesis of `completeness`
  (the projection of a self-communication cannot step) and is built into the
  bisimulation relation; `soundness` and `progress` do not need it.  `wf` is
  preserved by `cstep` (`cstep_wf`).

* **Network rules are pointwise.**  Networks are functions, as in the paper.
  Each rule of `nstep` fixes the behaviours of the processes in the label and
  requires all other processes to be unchanged, instead of displaying a
  product of the involved processes.  This makes the pairwise-distinctness
  side conditions of Fig. 2 unnecessary (they are derivable, see
  `nstep_cast_sender_not_receiver`) and makes Lemma 4.1 immediate.

* **Axioms.** `completeness` is axiom-free.  `soundness` and
  `deadlock_freedom` use `functional_extensionality` (from the standard
  library) to conclude the equality `N' = projn C'` between networks, which
  are functions.  `Print Assumptions` at the end of `Correctness.v` records
  this.
