# Rocq formalization of *A Core Choreographic Language with Multicast Knowledge of Choice and Recursion*

This directory mechanizes the definitions and results of
`../tex-functions/main.tex` in the Rocq Prover (tested with Rocq 9.1.1 and
its standard library).  It extends the formalization of the language without
procedures in `../rocq/`, keeping the same files, names and proof structure.

## Building

```
make          # generates Makefile.coq from _CoqProject and builds everything
make clean
```

## Files

| File | Paper | Contents |
|------|-------|----------|
| `Prelim.v` | §1.1 | The `lang` record of parameters (process names, variables, values, expressions, evaluation, procedure names), stores and the update `upd`, the selector `sel`, boolean membership helpers. |
| `Chor.v` | §1.2–1.3 | Actions and choreographies (Def. 1.2), procedure definitions `defs` (Def. 1.3), `pn` with the participants `procs` computed as a least fixed point (Def. 1.4, Lemma 1.5), `receivers`, the convention `rt` for runtime terms, labels (Def. 1.7), the semantics `cstep` (Def. 1.8, Fig. 1), store locality (Lemma 1.13), Remark 1.9 as `cstep_if_inv`, the grammar side conditions `wf`. |
| `Net.v` | §2 | Behaviours, local procedure definitions `ldefs` and networks (Def. 2.1), the semantics `nstep` (Def. 2.2, Fig. 2), locality and framing (Lemma 4.1), inversion (Lemma 4.2). |
| `EPP.v` | §3 | Endpoint projection `proj` / `projn` and the projection of the definitions `projd` (Def. 3.1), projection and process names (Lemma 4.3), projection invariance (Lemma 4.4). |
| `Correctness.v` | §4 | Well-formedness `wf_rt` (Def. 4.5) and its preservation (Lemma 4.7), completeness (Thm. 4.8), soundness (Thm. 4.9), bisimulation (Cor. 4.10), progress (Lemma 4.11), deadlock-freedom (Cor. 4.12), Remark 4.13. |
| `Example.v` | Ex. 1.6, 1.11, 3.3, 4.6 | A concrete instantiation with three processes and the procedure `Loop`. The participants, receivers and projected definitions are checked by computation, the execution of Ex. 1.11 is derived, and the network of Ex. 4.6 is shown to deadlock. |

## Correspondence with the paper

| Paper | Rocq |
|-------|------|
| Assumption 1.1 | `eval`, `beval` are functions (total and deterministic); guards are a separate class `BExpr` evaluating to `bool` |
| §1.1 (procedure names) | `PName`, with `PName_all` listing all of them |
| Def. 1.2 | `action`, `chor` (calls `CProc X`, runtime terms `CRT Ps X C`), `source` |
| Def. 1.3 | `defs` (`body`, `body_wf`, `body_source`) |
| Def. 1.4 | `pn_act`, `pn_with`, `procs`, `pn`, `receivers` (with `receivers_spec`) |
| Lemma 1.5 | `procs_fix`; leastness is `procs_least` |
| Convention for `∅ : X.C` | `rt`, with `pn_rt` |
| Def. 1.7 | `label`, `pn_lbl` |
| Def. 1.8 | `cstep` with constructors `CLocal`, `CCom`, `CCast`, `CDelay`, `CCall`, `CEnter`, `CInside` |
| Remark 1.9 | `cstep_if_inv` |
| Lemma 1.13 | `cstep_store_locality` |
| Def. 2.1 | `behaviour` (including `BCall`), `ldefs`, `network`, `terminated`, `agree_on` |
| Def. 2.2 | `nstep` with constructors `NLocal`, `NCom`, `NCast`, `NCall` |
| Def. 3.1 | `proj`, `projn`, `projd` |
| Lemma 4.1 (i) | `nstep_locality` |
| Lemma 4.1 (ii) | `nstep_frame` (and the more general `nstep_frame_gen`) |
| Lemma 4.2 | `nstep_inv_nonnil`, `nstep_inv_local`, `nstep_inv_send`, `nstep_inv_recv`, `nstep_inv_sendbr`, `nstep_inv_recvbr`, `nstep_inv_call` |
| Lemma 4.3 (i), (ii), (iii) | `proj_act_skip`; `pn_rt`, `proj_rt`; `proj_nil_iff` (from `proj_nil_of_not_pn` and `proj_nonnil_of_pn`) |
| Lemma 4.4 | `proj_invariance` |
| Def. 4.5 | `wf_rt` (with `source_wf_rt`) |
| Ex. 4.6 | `C_bad_not_wf_rt`, `C_bad_step`, `C_bad_net_not_complete`, `N_bad_deadlock` |
| Lemma 4.7 | `cstep_wf_rt` |
| Theorem 4.8 | `completeness` |
| Theorem 4.9 | `soundness` |
| Corollary 4.10 | `bisim_rel`, `bisimulation_forward`, `bisimulation_backward` |
| Lemma 4.11 | `progress` |
| Corollary 4.12 | `deadlock_freedom` (using `reach`, `stuck`, `reach_proj`) |
| Remark 4.13 | `pn_nil_iff_nil` |

## Design choices

The choices of `../rocq/` carry over unchanged: parameters bundled in
`lang`, guards as a separate class `BExpr`, sets of processes as lists, the
computed receiver set shared by `CCast` and the projection, pointwise network
rules, and the use of `functional_extensionality` only to conclude equalities
between networks.  The additions are as follows.

* **Procedure names.** The paper fixes a finite set of procedure names.
  `lang` gains a type `PName` and a list `PName_all` containing every
  procedure name.  This finiteness is used only to compute the least fixed
  point below.  Process names are still not assumed finite, and decidable
  equality on procedure names is not needed.

* **Definitions as classes.** The paper fixes one set of procedure
  definitions throughout.  It is the class `defs` (in `Chor.v`), whose fields
  are the bodies and proofs that they are source choreographies satisfying
  the grammar's side conditions.  Every later file opens its section with
  `Context {L : lang} {D : @defs L}`, so the statements of all theorems are
  those of `../rocq/`.  The network semantics is likewise parameterised by
  local definitions, the class `ldefs` (in `Net.v`).  `EPP.v` declares the
  projection of the definitions, `projd`, as an instance of `ldefs`.  Every
  network transition in `Correctness.v` and `Example.v` is therefore taken
  with respect to the projected definitions, as in §4 of the paper.

* **Participants as a least fixed point.**
  - `pn_with rho` is the paper's `pn_ρ`.
  - `procs_iter` iterates `ρ ↦ (X ↦ pn_ρ(body X))` from the everywhere-empty
    function, removing duplicates.
  - `procs` is the iterate at `procs_bound`, the number of procedure names
    times the number of processes occurring in the bodies.
  - Convergence by then is proved with a measure (the total number of
    distinct participants found so far): it is bounded and strictly
    increases until the iteration is stable.  Stability is decided by a
    boolean test, so no classical axiom is needed.
  - `procs_fix` is the fixed-point property (Lemma 1.5) and `procs_least`
    is leastness.  As in the paper, the correctness proofs use only
    `procs_fix`.
  - `pn` is its own fixpoint, which calls `procs` for procedure calls, so it
    unfolds exactly as in `../rocq/`; `pn_pn_with` relates it to `pn_with`.

* **Runtime terms and the convention for the empty set.** `CRT Ps X C` is
  the runtime term `Ps : X.C`.  The paper reads `∅ : X.C` as `C`; this is
  the function `rt`, used in the targets of `CCall` and `CEnter`.  Removing a
  process from a set is `remove`.

* **Two well-formedness predicates.**
  - `wf` records the side conditions of the grammar, as in `../rocq/`: `p <> q`
    in communications, and now also a nonempty set in runtime terms.
    `completeness` needs it, `soundness` and `progress` do not, and it is
    preserved by steps (`cstep_wf`).
  - `wf_rt` is the paper's well-formedness of runtime terms (Def. 4.5).
    `completeness` and `soundness` need it, every source choreography
    satisfies it (`source_wf_rt`), and steps preserve it (`cstep_wf_rt`).
  - The bisimulation relation `bisim_rel` and `deadlock_freedom` assume both.

* **Progress** is stated as in the paper, for `pn C <> []`, and proved by
  induction.  It therefore does not need the nonemptiness of the set in a
  runtime term.

* **Axioms.** `completeness` is axiom-free.  `soundness` and
  `deadlock_freedom` use `functional_extensionality` (from the standard
  library) to conclude the equality `N' = projn C'` between networks, which
  are functions.  `Print Assumptions` at the end of `Correctness.v` records
  this.
