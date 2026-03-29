/- # Main equivalence theorem: STF and Standard semantics produce the same result.
   Uses STF convergence + confluence to show observable equivalence. -/

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame
import VerilLean.Lang.Equiv.Confluence
import VerilLean.Lang.Equiv.StfTopological
import VerilLean.Lang.Equiv.StdTopological

namespace VerilLean.Lang.Equiv

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck
  (CombProcess UniqueWrites AcyclicDeps CompleteReads ProperAssignKind getProcesses)
open VerilLean.Lang.Equiv.Standard (ExecProcess StdStep StdExec Quiescent StdReachesQuiet)
open VerilLean.Lang.Equiv.EvalFrame
open VerilLean.Lang.Equiv.Confluence (confluence StateEquiv WellFoundedDeps)
open VerilLean.Lang.Equiv.StfTopological (stf_converges stf_reaches_quiet)
open VerilLean.Lang.Equiv.StdTopological (quiet_unique)
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

/- ## Main Equivalence Theorem

    For a well-formed Verilog module satisfying the 4 static predicates,
    the STF semantics and Standard semantics produce observably equivalent
    results.

    More precisely: if STF converges to some state sf_stf, and Standard
    execution reaches some quiescent state sf_std, then they agree on all
    fields (StateEquiv). -/
theorem stf_std_equiv
    (procs : List ExecProcess)
    (s0 : State)
    (inputs flops : List VId)
    -- The 4 static predicates
    (hUnique : UniqueWrites (procs.map (·.proc)))
    (hAcyclic : AcyclicDeps (procs.map (·.proc)))
    (hComplete : CompleteReads (procs.map (·.proc)) inputs flops)
    -- Write set correctness for all processes
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    -- Frame property for all processes
    (hFrame : ∀ ep, ep ∈ procs → ∀ s upd,
        (∀ v, v ∈ ep.proc.reads → haccess upd v = HMap.empty) →
        ep.exec (hupds s upd) = ep.exec s)
    -- Exec read-determinism: exec only depends on reads
    (hExecReads : ∀ ep, ep ∈ procs → ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    -- Pairwise disjoint writes (stronger than UniqueWrites: covers all processes)
    (hPairwiseW : procs.Pairwise (fun ep1 ep2 =>
        ∀ v, v ∈ ep1.proc.writes → v ∈ ep2.proc.writes → False))
    -- Well-founded dependency relation
    (hWF : WellFoundedDeps (procs.map (·.proc)))
    -- All processes are combinational
    (hAllComb : ∀ ep, ep ∈ procs → ep.proc.isComb = true)
    -- No process reads its own writes
    (hNoSelfDep : ∀ ep, ep ∈ procs → ∀ v, v ∈ ep.proc.reads → v ∉ ep.proc.writes)
    -- Write completeness: writes produce non-empty, same-shape, leaf updates
    (hWriteComplete : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → ∀ vid, vid ∈ ep.proc.writes →
        haccess u vid ≠ HMap.empty ∧
        HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    -- STF and Standard both produce results
    (sf_stf_fields : List (String × HMap))
    (sf_std : State)
    (hstf : stf_converges procs s0 (.str sf_stf_fields))
    (hstd : StdReachesQuiet procs s0 sf_std)
    (hnodup : HMapLemmas.NoDupKeys sf_stf_fields)
    (hUpdStr : ∀ ep, ep ∈ procs → ∀ u, ep.exec (.str sf_stf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_stf_fields.map Prod.fst)
    -- Compatibility: process execution produces compatible updates
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    StateEquiv (HMap.str sf_stf_fields) sf_std := by
  -- Step 1: STF convergence means sf_stf is reachable and quiescent
  have h1 : StdReachesQuiet procs s0 (.str sf_stf_fields) :=
    stf_reaches_quiet procs s0 inputs flops hAcyclic hComplete hWritesOk hPairwiseW
      sf_stf_fields hstf hnodup hUpdStr hCompat
  -- Step 2: Apply confluence — both sf_stf and sf_std are quiescent states
  -- reachable from s0, so they must be observably equivalent
  exact confluence procs inputs flops s0 hUnique hAcyclic hComplete
    hWritesOk hFrame hExecReads hWF hAllComb hNoSelfDep hWriteComplete hCompat
    (.str sf_stf_fields) sf_std h1 hstd

-- ## Corollaries

-- STF convergence implies a unique quiescent state (up to observable equivalence).
theorem stf_unique_fixpoint
    (procs : List ExecProcess)
    (s0 : State)
    (inputs flops : List VId)
    (hUnique : UniqueWrites (procs.map (·.proc)))
    (hAcyclic : AcyclicDeps (procs.map (·.proc)))
    (hComplete : CompleteReads (procs.map (·.proc)) inputs flops)
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hFrame : ∀ ep, ep ∈ procs → ∀ s upd,
        (∀ v, v ∈ ep.proc.reads → haccess upd v = HMap.empty) →
        ep.exec (hupds s upd) = ep.exec s)
    (hExecReads : ∀ ep, ep ∈ procs → ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    (hWF : WellFoundedDeps (procs.map (·.proc)))
    (hAllComb : ∀ ep, ep ∈ procs → ep.proc.isComb = true)
    (hNoSelfDep : ∀ ep, ep ∈ procs → ∀ v, v ∈ ep.proc.reads → v ∉ ep.proc.writes)
    (hWriteComplete : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → ∀ vid, vid ∈ ep.proc.writes →
        haccess u vid ≠ HMap.empty ∧
        HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u)
    (sf1 sf2 : State)
    (h1 : StdReachesQuiet procs s0 sf1)
    (h2 : StdReachesQuiet procs s0 sf2) :
    StateEquiv sf1 sf2 :=
  confluence procs inputs flops s0 hUnique hAcyclic hComplete hWritesOk hFrame hExecReads
    hWF hAllComb hNoSelfDep hWriteComplete hCompat sf1 sf2 h1 h2

-- ## Module-level well-formedness bundle

/- A module is well-formed for the equivalence proof if it satisfies
    the static predicates AND the semantic properties hold for the
    processes extracted from it. This bundles all hypotheses needed
    by `stf_std_equiv` into a single structure. -/
structure ModuleWellFormed (procs : List ExecProcess) (inputs flops_vids : List VId) where
  /-- P1: Every variable is written by at most one combinational process. -/
  unique : UniqueWrites (procs.map (·.proc))
  /-- P2: The dependency graph among combinational processes is acyclic. -/
  acyclic : AcyclicDeps (procs.map (·.proc))
  /-- P3: Every variable read by a combinational process is accounted for. -/
  complete : CompleteReads (procs.map (·.proc)) inputs flops_vids
  /-- Write-set correctness: exec only writes to declared write variables. -/
  writesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
      ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes
  /-- Frame property: execution is insensitive to non-read variables. -/
  frame : ∀ ep, ep ∈ procs → ∀ s upd,
      (∀ v, v ∈ ep.proc.reads → haccess upd v = HMap.empty) →
      ep.exec (hupds s upd) = ep.exec s
  /-- Read-determinism: execution depends only on reads. -/
  execReads : ∀ ep, ep ∈ procs → ∀ s1 s2 : State,
      (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
      ep.exec s1 = ep.exec s2
  /-- Pairwise disjoint writes across all processes. -/
  pairwiseW : procs.Pairwise (fun ep1 ep2 =>
      ∀ v, v ∈ ep1.proc.writes → v ∈ ep2.proc.writes → False)
  /-- Well-founded dependency relation among processes. -/
  wf : WellFoundedDeps (procs.map (·.proc))
  /-- All processes are combinational. -/
  allComb : ∀ ep, ep ∈ procs → ep.proc.isComb = true
  /-- No process reads its own writes. -/
  noSelfDep : ∀ ep, ep ∈ procs → ∀ v, v ∈ ep.proc.reads → v ∉ ep.proc.writes
  /-- Write completeness: writes produce non-empty, same-shape, leaf updates. -/
  writeComplete : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → ∀ vid, vid ∈ ep.proc.writes →
      haccess u vid ≠ HMap.empty ∧
      HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
      HMapLemmas.IsLeaf (haccess u vid)
  /-- Compatibility: process execution produces compatible updates. -/
  compat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u

/- ## Module-level Equivalence Theorem

    For a module whose extracted processes satisfy `ModuleWellFormed`,
    if the STF converges and the Standard semantics reaches quiescence,
    the results are observably equivalent.

    This is the module-level wrapper around `stf_std_equiv` that packages
    all hypotheses via `ModuleWellFormed`. -/
theorem module_equiv
    (procs : List ExecProcess)
    (inputs flops_vids : List VId)
    (hwf : ModuleWellFormed procs inputs flops_vids)
    (s0 : State)
    (sf_stf_fields : List (String × HMap))
    (sf_std : State)
    (hstf : stf_converges procs s0 (.str sf_stf_fields))
    (hstd : StdReachesQuiet procs s0 sf_std)
    (hnodup : HMapLemmas.NoDupKeys sf_stf_fields)
    (hUpdStr : ∀ ep, ep ∈ procs → ∀ u, ep.exec (.str sf_stf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_stf_fields.map Prod.fst) :
    StateEquiv (.str sf_stf_fields) sf_std :=
  stf_std_equiv procs s0 inputs flops_vids
    hwf.unique hwf.acyclic hwf.complete hwf.writesOk hwf.frame hwf.execReads
    hwf.pairwiseW hwf.wf hwf.allComb hwf.noSelfDep hwf.writeComplete
    sf_stf_fields sf_std hstf hstd hnodup hUpdStr hwf.compat

end VerilLean.Lang.Equiv
