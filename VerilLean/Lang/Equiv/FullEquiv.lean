/- # Full end-to-end equivalence.
   Concrete STF fixed-point iteration is observably equivalent to Standard quiescence. -/

import VerilLean.Lib.Lib
import VerilLean.Lib.HMapLemmas
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Analysis
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame
import VerilLean.Lang.Equiv.Confluence
import VerilLean.Lang.Equiv.StfTopological
import VerilLean.Lang.Equiv.StdTopological
import VerilLean.Lang.Equiv.Equiv
import VerilLean.Lang.Equiv.Bridge

namespace VerilLean.Lang.Equiv.FullEquiv

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck
  (CombProcess UniqueWrites AcyclicDeps CompleteReads ProperAssignKind getProcesses)
open VerilLean.Lang.Equiv.Standard (ExecProcess StdStep StdExec Quiescent StdReachesQuiet)
open VerilLean.Lang.Equiv.EvalFrame (CompatUpdate)
open VerilLean.Lang.Equiv.Confluence (StateEquiv WellFoundedDeps confluence)
open VerilLean.Lang.Equiv (ModuleWellFormed module_equiv)
open VerilLean.Lang.Equiv.StfTopological (stf_iterate stf_converges stf_reaches_quiet)
open VerilLean.Lang.Equiv.StdTopological (quiet_unique)
open VerilLean.Lang.Equiv.Bridge
  (moduleItemToExecProcess buildExecProcessesFromItems buildExecProcesses
   stf_iterate_eq_trsVModuleItems_acc stf_iterate_eq_trsVModuleDecl_acc)
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

/- ## End-to-end Semantic Bridge

    For a well-formed Verilog module satisfying the static predicates,
    if the concrete STF (`trsVModuleDecl` / `trsM_iff_rep`) converges to
    a state `sf_stf`, and the Standard (event-driven) semantics reaches
    a quiescent state `sf_std`, then `sf_stf` and `sf_std` are
    observably equivalent (agree on all fields via `haccess`).

    This combines:
    1. **Bridge** (Bridge.lean): converts `module_items` to `List ExecProcess`,
       and proves `stf_iterate` matches `trsVModuleItems`.
    2. **STF-Standard Equivalence** (Equiv.lean): proves abstract
       `stf_converges` + `StdReachesQuiet` implies `StateEquiv`.

    Hypotheses:
    - `procs`: the `ExecProcess` list built from the module's items
    - Static predicates: UniqueWrites, AcyclicDeps, CompleteReads
    - Semantic properties: write-set correctness, frame property,
      read-determinism, pairwise disjoint writes, well-founded deps,
      all combinational, no self-dependencies, write completeness,
      compatible updates
    - Convergence: abstract `stf_converges` on the built processes
    - Standard quiescence: `StdReachesQuiet` on the built processes -/
theorem concrete_stf_std_equiv
    (decls : Decls) (funcs : Funcs) (mtrss : MTrss)
    (ctxs : State) (cpos : HPath)
    (m : module_decl) (ifw₀ : IFW) (flops₀ : Flops)
    (inputs flops_vids : List VId)
    -- Build the process list from the concrete module
    (procs := buildExecProcesses decls funcs mtrss ctxs cpos ifw₀ flops₀ m)
    -- The 4 static predicates
    (hUnique : UniqueWrites (procs.map (·.proc)))
    (hAcyclic : AcyclicDeps (procs.map (·.proc)))
    (hComplete : CompleteReads (procs.map (·.proc)) inputs flops_vids)
    -- Semantic properties of the built processes
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hFrame : ∀ ep, ep ∈ procs → ∀ s upd,
        (∀ v, v ∈ ep.proc.reads → haccess upd v = HMap.empty) →
        ep.exec (hupds s upd) = ep.exec s)
    (hExecReads : ∀ ep, ep ∈ procs → ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    (hPairwiseW : procs.Pairwise (fun ep1 ep2 =>
        ∀ v, v ∈ ep1.proc.writes → v ∈ ep2.proc.writes → False))
    (hWF : WellFoundedDeps (procs.map (·.proc)))
    (hAllComb : ∀ ep, ep ∈ procs → ep.proc.isComb = true)
    (hNoSelfDep : ∀ ep, ep ∈ procs → ∀ v, v ∈ ep.proc.reads → v ∉ ep.proc.writes)
    (hWriteComplete : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, vid ∈ ep.proc.writes →
        haccess u vid ≠ HMap.empty ∧
        HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u)
    -- The abstract STF converges (built from Bridge)
    (s0 : State)
    (sf_stf_fields : List (String × HMap))
    (sf_std : State)
    (hstf : stf_converges procs s0 (.str sf_stf_fields))
    (hstd : StdReachesQuiet procs s0 sf_std)
    (hnodup : NoDupKeys sf_stf_fields)
    (hUpdStr : ∀ ep, ep ∈ procs → ∀ u, ep.exec (.str sf_stf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_stf_fields.map Prod.fst) :
    StateEquiv (.str sf_stf_fields) sf_std :=
  -- Directly apply the abstract stf_std_equiv from Equiv.lean
  VerilLean.Lang.Equiv.stf_std_equiv procs s0 inputs flops_vids
    hUnique hAcyclic hComplete hWritesOk hFrame hExecReads hPairwiseW hWF
    hAllComb hNoSelfDep hWriteComplete sf_stf_fields sf_std hstf hstd hnodup hUpdStr hCompat

/- ## Module-level Concrete Equivalence

    For a concrete Verilog module, given `decls`, `funcs`, `mtrss`, etc.,
    if the processes built via `buildExecProcesses` satisfy `ModuleWellFormed`,
    and the STF converges while Standard reaches quiescence, then the
    results are observably equivalent.

    This theorem composes:
    1. `buildExecProcesses` to extract `List ExecProcess` from the module
    2. `ModuleWellFormed` to bundle all required properties
    3. `module_equiv` (from Equiv.lean) to conclude `StateEquiv`

    For any specific module, one would:
    - Instantiate `decls`, `funcs`, `mtrss` from the module AST
    - Build the processes and prove `ModuleWellFormed`
    - Show convergence (by running the concrete iteration)
    - Conclude equivalence -/
theorem module_concrete_equiv
    (m : module_decl) (decls : Decls) (funcs : Funcs)
    (mtrss : MTrss) (ctxs : State) (cpos : HPath) (ifw : IFW) (flops : Flops)
    (inputs flops_vids : List VId)
    (procs := buildExecProcesses decls funcs mtrss ctxs cpos ifw flops m)
    (hwf : ModuleWellFormed procs inputs flops_vids)
    (s0 : State)
    (sf_stf_fields : List (String × HMap))
    (sf_std : State)
    (hstf : stf_converges procs s0 (.str sf_stf_fields))
    (hstd : StdReachesQuiet procs s0 sf_std)
    (hnodup : NoDupKeys sf_stf_fields)
    (hUpdStr : ∀ ep, ep ∈ procs → ∀ u, ep.exec (.str sf_stf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_stf_fields.map Prod.fst) :
    StateEquiv (.str sf_stf_fields) sf_std :=
  module_equiv procs inputs flops_vids hwf s0 sf_stf_fields sf_std
    hstf hstd hnodup hUpdStr

end VerilLean.Lang.Equiv.FullEquiv
