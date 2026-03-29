/- # Register state transition equivalence.
   always_ff blocks produce identical flop updates given equivalent wire states. -/

import VerilLean.Lib.Lib
import VerilLean.Lib.HMapLemmas
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame
import VerilLean.Lang.Equiv.Confluence
import VerilLean.Lang.Equiv.StfTopological
import VerilLean.Lang.Equiv.StdTopological
import VerilLean.Lang.Equiv.Equiv
import VerilLean.Lang.Equiv.Bridge
import VerilLean.Lang.Equiv.FullEquiv

namespace VerilLean.Lang.Equiv.RegisterEquiv

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck
  (CombProcess UniqueWrites AcyclicDeps CompleteReads ProperAssignKind
   stmtReads stmtWrites getProcesses)
open VerilLean.Lang.Equiv.Standard (ExecProcess StdStep StdExec Quiescent StdReachesQuiet)
open VerilLean.Lang.Equiv.EvalFrame (CompatUpdate)
open VerilLean.Lang.Equiv.Confluence (StateEquiv WellFoundedDeps)
open VerilLean.Lang.Equiv (ModuleWellFormed module_equiv)
open VerilLean.Lang.Equiv.StfTopological (stf_converges stf_reaches_quiet)
open VerilLean.Lang.Equiv.StdTopological (quiet_unique)
open VerilLean.Lang.Equiv.Bridge (buildExecProcesses)
open VerilLean.Lang.Equiv.FullEquiv (module_concrete_equiv)
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

-- ## Sequential process abstraction

/- A sequential (always_ff) process: reads from converged wire state,
    writes to flops via nonblocking assignments. -/
structure SeqProcess where
  /-- Variables read from the converged wire state. -/
  reads : List VId
  /-- Flop variables written (NBA targets). -/
  writes : List VId
  /-- Given a wire state, produce a flop delta. -/
  exec : State -> trsOk State
  deriving Inhabited

-- ## Building SeqProcesses from module items

-- Build a SeqProcess from an always_ff statement item.
def buildSeqProcess (decls : Decls) (funcs : Funcs) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (si : statement_item) : SeqProcess :=
  { reads := stmtReads si
    writes := stmtWrites si
    exec := fun wireState =>
      match trsVStatementItem decls funcs ctxs cpos ifw false si wireState with
      | .ok (_nw, fl, _ret) => .ok fl
      | .error e => .error e }

-- Extract SeqProcesses from a module_common_item (only always_ff blocks).
def getSeqProcessFromModuleCommonItem (decls : Decls) (funcs : Funcs)
    (ctxs : State) (cpos : HPath) (ifw : IFW)
    : module_common_item -> List SeqProcess
  | .always .always_ff (.stmt si) =>
      [buildSeqProcess decls funcs ctxs cpos ifw si]
  | _ => []

-- Extract SeqProcesses from a module_or_generate_item.
def getSeqProcessFromMOGI (decls : Decls) (funcs : Funcs)
    (ctxs : State) (cpos : HPath) (ifw : IFW)
    : module_or_generate_item -> List SeqProcess
  | .common ci => getSeqProcessFromModuleCommonItem decls funcs ctxs cpos ifw ci
  | .ins _ => []

-- Extract SeqProcesses from a non_port_module_item.
def getSeqProcessFromNPMI (decls : Decls) (funcs : Funcs)
    (ctxs : State) (cpos : HPath) (ifw : IFW)
    : non_port_module_item -> List SeqProcess
  | .module_or_generate_item mogi =>
      getSeqProcessFromMOGI decls funcs ctxs cpos ifw mogi
  | .generated_module_ins _ => []

-- Extract SeqProcesses from a module_item.
def getSeqProcessFromModuleItem (decls : Decls) (funcs : Funcs)
    (ctxs : State) (cpos : HPath) (ifw : IFW)
    : module_item -> List SeqProcess
  | .port_decl _ => []
  | .non_port np => getSeqProcessFromNPMI decls funcs ctxs cpos ifw np

-- Extract SeqProcesses from module_items.
def getSeqProcessesFromModuleItems (decls : Decls) (funcs : Funcs)
    (ctxs : State) (cpos : HPath) (ifw : IFW)
    : module_items -> List SeqProcess
  | .one mi => getSeqProcessFromModuleItem decls funcs ctxs cpos ifw mi
  | .cons mi mis =>
      getSeqProcessFromModuleItem decls funcs ctxs cpos ifw mi ++
      getSeqProcessesFromModuleItems decls funcs ctxs cpos ifw mis

-- Extract all SeqProcesses from a module declaration.
def getSeqProcesses (decls : Decls) (funcs : Funcs)
    (ctxs : State) (cpos : HPath) (ifw : IFW)
    (m : module_decl) : List SeqProcess :=
  match m with
  | .ansi _ _ _ items => getSeqProcessesFromModuleItems decls funcs ctxs cpos ifw items

-- ## Sequential process evaluation

/- Evaluate all sequential processes on a wire state, accumulating flop deltas.
    Each process sees the SAME wire state (not the accumulated flop state).
    The accumulator only collects flop deltas via hupds. -/
def evalSeqProcesses (seqProcs : List SeqProcess) (wireState : State) : trsOk State :=
  seqProcs.foldlM (fun acc sp => do
    let fl <- sp.exec wireState
    pure (hupds acc fl)) HMap.empty

-- ## Core theorem: flop updates are equivalent

/- Helper: foldlM over sequential processes with equal exec results produces
    equal accumulated states. -/
private theorem foldlM_seqProcs_eq
    (seqProcs : List SeqProcess)
    (wireState1 wireState2 : State)
    (hExecEq : forall sp, sp ∈ seqProcs ->
        sp.exec wireState1 = sp.exec wireState2)
    (acc : State) :
    seqProcs.foldlM (fun acc sp => do
      let fl <- sp.exec wireState1
      pure (hupds acc fl)) acc =
    seqProcs.foldlM (fun acc sp => do
      let fl <- sp.exec wireState2
      pure (hupds acc fl)) acc := by
  induction seqProcs generalizing acc with
  | nil => rfl
  | cons sp rest ih =>
    simp only [List.foldlM, bind, Except.bind]
    have heq := hExecEq sp (List.Mem.head _)
    rw [heq]
    cases sp.exec wireState2 with
    | error e => rfl
    | ok fl =>
      simp only [pure, Except.pure]
      exact ih (fun sp' hsp' => hExecEq sp' (List.Mem.tail _ hsp')) (hupds acc fl)

/- Flop updates equivalence: given equivalent wire states, sequential processes
    produce the same flop delta.

    This is the key register-level theorem. The proof is straightforward:
    StateEquiv gives agreement on all variables, hence on each process's reads.
    The frame hypothesis ensures exec results are equal. The foldlM then
    accumulates the same deltas. -/
theorem flop_updates_equiv
    (seqProcs : List SeqProcess)
    (wireState1 wireState2 : State)
    (hEquiv : StateEquiv wireState1 wireState2)
    (hFrame : forall sp, sp ∈ seqProcs ->
        forall s1 s2 : State,
        (forall v, v ∈ sp.reads -> haccess s1 v = haccess s2 v) ->
        sp.exec s1 = sp.exec s2) :
    evalSeqProcesses seqProcs wireState1 = evalSeqProcesses seqProcs wireState2 := by
  unfold evalSeqProcesses
  apply foldlM_seqProcs_eq
  intro sp hmem
  apply hFrame sp hmem
  intro v _hv
  exact hEquiv v

-- ## Additional well-formedness predicates for sequential processes

/- Each flop variable is written by at most one always_ff block.
    This is the sequential analogue of UniqueWrites for combinational processes. -/
def SeqUniqueWrites (seqProcs : List SeqProcess) : Prop :=
  forall (i j : Nat), i ≠ j ->
    forall (sp1 sp2 : SeqProcess),
      seqProcs[i]? = some sp1 -> seqProcs[j]? = some sp2 ->
      forall v, v ∈ sp1.writes -> v ∈ sp2.writes -> False

/- always_ff blocks only read from wire/input variables, not from flop next-states.
    This ensures no combinational dependency among sequential blocks. -/
def SeqReadsFromWires (seqProcs : List SeqProcess) (wireVars : List VId) : Prop :=
  forall sp, sp ∈ seqProcs -> forall v, v ∈ sp.reads -> v ∈ wireVars

-- ## End-to-end register transition equivalence

/- Full register transition equivalence: both wire state and flop next-state agree.

    Given:
    - A well-formed module with combinational processes satisfying ModuleWellFormed
    - The STF combinational convergence produces wire state sf_stf
    - The Standard semantics reaches quiescent wire state sf_std
    - Sequential processes extracted from the module

    Then:
    1. The wire states agree (from combinational equivalence)
    2. The flop updates agree (from flop_updates_equiv)

    This theorem composes module_concrete_equiv with flop_updates_equiv. -/
theorem register_transition_equiv
    (m : module_decl)
    (decls : Decls) (funcs : Funcs)
    (mtrss : MTrss) (ctxs : State) (cpos : HPath)
    (ifw : IFW) (flops : Flops)
    (inputs flops_vids : List VId)
    -- Combinational processes and well-formedness
    (procs := buildExecProcesses decls funcs mtrss ctxs cpos ifw flops m)
    (hwf : ModuleWellFormed procs inputs flops_vids)
    -- Combinational convergence results
    (s0 : State)
    (sf_stf_fields : List (String × HMap))
    (sf_std : State)
    (hstf : stf_converges procs s0 (.str sf_stf_fields))
    (hstd : StdReachesQuiet procs s0 sf_std)
    (hnodup : NoDupKeys sf_stf_fields)
    (hUpdStr : forall ep, ep ∈ procs -> forall u, ep.exec (.str sf_stf_fields) = .ok u ->
        ∃ u_fields, u = .str u_fields ∧
          forall k, k ∈ u_fields.map Prod.fst -> k ∈ sf_stf_fields.map Prod.fst)
    -- Sequential processes
    (seqProcs : List SeqProcess)
    (hSeqFrame : forall sp, sp ∈ seqProcs ->
        forall s1 s2 : State,
        (forall v, v ∈ sp.reads -> haccess s1 v = haccess s2 v) ->
        sp.exec s1 = sp.exec s2) :
    -- Wire states agree (from combinational proof)
    StateEquiv (.str sf_stf_fields) sf_std ∧
    -- Flop updates agree
    evalSeqProcesses seqProcs (.str sf_stf_fields) = evalSeqProcesses seqProcs sf_std := by
  constructor
  · -- Wire state equivalence from the existing combinational proof
    exact module_concrete_equiv m decls funcs mtrss ctxs cpos ifw flops inputs flops_vids
      (procs := procs) hwf s0 sf_stf_fields sf_std hstf hstd hnodup hUpdStr
  · -- Flop update equivalence from flop_updates_equiv
    have hCombEquiv : StateEquiv (.str sf_stf_fields) sf_std :=
      module_concrete_equiv m decls funcs mtrss ctxs cpos ifw flops inputs flops_vids
        (procs := procs) hwf s0 sf_stf_fields sf_std hstf hstd hnodup hUpdStr
    exact flop_updates_equiv seqProcs (.str sf_stf_fields) sf_std hCombEquiv hSeqFrame

/- Corollary: flop updates from equivalent wire states are definitionally equal
    (not just StateEquiv but actual propositional equality of the trsOk result).
    This is stronger than StateEquiv and useful for connecting to concrete
    next-state computations. -/
theorem flop_updates_eq
    (seqProcs : List SeqProcess)
    (wireState1 wireState2 : State)
    (hEquiv : StateEquiv wireState1 wireState2)
    (hFrame : forall sp, sp ∈ seqProcs ->
        forall s1 s2 : State,
        (forall v, v ∈ sp.reads -> haccess s1 v = haccess s2 v) ->
        sp.exec s1 = sp.exec s2)
    (hOk1 : ∃ fl1, evalSeqProcesses seqProcs wireState1 = .ok fl1) :
    ∃ fl, evalSeqProcesses seqProcs wireState1 = .ok fl ∧
          evalSeqProcesses seqProcs wireState2 = .ok fl := by
  obtain ⟨fl1, hfl1⟩ := hOk1
  have heq := flop_updates_equiv seqProcs wireState1 wireState2 hEquiv hFrame
  rw [hfl1] at heq
  exact ⟨fl1, hfl1, heq.symm⟩

end VerilLean.Lang.Equiv.RegisterEquiv
