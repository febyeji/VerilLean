/- # Standard (event-driven) Verilog semantics.
   Deterministic and non-deterministic formulations for simulation and proofs. -/

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Analysis
import VerilLean.Lang.Semantics
import VerilLean.Lang.Equiv.StaticCheck

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck (CombProcess)
open VerilLean.Lib

namespace VerilLean.Lang.Equiv.Standard

-- ## Process execution abstraction

-- A process executor: given a state, produces an updated state.
abbrev ProcExec := State → trsOk State

-- A process bundled with its executor.
structure ExecProcess where
  -- Static information about the process (reads, writes, combinational flag).
  proc : CombProcess
  -- The function that evaluates this process on a given state.
  exec : ProcExec

-- ## Triggering

/- Check if a process is triggered by a set of changed variables.
    A process is triggered when it is combinational and at least one
    of its read variables appears in the changed set. -/
def isTriggered (proc : CombProcess) (changed : List VId) : Bool :=
  proc.isComb && proc.reads.any (fun r => changed.any (fun c => r == c))

-- ## Deterministic execution (computation)

/- Execute a single step: trigger all sensitive processes and execute them
    in list order. Returns (new_state, newly_changed_variables).

    Implemented as a left-fold over triggered processes: each process sees
    the state produced by all previously-executed processes in this step. -/
def execStep (procs : List ExecProcess) (s : State) (changed : List VId)
    : trsOk (State × List VId) :=
  let triggered := procs.filter (fun ep => isTriggered ep.proc changed)
  triggered.foldlM
    (fun (acc : State × List VId) ep => do
      let updates ← ep.exec acc.1
      pure (hupds acc.1 updates, acc.2 ++ ep.proc.writes))
    (s, [])

/- Execute until quiescence (no more triggered processes).
    Uses explicit fuel to ensure termination. Returns `.error .notUnfoldable`
    if fuel runs out before quiescence. -/
def execUntilQuiet (fuel : Nat) (procs : List ExecProcess) (s : State)
    (changed : List VId) : trsOk State :=
  match fuel with
  | 0 => .error .notUnfoldable
  | fuel + 1 =>
    let triggered := procs.filter (fun ep => isTriggered ep.proc changed)
    if triggered.isEmpty then
      pure s
    else do
      let (s', newChanged) ← execStep procs s changed
      execUntilQuiet fuel procs s' newChanged

/- Full standard semantics for one combinational evaluation cycle.
    Start with an initial state and initial changed variables (typically
    all inputs and flop outputs), and iterate until quiescence. -/
def stdEval (fuel : Nat) (procs : List ExecProcess) (initialState : State)
    (initialChanged : List VId) : trsOk State :=
  execUntilQuiet fuel procs initialState initialChanged

-- ## Non-deterministic execution (for proofs)

/- One process execution step: pick any process and execute it.
    The step does not require the process to be "triggered" — the
    `Quiescent` predicate handles convergence separately. -/
inductive StdStep (procs : List ExecProcess) : State → State → Prop where
  | step (s : State) (ep : ExecProcess) (updates : State) :
      ep ∈ procs →
      ep.exec s = .ok updates →
      StdStep procs s (hupds s updates)

-- Multi-step execution: reflexive-transitive closure of `StdStep`.
inductive StdExec (procs : List ExecProcess) : State → State → Prop where
  | refl (s : State) :
      StdExec procs s s
  | step (s1 s2 s3 : State) :
      StdStep procs s1 s2 →
      StdExec procs s2 s3 →
      StdExec procs s1 s3

-- ## Fixed-point / quiescence conditions

-- A process is "settled" in a state if executing it does not change the state.
def isSettled (ep : ExecProcess) (s : State) : Prop :=
  ∃ updates, ep.exec s = .ok updates ∧ hupds s updates = s

-- A process is "unsettled" in a state if executing it changes the state.
def isUnsettled (ep : ExecProcess) (s : State) : Prop :=
  ∃ updates, ep.exec s = .ok updates ∧ hupds s updates ≠ s

/- A state is quiescent with respect to a set of processes when every
    combinational process is settled (i.e., at its fixed point). -/
def Quiescent (procs : List ExecProcess) (s : State) : Prop :=
  ∀ ep, ep ∈ procs → ep.proc.isComb = true → isSettled ep s

-- ## Main predicate for equivalence proofs

/- The standard semantics reaches a quiescent state `sf` from initial state `s0`.
    This is the key predicate used in the equivalence theorem: any quiescent
    state reachable from the initial state should equal the STF result. -/
def StdReachesQuiet (procs : List ExecProcess) (s0 sf : State) : Prop :=
  StdExec procs s0 sf ∧ Quiescent procs sf

end VerilLean.Lang.Equiv.Standard
