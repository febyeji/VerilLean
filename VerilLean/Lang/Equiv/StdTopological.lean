/- # Standard execution quiescence.
   Quiescent states are unique (via confluence) and correspond to STF fixed points. -/

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame
import VerilLean.Lang.Equiv.Confluence
import VerilLean.Lang.Equiv.StfTopological

namespace VerilLean.Lang.Equiv.StdTopological

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck (CombProcess UniqueWrites AcyclicDeps CompleteReads)
open VerilLean.Lang.Equiv.Standard (ExecProcess StdStep StdExec Quiescent StdReachesQuiet
  isSettled)
open VerilLean.Lang.Equiv.EvalFrame
open VerilLean.Lang.Equiv.Confluence (confluence StateEquiv WellFoundedDeps)
open VerilLean.Lang.Equiv.StfTopological (stf_converges stf_iterate stf_iterate_n)
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

-- ## Helper: settled processes don't change state in stf_iterate

-- If all processes are settled in sf, then stf_iterate produces sf.
theorem stf_iterate_settled (procs : List ExecProcess) (sf : State)
    (hall_settled : ∀ ep, ep ∈ procs → isSettled ep sf) :
    stf_iterate procs sf = .ok sf := by
  unfold stf_iterate
  -- Generalize: show foldlM f sf procs = .ok sf when all procs are settled
  suffices h : ∀ (ps : List ExecProcess),
      (∀ ep, ep ∈ ps → isSettled ep sf) →
      List.foldlM (fun acc ep => do let u ← ep.exec acc; pure (hupds acc u)) sf ps = Except.ok sf from
    h procs hall_settled
  intro ps
  induction ps with
  | nil => intro _; rfl
  | cons ep rest ih =>
    intro hsettled
    -- ep is settled
    obtain ⟨u, hu_exec, hu_upd⟩ := hsettled ep (List.Mem.head _)
    show Except.bind (Except.bind (ep.exec sf) (fun u => Except.ok (hupds sf u)))
          (fun s' => List.foldlM (fun acc ep => Except.bind (ep.exec acc) (fun u => Except.ok (hupds acc u))) s' rest) = Except.ok sf
    rw [hu_exec]
    show Except.bind (Except.ok (hupds sf u))
          (fun s' => List.foldlM _ s' rest) = Except.ok sf
    simp only [Except.bind]
    rw [hu_upd]
    exact ih (fun ep' hep' => hsettled ep' (List.Mem.tail _ hep'))

-- ## Quiescence uniqueness (via confluence)

/- If standard execution reaches quiescence from two different execution
    orders, the results agree. This is a direct consequence of confluence. -/
theorem quiet_unique
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
  confluence procs inputs flops s0 hUnique hAcyclic hComplete hWritesOk hFrame hExecReads hWF hAllComb hNoSelfDep hWriteComplete hCompat sf1 sf2 h1 h2

end VerilLean.Lang.Equiv.StdTopological
