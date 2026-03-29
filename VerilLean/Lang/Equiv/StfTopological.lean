/- # STF fixed-point iteration implies quiescence.
   The STF result is reachable via StdExec and is Quiescent. -/

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame
import VerilLean.Lang.Equiv.Confluence

namespace VerilLean.Lang.Equiv.StfTopological

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck (CombProcess UniqueWrites AcyclicDeps CompleteReads)
open VerilLean.Lang.Equiv.Standard (ExecProcess StdStep StdExec Quiescent StdReachesQuiet
  isSettled)
open VerilLean.Lang.Equiv.EvalFrame
open VerilLean.Lang.Equiv.Confluence
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

-- ## STF convergence

/- One STF iteration: fold all processes over the state, applying each
    process's updates in list order. -/
def stf_iterate (procs : List ExecProcess) (s : State) : trsOk State :=
  procs.foldlM (fun acc ep => do
    let u ← ep.exec acc
    pure (hupds acc u)) s

/- Apply stf_iterate n times, starting from s0. If any iteration fails,
    the state is left unchanged from that point. -/
def stf_iterate_n (procs : List ExecProcess) : Nat → State → State
  | 0, s => s
  | n + 1, s =>
    match stf_iterate procs s with
    | .ok s' => stf_iterate_n procs n s'
    | .error _ => s

/- STF convergence: iterating the module evaluation produces a fixed point.
    There exists some number of iterations n such that iterating all processes
    n times from s0 produces sf, and one more iteration produces sf again. -/
def stf_converges (procs : List ExecProcess) (s0 sf : State) : Prop :=
  ∃ n : Nat,
    (stf_iterate_n procs n s0 = sf) ∧
    (stf_iterate procs sf = .ok sf)

-- ## Helper: one STF iteration is a sequence of StdSteps

/- Helper: foldlM over a sublist produces a StdExec chain.
    One STF iteration corresponds to executing each process in sequence,
    which is a chain of StdStep applications. -/
private theorem foldlM_std_exec (procs ps : List ExecProcess) (acc : State) (sf : State)
    (hsub : ∀ ep, ep ∈ ps → ep ∈ procs)
    (hfold : ps.foldlM (fun acc ep => do let u ← ep.exec acc; pure (hupds acc u)) acc = .ok sf) :
    StdExec procs acc sf := by
  induction ps generalizing acc with
  | nil =>
    have : acc = sf := by simpa [List.foldlM, pure, Except.pure] using hfold
    rw [this]; exact StdExec.refl sf
  | cons ep rest ih =>
    -- foldlM (ep :: rest) acc = (do let u ← ep.exec acc; pure (hupds acc u)) >>= foldlM rest
    -- Since the overall result is .ok sf, the first step must succeed
    -- i.e., ep.exec acc must return .ok u for some u
    have hfold' := hfold
    simp only [List.foldlM, bind, Except.bind] at hfold'
    -- After simp, hfold' should have the intermediate step exposed
    -- ep.exec acc could be .ok or .error; if error, the bind propagates error
    -- and we can't get .ok sf, contradiction
    cases hexec : ep.exec acc with
    | error e =>
      -- Substituting into hfold gives hfold' : .error e = .ok sf
      simp only [hexec] at hfold'
      -- hfold' : Except.error e = Except.ok sf, which is False
      nomatch hfold'
    | ok u =>
      simp only [hexec] at hfold'
      -- hfold' now says: foldlM rest (hupds acc u) = .ok sf
      have hstep : StdStep procs acc (hupds acc u) :=
        StdStep.step acc ep u (hsub ep (List.Mem.head _)) hexec
      have hrest : StdExec procs (hupds acc u) sf :=
        ih (hupds acc u) (fun ep' hep' => hsub ep' (List.Mem.tail _ hep')) hfold'
      exact StdExec.step acc (hupds acc u) sf hstep hrest

theorem stf_iterate_is_std_exec (procs : List ExecProcess) (s sf : State)
    (h : stf_iterate procs s = .ok sf) :
    StdExec procs s sf := by
  exact foldlM_std_exec procs procs s sf (fun _ h => h) h

-- ## STF convergence implies quiescence

/- Helper: if foldlM over a suffix of processes starting from some state s
    returns sf, and no process in the suffix writes to variable v
    (by write-set correctness), then haccess sf v = haccess s v. -/
private theorem foldlM_preserves_unwritten
    (ps : List ExecProcess) (s sf : State)
    (hfold : ps.foldlM (fun acc ep => do let u ← ep.exec acc; pure (hupds acc u)) s = .ok sf)
    (hWritesOk : ∀ ep, ep ∈ ps → ∀ st u, ep.exec st = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (v : VId) (hv : ∀ ep, ep ∈ ps → v ∉ ep.proc.writes)
    (hCompat : ∀ ep, ep ∈ ps → ∀ st u, ep.exec st = .ok u → CompatUpdate st u) :
    haccess sf v = haccess s v := by
  induction ps generalizing s with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at hfold
    rw [← hfold]
  | cons ep rest ih =>
    simp only [List.foldlM, bind, Except.bind] at hfold
    cases hexec : ep.exec s with
    | error e => simp [hexec] at hfold
    | ok u =>
      simp [hexec] at hfold
      have hv_ep : v ∉ ep.proc.writes := hv ep (List.Mem.head _)
      have hu_v : haccess u v = HMap.empty := by
        exact Classical.byContradiction fun h =>
          hv_ep (hWritesOk ep (List.Mem.head _) s u hexec v h)
      have hcompat_su : CompatUpdate s u := hCompat ep (List.Mem.head _) s u hexec
      have h1 : haccess (hupds s u) v = haccess s v := haccess_hupds_miss s u v hu_v hcompat_su
      have h2 : haccess sf v = haccess (hupds s u) v :=
        ih (hupds s u) hfold
          (fun ep' hep' => hWritesOk ep' (List.Mem.tail _ hep'))
          (fun ep' hep' => hv ep' (List.Mem.tail _ hep'))
          (fun ep' hep' => hCompat ep' (List.Mem.tail _ hep'))
      rw [h2, h1]

/- Core fold decomposition: under pairwise-disjoint writes + write-set
    correctness, if foldlM starting from sf returns sf, then each step is
    identity (the accumulator stays sf throughout).

    At each step, ep.exec sf = .ok u and we show hupds sf u = sf. For any vid:
    - If vid ∈ ep.proc.writes: by pairwise disjointness, no later process
      writes vid. By foldlM_preserves_unwritten, the fold after this step
      preserves vid, so haccess (hupds sf u) vid = haccess sf vid.
    - If vid ∉ ep.proc.writes: by write-set correctness, haccess u vid = .empty.
      By haccess_hupds_miss, haccess (hupds sf u) vid = haccess sf vid.
    By hupds_eq_of_haccess_agree, hupds sf u = sf. -/
private theorem fold_acc_stays_sf
    (ps : List ExecProcess) (sf_fields : List (String × HMap))
    (hfold : ps.foldlM (fun acc ep => do let u ← ep.exec acc; pure (hupds acc u)) (.str sf_fields) = .ok (.str sf_fields))
    (hWritesOk : ∀ ep, ep ∈ ps → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hPairwise : ps.Pairwise (fun ep1 ep2 =>
        ∀ v, v ∈ ep1.proc.writes → v ∈ ep2.proc.writes → False))
    -- Well-formedness: state has no duplicate keys
    (hnodup : NoDupKeys sf_fields)
    -- Process execution on .str states produces .str updates with contained keys
    (hUpdStr : ∀ ep, ep ∈ ps → ∀ u, ep.exec (.str sf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_fields.map Prod.fst)
    -- Compatibility: process execution produces compatible updates
    (hCompat : ∀ ep, ep ∈ ps → ∀ st u, ep.exec st = .ok u → CompatUpdate st u)
    :
    ∀ ep, ep ∈ ps → isSettled ep (.str sf_fields) := by
  induction ps with
  | nil => intro ep hep; simp at hep
  | cons ep0 rest ih =>
    simp only [List.foldlM, bind, Except.bind] at hfold
    cases hexec0 : ep0.exec (.str sf_fields) with
    | error e => simp [hexec0] at hfold
    | ok u0 =>
      simp [hexec0] at hfold
      have hPW := List.pairwise_cons.mp hPairwise
      -- u0 must be .str with contained keys (by hUpdStr)
      obtain ⟨u0_fields, hu0_eq, hkeys⟩ := hUpdStr ep0 (List.Mem.head _) u0 hexec0
      subst hu0_eq
      have hstep_id : hupds (.str sf_fields) (.str u0_fields) = .str sf_fields := by
        apply hupds_eq_of_haccess_agree
        · intro vid
          by_cases hvid : haccess (.str u0_fields) vid = HMap.empty
          · exact haccess_hupds_miss (.str sf_fields) (.str u0_fields) vid hvid (by simp [CompatUpdate])
          · have hvid_writes : vid ∈ ep0.proc.writes :=
              hWritesOk ep0 (List.Mem.head _) (.str sf_fields) (.str u0_fields) hexec0 vid hvid
            have hno_later : ∀ ep', ep' ∈ rest → vid ∉ ep'.proc.writes := by
              intro ep' hep' hvid'
              exact hPW.1 ep' hep' vid hvid_writes hvid'
            exact (foldlM_preserves_unwritten rest (hupds (.str sf_fields) (.str u0_fields)) (.str sf_fields) hfold
              (fun ep' hep' => hWritesOk ep' (List.Mem.tail _ hep'))
              vid hno_later
              (fun ep' hep' => hCompat ep' (List.Mem.tail _ hep'))).symm
        · exact hnodup
        · exact hkeys
      rw [hstep_id] at hfold
      intro ep hep
      cases List.mem_cons.mp hep with
      | inl heq =>
        subst heq
        exact ⟨.str u0_fields, hexec0, hstep_id⟩
      | inr hep_rest =>
        exact ih hfold
          (fun ep' hep' => hWritesOk ep' (List.Mem.tail _ hep'))
          hPW.2
          (fun ep' hep' u hexec => hUpdStr ep' (List.Mem.tail _ hep') u hexec)
          (fun ep' hep' => hCompat ep' (List.Mem.tail _ hep')) ep hep_rest

-- ## STF convergence implies quiescence

/- STF convergence implies quiescence: if iterating all processes one more
    time doesn't change the state, then every combinational process is settled.

    Requires pairwise-disjoint writes and write-set correctness. -/
theorem stf_convergence_is_quiescent (procs : List ExecProcess) (s0 : State)
    (sf_fields : List (String × HMap))
    (hconv : stf_converges procs s0 (.str sf_fields))
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hPairwiseW : procs.Pairwise (fun ep1 ep2 =>
        ∀ v, v ∈ ep1.proc.writes → v ∈ ep2.proc.writes → False))
    (hnodup : NoDupKeys sf_fields)
    (hUpdStr : ∀ ep, ep ∈ procs → ∀ u, ep.exec (.str sf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_fields.map Prod.fst)
    (hCompat : ∀ ep, ep ∈ procs → ∀ st u, ep.exec st = .ok u → CompatUpdate st u) :
    Quiescent procs (.str sf_fields) := by
  obtain ⟨_, _, hfix⟩ := hconv
  intro ep hep _hisComb
  unfold stf_iterate at hfix
  exact fold_acc_stays_sf procs sf_fields hfix hWritesOk hPairwiseW hnodup hUpdStr hCompat ep hep

-- Helper: transitivity of StdExec
private theorem StdExec.trans' {procs : List ExecProcess} {s1 s2 s3 : State}
    (h1 : StdExec procs s1 s2) (h2 : StdExec procs s2 s3) :
    StdExec procs s1 s3 := by
  induction h1 with
  | refl _ => exact h2
  | step _ _ _ hstep _ ih => exact StdExec.step _ _ _ hstep (ih h2)

-- ## STF convergence implies reachability

/- STF convergence implies reachability via standard steps: each iteration
    of the fold corresponds to a sequence of StdStep applications. -/
theorem stf_convergence_reachable (procs : List ExecProcess) (s0 sf : State)
    (hconv : stf_converges procs s0 sf) :
    StdExec procs s0 sf := by
  obtain ⟨n, hiter, _⟩ := hconv
  -- By induction on n: each stf_iterate_n step is a sequence of StdSteps
  revert s0 sf
  induction n with
  | zero =>
    intro s0 sf hiter _
    simp [stf_iterate_n] at hiter
    rw [← hiter]
    exact StdExec.refl s0
  | succ k ih =>
    intro s0 sf hiter hfix
    simp [stf_iterate_n] at hiter
    split at hiter
    case h_1 s' hs' =>
      -- stf_iterate procs s0 = .ok s'
      -- stf_iterate_n k s' = sf
      have hstep : StdExec procs s0 s' := stf_iterate_is_std_exec procs s0 s' hs'
      have hrest : StdExec procs s' sf := ih s' sf hiter hfix
      exact StdExec.trans' hstep hrest
    case h_2 e he =>
      -- stf_iterate failed, so sf = s0
      rw [← hiter]
      exact StdExec.refl s0

-- ## Main theorem

/- The STF fixed-point iteration, upon convergence, produces a quiescent state
    reachable from the initial state via standard execution steps.

    Intuition: STF iterates all module items in order until convergence.
    Each iteration effectively executes all processes. After convergence,
    the state is a fixed point where no process would change anything.
    This is exactly what Quiescent means in the Standard semantics.

    We show that the STF result is reachable via StdExec and is Quiescent. -/
theorem stf_reaches_quiet
    (procs : List ExecProcess)
    (s0 : State)
    (inputs flops : List VId)
    (_hAcyclic : AcyclicDeps (procs.map (·.proc)))
    (_hComplete : CompleteReads (procs.map (·.proc)) inputs flops)
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hPairwiseW : procs.Pairwise (fun ep1 ep2 =>
        ∀ v, v ∈ ep1.proc.writes → v ∈ ep2.proc.writes → False))
    (sf_fields : List (String × HMap))
    (hstf : stf_converges procs s0 (.str sf_fields))
    (hnodup : NoDupKeys sf_fields)
    (hUpdStr : ∀ ep, ep ∈ procs → ∀ u, ep.exec (.str sf_fields) = .ok u →
        ∃ u_fields, u = .str u_fields ∧
          ∀ k, k ∈ u_fields.map Prod.fst → k ∈ sf_fields.map Prod.fst)
    (hCompat : ∀ ep, ep ∈ procs → ∀ st u, ep.exec st = .ok u → CompatUpdate st u) :
    StdReachesQuiet procs s0 (.str sf_fields) := by
  constructor
  · exact stf_convergence_reachable procs s0 (.str sf_fields) hstf
  · exact stf_convergence_is_quiescent procs s0 sf_fields hstf hWritesOk hPairwiseW hnodup hUpdStr hCompat

end VerilLean.Lang.Equiv.StfTopological
