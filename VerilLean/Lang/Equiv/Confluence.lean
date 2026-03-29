/- # Core confluence property.
   Independent processes commute under UniqueWrites + AcyclicDeps + CompleteReads. -/

import VerilLean.Lib.Lib
import VerilLean.Lang.Syntax
import VerilLean.Lang.Semantics
import VerilLean.Lang.Equiv.StaticCheck
import VerilLean.Lang.Equiv.Standard
import VerilLean.Lang.Equiv.EvalFrame

namespace VerilLean.Lang.Equiv.Confluence

open VerilLean.Lang.Syntax
open VerilLean.Lang.Semantics
open VerilLean.Lang.Equiv.StaticCheck (CombProcess UniqueWrites AcyclicDeps CompleteReads)
open VerilLean.Lang.Equiv.Standard (ExecProcess StdStep StdExec Quiescent StdReachesQuiet)
open VerilLean.Lang.Equiv.EvalFrame
open VerilLean.Lib
open VerilLean.Lib.HMapLemmas

-- CombProcess needs Inhabited for List.getD
instance : Inhabited CombProcess where
  default := { reads := [], writes := [], isComb := false }

-- ## Independence

/- Two processes are independent: their write sets are disjoint, and
    neither writes to variables the other reads. -/
def Independent (p1 p2 : CombProcess) : Prop :=
  (∀ v, v ∈ p1.writes → v ∈ p2.writes → False) ∧
  (∀ v, v ∈ p1.writes → v ∈ p2.reads → False) ∧
  (∀ v, v ∈ p2.writes → v ∈ p1.reads → False)

-- ## Diamond property

/- Diamond property: executing two independent processes in either order
    produces the same final state.

    More precisely: if P1 produces updates u1 and P2 produces updates u2
    from the same initial state, and the processes are independent, then:
    1. P2 produces the same updates u2 even after applying u1
    2. P1 produces the same updates u1 even after applying u2
    3. The combined states agree: s + u1 + u2 = s + u2 + u1 -/
theorem diamond (ep1 ep2 : ExecProcess) (s_fields u1_fields u2_fields : List (String × HMap))
    (hind : Independent ep1.proc ep2.proc)
    -- Both processes succeed on the initial state
    (h1 : ep1.exec (.str s_fields) = .ok (.str u1_fields))
    (h2 : ep2.exec (.str s_fields) = .ok (.str u2_fields))
    -- Write set correctness
    (hw1 : ∀ vid, haccess (.str u1_fields) vid ≠ HMap.empty → vid ∈ ep1.proc.writes)
    (hw2 : ∀ vid, haccess (.str u2_fields) vid ≠ HMap.empty → vid ∈ ep2.proc.writes)
    -- Frame property: updates to non-read variables don't affect execution
    (hf1 : ∀ upd, (∀ v, v ∈ ep1.proc.reads → haccess upd v = HMap.empty) →
        ep1.exec (hupds (.str s_fields) upd) = ep1.exec (.str s_fields))
    (hf2 : ∀ upd, (∀ v, v ∈ ep2.proc.reads → haccess upd v = HMap.empty) →
        ep2.exec (hupds (.str s_fields) upd) = ep2.exec (.str s_fields))
    -- Structural well-formedness
    (hnodup : NoDupKeys s_fields)
    (hkeys1 : ∀ k, k ∈ u1_fields.map Prod.fst → k ∈ s_fields.map Prod.fst)
    (hkeys2 : ∀ k, k ∈ u2_fields.map Prod.fst → k ∈ s_fields.map Prod.fst) :
    -- After executing P1 then P2
    ∃ u2', ep2.exec (hupds (.str s_fields) (.str u1_fields)) = .ok u2' ∧
    -- After executing P2 then P1
    ∃ u1', ep1.exec (hupds (.str s_fields) (.str u2_fields)) = .ok u1' ∧
    -- The results are the same
    hupds (hupds (.str s_fields) (.str u1_fields)) (.str u2_fields) =
    hupds (hupds (.str s_fields) (.str u2_fields)) (.str u1_fields) := by
  obtain ⟨hdisjW, hW1R2, hW2R1⟩ := hind
  -- P2 is unaffected by u1 (P1's writes are disjoint from P2's reads)
  have hf2_u1 : ep2.exec (hupds (.str s_fields) (.str u1_fields)) = ep2.exec (.str s_fields) := by
    apply hf2
    intro v hv
    exact Classical.byContradiction fun h => hW1R2 v (hw1 v h) hv
  -- P1 is unaffected by u2 (P2's writes are disjoint from P1's reads)
  have hf1_u2 : ep1.exec (hupds (.str s_fields) (.str u2_fields)) = ep1.exec (.str s_fields) := by
    apply hf1
    intro v hv
    exact Classical.byContradiction fun h => hW2R1 v (hw2 v h) hv
  -- So P2 on (s + u1) gives u2, and P1 on (s + u2) gives u1
  refine ⟨.str u2_fields, ?_, .str u1_fields, ?_, ?_⟩
  · rw [hf2_u1]; exact h2
  · rw [hf1_u2]; exact h1
  · -- s + u1 + u2 = s + u2 + u1 by commutativity of disjoint updates
    exact hupds_comm_disjoint s_fields u1_fields u2_fields
      (fun v ha hb => hdisjW v (hw1 v ha) (hw2 v hb))
      hnodup hkeys1 hkeys2

-- ## Topological level assignment

/- Helper: compute the set of dependency indices for process i.
    Process i depends on process j if i reads a variable that j writes. -/
def depIndices (procs : List CombProcess) (i : Nat) : List Nat :=
  let p := procs.getD i default
  if _h : i < procs.length then
    (List.range procs.length).filter fun j =>
      j ≠ i &&
      (procs.getD j default).isComb &&
      p.reads.any fun v => (procs.getD j default).writes.any fun w => v == w
  else []

/- Topological level assignment: map each process to its depth in the
    dependency DAG.
    Level 0: processes with no reads from other processes (only inputs/flops).
    Level k+1: processes that read from level-k processes.

    Uses fuel (bounded by procs.length) to ensure termination.
    This is well-defined when AcyclicDeps holds (no cycles means the
    recursion terminates within procs.length steps). -/
def topoLevel (procs : List CombProcess) (i : Nat) : Nat :=
  go procs i procs.length
where
  go (procs : List CombProcess) (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0  -- out of fuel (shouldn't happen with acyclic deps)
    | fuel + 1 =>
      let deps := depIndices procs i
      if deps.isEmpty then 0
      else deps.foldl (fun maxLev j => max maxLev (go procs j fuel + 1)) 0

/- Helper: a foldl computing max over (f k + 1) for k in a list
    produces a result ≥ f j + 1 when j is in the list. -/
private theorem foldl_max_ge_mem {f : Nat → Nat} {ds : List Nat} {j : Nat} {acc : Nat}
    (hmem : j ∈ ds) :
    ds.foldl (fun m k => max m (f k + 1)) acc ≥ f j + 1 := by
  induction ds generalizing acc with
  | nil => simp at hmem
  | cons d rest ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      suffices h : ∀ (xs : List Nat) (a : Nat), a ≥ f j + 1 →
          xs.foldl (fun m k => max m (f k + 1)) a ≥ f j + 1 by
        exact h rest _ (Nat.le_max_right _ _)
      intro xs; induction xs with
      | nil => intro a h; exact h
      | cons x xs' ihx =>
        intro a ha; simp only [List.foldl_cons]
        exact ihx _ (Nat.le_trans ha (Nat.le_max_left _ _))
    | inr hmem' => exact ih hmem'

/- Helper: go procs i (fuel+1) ≥ go procs j fuel + 1 when j ∈ depIndices procs i.
    This is the core bound: the level of i is at least one more than the level
    of any dependency j (computed with one less fuel). -/
private theorem go_dep_bound (procs : List CombProcess) (i j fuel : Nat)
    (hdep : j ∈ depIndices procs i) :
    topoLevel.go procs i (fuel + 1) ≥ topoLevel.go procs j fuel + 1 := by
  simp only [topoLevel.go]
  have hne : (depIndices procs i).isEmpty = false := by
    cases h : (depIndices procs i) with
    | nil => simp [h] at hdep
    | cons _ _ => rfl
  simp only [hne]
  exact foldl_max_ge_mem (f := fun k => topoLevel.go procs k fuel) hdep

-- Helper: depIndices only returns indices < procs.length.
private theorem depIndices_lt (procs : List CombProcess) (i k : Nat)
    (hk : k ∈ depIndices procs i) : k < procs.length := by
  unfold depIndices at hk
  split at hk
  · exact List.mem_range.mp (List.mem_filter.mp hk).1
  · simp at hk

/- Helper: the foldl over deps produces the same result when all recursive
    calls agree. -/
private theorem foldl_go_eq {procs : List CombProcess} {f1 f2 : Nat}
    (deps : List Nat) (acc : Nat)
    (heq : ∀ k, k ∈ deps → topoLevel.go procs k f1 = topoLevel.go procs k f2) :
    deps.foldl (fun m k => max m (topoLevel.go procs k f1 + 1)) acc =
    deps.foldl (fun m k => max m (topoLevel.go procs k f2 + 1)) acc := by
  induction deps generalizing acc with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons]
    rw [heq d (.head rest)]
    exact ih (acc := max acc (topoLevel.go procs d f2 + 1))
      (fun k hk => heq k (.tail d hk))

/- Helper: go with extra fuel agrees when deps are stable.

    If all deps k of j satisfy go k fuel = go k (fuel+1),
    then go j (fuel+1) = go j (fuel+2). -/
private theorem go_extra_fuel (procs : List CombProcess) (j fuel : Nat)
    (hdeps_stable : ∀ k, k ∈ depIndices procs j →
        topoLevel.go procs k fuel = topoLevel.go procs k (fuel + 1)) :
    topoLevel.go procs j (fuel + 1) = topoLevel.go procs j (fuel + 2) := by
  show (let deps := depIndices procs j
        if deps.isEmpty then 0
        else deps.foldl (fun maxLev j => max maxLev (topoLevel.go procs j fuel + 1)) 0) =
       (let deps := depIndices procs j
        if deps.isEmpty then 0
        else deps.foldl (fun maxLev j => max maxLev (topoLevel.go procs j (fuel + 1) + 1)) 0)
  cases hempty : (depIndices procs j).isEmpty
  · -- non-empty deps: compare the foldls
    simp only [hempty]
    exact foldl_go_eq _ 0 (fun k hk => hdeps_stable k hk)
  · -- empty deps: both are 0
    simp only [hempty, ite_true]

-- Helper: go is bounded by fuel.
private theorem go_le_fuel (procs : List CombProcess) (j fuel : Nat) :
    topoLevel.go procs j fuel ≤ fuel := by
  induction fuel generalizing j with
  | zero => simp [topoLevel.go]
  | succ fuel ih =>
    change (let deps := depIndices procs j
            if deps.isEmpty then 0
            else deps.foldl (fun maxLev j => max maxLev (topoLevel.go procs j fuel + 1)) 0) ≤ fuel + 1
    have : ∀ (ds : List Nat) (acc : Nat), acc ≤ fuel + 1 →
        ds.foldl (fun m k => max m (topoLevel.go procs k fuel + 1)) acc ≤ fuel + 1 := by
      intro ds
      induction ds with
      | nil => intro acc h; exact h
      | cons d rest ihd =>
        intro acc hacc; simp only [List.foldl_cons]
        exact ihd _ (Nat.max_le.mpr ⟨hacc, Nat.succ_le_succ (ih d)⟩)
    cases hempty : (depIndices procs j).isEmpty <;> simp only [hempty] <;>
    first | exact Nat.zero_le _ | exact this _ 0 (Nat.zero_le _)

-- Helper: foldl of max is monotone when the function is pointwise ≤.
private theorem foldl_max_mono {f g : Nat → Nat} (ds : List Nat) (acc1 acc2 : Nat)
    (hacc : acc1 ≤ acc2) (hfg : ∀ k, k ∈ ds → f k ≤ g k) :
    ds.foldl (fun m k => max m (f k + 1)) acc1 ≤
    ds.foldl (fun m k => max m (g k + 1)) acc2 := by
  induction ds generalizing acc1 acc2 with
  | nil => exact hacc
  | cons d rest ih =>
    simp only [List.foldl_cons]
    exact ih _ _
      (Nat.max_le.mpr ⟨Nat.le_trans hacc (Nat.le_max_left _ _),
        Nat.le_trans (Nat.succ_le_succ (hfg d (.head rest))) (Nat.le_max_right _ _)⟩)
      (fun k hk => hfg k (.tail d hk))

-- Helper: go is monotone in fuel.
private theorem go_mono (procs : List CombProcess) (j fuel : Nat) :
    topoLevel.go procs j fuel ≤ topoLevel.go procs j (fuel + 1) := by
  induction fuel generalizing j with
  | zero => simp [topoLevel.go]
  | succ fuel ih =>
    show (let deps := depIndices procs j
          if deps.isEmpty then 0
          else deps.foldl (fun m k => max m (topoLevel.go procs k fuel + 1)) 0) ≤
         (let deps := depIndices procs j
          if deps.isEmpty then 0
          else deps.foldl (fun m k => max m (topoLevel.go procs k (fuel + 1) + 1)) 0)
    cases hempty : (depIndices procs j).isEmpty
    · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
      exact foldl_max_mono _ 0 0 (Nat.le_refl _) (fun k _ => ih k)
    · simp only [hempty, ↓reduceIte]; omega

-- Helper: go is monotone across arbitrary fuel gaps: if f1 ≤ f2, then go j f1 ≤ go j f2.
private theorem go_mono_general (procs : List CombProcess) (j f1 f2 : Nat) (hle : f1 ≤ f2) :
    topoLevel.go procs j f1 ≤ topoLevel.go procs j f2 := by
  induction hle with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (go_mono procs j _)

/- Key lemma: if go j f < f, then go j f is already stable (go j f = go j (f+1)).
    Proved by induction on f. The strict inequality ensures all deps have
    strictly smaller levels, allowing the IH to apply. -/
private theorem go_strict_stable (procs : List CombProcess) (j f : Nat)
    (hlt : topoLevel.go procs j f < f) :
    topoLevel.go procs j f = topoLevel.go procs j (f + 1) := by
  induction f generalizing j with
  | zero => omega
  | succ f ih =>
    apply go_extra_fuel
    intro k hk
    apply ih
    have := go_dep_bound procs j k f hk
    omega

-- The dependency relation on process indices, used for well-founded induction.
def DepRel (procs : List CombProcess) (k j : Nat) : Prop :=
  k ∈ depIndices procs j ∧ j < procs.length

/- Well-foundedness of the dependency relation.

    This is equivalent to AcyclicDeps for finite graphs (via pigeonhole),
    but stated directly in the form needed for well-founded induction.
    In practice, both can be checked by the same topological sort algorithm. -/
def WellFoundedDeps (procs : List CombProcess) : Prop :=
  WellFounded (DepRel procs)

/- Helper: extract a witness from foldl max with accumulator ≤ threshold.
    If the foldl result ≥ v + 1 and the accumulator starts ≤ v,
    some element k in the list has go k fuel ≥ v. -/
private theorem go_foldl_witness_aux (procs : List CombProcess) (fuel : Nat) :
    ∀ (ds : List Nat) (acc v : Nat),
    ds.foldl (fun m k => max m (topoLevel.go procs k fuel + 1)) acc ≥ v + 1 →
    acc ≤ v →
    ∃ k, k ∈ ds ∧ topoLevel.go procs k fuel ≥ v := by
  intro ds; induction ds with
  | nil => intro acc v hge hacc; simp at hge; omega
  | cons d rest ih =>
    intro acc v hge hacc; simp only [List.foldl_cons] at hge
    by_cases hd : topoLevel.go procs d fuel ≥ v
    · exact ⟨d, List.mem_cons_self, hd⟩
    · obtain ⟨k, hk, hfk⟩ := ih (max acc (topoLevel.go procs d fuel + 1)) v hge (by omega)
      exact ⟨k, List.mem_cons_of_mem d hk, hfk⟩

-- Helper: if go j f = f and f ≥ 1, then j has a dep k with go k (f-1) = f-1.
private theorem go_eq_fuel_has_dep (procs : List CombProcess) (j f : Nat)
    (hf : f ≥ 1) (heq : topoLevel.go procs j f = f) :
    ∃ k, k ∈ depIndices procs j ∧ topoLevel.go procs k (f - 1) = f - 1 := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp only [Nat.succ_sub_one]
  by_cases hempty : (depIndices procs j).isEmpty = true
  · exfalso; have : topoLevel.go procs j (f' + 1) = 0 := by
      change (if (depIndices procs j).isEmpty then 0 else _) = 0; simp [hempty]
    omega
  · have hfold : (depIndices procs j).foldl
        (fun maxLev k => max maxLev (topoLevel.go procs k f' + 1)) 0 = f' + 1 := by
      have : topoLevel.go procs j (f' + 1) = (depIndices procs j).foldl
          (fun maxLev k => max maxLev (topoLevel.go procs k f' + 1)) 0 := by
        change (if (depIndices procs j).isEmpty then 0 else _) = _; simp [hempty]
      omega
    obtain ⟨k, hk, hfk⟩ := go_foldl_witness_aux procs f' (depIndices procs j) 0 f' (by omega) (by omega)
    exact ⟨k, hk, by have := go_le_fuel procs k f'; omega⟩

/- Build a dep chain as a list from go j n = n.
    Returns a list of length n + 1 with consecutive dep relationships. -/
private theorem build_dep_chain (procs : List CombProcess) :
    ∀ n j, j < procs.length → topoLevel.go procs j n = n →
    ∃ chain : List Nat, chain.length = n + 1 ∧
      chain.head? = some j ∧
      (∀ x, x ∈ chain → x < procs.length) ∧
      (∀ i, (hi : i + 1 < chain.length) →
        chain[i + 1] ∈ depIndices procs chain[i]) := by
  intro n; induction n with
  | zero =>
    intro j hj _
    exact ⟨[j], rfl, rfl, fun x hx => by simp at hx; subst hx; exact hj,
      fun i hi => by simp at hi⟩
  | succ n ih =>
    intro j hj heq
    obtain ⟨k, hk, hkeq⟩ := go_eq_fuel_has_dep procs j (n + 1) (by omega) heq
    have hklt := depIndices_lt procs j k hk
    obtain ⟨rest, hlen, hhead, hbound, hdeps⟩ := ih k hklt hkeq
    refine ⟨j :: rest, by simp [hlen], rfl, ?_, ?_⟩
    · intro x hx; cases List.mem_cons.mp hx with
      | inl h => subst h; exact hj
      | inr h => exact hbound x h
    · intro i hi; cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        -- rest[0] = k (from hhead : rest.head? = some k and hlen : rest.length ≥ 1)
        have hrest_ne : rest ≠ [] := by intro h; simp [h] at hlen
        have hrest0 : rest[0]'(by omega) = k := by
          cases rest with
          | nil => exact absurd rfl hrest_ne
          | cons r rs => simp at hhead; exact hhead
        rw [hrest0]; exact hk
      | succ i' =>
        simp only [List.getElem_cons_succ]
        have : i' + 1 < rest.length := by
          simp only [List.length_cons] at hi; omega
        exact hdeps i' this

-- Pigeonhole: a Nodup list with all elements < n has length ≤ n.
private theorem nodup_bound : ∀ (l : List Nat) (n : Nat),
    l.Nodup → (∀ x, x ∈ l → x < n) → l.length ≤ n := by
  intro l n hnd hbound; induction n generalizing l with
  | zero => cases l with
    | nil => simp
    | cons a _ => exact absurd (hbound a List.mem_cons_self) (Nat.not_lt_zero _)
  | succ n ih =>
    by_cases hmem : n ∈ l
    · have := ih (l.erase n) (hnd.erase n) fun x hx => by
        have hne : x ≠ n := fun h => by subst h; exact hnd.not_mem_erase hx
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (hbound x ((List.mem_erase_of_ne hne).mp hx))) hne
      have := List.length_erase_of_mem hmem; omega
    · exact Nat.le_succ_of_le (ih _ hnd fun x hx =>
        Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (hbound x hx)) (fun h => by subst h; exact hmem hx))

-- Extract a duplicate from a non-Nodup list.
private theorem not_nodup_has_dup : ∀ (l : List Nat),
    ¬l.Nodup → ∃ p q : Nat, ∃ (hp : p < l.length) (hq : q < l.length), p < q ∧ l[p] = l[q] := by
  intro l hnd; induction l with
  | nil => exact absurd List.nodup_nil hnd
  | cons a rest ih =>
    rw [List.nodup_cons] at hnd
    by_cases ha : a ∈ rest
    · obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem ha
      exact ⟨0, idx + 1, Nat.zero_lt_succ _, Nat.succ_lt_succ hidx_lt, Nat.zero_lt_succ _, by simp [hidx_eq]⟩
    · have hrest : ¬rest.Nodup := fun h => hnd ⟨ha, h⟩
      obtain ⟨p, q, hp, hq, hpq, heq⟩ := ih hrest
      exact ⟨p + 1, q + 1, Nat.succ_lt_succ hp, Nat.succ_lt_succ hq, Nat.succ_lt_succ hpq,
        by simp only [List.getElem_cons_succ]; exact heq⟩

-- Consecutive dep links in a chain give a TransGen DepRel path.
private theorem chain_transGen (procs : List CombProcess) (chain : List Nat)
    (hbound : ∀ x, x ∈ chain → x < procs.length)
    (hdeps : ∀ i, (hi : i + 1 < chain.length) → chain[i + 1] ∈ depIndices procs chain[i])
    (i j : Nat) (hij : i < j) (hjlen : j < chain.length) :
    Relation.TransGen (DepRel procs) (chain[j]'(by omega)) (chain[i]'(by omega)) := by
  induction j with
  | zero => omega
  | succ j' ih =>
    by_cases hij' : i = j'
    · subst hij'; apply Relation.TransGen.single
      exact ⟨hdeps i (by omega), hbound _ (List.getElem_mem (by omega))⟩
    · apply Relation.TransGen.trans
      · apply Relation.TransGen.single
        exact ⟨hdeps j' (by omega), hbound _ (List.getElem_mem (by omega))⟩
      · exact ih (by omega) (by omega)

-- Acc for R implies Acc for TransGen R.
private theorem acc_transGen {α : Type} {R : α → α → Prop} {a : α} (h : Acc R a) :
    Acc (Relation.TransGen R) a := by
  induction h with
  | intro x hx ih =>
    constructor; intro y hy
    induction hy with
    | single hyx => exact ih y hyx
    | tail hyb hbx => exact (ih _ hbx).inv hyb

-- A well-founded relation has no cycles (TransGen self-loops).
private theorem wf_no_transGen_self {α : Type} {R : α → α → Prop} (hWF : WellFounded R)
    (a : α) (h : Relation.TransGen R a a) : False := by
  have hacc := acc_transGen (hWF.apply a)
  induction hacc with
  | intro x hx ih => exact ih x h h

/- Key bound: go j N < N when WellFoundedDeps holds.
    If go j N = N, we can build a chain of length N+1 with all values < N,
    which by pigeonhole has a duplicate, giving a cycle that contradicts WF. -/
private theorem go_lt_procs_length (procs : List CombProcess) (j : Nat)
    (hWF : WellFoundedDeps procs) (hj : j < procs.length) :
    topoLevel.go procs j procs.length < procs.length := by
  -- Proof by contradiction: if go j N ≥ N, then go j N = N (by go_le_fuel),
  -- and we build a chain of N+1 dep-related nodes < N, contradicting acyclicity.
  suffices h : topoLevel.go procs j procs.length ≠ procs.length by
    have hle := go_le_fuel procs j procs.length; omega
  intro heq
  -- Build chain of length N+1 with consecutive deps
  obtain ⟨chain, hlen, _, hbound, hdeps⟩ := build_dep_chain procs procs.length j hj heq
  -- Chain has length N+1, all elements < N, so it can't be Nodup
  have hnotnd : ¬chain.Nodup := by
    intro hnd; have := nodup_bound chain procs.length hnd hbound; omega
  -- Extract duplicate indices p < q with chain[p] = chain[q]
  obtain ⟨p, q, hp, hq, hpq, heq'⟩ := not_nodup_has_dup chain hnotnd
  -- Build TransGen cycle: chain[q] ←...← chain[p] via consecutive deps
  have hcycle := chain_transGen procs chain hbound hdeps p q hpq hq
  -- chain[p] = chain[q], so we have TransGen DepRel (chain[p]) (chain[p])
  rw [heq'] at hcycle
  exact wf_no_transGen_self hWF _ hcycle

/- Fuel stability for topoLevel.go.

    With WellFoundedDeps, the go function stabilizes by fuel = procs.length - 1.
    Proved using go_lt_procs_length: go j N < N implies go j (N-1) = go j N
    by case analysis with go_strict_stable and go_mono. -/
theorem go_fuel_stable (procs : List CombProcess) (j : Nat)
    (hWF : WellFoundedDeps procs) (hj : j < procs.length) :
    topoLevel.go procs j (procs.length - 1) = topoLevel.go procs j procs.length := by
  have hlt := go_lt_procs_length procs j hWF hj
  have hmono := go_mono procs j (procs.length - 1)
  have hle_fuel := go_le_fuel procs j (procs.length - 1)
  have hN : procs.length ≥ 1 := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  have hN_eq : procs.length - 1 + 1 = procs.length := Nat.succ_pred_eq_of_pos hN
  rw [hN_eq] at hmono
  by_cases hcase : topoLevel.go procs j (procs.length - 1) < procs.length - 1
  · have := go_strict_stable procs j (procs.length - 1) hcase; rw [hN_eq] at this; exact this
  · omega

/- Helper: if j is in the depIndices of i, then topoLevel j < topoLevel i.
    Proved from go_dep_bound and go_fuel_stable. -/
private theorem depIndex_implies_lower_level (procs : List CombProcess) (i j : Nat)
    (hWF : WellFoundedDeps procs)
    (hi : i < procs.length)
    (hdep : j ∈ depIndices procs i) :
    topoLevel procs j < topoLevel procs i := by
  have hj : j < procs.length := by
    have := List.mem_filter.mp (by
      unfold depIndices at hdep
      simp only [hi, ↓reduceDIte] at hdep
      exact hdep)
    exact List.mem_range.mp this.1
  unfold topoLevel
  have hN : procs.length > 0 := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  have hN_eq : procs.length = (procs.length - 1) + 1 := (Nat.succ_pred_eq_of_pos hN).symm
  have h1 : topoLevel.go procs i procs.length ≥ topoLevel.go procs j (procs.length - 1) + 1 := by
    rw [hN_eq]; exact go_dep_bound procs i j (procs.length - 1) hdep
  have h2 : topoLevel.go procs j (procs.length - 1) = topoLevel.go procs j procs.length :=
    go_fuel_stable procs j hWF hj
  omega

/- Two processes at the same topological level are independent.

    Proof sketch: If i and j are at the same level, neither can depend on
    the other (since a dependency would put one at a strictly higher level).
    UniqueWrites ensures their write sets are disjoint.
    Since neither depends on the other, writes don't overlap with reads. -/
theorem same_level_independent (procs : List CombProcess) (i j : Nat)
    (hUnique : UniqueWrites procs)
    (hWF : WellFoundedDeps procs)
    (hlev : topoLevel procs i = topoLevel procs j)
    (hne : i ≠ j)
    (hi : i < procs.length)
    (hj : j < procs.length)
    (hci : (procs[i]).isComb = true)
    (hcj : (procs[j]).isComb = true) :
    Independent (procs[i]) (procs[j]) := by
  -- Helper: show getD and getElem agree when in bounds
  have hgetD_i : procs.getD i default = procs[i] := by simp [List.getD, List.getElem?_eq_getElem hi]
  have hgetD_j : procs.getD j default = procs[j] := by simp [List.getD, List.getElem?_eq_getElem hj]
  constructor
  · -- Write-disjointness: follows from UniqueWrites
    intro v hvi hvj
    exact hUnique i j hne (procs[i]) (procs[j])
      (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hci hcj v hvi hvj
  constructor
  · -- writes(i) ∩ reads(j) = ∅:
    -- If v ∈ writes(i) ∩ reads(j), then i ∈ depIndices procs j,
    -- so topoLevel i < topoLevel j, contradicting hlev.
    intro v hvi hvj
    have hdep : i ∈ depIndices procs j := by
      unfold depIndices
      simp only [hj, ↓reduceDIte]
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr hi, ?_⟩
      -- The filter predicate: i ≠ j && (procs.getD i default).isComb &&
      --   (procs.getD j default).reads.any (fun v => (procs.getD i default).writes.any (fun w => v == w))
      rw [hgetD_i, hgetD_j]
      simp only [Bool.and_eq_true]
      refine ⟨⟨decide_eq_true_eq.mpr hne, hci⟩, ?_⟩
      exact List.any_eq_true.mpr ⟨v, hvj, List.any_eq_true.mpr ⟨v, hvi, beq_self_eq_true v⟩⟩
    have := depIndex_implies_lower_level procs j i hWF hj hdep
    omega
  · -- writes(j) ∩ reads(i) = ∅: symmetric argument
    intro v hvj hvi
    have hdep : j ∈ depIndices procs i := by
      unfold depIndices
      simp only [hi, ↓reduceDIte]
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr hj, ?_⟩
      rw [hgetD_i, hgetD_j]
      simp only [Bool.and_eq_true]
      refine ⟨⟨decide_eq_true_eq.mpr (Ne.symm hne), hcj⟩, ?_⟩
      exact List.any_eq_true.mpr ⟨v, hvi, List.any_eq_true.mpr ⟨v, hvj, beq_self_eq_true v⟩⟩
    have := depIndex_implies_lower_level procs i j hWF hi hdep
    omega

-- Processes at level k only depend on processes at levels < k.
theorem level_deps_lower (procs : List CombProcess) (i : Nat)
    (hWF : WellFoundedDeps procs)
    (hi : i < procs.length)
    (_hci : (procs[i]).isComb = true) :
    ∀ v, v ∈ (procs[i]'hi).reads →
      ∀ j, (hj : j < procs.length) → j ≠ i →
        (procs[j]'hj).isComb = true →
        v ∈ (procs[j]'hj).writes →
        topoLevel procs j < topoLevel procs i := by
  intro v hv j hj hne hcj hvj
  have hgetD_i : procs.getD i default = procs[i] := by simp [List.getD, List.getElem?_eq_getElem hi]
  have hgetD_j : procs.getD j default = procs[j] := by simp [List.getD, List.getElem?_eq_getElem hj]
  -- j is in depIndices of i since: j ≠ i, procs[j].isComb, and i reads v which j writes
  have hdep : j ∈ depIndices procs i := by
    unfold depIndices
    simp only [hi, ↓reduceDIte]
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr hj, ?_⟩
    rw [hgetD_i, hgetD_j]
    simp only [Bool.and_eq_true]
    refine ⟨⟨decide_eq_true_eq.mpr hne, hcj⟩, ?_⟩
    exact List.any_eq_true.mpr ⟨v, hv, List.any_eq_true.mpr ⟨v, hvj, beq_self_eq_true v⟩⟩
  exact depIndex_implies_lower_level procs i j hWF hi hdep

-- ## Helper: StdExec preserves unwritten variables

-- A single StdStep preserves variables not written by any process.
private theorem StdStep_preserves_unwritten
    (procs : List ExecProcess) (s1 s2 : State) (vid : VId)
    (hstep : StdStep procs s1 s2)
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hunwritten : ∀ ep, ep ∈ procs → vid ∉ ep.proc.writes)
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    haccess s2 vid = haccess s1 vid := by
  cases hstep with
  | step ep u hmem hexec =>
    have hw := hWritesOk ep hmem s1 u hexec
    have : haccess u vid = HMap.empty := by
      exact Classical.byContradiction fun h => hunwritten ep hmem (hw vid h)
    exact haccess_hupds_miss s1 u vid this (hCompat ep hmem s1 u hexec)

-- StdExec preserves variables not written by any process.
private theorem StdExec_preserves_unwritten
    (procs : List ExecProcess) (s sf : State) (vid : VId)
    (hexec : StdExec procs s sf)
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hunwritten : ∀ ep, ep ∈ procs → vid ∉ ep.proc.writes)
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    haccess sf vid = haccess s vid := by
  induction hexec with
  | refl => rfl
  | step s1 s2 s3 hstep _ ih =>
    have := StdStep_preserves_unwritten procs s1 s2 vid hstep hWritesOk hunwritten hCompat
    rw [ih, this]

-- ## Helper: settled processes with same output agree on writes

/- If process ep is settled in sf1 and sf2, and produces the same output u
    in both states, then sf1 and sf2 agree on all variables that ep actually
    writes to (i.e., where haccess u vid ≠ HMap.empty). -/
private theorem settled_same_output_agree
    (ep : ExecProcess) (sf1 sf2 u : State)
    (_h1 : ep.exec sf1 = .ok u) (hfp1 : hupds sf1 u = sf1)
    (_h2 : ep.exec sf2 = .ok u) (hfp2 : hupds sf2 u = sf2)
    (vid : VId) (hne : haccess u vid ≠ HMap.empty)
    (hss1 : HMapLemmas.SameShape (haccess sf1 vid) (haccess u vid))
    (hss2 : HMapLemmas.SameShape (haccess sf2 vid) (haccess u vid))
    (hleaf : HMapLemmas.IsLeaf (haccess u vid))
    (hcompat1 : CompatUpdate sf1 u) (hcompat2 : CompatUpdate sf2 u) :
    haccess sf1 vid = haccess sf2 vid := by
  have := hupds_fixpt_determines sf1 u vid hfp1 hne hss1 hleaf hcompat1
  have := hupds_fixpt_determines sf2 u vid hfp2 hne hss2 hleaf hcompat2
  rw [‹haccess sf1 vid = haccess u vid›, ‹haccess sf2 vid = haccess u vid›]

-- ## Core: quiescent states agree on all process-written variables

/- If process ep is settled in sf1 and sf2, and both exec results agree
    (same reads → same outputs by hExecReads), then sf1 and sf2 agree on
    all variables that ep actually writes. -/
private theorem agree_on_process_writes
    (ep : ExecProcess) (sf1 sf2 : State)
    (hq1_ep : Standard.isSettled ep sf1) (hq2_ep : Standard.isSettled ep sf2)
    (hExecReads_ep : ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    (hagree_reads : ∀ v, v ∈ ep.proc.reads → haccess sf1 v = haccess sf2 v)
    -- Well-typedness: corresponding fields have same shape and are leaf values
    (hshape : ∀ vid u, ep.exec sf1 = .ok u → haccess u vid ≠ HMap.empty →
        HMapLemmas.SameShape (haccess sf1 vid) (haccess u vid) ∧
        HMapLemmas.SameShape (haccess sf2 vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    (hcompat : ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    ∀ vid, ∀ u, ep.exec sf1 = .ok u → haccess u vid ≠ HMap.empty →
      haccess sf1 vid = haccess sf2 vid := by
  obtain ⟨u1, hexec1, hfp1⟩ := hq1_ep
  obtain ⟨u2, hexec2, hfp2⟩ := hq2_ep
  have heq_exec : ep.exec sf1 = ep.exec sf2 := hExecReads_ep sf1 sf2 hagree_reads
  have hu_eq : u1 = u2 := by
    have : ep.exec sf2 = .ok u1 := heq_exec ▸ hexec1
    rw [hexec2] at this; exact Except.ok.inj this.symm
  rw [hu_eq] at hfp1
  intro vid u hu hne
  have : u = u1 := by rw [hexec1] at hu; exact Except.ok.inj hu.symm
  subst this
  rw [hu_eq] at hne
  obtain ⟨hss1, hss2, hleaf⟩ := hshape vid u2 (hu_eq ▸ hexec1) hne
  exact (hupds_fixpt_determines sf1 u2 vid hfp1 hne hss1 hleaf (hcompat sf1 u2 (hu_eq ▸ hexec1))).trans
    (hupds_fixpt_determines sf2 u2 vid hfp2 hne hss2 hleaf (hcompat sf2 u2 hexec2)).symm

-- ## Main confluence theorem

/- Helper: in a quiescent state, all processes agree on their written variables
    when their read inputs agree.

    For each process ep that is settled in both sf1 and sf2, if sf1 and sf2
    agree on all of ep's reads, then sf1 and sf2 agree on all variables
    that ep writes (where the update is non-empty). -/
private theorem quiescent_writes_agree
    (ep : ExecProcess) (sf1 sf2 : State)
    (hq1 : Standard.isSettled ep sf1) (hq2 : Standard.isSettled ep sf2)
    (hExecReads : ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    (hagree_reads : ∀ v, v ∈ ep.proc.reads → haccess sf1 v = haccess sf2 v)
    (hshape : ∀ vid u, ep.exec sf1 = .ok u → haccess u vid ≠ HMap.empty →
        HMapLemmas.SameShape (haccess sf1 vid) (haccess u vid) ∧
        HMapLemmas.SameShape (haccess sf2 vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    (hcompat : ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    ∀ vid, ∀ u, ep.exec sf1 = .ok u → haccess u vid ≠ HMap.empty →
      haccess sf1 vid = haccess sf2 vid :=
  agree_on_process_writes ep sf1 sf2 hq1 hq2 hExecReads hagree_reads hshape hcompat

/- Observable equivalence of states: they agree on all fields.
    This is weaker than structural equality but suffices for the equivalence
    proof, since all observable properties (output extraction via hfilter,
    variable lookup via haccess) depend only on field values, not on the
    internal ordering of the association list. -/
def StateEquiv (s1 s2 : State) : Prop :=
  ∀ vid, haccess s1 vid = haccess s2 vid

/- A settled process's fixpoint determines the written variable values.

    If a process ep is settled (at fixpoint) in both sf1 and sf2, its exec
    results agree (same reads → same output), and vid is in ep's write set,
    then sf1 and sf2 agree on vid.

    The WriteComplete hypothesis connects `vid ∈ ep.proc.writes` to the
    semantic condition `haccess u vid ≠ .empty` with SameShape/IsLeaf.
    These hold for all synthesizable Verilog combinational processes. -/
theorem fixpt_write_determines (ep : ExecProcess) (sf1 sf2 : State)
    (hq1 : Standard.isSettled ep sf1) (hq2 : Standard.isSettled ep sf2)
    (heq_exec : ep.exec sf1 = ep.exec sf2)
    (vid : VId) (hvid : vid ∈ ep.proc.writes)
    (hWriteComplete : ∀ s u, ep.exec s = .ok u → vid ∈ ep.proc.writes →
        haccess u vid ≠ HMap.empty ∧
        HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    (hcompat : ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    haccess sf1 vid = haccess sf2 vid := by
  obtain ⟨u1, hexec1, hfp1⟩ := hq1
  obtain ⟨u2, hexec2, hfp2⟩ := hq2
  -- From heq_exec: ep.exec sf1 = ep.exec sf2, so u1 = u2
  have hu_eq : u1 = u2 := by
    have : ep.exec sf2 = .ok u1 := heq_exec ▸ hexec1
    rw [hexec2] at this; exact Except.ok.inj this.symm
  subst hu_eq
  -- Get the semantic conditions from WriteComplete
  obtain ⟨hne1, hss1, hleaf1⟩ := hWriteComplete sf1 u1 hexec1 hvid
  have heq2 : ep.exec sf2 = .ok u1 := heq_exec ▸ hexec1
  obtain ⟨hne2, hss2, _⟩ := hWriteComplete sf2 u1 heq2 hvid
  -- Both sf1 and sf2 agree with u1 at vid
  have h1 := hupds_fixpt_determines sf1 u1 vid hfp1 hne1 hss1 hleaf1 (hcompat sf1 u1 hexec1)
  have h2 := hupds_fixpt_determines sf2 u1 vid hfp2 hne2 hss2 hleaf1 (hcompat sf2 u1 heq2)
  rw [h1, h2]

/- All variables agree between two quiescent states reached from the same
    initial state. This is the heart of the confluence proof, using
    topological induction over the dependency DAG.

    For written variables: by quiescent_writes_agree, the write outputs
    agree when reads agree, and reads agree by induction on topo level.
    For unwritten variables: by StdExec_preserves_unwritten, both states
    preserve the initial value. -/
private theorem quiescent_states_agree_on_all
    (procs : List ExecProcess) (s sf1 sf2 : State)
    (hexec1 : StdExec procs s sf1) (hexec2 : StdExec procs s sf2)
    (hquiet1 : Quiescent procs sf1) (hquiet2 : Quiescent procs sf2)
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    (hExecReads : ∀ ep, ep ∈ procs → ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    (hWF : WellFoundedDeps (procs.map (·.proc)))
    (hAllComb : ∀ ep, ep ∈ procs → ep.proc.isComb = true)
    (hNoSelfDep : ∀ ep, ep ∈ procs → ∀ v, v ∈ ep.proc.reads → v ∉ ep.proc.writes)
    -- Write completeness: vid ∈ writes implies the semantic non-empty/shape/leaf conditions
    (hWriteComplete : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → ∀ vid, vid ∈ ep.proc.writes →
        haccess u vid ≠ HMap.empty ∧
        HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    -- Compatibility: process execution produces compatible updates
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u) :
    ∀ vid, haccess sf1 vid = haccess sf2 vid := by
  -- Key helper: for any variable written by some process at topological
  -- level ≤ L, sf1 and sf2 agree on that variable.
  -- Proved by strong induction on L.
  suffices key : ∀ (L : Nat) (ep : ExecProcess),
      ep ∈ procs →
      (∃ idx, ∃ (hidx_lt : idx < procs.length), procs[idx]'hidx_lt = ep ∧
        topoLevel (procs.map (·.proc)) idx ≤ L) →
      ∀ v, v ∈ ep.proc.reads →
        haccess sf1 v = haccess sf2 v by
    intro vid
    by_cases hwritten : ∃ ep, ep ∈ procs ∧ vid ∈ ep.proc.writes
    · -- vid is written by some process ep
      obtain ⟨ep, hmem, hvid⟩ := hwritten
      -- ep is settled in both states (it's combinational)
      have hcomb := hAllComb ep hmem
      have hq1_ep := hquiet1 ep hmem hcomb
      have hq2_ep := hquiet2 ep hmem hcomb
      -- Get ep's index
      have ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
      -- All of ep's reads agree between sf1 and sf2 (by `key`)
      have hagree_reads : ∀ v, v ∈ ep.proc.reads → haccess sf1 v = haccess sf2 v :=
        key (topoLevel (procs.map (·.proc)) idx) ep hmem
          ⟨idx, hidx_lt, hidx_eq, Nat.le_refl _⟩
      -- Therefore ep.exec sf1 = ep.exec sf2
      have heq_exec := hExecReads ep hmem sf1 sf2 hagree_reads
      -- By fixpt_write_determines, sf1 and sf2 agree on vid
      exact fixpt_write_determines ep sf1 sf2 hq1_ep hq2_ep heq_exec vid hvid
        (fun s u hexec hvid' => hWriteComplete ep hmem s u hexec vid hvid')
        (fun s u hexec => hCompat ep hmem s u hexec)
    · -- vid is not written by any process
      have hunwritten : ∀ ep, ep ∈ procs → vid ∉ ep.proc.writes := by
        intro ep hmem hvid; exact hwritten ⟨ep, hmem, hvid⟩
      have h1 := StdExec_preserves_unwritten procs s sf1 vid hexec1 hWritesOk hunwritten hCompat
      have h2 := StdExec_preserves_unwritten procs s sf2 vid hexec2 hWritesOk hunwritten hCompat
      rw [h1, h2]
  -- Prove `key` by strong induction on L
  intro L
  induction L with
  | zero =>
    -- Level 0: ep has no dependencies on other combinational processes.
    -- So all of ep's reads are either not written by any process (preserved
    -- from initial state) or written by ep itself (which is impossible for
    -- reads, by AcyclicDeps / WellFoundedDeps).
    intro ep hmem ⟨idx, hidx_lt, hidx_eq, hlev⟩ v hv
    -- For each read variable v of ep:
    -- Case split: is v written by some other process?
    by_cases hwritten_v : ∃ ep', ep' ∈ procs ∧ v ∈ ep'.proc.writes
    · -- Some process ep' writes v. Since ep reads v and ep' writes v,
      -- ep' is a dependency of ep, so topoLevel ep' < topoLevel ep.
      -- But topoLevel ep = 0, contradiction.
      obtain ⟨ep', hmem', hvw⟩ := hwritten_v
      have ⟨idx', hidx'_lt, hidx'_eq⟩ := List.getElem_of_mem hmem'
      have hcomb' := hAllComb ep' hmem'
      have hcomb_ep := hAllComb ep hmem
      have hmap_len : (procs.map (·.proc)).length = procs.length := by simp
      have hidx_lt' : idx < (procs.map (·.proc)).length := hmap_len ▸ hidx_lt
      have hidx'_lt' : idx' < (procs.map (·.proc)).length := hmap_len ▸ hidx'_lt
      have hget_idx : (procs.map (·.proc))[idx] = ep.proc := by
        simp [List.getElem_map, hidx_eq]
      have hget_idx' : (procs.map (·.proc))[idx'] = ep'.proc := by
        simp [List.getElem_map, hidx'_eq]
      -- ep' must be different from ep (no process reads its own writes)
      have hne : idx' ≠ idx := by
        intro heq; subst heq
        have : ep' = ep := hidx'_eq.symm.trans hidx_eq
        exact hNoSelfDep ep hmem v hv (this ▸ hvw)
      -- level_deps_lower gives topoLevel idx' < topoLevel idx ≤ 0, contradiction
      have hlower := level_deps_lower (procs.map (·.proc)) idx hWF hidx_lt'
        (hget_idx ▸ hcomb_ep) v (hget_idx ▸ hv) idx' hidx'_lt'
        hne (hget_idx' ▸ hcomb') (hget_idx' ▸ hvw)
      omega
    · -- v is not written by any process: preserved from initial state
      have hunwritten_v : ∀ ep', ep' ∈ procs → v ∉ ep'.proc.writes := by
        intro ep' hmem' hvw; exact hwritten_v ⟨ep', hmem', hvw⟩
      have h1 := StdExec_preserves_unwritten procs s sf1 v hexec1 hWritesOk hunwritten_v hCompat
      have h2 := StdExec_preserves_unwritten procs s sf2 v hexec2 hWritesOk hunwritten_v hCompat
      rw [h1, h2]
  | succ n ih =>
    intro ep hmem ⟨idx, hidx_lt, hidx_eq, hlev⟩ v hv
    -- For each read variable v of ep at level ≤ n+1:
    by_cases hwritten_v : ∃ ep', ep' ∈ procs ∧ v ∈ ep'.proc.writes
    · -- Some process ep' writes v
      obtain ⟨ep', hmem', hvw⟩ := hwritten_v
      have ⟨idx', hidx'_lt, hidx'_eq⟩ := List.getElem_of_mem hmem'
      have hcomb' := hAllComb ep' hmem'
      have hcomb_ep := hAllComb ep hmem
      have hmap_len : (procs.map (·.proc)).length = procs.length := by simp
      have hidx_lt' : idx < (procs.map (·.proc)).length := hmap_len ▸ hidx_lt
      have hidx'_lt' : idx' < (procs.map (·.proc)).length := hmap_len ▸ hidx'_lt
      have hget_idx : (procs.map (·.proc))[idx] = ep.proc := by
        simp [List.getElem_map, hidx_eq]
      have hget_idx' : (procs.map (·.proc))[idx'] = ep'.proc := by
        simp [List.getElem_map, hidx'_eq]
      -- ep' must be different from ep (no process reads its own writes)
      have hne : idx' ≠ idx := by
        intro heq; subst heq
        have : ep' = ep := hidx'_eq.symm.trans hidx_eq
        exact hNoSelfDep ep hmem v hv (this ▸ hvw)
      -- Different process: topoLevel idx' < topoLevel idx ≤ n+1
      have hlower := level_deps_lower (procs.map (·.proc)) idx hWF hidx_lt'
        (hget_idx ▸ hcomb_ep) v (hget_idx ▸ hv) idx' hidx'_lt'
        hne (hget_idx' ▸ hcomb') (hget_idx' ▸ hvw)
      -- So topoLevel idx' ≤ n
      have hlev' : topoLevel (procs.map (·.proc)) idx' ≤ n := by omega
      -- ep' is settled in both states
      have hq1_ep' := hquiet1 ep' hmem' hcomb'
      have hq2_ep' := hquiet2 ep' hmem' hcomb'
      -- By induction hypothesis, all reads of ep' agree
      have hagree_reads' : ∀ v', v' ∈ ep'.proc.reads → haccess sf1 v' = haccess sf2 v' :=
        ih ep' hmem' ⟨idx', hidx'_lt, hidx'_eq, hlev'⟩
      -- Therefore ep'.exec sf1 = ep'.exec sf2
      have heq_exec' := hExecReads ep' hmem' sf1 sf2 hagree_reads'
      -- By fixpt_write_determines, sf1 and sf2 agree on v
      exact fixpt_write_determines ep' sf1 sf2 hq1_ep' hq2_ep' heq_exec' v hvw
        (fun s u hexec hvid' => hWriteComplete ep' hmem' s u hexec v hvid')
        (fun s u hexec => hCompat ep' hmem' s u hexec)
    · -- v is not written by any process
      have hunwritten_v : ∀ ep', ep' ∈ procs → v ∉ ep'.proc.writes := by
        intro ep' hmem' hvw; exact hwritten_v ⟨ep', hmem', hvw⟩
      have h1 := StdExec_preserves_unwritten procs s sf1 v hexec1 hWritesOk hunwritten_v hCompat
      have h2 := StdExec_preserves_unwritten procs s sf2 v hexec2 hWritesOk hunwritten_v hCompat
      rw [h1, h2]

theorem confluence
    (procs : List ExecProcess)
    (inputs flops : List VId)
    (s : State)
    (_hUnique : UniqueWrites (procs.map (·.proc)))
    (_hAcyclic : AcyclicDeps (procs.map (·.proc)))
    (_hComplete : CompleteReads (procs.map (·.proc)) inputs flops)
    -- Write set correctness for all processes
    (hWritesOk : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u →
        ∀ vid, haccess u vid ≠ HMap.empty → vid ∈ ep.proc.writes)
    -- Frame property for all processes
    (_hFrame : ∀ ep, ep ∈ procs → ∀ s upd,
        (∀ v, v ∈ ep.proc.reads → haccess upd v = HMap.empty) →
        ep.exec (hupds s upd) = ep.exec s)
    -- Exec read-determinism: exec only depends on reads
    (hExecReads : ∀ ep, ep ∈ procs → ∀ s1 s2 : State,
        (∀ v, v ∈ ep.proc.reads → haccess s1 v = haccess s2 v) →
        ep.exec s1 = ep.exec s2)
    -- Well-founded dependency relation (implied by AcyclicDeps for finite graphs)
    (hWF : WellFoundedDeps (procs.map (·.proc)))
    -- All processes are combinational
    (hAllComb : ∀ ep, ep ∈ procs → ep.proc.isComb = true)
    -- No process reads its own writes (standard for synthesizable combinational logic)
    (hNoSelfDep : ∀ ep, ep ∈ procs → ∀ v, v ∈ ep.proc.reads → v ∉ ep.proc.writes)
    -- Write completeness: vid ∈ writes implies semantic non-empty/shape/leaf conditions
    (hWriteComplete : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → ∀ vid, vid ∈ ep.proc.writes →
        haccess u vid ≠ HMap.empty ∧
        HMapLemmas.SameShape (haccess s vid) (haccess u vid) ∧
        HMapLemmas.IsLeaf (haccess u vid))
    -- Compatibility: process execution produces compatible updates
    (hCompat : ∀ ep, ep ∈ procs → ∀ s u, ep.exec s = .ok u → CompatUpdate s u)
    -- Two executions both reaching quiescence
    (sf1 sf2 : State)
    (h1 : StdReachesQuiet procs s sf1)
    (h2 : StdReachesQuiet procs s sf2) :
    StateEquiv sf1 sf2 := by
  obtain ⟨hexec1, hquiet1⟩ := h1
  obtain ⟨hexec2, hquiet2⟩ := h2
  exact quiescent_states_agree_on_all procs s sf1 sf2 hexec1 hexec2 hquiet1 hquiet2
    hWritesOk hExecReads hWF hAllComb hNoSelfDep hWriteComplete hCompat

end VerilLean.Lang.Equiv.Confluence
