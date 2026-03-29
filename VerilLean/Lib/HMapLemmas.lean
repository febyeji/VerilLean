-- Lemmas about HMap operations, particularly haccessV and hupds.

import VerilLean.Lib.HMap
import VerilLean.Lang.Syntax

set_option linter.unusedSimpArgs false

namespace VerilLean.Lib.HMapLemmas

open VerilLean.Lib
open VerilLean.Lang.Syntax (VId)

-- ## Basic hupds equations

@[simp] theorem hupds_empty_left (h : HMap) : hupds .empty h = h := by simp [hupds]
@[simp] theorem hupds_empty_right (s : HMap) : hupds s .empty = s := by cases s <;> rfl

-- ## haccessV ↔ find? bridge

/- haccessV returns the value from the first entry with matching key,
    agreeing with find? on the same predicate. -/
theorem haccessV_of_find_some {vid : String} {fs : List (String × HMap)} {k : String} {v : HMap}
    (h : fs.find? (fun p => p.1 == vid) = some (k, v)) : haccessV vid fs = v := by
  induction fs with
  | nil => simp [List.find?] at h
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.find?] at h
    by_cases hkv : k' = vid
    · subst hkv; simp at h; simp [haccessV, h.2]
    · have hne : (k' == vid) = false := by simp [BEq.beq]; exact hkv
      rw [hne] at h
      simp only [haccessV, show (vid == k') = false from by simp [BEq.beq]; exact Ne.symm hkv]
      exact ih h

-- haccessV returns .empty when no entry has a matching key.
theorem haccessV_of_find_none {vid : String} {fs : List (String × HMap)}
    (h : fs.find? (fun p => p.1 == vid) = none) : haccessV vid fs = .empty := by
  induction fs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.find?] at h
    by_cases hkv : k' = vid
    · subst hkv; simp at h
    · have hne : (k' == vid) = false := by simp [BEq.beq]; exact hkv
      rw [hne] at h
      simp only [haccessV, show (vid == k') = false from by simp [BEq.beq]; exact Ne.symm hkv]
      exact ih h

-- ## find? on hupdsStr

/- hupdsStr preserves keys from the first list, merging values with hupds
    where keys match in the second list. -/
theorem find_hupdsStr (vid : String) (s1 s2 : List (String × HMap)) :
    (hupdsStr s1 s2).find? (fun p => p.1 == vid) =
    match s1.find? (fun p => p.1 == vid) with
    | some (k, v1) =>
      match s2.find? (fun p => p.1 == k) with
      | some (_, v2) => some (k, hupds v1 v2)
      | none => some (k, v1)
    | none => none := by
  induction s1 with
  | nil => simp [hupdsStr, List.find?]
  | cons p rest ih =>
    obtain ⟨k, v1⟩ := p
    simp only [hupdsStr, List.find?]
    by_cases hkv : k = vid
    · subst hkv; simp only [beq_self_eq_true]
      split
      · rename_i v2 hf; simp [hf]
      · rename_i hf; simp [hf]
    · have hne : (k == vid) = false := by simp [BEq.beq]; exact hkv
      simp only [hne]; split <;> simp [hne, ih]

-- ## any / find? equivalence for association list keys

-- A key appears in an association list (via any) iff find? returns some.
theorem any_keys_iff_find (vid : String) (fs : List (String × HMap)) :
    (fs.any (fun x => x.1 == vid)) = true ↔ fs.find? (fun p => p.1 == vid) ≠ none := by
  induction fs with
  | nil => simp [List.any, List.find?]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.any, List.find?, Bool.or_eq_true]
    by_cases h : k = vid
    · subst h; simp
    · simp [show (k == vid) = false from by simp [BEq.beq]; exact h, ih]

-- ## find? distributes over append

-- find? on a concatenation: search the first list, fall through to second.
theorem find_append (vid : String) (xs ys : List (String × HMap)) :
    (xs ++ ys).find? (fun p => p.1 == vid) =
    match xs.find? (fun p => p.1 == vid) with
    | some r => some r
    | none => ys.find? (fun p => p.1 == vid) := by
  induction xs with
  | nil => simp [List.find?]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, List.find?]
    by_cases hkv : k = vid
    · subst hkv; simp
    · simp [show (k == vid) = false from by simp [BEq.beq]; exact hkv, ih]

-- ## haccessV distributes over append

-- haccessV over a concatenation: search the first list, fall through to second.
theorem haccessV_append (vid : String) (xs ys : List (String × HMap)) :
    haccessV vid (xs ++ ys) =
    match xs.find? (fun p => p.1 == vid) with
    | some (_, v) => v
    | none => haccessV vid ys := by
  induction xs with
  | nil => simp [List.find?, haccessV]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.cons_append, haccessV, List.find?]
    by_cases hkv : vid = k
    · subst hkv; simp
    · have hne : (k == vid) = false := by simp [BEq.beq]; exact Ne.symm hkv
      have hne2 : (vid == k) = false := by simp [BEq.beq]; exact hkv
      simp [hne, hne2, ih]

-- ## haccessV on hupdsStr: miss and hit cases

-- If vid is not found in s2, then haccessV vid (hupdsStr s1 s2) = haccessV vid s1.
theorem haccessV_hupdsStr_miss (vid : String) (s1 s2 : List (String × HMap))
    (hmiss : s2.find? (fun p => p.1 == vid) = none) :
    haccessV vid (hupdsStr s1 s2) = haccessV vid s1 := by
  induction s1 with
  | nil => simp [hupdsStr, haccessV]
  | cons p rest ih =>
    obtain ⟨k, v1⟩ := p
    simp only [hupdsStr]
    by_cases hkv : vid = k
    · subst hkv
      rw [hmiss]; simp [haccessV]
    · have hne : (vid == k) = false := by simp [BEq.beq]; exact hkv
      split <;> simp only [haccessV, hne] <;> exact ih

-- If vid is found in s2, haccessV on hupdsStr factors through haccessV on s1.
theorem haccessV_hupdsStr_hit (vid : String) (s1 s2 : List (String × HMap))
    {k2 : String} {v2 : HMap}
    (hhit : s2.find? (fun p => p.1 == vid) = some (k2, v2)) :
    haccessV vid (hupdsStr s1 s2) =
    match s1.find? (fun p => p.1 == vid) with
    | some (_, v1) => hupds v1 v2
    | none => .empty := by
  induction s1 with
  | nil => simp [hupdsStr, haccessV, List.find?]
  | cons p rest ih =>
    obtain ⟨k, v1⟩ := p
    simp only [hupdsStr, List.find?]
    by_cases hkv : vid = k
    · subst hkv
      rw [hhit]; simp [haccessV]
    · have hne : (vid == k) = false := by simp [BEq.beq]; exact hkv
      have hne2 : (k == vid) = false := by simp [BEq.beq]; exact Ne.symm hkv
      rw [hne2]
      split <;> simp only [haccessV, hne] <;> exact ih

-- ## haccessV on hbinUStr2: miss and general cases

-- If vid is not found in s2, then haccessV vid (hbinUStr2 s1 s2) = .empty.
theorem haccessV_hbinUStr2_miss (vid : String) (s1 s2 : List (String × HMap))
    (hmiss : s2.find? (fun p => p.1 == vid) = none) :
    haccessV vid (hbinUStr2 s1 s2) = .empty := by
  unfold hbinUStr2
  induction s2 with
  | nil => simp [List.filter, haccessV]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.find?] at hmiss
    by_cases hkv : k = vid
    · subst hkv; simp at hmiss
    · have hne : (k == vid) = false := by simp [BEq.beq]; exact hkv
      rw [hne] at hmiss
      simp only [List.filter]
      have hne2 : (vid == k) = false := by simp [BEq.beq]; exact Ne.symm hkv
      cases hfilt : (!(s1.any fun (k', _) => k' == k))
      · simp only [hfilt, ↓reduceIte]; exact ih hmiss
      · simp only [hfilt, ↓reduceIte, haccessV, hne2]; exact ih hmiss

-- haccessV on hbinUStr2: entries from s2 not in s1.
theorem haccessV_hbinUStr2 (vid : String) (s1 s2 : List (String × HMap)) :
    haccessV vid (hbinUStr2 s1 s2) =
    if s1.any (fun p => p.1 == vid) then .empty
    else haccessV vid s2 := by
  unfold hbinUStr2
  induction s2 with
  | nil => simp [List.filter, haccessV]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.filter]
    by_cases hkv : vid = k
    · subst hkv
      cases hin : (s1.any (fun p => p.1 == vid))
      · simp only [hin, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
        simp [haccessV]
      · simp only [hin, Bool.not_true, ↓reduceIte]
        rw [ih]; simp [hin]
    · have hne : (vid == k) = false := by simp [BEq.beq]; exact hkv
      cases hfilt : (!(s1.any fun (k', _) => k' == k))
      · simp only [hfilt, ↓reduceIte]
        rw [ih]; simp [haccessV, hne]
      · simp only [hfilt, ↓reduceIte, haccessV, hne]
        exact ih

-- ## haccess on non-str cases

@[simp] theorem haccess_empty (vid : VId) : haccess .empty vid = .empty := rfl
@[simp] theorem haccess_bits (b : SZ) (vid : VId) : haccess (.bits b) vid = .empty := rfl
@[simp] theorem haccess_arr (vs : List (Int × HMap)) (vid : VId) :
    haccess (.arr vs) vid = .empty := rfl
@[simp] theorem haccess_str (fs : List (String × HMap)) (vid : VId) :
    haccess (.str fs) vid = haccessV vid fs := rfl

-- ## find? key equality

-- If find? for vid returns (k, v), then k = vid.
theorem find_key_eq {vid : String} {fs : List (String × HMap)} {k : String} {v : HMap}
    (h : fs.find? (fun p => p.1 == vid) = some (k, v)) : k = vid := by
  induction fs with
  | nil => simp [List.find?] at h
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.find?] at h
    by_cases hkv : k' = vid
    · subst hkv; simp at h; exact h.1.symm
    · have hne : (k' == vid) = false := by simp [BEq.beq]; exact hkv
      rw [hne] at h; exact ih h

-- haccessV agrees with find? when both find the same key.
theorem haccessV_eq_of_find {vid : String} {fs : List (String × HMap)} {k : String} {v : HMap}
    (h : fs.find? (fun p => p.1 == vid) = some (k, v)) : haccessV vid fs = v :=
  haccessV_of_find_some h

-- ## find? on hupdsStr: some implies some

-- If s1 has vid, then hupdsStr s1 s2 also has vid (with a possibly updated value).
theorem find_hupdsStr_some_of_s1_some (vid : String) (s1 s2 : List (String × HMap))
    {k : String} {v1 : HMap}
    (h : s1.find? (fun p => p.1 == vid) = some (k, v1)) :
    ∃ v, (hupdsStr s1 s2).find? (fun p => p.1 == vid) = some (k, v) := by
  have hfs := find_hupdsStr vid s1 s2; rw [h] at hfs; dsimp at hfs
  cases hf2 : s2.find? (fun p => p.1 == k)
  · rw [hf2] at hfs; dsimp at hfs; exact ⟨v1, hfs⟩
  · rename_i p2; rw [hf2] at hfs; dsimp at hfs; exact ⟨hupds v1 p2.2, hfs⟩

-- ## Core composition: haccessV on hupdsStr ++ hbinUStr2

-- When haccessV vid s2 = .empty, haccessV vid (hupdsStr s1 s2 ++ hbinUStr2 s1 s2) = haccessV vid s1.
theorem haccessV_hupds_combined_miss (s1 s2 : List (String × HMap)) (vid : VId)
    (hmiss : haccessV vid s2 = HMap.empty) :
    haccessV vid (hupdsStr s1 s2 ++ hbinUStr2 s1 s2) = haccessV vid s1 := by
  cases hf2 : s2.find? (fun p => p.1 == vid)
  case none =>
    have hstr_eq := haccessV_hupdsStr_miss vid s1 s2 hf2
    have hbin_eq := haccessV_hbinUStr2_miss vid s1 s2 hf2
    rw [haccessV_append]
    cases hfs : (hupdsStr s1 s2).find? (fun p => p.1 == vid)
    · dsimp; rw [hbin_eq, ← hstr_eq, haccessV_of_find_none hfs]
    · rename_i p; obtain ⟨kk, vv⟩ := p; dsimp; rw [← hstr_eq, haccessV_of_find_some hfs]
  case some p2 =>
    obtain ⟨k2, v2⟩ := p2
    have hv2 : v2 = .empty := by
      have := haccessV_of_find_some hf2; rw [hmiss] at this; exact this.symm
    subst hv2
    rw [haccessV_append]
    cases hfs : (hupdsStr s1 s2).find? (fun p => p.1 == vid)
    · dsimp
      rw [haccessV_hbinUStr2]
      have hht := haccessV_hupdsStr_hit vid s1 s2 hf2
      rw [haccessV_of_find_none hfs] at hht
      cases hin : s1.find? (fun p => p.1 == vid)
      · rw [hin] at hht; dsimp at hht; rw [haccessV_of_find_none hin]
        cases s1.any (fun p => p.1 == vid) <;> simp [hmiss]
      · rename_i p1; exfalso
        have ⟨v, hfss⟩ := find_hupdsStr_some_of_s1_some vid s1 s2 hin
        rw [hfs] at hfss; simp at hfss
    · rename_i p; obtain ⟨kk, vv⟩ := p; dsimp
      have hvv := haccessV_of_find_some hfs
      have hht := haccessV_hupdsStr_hit vid s1 s2 hf2
      rw [hvv] at hht
      cases hin : s1.find? (fun p => p.1 == vid)
      · rw [hin] at hht; dsimp at hht; rw [hht, haccessV_of_find_none hin]
      · rename_i p1; obtain ⟨k1, v1⟩ := p1
        rw [hin] at hht; dsimp at hht
        rw [hht, hupds_empty_right]; exact (haccessV_of_find_some hin).symm

-- ## find? on hupdsStr: none from s1 none

-- If s1 has no entry for vid, neither does hupdsStr s1 s2.
theorem find_hupdsStr_none_of_s1_none (vid : String) (s1 s2 : List (String × HMap))
    (h : s1.find? (fun p => p.1 == vid) = none) :
    (hupdsStr s1 s2).find? (fun p => p.1 == vid) = none := by
  have := find_hupdsStr vid s1 s2; rw [h] at this; exact this

-- ## haccess_hupds for .str .str case

-- haccess distributes over hupds for .str maps.
theorem haccess_hupds_str_str (s1 s2 : List (String × HMap)) (vid : VId) :
    haccessV vid (hupdsStr s1 s2 ++ hbinUStr2 s1 s2) = hupds (haccessV vid s1) (haccessV vid s2) := by
  rw [haccessV_append]
  have hfs_char := find_hupdsStr vid s1 s2
  cases hf1 : s1.find? (fun p => p.1 == vid)
  case none =>
    rw [hf1] at hfs_char; dsimp at hfs_char
    rw [hfs_char]; dsimp
    have h1 := haccessV_of_find_none hf1
    cases hf2 : s2.find? (fun p => p.1 == vid)
    case none =>
      rw [haccessV_hbinUStr2_miss vid s1 s2 hf2, h1, haccessV_of_find_none hf2]; rfl
    case some p2 =>
      obtain ⟨k2, v2⟩ := p2
      rw [haccessV_hbinUStr2, h1, haccessV_of_find_some hf2, hupds_empty_left]
      have : (s1.any (fun p => p.1 == vid)) = false := by
        rw [Bool.eq_false_iff]; intro h; exact ((any_keys_iff_find vid s1).mp h) hf1
      rw [this]; simp
  case some p1 =>
    obtain ⟨k1, v1⟩ := p1
    rw [hf1] at hfs_char; dsimp at hfs_char
    have hk1 : k1 = vid := find_key_eq hf1
    have h1 := haccessV_of_find_some hf1
    cases hf2 : s2.find? (fun p => p.1 == k1)
    case none =>
      rw [hf2] at hfs_char; dsimp at hfs_char; rw [hfs_char]; dsimp; rw [h1]
      have : s2.find? (fun p => p.1 == vid) = none := by rw [← hk1]; exact hf2
      rw [haccessV_of_find_none this, hupds_empty_right]
    case some p2 =>
      obtain ⟨k2, v2⟩ := p2
      rw [hf2] at hfs_char; dsimp at hfs_char; rw [hfs_char]; dsimp; rw [h1]
      have : s2.find? (fun p => p.1 == vid) = some (k2, v2) := by rw [← hk1]; exact hf2
      rw [haccessV_of_find_some this]

-- ## hupds fixpoint implies equality (for same-type HMaps)

/- Two HMaps have the same top-level constructor. In well-typed Verilog states,
    all fields accessed by haccess at the same path have the same shape. -/
inductive SameShape : HMap → HMap → Prop where
  | empty : SameShape .empty .empty
  | bits : SameShape (.bits a) (.bits b)
  | arr : SameShape (.arr a) (.arr b)
  | str : SameShape (.str a) (.str b)

/- An HMap is a leaf value (bits). In the Verilog semantics, process updates
    always write leaf (bits) values to individual variables, never structured
    values. This predicate is used to restrict fixpoint theorems to the
    provable cases. -/
inductive IsLeaf : HMap → Prop where
  | bits : IsLeaf (.bits b)

/- If hupds a b = a, b ≠ .empty, and a and b have the same top-level
    constructor (SameShape), then a = b.

    Proved for leaf types (.empty, .bits). The .arr/.arr and .str/.str cases
    are unprovable in general (a may have extra keys not in b) but never
    arise in the Verilog semantics because process updates write leaf values.

    For the actually-needed case (leaf updates), use hupds_fixpt_eq_leaf. -/
theorem hupds_fixpt_eq_leaf (a b : HMap) (hfp : hupds a b = a) (hne : b ≠ .empty)
    (hss : SameShape a b) (hleaf : IsLeaf b) : a = b := by
  match a, b, hss, hleaf with
  | .bits _, .bits _, _, _ => simp [hupds] at hfp; congr; exact hfp.symm

-- ## hupds self-idempotency: hupds a a = a

-- A key from a list is found by any on that list.
private theorem any_self_key_str (k : String) (v : HMap) (s : List (String × HMap))
    (hmem : (k, v) ∈ s) : s.any (fun (k', _) => k' == k) = true := by
  exact List.any_eq_true.mpr ⟨(k, v), hmem, beq_self_eq_true k⟩

private theorem any_self_key_int (k : Int) (v : HMap) (s : List (Int × HMap))
    (hmem : (k, v) ∈ s) : s.any (fun (k', _) => k' == k) = true := by
  exact List.any_eq_true.mpr ⟨(k, v), hmem, beq_self_eq_true k⟩

-- Every key that appears in a list is found by `any`.
private theorem any_key_mem_str {k : String} {v : HMap} {s : List (String × HMap)}
    (h : (k, v) ∈ s) : (s.any fun (k', _) => k' == k) = true :=
  List.any_eq_true.mpr ⟨(k, v), h, beq_self_eq_true k⟩

private theorem any_key_mem_int {k : Int} {v : HMap} {s : List (Int × HMap)}
    (h : (k, v) ∈ s) : (s.any fun (k', _) => k' == k) = true :=
  List.any_eq_true.mpr ⟨(k, v), h, beq_self_eq_true k⟩

-- hbinUStr2 s s = [] (every key in s is in s).
theorem hbinUStr2_self (s : List (String × HMap)) :
    hbinUStr2 s s = [] := by
  unfold hbinUStr2
  apply List.filter_eq_nil_iff.mpr
  intro ⟨k, v⟩ hmem
  show ¬(!(s.any fun (k', _) => k' == k)) = true
  rw [any_key_mem_str hmem]; simp

-- hbinUArr2 s s = [] (every key in s is in s).
theorem hbinUArr2_self (s : List (Int × HMap)) :
    hbinUArr2 s s = [] := by
  unfold hbinUArr2
  apply List.filter_eq_nil_iff.mpr
  intro ⟨k, v⟩ hmem
  show ¬(!(s.any fun (k', _) => k' == k)) = true
  rw [any_key_mem_int hmem]; simp

-- find? on a list finds the first entry with matching key.
theorem find_self_head (k : String) (v : HMap) (rest : List (String × HMap)) :
    ((k, v) :: rest).find? (fun p => p.1 == k) = some (k, v) := by
  simp [List.find?]

theorem find_self_head_int (k : Int) (v : HMap) (rest : List (Int × HMap)) :
    ((k, v) :: rest).find? (fun p => p.1 == k) = some (k, v) := by
  simp [List.find?]

-- hupdsStr preserves list structure: it only changes values, not keys or length.
theorem hupdsStr_keys (s1 s2 : List (String × HMap)) :
    (hupdsStr s1 s2).map Prod.fst = s1.map Prod.fst := by
  induction s1 with
  | nil => simp [hupdsStr]
  | cons p rest ih =>
    obtain ⟨k, v1⟩ := p
    simp only [hupdsStr]
    split <;> simp [ih]

-- ## hupds identity from haccess agreement

-- hbinUStr2 is empty when all keys of s2 appear in s1.
theorem hbinUStr2_empty_of_keys_subset (s1 s2 : List (String × HMap))
    (hsub : ∀ k v, (k, v) ∈ s2 → (s1.any fun (k', _) => k' == k) = true) :
    hbinUStr2 s1 s2 = [] := by
  unfold hbinUStr2
  apply List.filter_eq_nil_iff.mpr
  intro ⟨k, v⟩ hmem
  show ¬(!(s1.any fun (k', _) => k' == k)) = true
  rw [hsub k v hmem]; simp

-- No duplicate keys in an association list.
def NoDupKeys (fs : List (String × HMap)) : Prop :=
  fs.map Prod.fst |>.Nodup

-- Helper: extract the rest-of-list haccessV from the cons case.
private theorem haccessV_hupdsStr_rest (vid k : String) (v1 : HMap)
    (rest s2 : List (String × HMap)) (hne : vid ≠ k)
    (hval : haccessV vid (hupdsStr ((k, v1) :: rest) s2) = haccessV vid ((k, v1) :: rest)) :
    haccessV vid (hupdsStr rest s2) = haccessV vid rest := by
  have hne' : (vid == k) = false := by simp [BEq.beq]; exact hne
  simp only [hupdsStr] at hval
  split at hval <;> simp only [haccessV, hne'] at hval <;> exact hval

/- If hupdsStr s1 s2 value matches s1 for all keys, and s1 has no duplicate keys,
    then hupdsStr s1 s2 = s1. -/
theorem hupdsStr_id_of_haccessV_eq (s1 s2 : List (String × HMap))
    (hnodup : NoDupKeys s1)
    (hval : ∀ vid, haccessV vid (hupdsStr s1 s2) = haccessV vid s1) :
    hupdsStr s1 s2 = s1 := by
  induction s1 with
  | nil => simp [hupdsStr]
  | cons p rest ih =>
    obtain ⟨k, v1⟩ := p
    have hnodup' : (k :: rest.map Prod.fst).Nodup := hnodup
    have hk_not_in_rest : k ∉ rest.map Prod.fst :=
      (List.nodup_cons.mp hnodup').1
    have hnodup_rest : NoDupKeys rest :=
      (List.nodup_cons.mp hnodup').2
    -- For vid ≠ k, extract rest equality
    -- For vid = k, k is not in rest (no duplicates), so haccessV k rest = .empty
    have ih_hyp : ∀ vid, haccessV vid (hupdsStr rest s2) = haccessV vid rest := by
      intro vid
      by_cases hkv : vid = k
      · subst hkv
        -- k not in rest, so haccessV k rest = .empty
        -- and haccessV k (hupdsStr rest s2) = .empty (since hupdsStr preserves keys)
        have hk_none : rest.find? (fun p => p.1 == vid) = none := by
          exact List.find?_eq_none.mpr (fun ⟨k', v'⟩ hmem => by
            simp [BEq.beq]
            intro heq
            exact hk_not_in_rest (heq ▸ List.mem_map.mpr ⟨(k', v'), hmem, rfl⟩))
        have hk_rest : haccessV vid rest = .empty :=
          haccessV_of_find_none hk_none
        have hk_upd : haccessV vid (hupdsStr rest s2) = .empty := by
          apply haccessV_of_find_none
          rw [find_hupdsStr, hk_none]
        rw [hk_upd, hk_rest]
      · exact haccessV_hupdsStr_rest vid k v1 rest s2 hkv (hval vid)
    have ih_result := ih hnodup_rest ih_hyp
    simp only [hupdsStr]
    cases hf : s2.find? (fun p => p.1 == k)
    · -- k not in s2: entry unchanged
      simp only [hf]
      rw [ih_result]
    · -- k in s2: merged value = v1
      rename_i p2
      obtain ⟨k2, v2⟩ := p2
      simp only [hf]
      have hval_k := hval k
      simp only [hupdsStr, hf, haccessV, beq_self_eq_true, ite_true] at hval_k
      rw [hval_k, ih_result]

-- Helper: any_key_eq for membership in map.
theorem any_key_of_mem_map {k : String} {s1 : List (String × HMap)}
    (h : k ∈ s1.map Prod.fst) : (s1.any fun (k', _) => k' == k) = true := by
  obtain ⟨⟨k', v'⟩, hm, hkk'⟩ := List.mem_map.mp h
  exact List.any_eq_true.mpr ⟨(k', v'), hm, by simp at hkk'; simp [BEq.beq, hkk']⟩

/- Specialized version with additional hypotheses needed for the .str case.
    The NoDupKeys and key-subset conditions always hold in the Verilog semantics. -/
theorem hupds_eq_of_haccess_agree_str (s1 s2 : List (String × HMap))
    (h : ∀ vid, haccessV vid (hupdsStr s1 s2 ++ hbinUStr2 s1 s2) = haccessV vid s1)
    (hkeys : ∀ k, k ∈ s2.map Prod.fst → k ∈ s1.map Prod.fst)
    (hnodup : NoDupKeys s1) :
    hupdsStr s1 s2 ++ hbinUStr2 s1 s2 = s1 := by
  have hbin_empty : hbinUStr2 s1 s2 = [] := by
    apply hbinUStr2_empty_of_keys_subset
    intro k v hmem
    exact any_key_of_mem_map (hkeys k (List.mem_map.mpr ⟨(k, v), hmem, rfl⟩))
  rw [hbin_empty, List.append_nil] at h ⊢
  exact hupdsStr_id_of_haccessV_eq s1 s2 hnodup h

/- If haccess (hupds s u) agrees with haccess s for all fields,
    then hupds s u = s.

    Specialized to the case where s = .str s1 (which is always true in the
    Verilog semantics). For the .str/.str sub-case, requires NoDupKeys and
    key containment (both always true in Verilog). -/
theorem hupds_eq_of_haccess_agree {s1 s2 : List (String × HMap)}
    (h : ∀ vid, haccess (hupds (.str s1) (.str s2)) vid = haccess (.str s1) vid)
    (hnodup : NoDupKeys s1)
    (hkeys : ∀ k, k ∈ s2.map Prod.fst → k ∈ s1.map Prod.fst) :
    hupds (.str s1) (.str s2) = .str s1 := by
  simp only [hupds]; congr 1
  exact hupds_eq_of_haccess_agree_str s1 s2
    (fun vid => by simp only [haccess] at h; exact h vid) hkeys hnodup

-- ## haccessV on hiterStr: modification only affects the target key

-- haccessV on hiterStr for a different key is unchanged.
theorem haccessV_hiterStr_ne (vid key : String) (f : HMap → HMap) (d : HMap)
    (fs : List (String × HMap)) (hne : vid ≠ key) :
    haccessV vid (hiterStr f d key fs) = haccessV vid fs := by
  induction fs with
  | nil =>
    have hne' : (vid == key) = false := by simp [BEq.beq]; exact hne
    simp [hiterStr, haccessV, hne']
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases hkk : key = k
    · -- key = k, hiterStr replaces (k, v) with (k, f v)
      subst hkk
      simp only [hiterStr, beq_self_eq_true, ↓reduceIte]
      -- vid ≠ key, so haccessV vid ((key, f v) :: rest) = haccessV vid rest
      have hne' : (vid == key) = false := by
        simp [BEq.beq]; exact hne
      simp [haccessV, hne']
    · -- key ≠ k, hiterStr recurses to (k, v) :: hiterStr f d key rest
      have hkk' : (key == k) = false := by
        simp [BEq.beq]; exact hkk
      -- First reduce hiterStr
      have hstep : hiterStr f d key ((k, v) :: rest) = (k, v) :: hiterStr f d key rest := by
        simp [hiterStr, hkk']
      rw [hstep]
      -- Goal: haccessV vid ((k, v) :: hiterStr f d key rest) = haccessV vid ((k, v) :: rest)
      by_cases hvk : vid = k
      · subst hvk; simp [haccessV, beq_self_eq_true]
      · have hvk' : (vid == k) = false := by simp [BEq.beq]; exact hvk
        simp only [haccessV, hvk', ↓reduceIte]
        exact ih

-- haccess on hadd for a single-step vid path: different key is unchanged.
theorem haccess_hadd_ne (h : HMap) (key : String) (v : HMap) (vid : VId)
    (hne : vid ≠ key) :
    haccess (hadd h [HElt.vid key] v) vid = haccess h vid := by
  match h with
  | .empty => rfl
  | .bits _ => rfl
  | .arr _ => rfl
  | .str fs =>
    simp only [hadd, haccess]
    exact haccessV_hiterStr_ne vid key (fun _ => v) v fs hne

/- haccess on hadd for a multi-step vid path: different key is unchanged.
    This generalizes `haccess_hadd_ne` to paths of the form `HElt.vid key :: rest`. -/
theorem haccess_hadd_vid_cons_ne (h : HMap) (key : String) (rest : HPath) (v : HMap) (vid : VId)
    (hne : vid ≠ key) :
    haccess (hadd h (HElt.vid key :: rest) v) vid = haccess h vid := by
  match rest with
  | [] => exact haccess_hadd_ne h key v vid hne
  | r :: rs =>
    match h with
    | .empty => rfl
    | .bits _ => rfl
    | .arr _ => rfl
    | .str fs =>
      simp only [hadd, haccess]
      exact haccessV_hiterStr_ne vid key _ _ fs hne

-- ## Association list extensionality

/- Two association lists with the same key order, NoDupKeys, and same haccessV
    values at all keys are equal.

    This is the key extensionality lemma for .str HMaps: if two .str maps
    have the same key structure and agree on all field lookups, they are
    structurally equal. -/
theorem assocList_ext_of_nodup_keys
    (l1 l2 : List (String × HMap))
    (hnodup1 : NoDupKeys l1)
    (hkeys2 : l2.map Prod.fst = l1.map Prod.fst)
    (hval : ∀ vid, haccessV vid l1 = haccessV vid l2) :
    l1 = l2 := by
  -- Induction on l1, with l2 constrained by hkeys2
  induction l1 generalizing l2 with
  | nil =>
    have : l2.map Prod.fst = [] := hkeys2
    exact (List.map_eq_nil_iff.mp this).symm
  | cons p1 rest1 ih =>
    obtain ⟨k1, v1⟩ := p1
    cases l2 with
    | nil => simp at hkeys2
    | cons p2 rest2 =>
      obtain ⟨k2, v2⟩ := p2
      simp only [List.map_cons, List.cons.injEq] at hkeys2
      have hkeq := hkeys2.1; subst hkeq
      -- After subst, k1 is replaced by k2 (or vice versa).
      -- Values agree
      have hveq : v1 = v2 := by
        have h := hval k2
        simp only [haccessV, beq_self_eq_true, ↓reduceIte] at h
        exact h
      subst hveq
      have hnodup_rest : NoDupKeys rest1 := (List.nodup_cons.mp hnodup1).2
      congr 1
      exact ih rest2 hnodup_rest hkeys2.2 (fun vid => by
        have h := hval vid
        by_cases hkv : vid = k2
        · subst hkv
          have hk_notin_rest1 : vid ∉ rest1.map Prod.fst := (List.nodup_cons.mp hnodup1).1
          have hk_notin_rest2 : vid ∉ rest2.map Prod.fst := hkeys2.2 ▸ hk_notin_rest1
          have h1 : haccessV vid rest1 = .empty :=
            haccessV_of_find_none (List.find?_eq_none.mpr (fun ⟨k', v'⟩ hm => by
              simp [BEq.beq]; intro heq
              exact hk_notin_rest1 (heq ▸ List.mem_map.mpr ⟨(k', v'), hm, rfl⟩)))
          have h2 : haccessV vid rest2 = .empty :=
            haccessV_of_find_none (List.find?_eq_none.mpr (fun ⟨k', v'⟩ hm => by
              simp [BEq.beq]; intro heq
              exact hk_notin_rest2 (heq ▸ List.mem_map.mpr ⟨(k', v'), hm, rfl⟩)))
          rw [h1, h2]
        · have hne : (vid == k2) = false := by simp [BEq.beq]; exact hkv
          simp only [haccessV, hne, ↓reduceIte] at h
          exact h)

end VerilLean.Lib.HMapLemmas
