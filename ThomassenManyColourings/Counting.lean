/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3

/-!
# Counting extensions

`ExtSet H S c L f₀` is the set of colourings of `S` extending the precolouring `f₀` on `c`
(and equal to `f₀` off `S`, so that distinct elements are distinct colourings of `S`). It is
finite. Across a separation `S = S₁ ∪ S₂` whose common part lies on the outer cycle `c₂` of
`S₂`, every extension of an extension to `S₁` is an extension to `S`, and extensions of distinct
colourings of `S₁` are distinct; hence `#ext(S) ≥ #ext(S₁) · min #ext(S₂)`.

The bound `N ≥ 2^{n/9 - r/3}` of Theorem 4 is written `2^n ≤ N^9 · 8^r` (`Bound4`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The colourings of `S` extending `f₀` on `c` (equal to `f₀` off `S`). -/
def ExtSet (H : SimpleGraph V) (S : Finset V) (c : List V) (L : V → Finset C) (f₀ : V → C) :
    Set (V → C) :=
  {f | (∀ v, (v ∉ S ∨ v ∈ c) → f v = f₀ v) ∧ (∀ v ∈ S, v ∉ c → f v ∈ L v) ∧
    IsProperOn H S f}

theorem extSet_finite (H : SimpleGraph V) (S : Finset V) (c : List V) (L : V → Finset C)
    (f₀ : V → C) : (ExtSet H S c L f₀).Finite := by
  classical
  let T : S → Set C := fun v => (insert (f₀ v) (L v) : Finset C)
  have hT : (Set.univ.pi T).Finite := Set.Finite.pi (fun v => Finset.finite_toSet _)
  let ext : (S → C) → V → C := fun h v => if hv : v ∈ S then h ⟨v, hv⟩ else f₀ v
  refine (hT.image ext).subset ?_
  intro f hf
  refine ⟨fun v => f v, ?_, ?_⟩
  · intro v _
    simp only [T, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    by_cases hvc : (v : V) ∈ c
    · exact Or.inl (hf.1 v (Or.inr hvc))
    · exact Or.inr (hf.2.1 v v.2 hvc)
  · funext v
    by_cases hv : v ∈ S
    · simp [ext, hv]
    · simp [ext, hv, hf.1 v (Or.inl hv)]

omit [DecidableEq C] in
theorem extSet_nonempty_iff {H : SimpleGraph V} {S : Finset V} {c : List V}
    {L : V → Finset C} {f₀ : V → C} : (ExtSet H S c L f₀).Nonempty ↔ Extends H S c L f₀ := by
  classical
  constructor
  · rintro ⟨f, h1, h2, h3⟩
    exact ⟨f, fun v hv => h1 v (Or.inr hv), h2, h3⟩
  · rintro ⟨f, h1, h2, h3⟩
    refine ⟨fun v => if v ∈ S ∧ v ∉ c then f v else f₀ v, ?_, ?_, ?_⟩
    · intro v hv
      have : ¬ (v ∈ S ∧ v ∉ c) := by tauto
      simp [this]
    · intro v hv hvc
      simp [hv, hvc, h2 v hv hvc]
    · intro p hp q hq hpq
      have ep : (if p ∈ S ∧ p ∉ c then f p else f₀ p) = f p := by
        by_cases hpc : p ∈ c
        · simp [hpc, h1 p hpc]
        · simp [hp, hpc]
      have eq : (if q ∈ S ∧ q ∉ c then f q else f₀ q) = f q := by
        by_cases hqc : q ∈ c
        · simp [hqc, h1 q hqc]
        · simp [hq, hqc]
      simp only at ep eq ⊢
      rw [ep, eq]; exact h3 p hp q hq hpq

omit [DecidableEq C] in
/-- Extensions of an extension to `S₁` are extensions to `S`. -/
theorem extSet_glue_mem {H : SimpleGraph V} {S S₁ S₂ : Finset V} {c c₁ c₂ : List V}
    {L : V → Finset C} {f₀ f₁ f₂ : V → C} (hU : S₁ ∪ S₂ = S)
    (hX : ∀ p ∈ S₁, ∀ q ∈ S₂, H.Adj p q → p ∈ S₂ ∨ q ∈ S₁)
    (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ c₂)
    (hc : ∀ z ∈ c, (z ∈ S₁ → z ∈ c₁) ∧ (z ∈ S₂ → z ∈ c₂))
    (hc₂ : ∀ z ∈ c₂, z ∉ S₁ → z ∈ c) (hl : ∀ z ∈ c₁, z ∈ S → z ∉ c → f₀ z ∈ L z)
    (h₁ : f₁ ∈ ExtSet H S₁ c₁ L f₀) (h₂ : f₂ ∈ ExtSet H S₂ c₂ L f₁) :
    f₂ ∈ ExtSet H S c L f₀ := by
  obtain ⟨a1, b1, p1⟩ := h₁
  obtain ⟨a2, b2, p2⟩ := h₂
  have hS₁ : ∀ z ∈ S₁, z ∈ S := fun z hz => hU ▸ Finset.mem_union_left _ hz
  have hS₂ : ∀ z ∈ S₂, z ∈ S := fun z hz => hU ▸ Finset.mem_union_right _ hz
  -- on `S₁` (and off `S₂`), `f₂` is `f₁`
  have e21 : ∀ z, (z ∈ S₁ ∨ z ∉ S₂) → f₂ z = f₁ z := by
    intro z hz
    by_cases h2 : z ∈ S₂
    · rcases hz with h1 | h1
      · exact a2 z (Or.inr (hI z h1 h2))
      · exact absurd h2 h1
    · exact a2 z (Or.inl h2)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · have h1 : z ∉ S₁ := fun h => hz (hS₁ z h)
      have h2 : z ∉ S₂ := fun h => hz (hS₂ z h)
      rw [a2 z (Or.inl h2), a1 z (Or.inl h1)]
    · by_cases h2 : z ∈ S₂
      · rw [a2 z (Or.inr ((hc z hz).2 h2))]
        by_cases h1 : z ∈ S₁
        · exact a1 z (Or.inr ((hc z hz).1 h1))
        · exact a1 z (Or.inl h1)
      · rw [a2 z (Or.inl h2)]
        by_cases h1 : z ∈ S₁
        · exact a1 z (Or.inr ((hc z hz).1 h1))
        · exact a1 z (Or.inl h1)
  · intro z hz hzc
    have hval1 : z ∈ S₁ → f₁ z ∈ L z := by
      intro h1
      by_cases hz1 : z ∈ c₁
      · rw [a1 z (Or.inr hz1)]; exact hl z hz1 hz hzc
      · exact b1 z h1 hz1
    by_cases h2 : z ∈ S₂
    · by_cases hz2 : z ∈ c₂
      · rw [a2 z (Or.inr hz2)]
        by_cases h1 : z ∈ S₁
        · exact hval1 h1
        · exact absurd (hc₂ z hz2 h1) hzc
      · exact b2 z h2 hz2
    · rw [e21 z (Or.inr h2)]
      exact hval1 ((Finset.mem_union.mp (hU ▸ hz)).resolve_right h2)
  · intro p hp q hq hpq
    by_cases hp2 : p ∈ S₂
    · by_cases hq2 : q ∈ S₂
      · exact p2 p hp2 q hq2 hpq
      · have hq1 : q ∈ S₁ := (Finset.mem_union.mp (hU ▸ hq)).resolve_right hq2
        rcases hX q hq1 p hp2 hpq.symm with h | h
        · exact absurd h hq2
        · rw [e21 p (Or.inl h), e21 q (Or.inl hq1)]; exact p1 p h q hq1 hpq
    · have hp1 : p ∈ S₁ := (Finset.mem_union.mp (hU ▸ hp)).resolve_right hp2
      by_cases hq1 : q ∈ S₁
      · rw [e21 p (Or.inl hp1), e21 q (Or.inl hq1)]; exact p1 p hp1 q hq1 hpq
      · have hq2 : q ∈ S₂ := (Finset.mem_union.mp (hU ▸ hq)).resolve_left hq1
        rcases hX p hp1 q hq2 hpq with h | h
        · exact absurd h hp2
        · exact absurd h hq1

omit [DecidableEq C] in
/-- Extensions of distinct colourings of `S₁` are distinct. -/
theorem extSet_glue_disjoint {H : SimpleGraph V} {S₁ S₂ : Finset V} {c₁ c₂ : List V}
    {L : V → Finset C} {f₀ f₁ f₁' f₂ : V → C} (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ c₂)
    (h₁ : f₁ ∈ ExtSet H S₁ c₁ L f₀) (h₁' : f₁' ∈ ExtSet H S₁ c₁ L f₀)
    (h₂ : f₂ ∈ ExtSet H S₂ c₂ L f₁) (h₂' : f₂ ∈ ExtSet H S₂ c₂ L f₁') : f₁ = f₁' := by
  funext z
  by_cases hz : z ∈ S₁
  · have hz' : z ∉ S₂ ∨ z ∈ c₂ := by
      by_cases h2 : z ∈ S₂
      · exact Or.inr (hI z hz h2)
      · exact Or.inl h2
    rw [← h₂.1 z hz', h₂'.1 z hz']
  · rw [h₁.1 z (Or.inl hz), h₁'.1 z (Or.inl hz)]

/-- **Counting across a separation**: `#ext(S) ≥ #ext(S₁) · M` when every colouring of `S₁`
has at least `M` extensions to `S₂`. -/
theorem ncard_extSet_glue {H : SimpleGraph V} {S S₁ S₂ : Finset V} {c c₁ c₂ : List V}
    {L : V → Finset C} {f₀ : V → C} (M : ℕ) (hU : S₁ ∪ S₂ = S)
    (hX : ∀ p ∈ S₁, ∀ q ∈ S₂, H.Adj p q → p ∈ S₂ ∨ q ∈ S₁)
    (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ c₂)
    (hc : ∀ z ∈ c, (z ∈ S₁ → z ∈ c₁) ∧ (z ∈ S₂ → z ∈ c₂))
    (hc₂ : ∀ z ∈ c₂, z ∉ S₁ → z ∈ c) (hl : ∀ z ∈ c₁, z ∈ S → z ∉ c → f₀ z ∈ L z)
    (hM : ∀ f₁ ∈ ExtSet H S₁ c₁ L f₀, M ≤ (ExtSet H S₂ c₂ L f₁).ncard) :
    (ExtSet H S₁ c₁ L f₀).ncard * M ≤ (ExtSet H S c L f₀).ncard := by
  classical
  set E₁ := (extSet_finite H S₁ c₁ L f₀).toFinset
  let E : (V → C) → Finset (V → C) := fun f₁ => (extSet_finite H S₂ c₂ L f₁).toFinset
  have hsub : E₁.biUnion E ⊆ (extSet_finite H S c L f₀).toFinset := by
    intro f hf
    simp only [Finset.mem_biUnion, E₁, E, Set.Finite.mem_toFinset] at hf ⊢
    obtain ⟨f₁, h1, h2⟩ := hf
    exact extSet_glue_mem hU hX hI hc hc₂ hl h1 h2
  have hdisj : (E₁ : Set (V → C)).PairwiseDisjoint E := by
    intro f₁ h1 f₁' h1' hne
    simp only [Set.Finite.coe_toFinset, E₁] at h1 h1'
    refine Finset.disjoint_left.mpr (fun f₂ ha hb => hne ?_)
    simp only [E, Set.Finite.mem_toFinset] at ha hb
    exact extSet_glue_disjoint hI h1 h1' ha hb
  rw [Set.ncard_eq_toFinset_card _ (extSet_finite H S₁ c₁ L f₀),
    Set.ncard_eq_toFinset_card _ (extSet_finite H S c L f₀)]
  calc E₁.card * M = E₁.card • M := by rw [smul_eq_mul]
    _ ≤ ∑ f₁ ∈ E₁, (E f₁).card := by
        apply Finset.card_nsmul_le_sum
        intro f₁ hf₁
        simp only [E₁, Set.Finite.mem_toFinset] at hf₁
        have := hM f₁ hf₁
        rwa [Set.ncard_eq_toFinset_card _ (extSet_finite H S₂ c₂ L f₁)] at this
    _ = (E₁.biUnion E).card := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

omit [DecidableEq C] in
/-- **Deleting a precoloured vertex**: colourings of `S` are colourings of `S − v` with the
colour of `v` removed from the lists of its neighbours. -/
theorem extSet_erase_pc {H : SimpleGraph V} {S : Finset V} {c₀ c₀' : List V} {v : V}
    {L L' : V → Finset C} {g : V → C} [DecidableEq C] (hv : v ∈ c₀) (hvS : v ∈ S)
    (hc' : ∀ w, w ∈ c₀' ↔ w ∈ c₀ ∧ w ≠ v)
    (hL₁ : ∀ u ∈ S, u ∉ c₀ → H.Adj v u → L' u = (L u).erase (g v))
    (hL₂ : ∀ u ∈ S, u ∉ c₀ → ¬ H.Adj v u → L' u = L u)
    (hpc : ∀ w ∈ c₀, w ∈ S → H.Adj v w → g v ≠ g w) :
    ExtSet H S c₀ L g = ExtSet H (S.erase v) c₀' L' g := by
  ext f
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun w hw => ?_, fun w hw hwc => ?_, fun p hp q hq hpq =>
      h3 p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq) hpq⟩
    · rcases hw with hw | hw
      · by_cases hwv : w = v
        · exact h1 w (Or.inr (hwv ▸ hv))
        · exact h1 w (Or.inl (fun h => hw (Finset.mem_erase.mpr ⟨hwv, h⟩)))
      · exact h1 w (Or.inr ((hc' w).1 hw).1)
    · have hwv := Finset.ne_of_mem_erase hw
      have hwS := Finset.mem_of_mem_erase hw
      have hwc0 : w ∉ c₀ := fun h => hwc ((hc' w).2 ⟨h, hwv⟩)
      by_cases hadj : H.Adj v w
      · rw [hL₁ w hwS hwc0 hadj]
        refine Finset.mem_erase.mpr ⟨?_, h2 w hwS hwc0⟩
        rw [← h1 v (Or.inr hv)]
        exact (h3 v hvS w hwS hadj).symm
      · rw [hL₂ w hwS hwc0 hadj]; exact h2 w hwS hwc0
  · rintro ⟨h1, h2, h3⟩
    have hfv : f v = g v := h1 v (Or.inl (by simp))
    refine ⟨fun w hw => ?_, fun w hw hwc => ?_, fun p hp q hq hpq => ?_⟩
    · rcases hw with hw | hw
      · exact h1 w (Or.inl (fun h => hw (Finset.mem_of_mem_erase h)))
      · by_cases hwv : w = v
        · rw [hwv]; exact hfv
        · exact h1 w (Or.inr ((hc' w).2 ⟨hw, hwv⟩))
    · have hwv : w ≠ v := fun e => hwc (e ▸ hv)
      have := h2 w (Finset.mem_erase.mpr ⟨hwv, hw⟩) (fun h => hwc ((hc' w).1 h).1)
      by_cases hadj : H.Adj v w
      · rw [hL₁ w hw hwc hadj] at this; exact Finset.mem_of_mem_erase this
      · rwa [hL₂ w hw hwc hadj] at this
    · have key : ∀ w ∈ S, w ≠ v → H.Adj v w → f v ≠ f w := by
        intro w hw hwv hvw
        rw [hfv]
        by_cases hwc : w ∈ c₀
        · rw [h1 w (Or.inr ((hc' w).2 ⟨hwc, hwv⟩))]; exact hpc w hwc hw hvw
        · have := h2 w (Finset.mem_erase.mpr ⟨hwv, hw⟩) (fun h => hwc ((hc' w).1 h).1)
          rw [hL₁ w hw hwc hvw] at this
          exact (Finset.ne_of_mem_erase this).symm
      by_cases hpv : p = v
      · subst hpv
        exact key q hq (fun e => H.loopless.irrefl _ (e ▸ hpq)) hpq
      by_cases hqv : q = v
      · subst hqv
        exact (key p hp hpv hpq.symm).symm
      exact h3 p (Finset.mem_erase.mpr ⟨hpv, hp⟩) q (Finset.mem_erase.mpr ⟨hqv, hq⟩) hpq

end ThomassenManyColourings
