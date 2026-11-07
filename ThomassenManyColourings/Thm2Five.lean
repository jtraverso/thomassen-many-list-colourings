/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Lemma1

/-!
# Theorem 2 for outer cycles of length five

A proper precolouring of an outer cycle of length five extends to the interior (lists of size
at least five) unless an interior vertex is joined to all five outer vertices and its list
consists of their colours.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

/-- No interior vertex joined to the whole outer cycle `c` has only the colours of `c`. -/
def NoHubExc (H : SimpleGraph V) (S : Finset V) (c : List V) (L : V → Finset C)
    (f₀ : V → C) : Prop :=
  ∀ u ∈ S, u ∉ c → (∀ y ∈ c, H.Adj u y) → ∃ col ∈ L u, ∀ y ∈ c, f₀ y ≠ col

/-- A pentagon with the chord `c₀ c₂` splits into a triangle and a quadrilateral. -/
theorem five_chord (H : SimpleGraph V) {S : Finset V} {c₀ c₁ c₂ c₃ c₄ : V}
    (hNT : T.NT H S [c₀, c₁, c₂, c₃, c₄]) (h02 : H.Adj c₀ c₂) (L : V → Finset C) (f₀ : V → C)
    (hprop : ∀ x ∈ [c₀, c₁, c₂, c₃, c₄], ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj x y → f₀ x ≠ f₀ y)
    (h5 : ∀ x ∈ S, x ∉ [c₀, c₁, c₂, c₃, c₄] → 5 ≤ (L x).card) :
    Extends H S [c₀, c₁, c₂, c₃, c₄] L f₀ := by
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ :=
    T.chord (x := c₀) (l₁ := [c₁]) (y := c₂) (l₂ := [c₃, c₄]) (by simpa using hNT) (by simp)
      (by simp) h02
  have h₁' : T.NT H S₁ [c₀, c₁, c₂] := by simpa using h₁
  have h₂' : T.NT H S₂ [c₂, c₃, c₄, c₀] := by simpa using h₂
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = c₀ ∨ w = c₂ := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  have hc1 : c₁ ∉ S₂ := fun h => (hmem c₁ (T.subset h₁' c₁ (by simp)) h).elim
    (fun e => hnd.1.1 e.symm) (fun e => hnd.2.1.1 e)
  have hc3 : c₃ ∉ S₁ := fun h => (hmem c₃ h (T.subset h₂' c₃ (by simp))).elim
    (fun e => hnd.1.2.2.1 e.symm) (fun e => hnd.2.2.1.1 e.symm)
  have hc4 : c₄ ∉ S₁ := fun h => (hmem c₄ h (T.subset h₂' c₄ (by simp))).elim
    (fun e => hnd.1.2.2.2 e.symm) (fun e => hnd.2.2.1.2 e.symm)
  obtain ⟨f₁, hf₁c, hf₁L, hf₁p⟩ := T.thm2_three H h₁' L f₀
    (fun x hx y hy => hprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₁ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.1, hxc.2.1, hxc.2.2, fun e => hc3 (e ▸ hx), fun e => hc4 (e ▸ hx)⟩)
  obtain ⟨f₂, hf₂c, hf₂L, hf₂p⟩ := T.thm2_four H _ S₂ rfl c₂ c₃ c₄ c₀ h₂' L f₀
    (fun x hx y hy => hprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₂ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.2.2.2, fun e => hc1 (e ▸ hx), hxc.1, hxc.2.1, hxc.2.2.1⟩)
  have hc1S₁ : c₁ ∈ S₁ := T.subset h₁' c₁ (by simp)
  refine ⟨fun x => if x ∈ S₁ then f₁ x else f₂ x, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp)]
    · simp [hc1S₁, hf₁c x (by simp)]
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp)]
    · simp [hc3, hf₂c x (by simp)]
    · simp [hc4, hf₂c x (by simp)]
  · intro x hx hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc
    by_cases h1 : x ∈ S₁
    · simp only [h1, if_true]
      exact hf₁L x h1 (by simp [hxc.1, hxc.2.1, hxc.2.2.1])
    · simp only [h1, if_false]
      have h2 : x ∈ S₂ := (Finset.mem_union.mp (hU ▸ hx)).resolve_left h1
      exact hf₂L x h2 (by simp [hxc.2.2.1, hxc.2.2.2.1, hxc.2.2.2.2, hxc.1])
  · refine isProperOn_glue hU hX hf₁p hf₂p ?_
    intro x h1 h2
    rcases hmem x h1 h2 with rfl | rfl
    · rw [hf₂c x (by simp), hf₁c x (by simp)]
    · rw [hf₂c x (by simp), hf₁c x (by simp)]

set_option maxHeartbeats 2000000 in
/-- A pentagon with an interior vertex `u` joined to `c₀, c₂`: colour `u` and cut along
`c₀ u c₂` into a quadrilateral and a pentagon. -/
theorem five_cut (H : SimpleGraph V) {S : Finset V} {c₀ c₁ c₂ c₃ c₄ u : V}
    (hNT : T.NT H S [c₀, c₁, c₂, c₃, c₄]) (huS : u ∈ S) (hu : u ∉ [c₀, c₁, c₂, c₃, c₄])
    (hu0 : H.Adj u c₀) (hu2 : H.Adj u c₂) (h02 : ¬ H.Adj c₀ c₂) (L : V → Finset C) (f₀ : V → C)
    (hprop : ∀ x ∈ [c₀, c₁, c₂, c₃, c₄], ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj x y → f₀ x ≠ f₀ y)
    (h5 : ∀ x ∈ S, x ∉ [c₀, c₁, c₂, c₃, c₄] → 5 ≤ (L x).card)
    {col : C} (hcol : col ∈ L u) (hcolC : ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj u y → f₀ y ≠ col)
    (hB : H.Adj u c₃ ∨ H.Adj u c₄ ∨
      ∀ w ∈ S, w ∉ [c₀, c₁, c₂, c₃, c₄] → ¬ (H.Adj w c₀ ∧ H.Adj w c₂ ∧ H.Adj w c₃ ∧ H.Adj w c₄))
    (ih : ∀ S' : Finset V, S'.card < S.card → ∀ d₀ d₁ d₂ d₃ d₄ : V,
      T.NT H S' [d₀, d₁, d₂, d₃, d₄] → ∀ g : V → C,
      (∀ x ∈ [d₀, d₁, d₂, d₃, d₄], ∀ y ∈ [d₀, d₁, d₂, d₃, d₄], H.Adj x y → g x ≠ g y) →
      (∀ x ∈ S', x ∉ [d₀, d₁, d₂, d₃, d₄] → 5 ≤ (L x).card) →
      NoHubExc H S' [d₀, d₁, d₂, d₃, d₄] L g → Extends H S' [d₀, d₁, d₂, d₃, d₄] L g) :
    Extends H S [c₀, c₁, c₂, c₃, c₄] L f₀ := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hu
  obtain ⟨hu0', hu1', hu2', hu3', hu4'⟩ := hu
  set g := Function.update f₀ u col with hg
  have hgu : g u = col := by simp [hg]
  have hgx : ∀ x, x ≠ u → g x = f₀ x := fun x hx => by simp [hg, hx]
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ :=
    T.cut (x := c₀) (l₁ := [c₁]) (y := c₂) (l₂ := [c₃, c₄]) (u := u) (by simpa using hNT) huS
      (by simp [hu0', hu1', hu2', hu3', hu4'])
      hu0 hu2 h02
  have h₁' : T.NT H S₁ [c₀, c₁, c₂, u] := by simpa using h₁
  have h₂' : T.NT H S₂ [c₂, c₃, c₄, c₀, u] := by simpa using h₂
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = c₀ ∨ w = c₂ ∨ w = u := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
  have hc1S₁ : c₁ ∈ S₁ := T.subset h₁' c₁ (by simp)
  have hc1 : c₁ ∉ S₂ := fun h => by
    rcases hmem c₁ hc1S₁ h with e | e | e
    · exact hnd.1.1 e.symm
    · exact hnd.2.1.1 e
    · exact hu1' e.symm
  have hc3S₂ : c₃ ∈ S₂ := T.subset h₂' c₃ (by simp)
  have hc4S₂ : c₄ ∈ S₂ := T.subset h₂' c₄ (by simp)
  have hc3 : c₃ ∉ S₁ := fun h => by
    rcases hmem c₃ h hc3S₂ with e | e | e
    · exact hnd.1.2.2.1 e.symm
    · exact hnd.2.2.1.1 e.symm
    · exact hu3' e.symm
  have hc4 : c₄ ∉ S₁ := fun h => by
    rcases hmem c₄ h hc4S₂ with e | e | e
    · exact hnd.1.2.2.2 e.symm
    · exact hnd.2.2.1.2 e.symm
    · exact hu4' e.symm
  have hgprop : ∀ x ∈ [c₀, c₁, c₂, c₃, c₄, u], ∀ y ∈ [c₀, c₁, c₂, c₃, c₄, u],
      H.Adj x y → g x ≠ g y := by
    intro x hx y hy hxy
    by_cases hxu : x = u
    · subst hxu
      have hyu : y ≠ x := fun e => H.loopless.irrefl _ (e ▸ hxy)
      rw [hgu, hgx y hyu]
      exact (hcolC y (by simp at hy ⊢; tauto) hxy).symm
    · by_cases hyu : y = u
      · subst hyu
        rw [hgu, hgx x hxu]
        exact hcolC x (by simp at hx ⊢; tauto) hxy.symm
      · rw [hgx x hxu, hgx y hyu]
        exact hprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto) hxy
  obtain ⟨f₁, hf₁c, hf₁L, hf₁p⟩ := T.thm2_four H _ S₁ rfl c₀ c₁ c₂ u h₁' L g
    (fun x hx y hy => hgprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₁ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.1, hxc.2.1, hxc.2.2.1, fun e => hc3 (e ▸ hx), fun e => hc4 (e ▸ hx)⟩)
  have hcard₂ : S₂.card < S.card :=
    Finset.card_lt_card ⟨hS₂, fun h => hc1 (h (hS₁ hc1S₁))⟩
  obtain ⟨f₂, hf₂c, hf₂L, hf₂p⟩ := ih S₂ hcard₂ c₂ c₃ c₄ c₀ u h₂' g
    (fun x hx y hy => hgprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₂ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.2.2.2.1, fun e => hc1 (e ▸ hx), hxc.1, hxc.2.1, hxc.2.2.1⟩)
    (by
      intro w hwS hwc hwall
      exfalso
      have hw0 := hwall c₀ (by simp)
      have hw2 := hwall c₂ (by simp)
      have hrotB : T.NT H S₂ (u :: [c₂, c₃, c₄, c₀]) := T.rotate_back (by simpa using h₂')
      rcases hB with h3 | h4 | hno
      · refine T.no_chord_of_crossing (y := u) (l₁ := [c₂]) (z := c₃) (l₂ := [c₄, c₀])
          (by simpa using hrotB) (by simp) (by simp) (p := c₂) (q := c₀) (by simp) (by simp)
          (Or.inr ⟨w, hwS, by simpa [or_comm, or_left_comm] using hwc, hw2, hw0⟩) h3
      · refine T.no_chord_of_crossing (y := u) (l₁ := [c₂, c₃]) (z := c₄) (l₂ := [c₀])
          (by simpa using hrotB) (by simp) (by simp) (p := c₂) (q := c₀) (by simp) (by simp)
          (Or.inr ⟨w, hwS, by simpa [or_comm, or_left_comm] using hwc, hw2, hw0⟩) h4
      · apply hno w (hS₂ hwS)
        · intro h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h hwc
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hwc (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact hc1 hwS
          · exact hwc (Or.inl rfl)
          · exact hwc (Or.inr (Or.inl rfl))
          · exact hwc (Or.inr (Or.inr (Or.inl rfl)))
        · exact ⟨hw0, hw2, hwall c₃ (by simp), hwall c₄ (by simp)⟩)
  refine ⟨fun x => if x ∈ S₁ then f₁ x else f₂ x, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp), hgx x (Ne.symm hu0')]
    · simp [hc1S₁, hf₁c x (by simp), hgx x (Ne.symm hu1')]
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp), hgx x (Ne.symm hu2')]
    · simp [hc3, hf₂c x (by simp), hgx x (Ne.symm hu3')]
    · simp [hc4, hf₂c x (by simp), hgx x (Ne.symm hu4')]
  · intro x hx hxc
    by_cases hxu : x = u
    · subst hxu
      simp [T.subset h₁' x (by simp), hf₁c x (by simp), hgu, hcol]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc
    by_cases h1 : x ∈ S₁
    · simp only [h1, if_true]
      exact hf₁L x h1 (by simp [hxc.1, hxc.2.1, hxc.2.2.1, hxu])
    · simp only [h1, if_false]
      have h2 : x ∈ S₂ := (Finset.mem_union.mp (hU ▸ hx)).resolve_left h1
      exact hf₂L x h2 (by simp [hxc.2.2.1, hxc.2.2.2.1, hxc.2.2.2.2, hxc.1, hxu])
  · refine isProperOn_glue hU hX hf₁p hf₂p ?_
    intro x h1 h2
    rcases hmem x h1 h2 with rfl | rfl | rfl
    · rw [hf₂c x (by simp), hf₁c x (by simp)]
    · rw [hf₂c x (by simp), hf₁c x (by simp)]
    · rw [hf₂c x (by simp), hf₁c x (by simp)]

/-- Three of five cyclically arranged conditions include two at distance two. -/
theorem pair_of_three (p0 p1 p2 p3 p4 : Prop) [Decidable p0] [Decidable p1] [Decidable p2]
    [Decidable p3] [Decidable p4]
    (h : 3 ≤ (if p0 then 1 else 0) + (if p1 then 1 else 0) + (if p2 then 1 else 0) +
      (if p3 then 1 else 0) + (if p4 then 1 else 0)) :
    (p0 ∧ p2) ∨ (p1 ∧ p3) ∨ (p2 ∧ p4) ∨ (p3 ∧ p0) ∨ (p4 ∧ p1) := by
  by_cases a0 : p0 <;> by_cases a1 : p1 <;> by_cases a2 : p2 <;> by_cases a3 : p3 <;>
    by_cases a4 : p4 <;>
    simp only [a0, a1, a2, a3, a4, if_true, if_false, true_and, and_true, false_and, and_false,
      or_false, false_or, true_or, or_true] at h ⊢ <;> omega

set_option maxHeartbeats 4000000 in
/-- **Theorem 2, pentagons.** -/
theorem thm2_five (H : SimpleGraph V) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∀ (c₀ c₁ c₂ c₃ c₄ : V),
    T.NT H S [c₀, c₁, c₂, c₃, c₄] → ∀ (L : V → Finset C) (f₀ : V → C),
    (∀ x ∈ [c₀, c₁, c₂, c₃, c₄], ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj x y → f₀ x ≠ f₀ y) →
    (∀ x ∈ S, x ∉ [c₀, c₁, c₂, c₃, c₄] → 5 ≤ (L x).card) →
    NoHubExc H S [c₀, c₁, c₂, c₃, c₄] L f₀ →
    Extends H S [c₀, c₁, c₂, c₃, c₄] L f₀ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS c₀ c₁ c₂ c₃ c₄ hNT L f₀ hprop h5 hhub
  have ih' : ∀ S' : Finset V, S'.card < S.card → ∀ d₀ d₁ d₂ d₃ d₄ : V,
      T.NT H S' [d₀, d₁, d₂, d₃, d₄] → ∀ g : V → C,
      (∀ x ∈ [d₀, d₁, d₂, d₃, d₄], ∀ y ∈ [d₀, d₁, d₂, d₃, d₄], H.Adj x y → g x ≠ g y) →
      (∀ x ∈ S', x ∉ [d₀, d₁, d₂, d₃, d₄] → 5 ≤ (L x).card) →
      NoHubExc H S' [d₀, d₁, d₂, d₃, d₄] L g → Extends H S' [d₀, d₁, d₂, d₃, d₄] L g :=
    fun S' h d₀ d₁ d₂ d₃ d₄ hN g hg h5' hh => ih _ (hS ▸ h) S' rfl d₀ d₁ d₂ d₃ d₄ hN L g hg h5' hh
  -- the rotations of the pentagon
  have r1 : T.NT H S [c₁, c₂, c₃, c₄, c₀] := by simpa using T.rotate hNT
  have r2 : T.NT H S [c₂, c₃, c₄, c₀, c₁] := by simpa using T.rotate r1
  have r3 : T.NT H S [c₃, c₄, c₀, c₁, c₂] := by simpa using T.rotate r2
  have r4 : T.NT H S [c₄, c₀, c₁, c₂, c₃] := by simpa using T.rotate r3
  -- transfer from a rotation
  have key : ∀ d₀ d₁ d₂ d₃ d₄ : V,
      (∀ y, y ∈ [d₀, d₁, d₂, d₃, d₄] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄]) →
      T.NT H S [d₀, d₁, d₂, d₃, d₄] →
      (H.Adj d₀ d₂ ∨ ∃ u ∈ S, u ∉ [d₀, d₁, d₂, d₃, d₄] ∧ H.Adj u d₀ ∧ H.Adj u d₂ ∧
        (∃ col ∈ L u, ∀ y ∈ [d₀, d₁, d₂, d₃, d₄], H.Adj u y → f₀ y ≠ col) ∧
        (H.Adj u d₃ ∨ H.Adj u d₄ ∨ ∀ w ∈ S, w ∉ [d₀, d₁, d₂, d₃, d₄] →
          ¬ (H.Adj w d₀ ∧ H.Adj w d₂ ∧ H.Adj w d₃ ∧ H.Adj w d₄))) →
      Extends H S [c₀, c₁, c₂, c₃, c₄] L f₀ := by
    intro d₀ d₁ d₂ d₃ d₄ hmem hN hconf
    have hprop' : ∀ x ∈ [d₀, d₁, d₂, d₃, d₄], ∀ y ∈ [d₀, d₁, d₂, d₃, d₄], H.Adj x y →
        f₀ x ≠ f₀ y := fun x hx y hy => hprop x ((hmem x).1 hx) y ((hmem y).1 hy)
    have h5' : ∀ x ∈ S, x ∉ [d₀, d₁, d₂, d₃, d₄] → 5 ≤ (L x).card :=
      fun x hx hxc => h5 x hx (fun h => hxc ((hmem x).2 h))
    apply extends_of_mem_iff hmem
    rcases hconf with h02 | ⟨u, huS, hu, hu0, hu2, ⟨col, hcol, hcolC⟩, hB⟩
    · exact T.five_chord H hN h02 L f₀ hprop' h5'
    · by_cases h02 : H.Adj d₀ d₂
      · exact T.five_chord H hN h02 L f₀ hprop' h5'
      · exact T.five_cut H hN huS hu hu0 hu2 h02 L f₀ hprop' h5' hcol hcolC hB ih'
  have m1 : ∀ y, y ∈ [c₁, c₂, c₃, c₄, c₀] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄] := by intro y; simp; tauto
  have m2 : ∀ y, y ∈ [c₂, c₃, c₄, c₀, c₁] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄] := by intro y; simp; tauto
  have m3 : ∀ y, y ∈ [c₃, c₄, c₀, c₁, c₂] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄] := by intro y; simp; tauto
  have m4 : ∀ y, y ∈ [c₄, c₀, c₁, c₂, c₃] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄] := by intro y; simp; tauto
  have m0 : ∀ y, y ∈ [c₀, c₁, c₂, c₃, c₄] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄] := fun y => Iff.rfl
  -- chords
  by_cases hc0 : H.Adj c₀ c₂
  · exact key _ _ _ _ _ m0 hNT (Or.inl hc0)
  by_cases hc1 : H.Adj c₁ c₃
  · exact key _ _ _ _ _ m1 r1 (Or.inl hc1)
  by_cases hc2 : H.Adj c₂ c₄
  · exact key _ _ _ _ _ m2 r2 (Or.inl hc2)
  by_cases hc3 : H.Adj c₃ c₀
  · exact key _ _ _ _ _ m3 r3 (Or.inl hc3)
  by_cases hc4 : H.Adj c₄ c₁
  · exact key _ _ _ _ _ m4 r4 (Or.inl hc4)
  -- counting cycle neighbours
  let cnt : V → ℕ := fun u =>
    (if H.Adj u c₀ then 1 else 0) + (if H.Adj u c₁ then 1 else 0) + (if H.Adj u c₂ then 1 else 0) +
      (if H.Adj u c₃ then 1 else 0) + (if H.Adj u c₄ then 1 else 0)
  set I := S.filter (fun u => u ∉ [c₀, c₁, c₂, c₃, c₄] ∧ 3 ≤ cnt u) with hI
  by_cases hIne : I.Nonempty
  · obtain ⟨u, huI, hmax⟩ := Finset.exists_max_image I cnt hIne
    obtain ⟨huS, hu, hu3⟩ : u ∈ S ∧ u ∉ [c₀, c₁, c₂, c₃, c₄] ∧ 3 ≤ cnt u := by
      simpa [hI] using huI
    -- a colour for `u`
    have hcolex : ∃ col ∈ L u, ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj u y → f₀ y ≠ col := by
      by_cases hall : ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj u y
      · obtain ⟨col, hcol, hcolC⟩ := hhub u huS hu hall
        exact ⟨col, hcol, fun y hy _ => hcolC y hy⟩
      · push_neg at hall
        obtain ⟨z, hz, hnz⟩ := hall
        have hL5 := h5 u huS hu
        let N : Finset C := ([c₀, c₁, c₂, c₃, c₄].toFinset.erase z).image f₀
        have hNc : N.card ≤ 4 := by
          refine Finset.card_image_le.trans ?_
          have := Finset.card_erase_of_mem (s := [c₀, c₁, c₂, c₃, c₄].toFinset)
            (List.mem_toFinset.mpr hz)
          have h2 := List.toFinset_card_le [c₀, c₁, c₂, c₃, c₄]
          simp only [List.length_cons, List.length_nil] at h2
          omega
        obtain ⟨col, hcol⟩ : ∃ col, col ∈ L u \ N := by
          apply Finset.Nonempty.exists_mem
          rw [← Finset.card_pos]
          have := Finset.le_card_sdiff N (L u)
          omega
        rw [Finset.mem_sdiff] at hcol
        refine ⟨col, hcol.1, fun y hy huy e => hcol.2 ?_⟩
        refine Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨?_, List.mem_toFinset.mpr hy⟩, e⟩
        rintro rfl; exact hnz huy
    obtain ⟨col, hcol, hcolC⟩ := hcolex
    -- a pair at distance two among the neighbours of `u`
    have hpair : (H.Adj u c₀ ∧ H.Adj u c₂) ∨ (H.Adj u c₁ ∧ H.Adj u c₃) ∨
        (H.Adj u c₂ ∧ H.Adj u c₄) ∨ (H.Adj u c₃ ∧ H.Adj u c₀) ∨ (H.Adj u c₄ ∧ H.Adj u c₁) :=
      pair_of_three _ _ _ _ _ hu3
    have hub_case : ∀ d₀ d₁ d₂ d₃ d₄ : V,
        (∀ y, y ∈ [d₀, d₁, d₂, d₃, d₄] ↔ y ∈ [c₀, c₁, c₂, c₃, c₄]) →
        T.NT H S [d₀, d₁, d₂, d₃, d₄] → H.Adj u d₀ → H.Adj u d₂ →
        (¬ H.Adj u d₃ → ¬ H.Adj u d₄ → cnt u ≤ 3) →
        (∀ w, H.Adj w d₀ → H.Adj w d₂ → H.Adj w d₃ → H.Adj w d₄ → 4 ≤ cnt w) →
        Extends H S [c₀, c₁, c₂, c₃, c₄] L f₀ := by
      intro d₀ d₁ d₂ d₃ d₄ hm hN hd0 hd2 hcu hcw
      refine key d₀ d₁ d₂ d₃ d₄ hm hN (Or.inr ⟨u, huS, fun h => hu ((hm u).1 h), hd0, hd2,
        ⟨col, hcol, fun y hy huy => hcolC y ((hm y).1 hy) huy⟩, ?_⟩)
      by_cases h3 : H.Adj u d₃
      · exact Or.inl h3
      by_cases h4 : H.Adj u d₄
      · exact Or.inr (Or.inl h4)
      refine Or.inr (Or.inr ?_)
      rintro w hwS hwc ⟨a, b, c, d⟩
      have h4w := hcw w a b c d
      have hwI : w ∈ I := by
        simp only [hI, Finset.mem_filter]
        exact ⟨hwS, fun h => hwc ((hm w).2 h), by omega⟩
      have := hmax w hwI
      have := hcu h3 h4
      omega
    rcases hpair with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · refine hub_case _ _ _ _ _ m0 hNT a b ?_ ?_
      · intro h3 h4; simp only [cnt, h3, h4, if_false]; split_ifs <;> omega
      · intro w a b c d; simp only [cnt, a, b, c, d, if_true]; split_ifs <;> omega
    · refine hub_case _ _ _ _ _ m1 r1 a b ?_ ?_
      · intro h3 h4; simp only [cnt, h3, h4, if_false]; split_ifs <;> omega
      · intro w a b c d; simp only [cnt, a, b, c, d, if_true]; split_ifs <;> omega
    · refine hub_case _ _ _ _ _ m2 r2 a b ?_ ?_
      · intro h3 h4; simp only [cnt, h3, h4, if_false]; split_ifs <;> omega
      · intro w a b c d; simp only [cnt, a, b, c, d, if_true]; split_ifs <;> omega
    · refine hub_case _ _ _ _ _ m3 r3 a b ?_ ?_
      · intro h3 h4; simp only [cnt, h3, h4, if_false]; split_ifs <;> omega
      · intro w a b c d; simp only [cnt, a, b, c, d, if_true]; split_ifs <;> omega
    · refine hub_case _ _ _ _ _ m4 r4 a b ?_ ?_
      · intro h3 h4; simp only [cnt, h3, h4, if_false]; split_ifs <;> omega
      · intro w a b c d; simp only [cnt, a, b, c, d, if_true]; split_ifs <;> omega
  · -- every interior vertex sees at most two outer vertices: Lemma E
    have hle2 : ∀ x ∈ S, x ∉ [c₀, c₁, c₂, c₃, c₄] → cnt x ≤ 2 := by
      intro x hx hxc
      by_contra h
      exact hIne ⟨x, by simp only [hI, Finset.mem_filter]; exact ⟨hx, hxc, by omega⟩⟩
    obtain ⟨f, hfP, hfL, hfp⟩ := T.lemmaE H n S hS [c₀, c₁, c₂, c₃, c₄] [] (by simp)
      (by simpa using hNT) L f₀ hprop
      (by
        intro x hx hxP
        let N : Finset V := (if H.Adj x c₀ then {c₀} else ∅) ∪ (if H.Adj x c₁ then {c₁} else ∅) ∪
          (if H.Adj x c₂ then {c₂} else ∅) ∪ (if H.Adj x c₃ then {c₃} else ∅) ∪
          (if H.Adj x c₄ then {c₄} else ∅)
        have hN : ∀ y ∈ [c₀, c₁, c₂, c₃, c₄], H.Adj x y → y ∈ N := by
          intro y hy hxy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [N, hxy]
        have hsing : ∀ (p : Prop) [Decidable p] (z : V),
            (if p then ({z} : Finset V) else ∅).card = if p then 1 else 0 := by
          intro p _ z; split_ifs <;> simp
        have hNc : N.card ≤ cnt x := by
          simp only [N, cnt]
          refine (Finset.card_union_le _ _).trans ?_
          refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
          refine (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _).trans ?_
          refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
            (Finset.card_union_le _ _) _) _) _).trans ?_
          simp only [hsing]
          exact le_refl _
        have := card_freeCols_ge (L := L) (f₀ := f₀) N hN
        have := hle2 x hx hxP
        have := h5 x hx hxP
        omega)
      (fun x hx hxc => h5 x hx (by simpa using hxc))
    exact ⟨f, hfP, hfL, hfp⟩

end NTCalc

end ThomassenManyColourings
