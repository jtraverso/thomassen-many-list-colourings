/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.LemmaE

/-!
# Theorem 2 for outer cycles of length three and four

A proper precolouring of an outer cycle of length three or four extends to the interior when the
interior vertices have lists of size at least five.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The conclusion of Theorem 2: the precolouring `f₀` of the outer cycle `c` extends. -/
def Extends (H : SimpleGraph V) (S : Finset V) (c : List V) (L : V → Finset C) (f₀ : V → C) :
    Prop :=
  ∃ f : V → C, (∀ x ∈ c, f x = f₀ x) ∧ (∀ x ∈ S, x ∉ c → f x ∈ L x) ∧ IsProperOn H S f

namespace NTCalc

variable (T : NTCalc V)

/-- **Theorem 2, triangles.** -/
theorem thm2_three (H : SimpleGraph V) {S : Finset V} {a b z : V} (hNT : T.NT H S [a, b, z])
    (L : V → Finset C) (f₀ : V → C)
    (hprop : ∀ x ∈ [a, b, z], ∀ y ∈ [a, b, z], H.Adj x y → f₀ x ≠ f₀ y)
    (h5 : ∀ x ∈ S, x ∉ [a, b, z] → 5 ≤ (L x).card) : Extends H S [a, b, z] L f₀ := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hab, haz⟩, hbz, -⟩ := hnd
  have hrot : T.NT H S (z :: [a, b]) := T.rotate_back (by simpa using hNT)
  obtain ⟨us, hus, hnb, hNT', -⟩ := T.delete hrot (by simp) (by
    intro w hw _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · left; rfl
    · right; rfl)
  have hzS : z ∈ S := T.subset hNT z (by simp)
  let L' : V → Finset C := fun x => if x ∈ us then (L x).erase (f₀ z) else L x
  have hus5 : ∀ u ∈ us, 5 ≤ (L u).card := by
    intro u hu
    obtain ⟨huS, hun⟩ := hus u hu
    exact h5 u huS (by simpa [or_comm, or_left_comm] using hun)
  obtain ⟨f', hf'a, hf'b, hf'L, hf'p⟩ := T.thm1 H _ (S.erase z) rfl a b us
    (by simpa using hNT') L' f₀ (hprop a (by simp) b (by simp) (T.adj_cons hNT))
    (by
      intro x hx
      simp only [L', hx, if_true]
      have := Finset.pred_card_le_card_erase (s := L x) (a := f₀ z)
      have := hus5 x hx
      omega)
    (by
      intro x hx hxc
      have hxu : x ∉ us := fun h => hxc (by simp [h])
      simp only [L', hxu, if_false]
      apply h5 x (Finset.mem_of_mem_erase hx)
      have hxz : x ≠ z := Finset.ne_of_mem_erase hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.1, hxc.2.1, hxz⟩)
  refine ⟨Function.update f' z (f₀ z), ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [Function.update_of_ne haz]; exact hf'a
    · rw [Function.update_of_ne hbz]; exact hf'b
    · simp
  · intro x hx hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc
    rw [Function.update_of_ne hxc.2.2]
    have hm := hf'L x (Finset.mem_erase.mpr ⟨hxc.2.2, hx⟩) hxc.1 hxc.2.1
    by_cases hxu : x ∈ us
    · simp only [L', hxu, if_true] at hm; exact Finset.mem_of_mem_erase hm
    · simpa [L', hxu] using hm
  · have hzn : ∀ w ∈ S, H.Adj z w → w ≠ z → f' w ≠ f₀ z := by
      intro w hw hzw hwz
      rcases hnb w hw hzw with h | h | h
      · simp only [List.head?_cons, Option.some.injEq] at h
        subst h; rw [hf'a]; exact hprop _ (by simp) z (by simp) hzw.symm
      · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h
        subst h; rw [hf'b]; exact hprop _ (by simp) z (by simp) hzw.symm
      · have hm := hf'L w (Finset.mem_erase.mpr ⟨hwz, hw⟩)
          (fun e => (hus w h).2 (by simp [e])) (fun e => (hus w h).2 (by simp [e]))
        simp only [L', h, if_true] at hm
        exact Finset.ne_of_mem_erase hm
    intro u hu w hw huw
    by_cases hu' : u = z
    · subst hu'
      have hwz : w ≠ u := fun e => H.loopless.irrefl _ (e ▸ huw)
      rw [Function.update_self, Function.update_of_ne hwz]
      exact (hzn w hw huw hwz).symm
    · by_cases hw' : w = z
      · subst hw'
        rw [Function.update_self, Function.update_of_ne hu']
        exact hzn u hu huw.symm hu'
      · rw [Function.update_of_ne hu', Function.update_of_ne hw']
        exact hf'p u (Finset.mem_erase.mpr ⟨hu', hu⟩) w (Finset.mem_erase.mpr ⟨hw', hw⟩) huw

theorem card_freeCols_ge {H : SimpleGraph V} {L : V → Finset C} {f₀ : V → C} {P : List V} {x : V}
    (N : Finset V) (hN : ∀ y ∈ P, H.Adj x y → y ∈ N) :
    (L x).card - N.card ≤ (freeCols H L f₀ P x).card := by
  classical
  have hsub : (L x) \ N.image f₀ ⊆ freeCols H L f₀ P x := by
    intro col hc
    rw [Finset.mem_sdiff, Finset.mem_image] at hc
    rw [mem_freeCols]
    exact ⟨hc.1, fun y hy hxy e => hc.2 ⟨y, hN y hy hxy, e⟩⟩
  calc (L x).card - N.card ≤ (L x).card - (N.image f₀).card := by
        have := Finset.card_image_le (s := N) (f := f₀); omega
    _ ≤ ((L x) \ N.image f₀).card := Finset.le_card_sdiff _ _
    _ ≤ _ := Finset.card_le_card hsub

theorem extends_of_mem_iff {H : SimpleGraph V} {S : Finset V} {c c' : List V}
    {L : V → Finset C} {f₀ : V → C} (h : ∀ x, x ∈ c ↔ x ∈ c') (he : Extends H S c L f₀) :
    Extends H S c' L f₀ := by
  obtain ⟨f, h1, h2, h3⟩ := he
  exact ⟨f, fun x hx => h1 x ((h x).2 hx), fun x hx hxc => h2 x hx (fun hc => hxc ((h x).1 hc)),
    h3⟩

/-- Theorem 2 for a quadrilateral with the chord `a c`. -/
theorem thm2_four_chord (H : SimpleGraph V) {S : Finset V} {a b c d : V}
    (hNT : T.NT H S [a, b, c, d]) (hac : H.Adj a c) (L : V → Finset C) (f₀ : V → C)
    (hprop : ∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], H.Adj x y → f₀ x ≠ f₀ y)
    (h5 : ∀ x ∈ S, x ∉ [a, b, c, d] → 5 ≤ (L x).card) : Extends H S [a, b, c, d] L f₀ := by
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hab, hac', had⟩, ⟨hbc, hbd⟩, hcd, -⟩ := hnd
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ :=
    T.chord (x := a) (l₁ := [b]) (y := c) (l₂ := [d]) (by simpa using hNT) (by simp) (by simp) hac
  have h₁' : T.NT H S₁ [a, b, c] := by simpa using h₁
  have h₂' : T.NT H S₂ [c, d, a] := by simpa using h₂
  have hmem : ∀ x, x ∈ S₁ → x ∈ S₂ → x = a ∨ x = c := by
    intro x h1 h2
    have : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
  have hdS₂ : d ∈ S₂ := T.subset h₂' d (by simp)
  have hbS₁ : b ∈ S₁ := T.subset h₁' b (by simp)
  have hdS₁ : d ∉ S₁ := fun h => (hmem d h hdS₂).elim (fun e => had e.symm) (fun e => hcd e.symm)
  have hbS₂ : b ∉ S₂ := fun h => (hmem b hbS₁ h).elim (fun e => hab e.symm) (fun e => hbc e)
  obtain ⟨f₁, hf₁c, hf₁L, hf₁p⟩ := T.thm2_three H h₁' L f₀
    (fun x hx y hy => hprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₁ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.1, hxc.2.1, hxc.2.2, fun e => hdS₁ (e ▸ hx)⟩)
  obtain ⟨f₂, hf₂c, hf₂L, hf₂p⟩ := T.thm2_three H h₂' L f₀
    (fun x hx y hy => hprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₂ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.2.2, fun e => hbS₂ (e ▸ hx), hxc.1, hxc.2.1⟩)
  refine ⟨fun x => if x ∈ S₁ then f₁ x else f₂ x, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp)]
    · simp [hbS₁, hf₁c x (by simp)]
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp)]
    · simp [hdS₁, hf₂c x (by simp)]
  · intro x hx hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc
    by_cases h1 : x ∈ S₁
    · simp only [h1, if_true]
      exact hf₁L x h1 (by simp [hxc.1, hxc.2.1, hxc.2.2.1])
    · simp only [h1, if_false]
      have h2 : x ∈ S₂ := by
        have : x ∈ S₁ ∪ S₂ := hU ▸ hx
        exact (Finset.mem_union.mp this).resolve_left h1
      exact hf₂L x h2 (by simp [hxc.1, hxc.2.2.1, hxc.2.2.2])
  · refine isProperOn_glue hU hX hf₁p hf₂p ?_
    intro x h1 h2
    rcases hmem x h1 h2 with rfl | rfl
    · rw [hf₂c x (by simp), hf₁c x (by simp)]
    · rw [hf₂c x (by simp), hf₁c x (by simp)]

/-- Theorem 2 for a quadrilateral with an interior vertex `u` joined to `a` and `c`. -/
theorem thm2_four_opp (H : SimpleGraph V) {S : Finset V} {a b c d u : V}
    (hNT : T.NT H S [a, b, c, d]) (huS : u ∈ S) (hu : u ∉ [a, b, c, d]) (hua : H.Adj u a)
    (huc : H.Adj u c) (hac : ¬ H.Adj a c) (L : V → Finset C) (f₀ : V → C)
    (hprop : ∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], H.Adj x y → f₀ x ≠ f₀ y)
    (h5 : ∀ x ∈ S, x ∉ [a, b, c, d] → 5 ≤ (L x).card)
    (ih : ∀ S' : Finset V, S'.card < S.card → ∀ a b c d : V, T.NT H S' [a, b, c, d] →
      ∀ g : V → C, (∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], H.Adj x y → g x ≠ g y) →
      (∀ x ∈ S', x ∉ [a, b, c, d] → 5 ≤ (L x).card) → Extends H S' [a, b, c, d] L g) :
    Extends H S [a, b, c, d] L f₀ := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hu
  obtain ⟨⟨hab, hac', had⟩, ⟨hbc, hbd⟩, hcd, -⟩ := hnd
  obtain ⟨hua', hub', huc', hud'⟩ := hu
  -- a colour for `u`
  have hL5 := h5 u huS (by simp [hua', hub', huc', hud'])
  obtain ⟨col, hcol⟩ : ∃ col, col ∈ (L u) \ ({f₀ a, f₀ b, f₀ c, f₀ d} : Finset C) := by
    apply Finset.Nonempty.exists_mem
    rw [← Finset.card_pos]
    have h1 := Finset.le_card_sdiff ({f₀ a, f₀ b, f₀ c, f₀ d} : Finset C) (L u)
    have h2 : ({f₀ a, f₀ b, f₀ c, f₀ d} : Finset C).card ≤ 4 := Finset.card_le_four
    omega
  rw [Finset.mem_sdiff] at hcol
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcol
  obtain ⟨hcolL, hca, hcb, hcc, hcd'⟩ := hcol
  set g := Function.update f₀ u col with hg
  have hgu : g u = col := by simp [hg]
  have hgx : ∀ x, x ≠ u → g x = f₀ x := fun x hx => by simp [hg, hx]
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ :=
    T.cut (x := a) (l₁ := [b]) (y := c) (l₂ := [d]) (by simpa using hNT) huS
      (by simp [hua', hub', huc', hud']) hua huc hac
  have h₁' : T.NT H S₁ [a, b, c, u] := by simpa using h₁
  have h₂' : T.NT H S₂ [c, d, a, u] := by simpa using h₂
  have hmem : ∀ x, x ∈ S₁ → x ∈ S₂ → x = a ∨ x = c ∨ x = u := by
    intro x h1 h2
    have : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
  have hdS₂ : d ∈ S₂ := T.subset h₂' d (by simp)
  have hbS₁ : b ∈ S₁ := T.subset h₁' b (by simp)
  have hdS₁ : d ∉ S₁ := fun h => by
    rcases hmem d h hdS₂ with e | e | e
    · exact had e.symm
    · exact hcd e.symm
    · exact hud' e.symm
  have hbS₂ : b ∉ S₂ := fun h => by
    rcases hmem b hbS₁ h with e | e | e
    · exact hab e.symm
    · exact hbc e
    · exact hub' e.symm
  have hgprop : ∀ x ∈ [a, b, c, d, u], ∀ y ∈ [a, b, c, d, u], H.Adj x y → g x ≠ g y := by
    intro x hx y hy hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    by_cases hxu : x = u
    · subst hxu
      have hyu : y ≠ x := fun e => H.loopless.irrefl _ (e ▸ hxy)
      rw [hgu, hgx y hyu]
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hca
      · exact hcb
      · exact hcc
      · exact hcd'
      · exact absurd rfl hyu
    · by_cases hyu : y = u
      · subst hyu
        rw [hgu, hgx x hxu]
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact Ne.symm hca
        · exact Ne.symm hcb
        · exact Ne.symm hcc
        · exact Ne.symm hcd'
        · exact absurd rfl hxu
      · rw [hgx x hxu, hgx y hyu]
        exact hprop x (by simp; tauto) y (by simp; tauto) hxy
  have hcard₁ : S₁.card < S.card :=
    Finset.card_lt_card ⟨hS₁, fun h => hdS₁ (h (T.subset hNT d (by simp)))⟩
  have hcard₂ : S₂.card < S.card :=
    Finset.card_lt_card ⟨hS₂, fun h => hbS₂ (h (T.subset hNT b (by simp)))⟩
  obtain ⟨f₁, hf₁c, hf₁L, hf₁p⟩ := ih S₁ hcard₁ a b c u h₁' g
    (fun x hx y hy => hgprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₁ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.1, hxc.2.1, hxc.2.2.1, fun e => hdS₁ (e ▸ hx)⟩)
  obtain ⟨f₂, hf₂c, hf₂L, hf₂p⟩ := ih S₂ hcard₂ c d a u h₂' g
    (fun x hx y hy => hgprop x (by simp at hx ⊢; tauto) y (by simp at hy ⊢; tauto))
    (by
      intro x hx hxc
      apply h5 x (hS₂ hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc ⊢
      exact ⟨hxc.2.2.1, fun e => hbS₂ (e ▸ hx), hxc.1, hxc.2.1⟩)
  refine ⟨fun x => if x ∈ S₁ then f₁ x else f₂ x, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp), hgx x (Ne.symm hua')]
    · simp [hbS₁, hf₁c x (by simp), hgx x (Ne.symm hub')]
    · simp [T.subset h₁' x (by simp), hf₁c x (by simp), hgx x (Ne.symm huc')]
    · simp [hdS₁, hf₂c x (by simp), hgx x (Ne.symm hud')]
  · intro x hx hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxc
    by_cases hxu : x = u
    · subst hxu
      simp [T.subset h₁' x (by simp), hf₁c x (by simp), hgu, hcolL]
    by_cases h1 : x ∈ S₁
    · simp only [h1, if_true]
      exact hf₁L x h1 (by simp [hxc.1, hxc.2.1, hxc.2.2.1, hxu])
    · simp only [h1, if_false]
      have h2 : x ∈ S₂ := by
        have : x ∈ S₁ ∪ S₂ := hU ▸ hx
        exact (Finset.mem_union.mp this).resolve_left h1
      exact hf₂L x h2 (by simp [hxc.1, hxc.2.2.1, hxc.2.2.2, hxu])
  · refine isProperOn_glue hU hX hf₁p hf₂p ?_
    intro x h1 h2
    rcases hmem x h1 h2 with rfl | rfl | rfl
    · rw [hf₂c x (by simp), hf₁c x (by simp)]
    · rw [hf₂c x (by simp), hf₁c x (by simp)]
    · rw [hf₂c x (by simp), hf₁c x (by simp)]

/-- **Theorem 2, quadrilaterals.** -/
theorem thm2_four (H : SimpleGraph V) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∀ (a b c d : V), T.NT H S [a, b, c, d] →
    ∀ (L : V → Finset C) (f₀ : V → C),
    (∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], H.Adj x y → f₀ x ≠ f₀ y) →
    (∀ x ∈ S, x ∉ [a, b, c, d] → 5 ≤ (L x).card) → Extends H S [a, b, c, d] L f₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS a b c d hNT L f₀ hprop h5
  have ih' : ∀ S' : Finset V, S'.card < S.card → ∀ a b c d : V, T.NT H S' [a, b, c, d] →
      ∀ g : V → C, (∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], H.Adj x y → g x ≠ g y) →
      (∀ x ∈ S', x ∉ [a, b, c, d] → 5 ≤ (L x).card) → Extends H S' [a, b, c, d] L g :=
    fun S' hS' a b c d h g hg h5' => ih _ (hS ▸ hS') S' rfl a b c d h L g hg h5'
  have hrot : T.NT H S [b, c, d, a] := by simpa using T.rotate hNT
  have hperm : ∀ x, x ∈ [b, c, d, a] ↔ x ∈ [a, b, c, d] := by intro x; simp; tauto
  have hprop' : ∀ x ∈ [b, c, d, a], ∀ y ∈ [b, c, d, a], H.Adj x y → f₀ x ≠ f₀ y :=
    fun x hx y hy => hprop x ((hperm x).1 hx) y ((hperm y).1 hy)
  have h5' : ∀ x ∈ S, x ∉ [b, c, d, a] → 5 ≤ (L x).card :=
    fun x hx hxc => h5 x hx (fun h => hxc ((hperm x).2 h))
  by_cases hac : H.Adj a c
  · exact T.thm2_four_chord H hNT hac L f₀ hprop h5
  by_cases hbd : H.Adj b d
  · exact extends_of_mem_iff hperm (T.thm2_four_chord H hrot hbd L f₀ hprop' h5')
  by_cases hu1 : ∃ u ∈ S, u ∉ [a, b, c, d] ∧ H.Adj u a ∧ H.Adj u c
  · obtain ⟨u, huS, hu, hua, huc⟩ := hu1
    exact T.thm2_four_opp H hNT huS hu hua huc hac L f₀ hprop h5 ih'
  by_cases hu2 : ∃ u ∈ S, u ∉ [a, b, c, d] ∧ H.Adj u b ∧ H.Adj u d
  · obtain ⟨u, huS, hu, hub, hud⟩ := hu2
    exact extends_of_mem_iff hperm (T.thm2_four_opp H hrot huS
      (fun h => hu ((hperm u).1 h)) hub hud hbd L f₀ hprop' h5' ih')
  -- every interior vertex sees at most two consecutive vertices of the cycle: Lemma E
  push_neg at hu1 hu2
  obtain ⟨f, hfP, hfL, hfp⟩ := T.lemmaE H n S hS [a, b, c, d] [] (by simp) (by simpa using hNT)
    L f₀ hprop
    (by
      intro x hx hxP
      classical
      have h5x := h5 x hx hxP
      let N : Finset V := (if H.Adj x a then {a} else {c}) ∪ (if H.Adj x b then {b} else {d})
      have hN : ∀ y ∈ [a, b, c, d], H.Adj x y → y ∈ N := by
        intro y hy hxy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · simp [N, hxy]
        · simp [N, hxy]
        · have : ¬ H.Adj x a := fun h => hu1 x hx hxP h hxy
          simp [N, this]
        · have : ¬ H.Adj x b := fun h => hu2 x hx hxP h hxy
          simp [N, this]
      have hNc : N.card ≤ 2 := by
        refine (Finset.card_union_le _ _).trans ?_
        have h1 : (if H.Adj x a then ({a} : Finset V) else {c}).card ≤ 1 := by
          split_ifs <;> simp
        have h2 : (if H.Adj x b then ({b} : Finset V) else {d}).card ≤ 1 := by
          split_ifs <;> simp
        omega
      have := card_freeCols_ge (L := L) (f₀ := f₀) N hN
      omega)
    (fun x hx hxc => h5 x hx (by simpa using hxc))
  exact ⟨f, hfP, hfL, hfp⟩

end NTCalc

end ThomassenManyColourings
