/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Final

/-!
# Exponentially many list colourings

**Corollary of Theorem 4.** If `H` on `S` is a near-triangulation and every vertex of `S` has a
list of at least five colours, then `H[S]` has at least `2^{|S|/9}` list colourings, that is
`2^{|S|} ≤ N^9`. The same holds for every spanning subgraph `G ≤ H`.

Proof: precolour an outer edge `x a` in two ways `(α, β₁)`, `(α, β₂)`; each precolouring extends
(Theorem 1) in at least `2^{(|S| - 2)/9}` ways (Theorem 4 with two precoloured vertices, where no
vertex has a list of size three).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The list colourings of `H[S]` (equal to `f₀` outside `S`). -/
def ColSet (H : SimpleGraph V) (S : Finset V) (L : V → Finset C) (f₀ : V → C) : Set (V → C) :=
  ExtSet H S [] L f₀

omit [DecidableEq V] [DecidableEq C] in
theorem colSet_mono {G H : SimpleGraph V} (hGH : G ≤ H) (S : Finset V) (L : V → Finset C)
    (f₀ : V → C) : ColSet H S L f₀ ⊆ ColSet G S L f₀ := by
  rintro f ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun u hu w hw huw => h3 u hu w hw (hGH huw)⟩

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Thomassen's corollary** for near-triangulations: `2^{|S|} ≤ N^9`. -/
theorem many_colourings (H : SimpleGraph V) {S : Finset V} {x a : V} {l : List V}
    (hNT : T.NT H S (x :: a :: l)) (L : V → Finset C) (h5 : ∀ v ∈ S, 5 ≤ (L v).card)
    (f₀ : V → C) : 2 ^ S.card ≤ (ColSet H S L f₀).ncard ^ 9 := by
  classical
  have hnd := T.nodup hNT
  have hxa : x ≠ a := by
    intro e; exact (List.nodup_cons.mp hnd).1 (by simp [e])
  have hxS : x ∈ S := T.subset hNT x (by simp)
  have haS : a ∈ S := T.subset hNT a (by simp)
  -- colours for the outer edge
  obtain ⟨α, hα⟩ : (L x).Nonempty := Finset.card_pos.mp (by have := h5 x hxS; omega)
  obtain ⟨β₁, hβ₁, β₂, hβ₂, hβ⟩ := Finset.one_lt_card.mp (show 1 < ((L a).erase α).card by
    have := Finset.pred_card_le_card_erase (s := L a) (a := α); have := h5 a haS; omega)
  rw [Finset.mem_erase] at hβ₁ hβ₂
  set g : C → V → C := fun β => Function.update (Function.update f₀ x α) a β with hg
  have hgx : ∀ β, g β x = α := fun β => by simp [hg, hxa]
  have hga : ∀ β, g β a = β := fun β => by simp [hg]
  have hgo : ∀ β v, v ≠ x → v ≠ a → g β v = f₀ v := fun β v h1 h2 => by simp [hg, h1, h2]
  -- each precoloured instance is inside `ColSet`
  have hsub : ∀ β ∈ [β₁, β₂], ExtSet H S [x, a] L (g β) ⊆ ColSet H S L f₀ := by
    intro β hβm f ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, fun v hv _ => ?_, h3⟩
    · rcases hv with hv | hv
      · rw [h1 v (Or.inl hv), hgo β v (fun e => hv (e ▸ hxS)) (fun e => hv (e ▸ haS))]
      · simp at hv
    · by_cases hvx : v = x
      · rw [hvx, h1 x (Or.inr (by simp)), hgx]; exact hα
      by_cases hva : v = a
      · rw [hva, h1 a (Or.inr (by simp)), hga]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hβm
        rcases hβm with rfl | rfl
        · exact hβ₁.2
        · exact hβ₂.2
      · exact h2 v hv (by simp [hvx, hva])
  have hdisj : Disjoint (ExtSet H S [x, a] L (g β₁)) (ExtSet H S [x, a] L (g β₂)) := by
    rw [Set.disjoint_left]
    intro f h1 h2
    have e1 := h1.1 a (Or.inr (by simp))
    have e2 := h2.1 a (Or.inr (by simp))
    rw [hga] at e1 e2
    exact hβ (e1.symm.trans e2)
  have hfin := extSet_finite H S [] L f₀
  have hN : (ExtSet H S [x, a] L (g β₁)).ncard + (ExtSet H S [x, a] L (g β₂)).ncard ≤
      (ColSet H S L f₀).ncard := by
    rw [← Set.ncard_union_eq hdisj (extSet_finite _ _ _ _ _) (extSet_finite _ _ _ _ _)]
    exact Set.ncard_le_ncard (Set.union_subset (hsub β₁ (by simp)) (hsub β₂ (by simp))) hfin
  -- each instance has at least `2^{(|S| - 2)/9}` colourings
  have hnC : nCount S [x, a] + 2 = S.card := by
    unfold nCount
    have : S.filter (· ∉ [x, a]) = (S.erase x).erase a := by
      ext v; simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons, List.not_mem_nil,
        or_false, not_or]; tauto
    rw [this, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxa.symm, haS⟩),
      Finset.card_erase_of_mem hxS]
    have : 2 ≤ S.card := by
      have := Finset.card_le_card (show ({x, a} : Finset V) ⊆ S by
        intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption)
      rwa [Finset.card_pair hxa] at this
    omega
  have hrC : rCount S [x, a] L = 0 := by
    unfold rCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro v hv ⟨-, h3⟩
    have := h5 v hv; omega
  have hB : ∀ β ∈ [β₁, β₂], β ≠ α →
      2 ^ nCount S [x, a] ≤ (ExtSet H S [x, a] L (g β)).ncard ^ 9 := by
    intro β _ hβα
    have hne : (ExtSet H S [x, a] L (g β)).Nonempty := by
      rw [extSet_nonempty_iff]
      obtain ⟨f, hfx, hfa, hfL, hf⟩ := T.thm1 H S.card S rfl x a l hNT L (g β)
        (by rw [hgx, hga]; exact fun e => hβα e.symm)
        (fun v hv => by have := h5 v (T.subset hNT v (by simp [hv])); omega)
        (fun v hv _ => h5 v hv)
      refine ⟨f, fun v hv => ?_, fun v hv hvn => hfL v hv ?_ ?_, hf⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hfx
        · exact hfa
      · intro e; exact hvn (by simp [e])
      · intro e; exact hvn (by simp [e])
    rcases l with _ | ⟨p, l'⟩
    · -- a single edge: `S = {x, a}`, `n = 0`
      have : nCount S [x, a] = 0 := by
        have hS := T.two hNT
        unfold nCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v hv hvn
        rw [hS] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn
        tauto
      rw [this, pow_zero]
      have := (Set.ncard_pos (extSet_finite _ _ _ _ _)).mpr hne
      exact Nat.one_le_pow _ _ this
    · obtain ⟨c, hc⟩ : ∃ c, (a :: p :: l').getLast? = some c :=
        ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
      have hh : Thm4Hyp H S x (a :: p :: l') a c L (g β) false := by
        refine ⟨rfl, hc, by simp, by rw [hgx, hga]; exact fun e => hβα e.symm, by simp,
          by simp, fun y hy _ => ?_, fun y hy _ => h5 y hy⟩
        have := h5 y (T.subset hNT y (by simp at hy ⊢; tauto)); omega
      have hconc := T.thm4 H hNT hh hne (fun h => by simp [Exc4] at h)
      have hpc : pcList false x a c = [x, a] := rfl
      rw [hpc] at hconc
      unfold Bound4 at hconc
      rw [hrC, pow_zero, mul_one] at hconc
      exact hconc
  have h1 := hB β₁ (by simp) hβ₁.1
  have h2 := hB β₂ (by simp) hβ₂.1
  -- `N ≥ N₁ + N₂ ≥ 2 min`, so `N^9 ≥ 2^9 · 2^{|S| - 2}`
  set m := min (ExtSet H S [x, a] L (g β₁)).ncard (ExtSet H S [x, a] L (g β₂)).ncard with hm
  have hmB : 2 ^ nCount S [x, a] ≤ m ^ 9 := by
    rcases min_choice (ExtSet H S [x, a] L (g β₁)).ncard (ExtSet H S [x, a] L (g β₂)).ncard
      with h | h <;> rw [hm, h] <;> assumption
  have h2m : 2 * m ≤ (ColSet H S L f₀).ncard := by
    have := min_le_left (ExtSet H S [x, a] L (g β₁)).ncard (ExtSet H S [x, a] L (g β₂)).ncard
    have := min_le_right (ExtSet H S [x, a] L (g β₁)).ncard (ExtSet H S [x, a] L (g β₂)).ncard
    omega
  rw [← hnC]
  calc 2 ^ (nCount S [x, a] + 2) = 4 * 2 ^ nCount S [x, a] := by ring
    _ ≤ 512 * m ^ 9 := by omega
    _ = (2 * m) ^ 9 := by ring
    _ ≤ (ColSet H S L f₀).ncard ^ 9 := Nat.pow_le_pow_left h2m 9

/-- **Thomassen's corollary** for spanning subgraphs of near-triangulations. -/
theorem many_colourings_sub {G H : SimpleGraph V} (hGH : G ≤ H) {S : Finset V} {x a : V}
    {l : List V} (hNT : T.NT H S (x :: a :: l)) (L : V → Finset C)
    (h5 : ∀ v ∈ S, 5 ≤ (L v).card) (f₀ : V → C) : 2 ^ S.card ≤ (ColSet G S L f₀).ncard ^ 9 :=
  (T.many_colourings H hNT L h5 f₀).trans (Nat.pow_le_pow_left
    (Set.ncard_le_ncard (colSet_mono hGH S L f₀) (extSet_finite _ _ _ _ _)) 9)

end NTCalc

end ThomassenManyColourings
