/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim9

/-!
# Theorem 4: symmetry

With three precoloured vertices, Theorem 4 is invariant under reversing the outer cycle (swap
`v₂` and `v_k`). Counts only depend on the set of precoloured vertices.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] [DecidableEq C] in
theorem extSet_congr {H : SimpleGraph V} {S : Finset V} {c₀ c₀' : List V} {L : V → Finset C}
    {f₀ : V → C} (h : ∀ v, v ∈ c₀ ↔ v ∈ c₀') : ExtSet H S c₀ L f₀ = ExtSet H S c₀' L f₀ := by
  ext f
  simp only [ExtSet, Set.mem_ofPred_eq, h]

theorem nCount_congr {S : Finset V} {c₀ c₀' : List V} (h : ∀ v, v ∈ c₀ ↔ v ∈ c₀') :
    nCount S c₀ = nCount S c₀' := by
  unfold nCount; congr 1; ext v; simp [h]

omit [DecidableEq C] in
theorem rCount_congr {S : Finset V} {c₀ c₀' : List V} {L : V → Finset C}
    (h : ∀ v, v ∈ c₀ ↔ v ∈ c₀') : rCount S c₀ L = rCount S c₀' L := by
  unfold rCount; congr 1; ext v; simp [h]

omit [DecidableEq V] in
theorem pc3_swap (x a c v : V) : v ∈ pcList true x c a ↔ v ∈ pcList true x a c := by
  simp [pcList]; tauto

/-- Theorem 4's conclusion with three precoloured vertices is symmetric in `v₂, v_k`. -/
theorem thm4concl_swap {H : SimpleGraph V} {S : Finset V} {x a c : V} {L : V → Finset C}
    {g : V → C} (h : Thm4Concl H S x c a L g true) : Thm4Concl H S x a c L g true := by
  intro hne hexc
  rw [extSet_congr (pc3_swap x c a), nCount_congr (pc3_swap x c a),
    rCount_congr (pc3_swap x c a)]
  apply h (by rw [extSet_congr (pc3_swap x a c)]; exact hne)
  rintro ⟨ht, u, hu, hun, h4, huc, hux, hua, hcard⟩
  refine hexc ⟨ht, u, hu, fun h' => hun (by simp at h' ⊢; tauto), h4, hua, hux, huc, ?_⟩
  rw [show ({g c, g x, g a} : Finset C) = {g a, g x, g c} by
    ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
  exact hcard

omit [DecidableEq V] [DecidableEq C] in
theorem Block.card_add_two_le {H : SimpleGraph V} {x : V} {P : List V} {U : Finset V}
    (h : Block H 3 x P U) : U.card + 2 ≤ P.length := by
  cases h with
  | tri => simp
  | wheel _ hm => simp; omega

omit [DecidableEq C] in
/-- A generalized wheel without wheels on triangles has at most `|P| - 2` centres. -/
theorem GW.card_add_two_le {H : SimpleGraph V} {x : V} {P : List V} {U : Finset V}
    (h : GW H 3 x P U) : U.card + 2 ≤ P.length := by
  induction h with
  | one hB => exact hB.card_add_two_le
  | @cons P Q b U U' hB hrest ih =>
    have h1 := hB.card_add_two_le
    have h2 := Finset.card_union_le U U'
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 ih ⊢
    omega

namespace NTCalc

variable (T : NTCalc V)

omit [DecidableEq C] in
/-- Reversing the outer cycle of a three-precoloured instance. -/
theorem thm4hyp_reverse {H : SimpleGraph V} {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} (hNT : T.NT H S (x :: P)) (hh : Thm4Hyp H S x P a c L g true) :
    T.NT H S (x :: P.reverse) ∧ Thm4Hyp H S x P.reverse c a L g true := by
  refine ⟨T.rotate_back (by simpa using T.reverse hNT), ?_⟩
  refine ⟨by rw [List.head?_reverse]; exact hh.last, by rw [List.getLast?_reverse]; exact hh.head,
    by simpa using hh.two_le, fun e => hh.xc rfl e, fun _ => hh.xa,
    fun _ hca => (hh.ac rfl hca.symm).symm, fun y hy hyn => hh.three y (List.mem_reverse.mp hy)
      (fun h => hyn ((pc3_swap x a c y).2 h)), fun y hy hyc => hh.five y hy (fun h => hyc ?_)⟩
  rcases List.mem_cons.mp h with e | h
  · exact e ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_reverse.mpr h)

end NTCalc

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Gluing along a chord at `v₁`**: colour the side of `v₂` (two precoloured vertices), then
extend to the side of `v_k` by Theorem 3 (no exceptional configuration there). -/
theorem thm4_glue_three (H : SimpleGraph V) {S S₁ S₂ : Finset V} {x : V} {P₁ P₂ : List V}
    {a y c : V} {L : V → Finset C} {g : V → C}
    (hNT₁ : T.NT H S₁ (x :: P₁)) (hh₁ : Thm4Hyp H S₁ x P₁ a y L g false)
    (hNT₂ : T.NT H S₂ (x :: P₂)) (hhead₂ : P₂.head? = some y) (hlast₂ : P₂.getLast? = some c)
    (htwo₂ : 2 ≤ P₂.length) (h3₂ : ∀ v ∈ P₂, v ≠ y → v ≠ c → 3 ≤ (L v).card)
    (h5₂ : ∀ v ∈ S₂, v ∉ x :: P₂ → 5 ≤ (L v).card)
    (hU : S₁ ∪ S₂ = S) (hX : ∀ p ∈ S₁, ∀ q ∈ S₂, H.Adj p q → p ∈ S₂ ∨ q ∈ S₁)
    (hI : ∀ z ∈ S₁, z ∈ S₂ → z = x ∨ z = y) (hcS₁ : c ∉ S₁) (haS₂ : a ∉ S₂) (hya : y ≠ a)
    (hxy : H.Adj x y) (hxc : g x ≠ g c) (hyc : ¬ H.Adj y c)
    (hnoE3 : ¬ Exc3 H S₂ x P₂ y c L)
    (hno4 : ∀ u ∈ S₂, u ∉ [c, x, y] → (L u).card = 4 → H.Adj u c → H.Adj u x → H.Adj u y →
      False)
    (hpos₂ : 0 < nCount S₂ [c, x, y])
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hpc : pcList true x a c = [c, x, a] := rfl
  have hpc₁ : pcList false x a y = [x, a] := rfl
  have hpc₂ : pcList true x y c = [c, x, y] := rfl
  intro hne _
  rw [hpc] at hne ⊢
  have hS₁ : S₁ ⊆ S := fun z hz => hU ▸ Finset.mem_union_left _ hz
  have hS₂ : S₂ ⊆ S := fun z hz => hU ▸ Finset.mem_union_right _ hz
  have hxS₁ : x ∈ S₁ := T.subset hNT₁ x (by simp)
  have hyS₁ : y ∈ S₁ := T.subset hNT₁ y (List.mem_cons_of_mem _
    (List.mem_of_mem_getLast? hh₁.last))
  have haS₁ : a ∈ S₁ := T.subset hNT₁ a (List.mem_cons_of_mem _
    (List.mem_of_mem_head? hh₁.head))
  have hcS₂ : c ∈ S₂ := T.subset hNT₂ c (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hlast₂))
  have hxa : x ≠ a := fun e => hh₁.xa (by rw [e])
  have hxy' : x ≠ y := fun e => H.loopless.irrefl _ (e ▸ hxy)
  -- counts split
  have hsplit : ∀ q : V → Prop, [DecidablePred q] →
      (S.filter (fun v => v ∉ [c, x, a] ∧ q v)).card =
        (S₁.filter (fun v => v ∉ [x, a] ∧ q v)).card +
          (S₂.filter (fun v => v ∉ [c, x, y] ∧ q v)).card := by
    intro q _
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_union, List.mem_cons, List.not_mem_nil, or_false,
        not_or]
      constructor
      · rintro ⟨hv, ⟨hvc, hvx, hva⟩, hq⟩
        by_cases h1 : v ∈ S₁
        · exact Or.inl ⟨h1, ⟨hvx, hva⟩, hq⟩
        · have h2 : v ∈ S₂ := (Finset.mem_union.mp (hU ▸ hv)).resolve_left h1
          exact Or.inr ⟨h2, ⟨hvc, hvx, fun e => h1 (e ▸ hyS₁)⟩, hq⟩
      · rintro (⟨h1, ⟨hvx, hva⟩, hq⟩ | ⟨h2, ⟨hvc, hvx, hvy⟩, hq⟩)
        · exact ⟨hS₁ h1, ⟨fun e => hcS₁ (e ▸ h1), hvx, hva⟩, hq⟩
        · exact ⟨hS₂ h2, ⟨hvc, hvx, fun e => haS₂ (e ▸ h2)⟩, hq⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
      rcases hI v h1.1 h2.1 with e | e
      · exact h2.2.1.2.1 e
      · exact h2.2.1.2.2 e
  have hn : nCount S [c, x, a] = nCount S₁ [x, a] + nCount S₂ [c, x, y] := by
    have := hsplit (fun _ => True)
    simp only [and_true] at this
    exact this
  have hr : rCount S [c, x, a] L = rCount S₁ [x, a] L + rCount S₂ [c, x, y] L := by
    unfold rCount; exact hsplit (fun v => (L v).card = 3)
  have hn₁pos : 0 < nCount S₁ [x, a] := by
    unfold nCount
    refine Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyS₁, ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hxy' e.symm, hya⟩
  -- the side of `v₂`
  have hne₁ : (ExtSet H S₁ [x, a] L g).Nonempty := by
    obtain ⟨f, h1, h2, h3⟩ := extSet_nonempty_iff.mp hne
    exact extSet_nonempty_iff.mpr ⟨f, fun v hv => h1 v (List.mem_cons_of_mem _ hv),
      fun v hv hvn => h2 v (hS₁ hv) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn ⊢
        exact ⟨fun e => hcS₁ (e ▸ hv), hvn⟩),
      fun p hp q hq hpq => h3 p (hS₁ hp) q (hS₁ hq) hpq⟩
  have hB1 := ih H S₁ x P₁ a y L g false hNT₁ hh₁ (by
    left; rw [hpc₁, hpc, hn]; omega) (by rw [hpc₁]; exact hne₁) (fun h => by simp [Exc4] at h)
  rw [hpc₁] at hB1
  -- extensions to the side of `v_k`
  set n₂ := nCount S₂ [c, x, y]
  set r₂ := rCount S₂ [c, x, y] L
  have hM : ∀ f₁ ∈ ExtSet H S₁ [x, a] L g, minM8 n₂ r₂ ≤ (ExtSet H S₂ [c, x, y] L f₁).ncard := by
    intro f₁ hf₁
    apply minM8_le
    have hf₁c : f₁ c = g c := hf₁.1 c (Or.inl hcS₁)
    have hf₁x : f₁ x = g x := hf₁.1 x (Or.inr (by simp))
    have hh₂ : Thm4Hyp H S₂ x P₂ y c L f₁ true := by
      refine ⟨hhead₂, hlast₂, htwo₂, hf₁.2.2 x hxS₁ y hyS₁ hxy, fun _ => by rw [hf₁x, hf₁c]; exact hxc,
        fun _ h => absurd h hyc, fun v hv hvn => h3₂ v hv (fun e => hvn (by simp [hpc₂, e]))
          (fun e => hvn (by simp [hpc₂, e])), h5₂⟩
    have hh3 : Thm3Hyp H S₂ x P₂ y c L f₁ :=
      ⟨hhead₂, hlast₂, htwo₂, ⟨hh₂.xa, hh₂.xc rfl, fun h => absurd h hyc⟩,
        fun v hv hvy hvc => h3₂ v hv hvy hvc, h5₂⟩
    have hne₂ : (ExtSet H S₂ [c, x, y] L f₁).Nonempty := by
      rcases T.thm3 H hNT₂ hh3 with h | h
      · exact extSet_nonempty_iff.mpr h
      · exact absurd h hnoE3
    have := ih H S₂ x P₂ y c L f₁ true hNT₂ hh₂ (by left; rw [hpc₂, hpc, hn]; omega)
      (by rw [hpc₂]; exact hne₂)
      (by
        rintro ⟨-, u, hu, hun, h4, huc, hux, huy, -⟩
        exact hno4 u hu hun h4 huc hux huy)
    rwa [hpc₂] at this
  have hglue := ncard_extSet_glue (H := H) (S := S) (S₁ := S₁) (S₂ := S₂) (c := [c, x, a])
    (c₁ := [x, a]) (c₂ := [c, x, y]) (L := L) (f₀ := g) (minM8 n₂ r₂) hU hX
    (fun z h1 h2 => by rcases hI z h1 h2 with e | e <;> simp [e])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨fun h => absurd h hcS₁, fun _ => by simp⟩
      · exact ⟨fun _ => by simp, fun _ => by simp⟩
      · exact ⟨fun _ => by simp, fun h => absurd h haS₂⟩)
    (fun z hz hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h | h
      · simp [h]
      · rw [h] at hn; exact absurd hxS₁ hn
      · rw [h] at hn; exact absurd hyS₁ hn)
    (fun z hz _ hzc => absurd (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto) hzc) hM
  rw [hn, hr]
  exact bound4_mono (bound4_mul hB1 (minM8_spec n₂ r₂)) hglue

end NTCalc

end ThomassenManyColourings
