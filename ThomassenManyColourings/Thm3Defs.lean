/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm2Five

/-!
# Theorem 3: statement and small cases

`G` (that is `H` on `S`) is a near-triangulation with outer cycle `x :: P`, `P = a … c`; the path
`c x a` is precoloured by `g`, the other outer vertices have lists of size at least three and the
interior vertices lists of size at least five. Then the precolouring extends, unless `G` contains a
generalized wheel with principal path `c x a` whose outer vertices lie on the outer cycle of `G`
and have exactly three colours (`Exc3`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The exceptional configuration of Theorem 3. -/
def Exc3 (H : SimpleGraph V) (S : Finset V) (x : V) (P : List V) (a c : V) (L : V → Finset C) :
    Prop :=
  ∃ (P' : List V) (U : Finset V), GW H 2 x P' U ∧ P'.Nodup ∧ P'.head? = some a ∧
    P'.getLast? = some c ∧
    (∀ y ∈ P', y ∈ P) ∧ (∀ u ∈ U, u ∈ S ∧ u ∉ x :: P) ∧
    ∀ y ∈ P', y ≠ a → y ≠ c → (L y).card = 3

/-- The hypotheses of Theorem 3 for the outer cycle `x :: P` with precoloured path `c x a`. -/
structure Thm3Hyp (H : SimpleGraph V) (S : Finset V) (x : V) (P : List V) (a c : V)
    (L : V → Finset C) (g : V → C) : Prop where
  head : P.head? = some a
  last : P.getLast? = some c
  two_le : 2 ≤ P.length
  ok : PathOK H x a c g
  three : ∀ y ∈ P, y ≠ a → y ≠ c → 3 ≤ (L y).card
  five : ∀ y ∈ S, y ∉ x :: P → 5 ≤ (L y).card

namespace NTCalc

variable (T : NTCalc V)

/-- **Theorem 3, triangles.** -/
theorem thm3_three (H : SimpleGraph V) {S : Finset V} {x a c : V} (hNT : T.NT H S [x, a, c])
    (L : V → Finset C) (g : V → C) (hh : Thm3Hyp H S x [a, c] a c L g) :
    Extends H S [c, x, a] L g := by
  have hperm : ∀ y, y ∈ [x, a, c] ↔ y ∈ [c, x, a] := by intro y; simp; tauto
  refine extends_of_mem_iff hperm (T.thm2_three H hNT L g ?_ ?_)
  · intro y hy z hz hyz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy hz
    obtain ⟨hxa, hxc, hac⟩ := hh.ok
    rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
    · exact absurd hyz (H.loopless.irrefl _)
    · exact hxa
    · exact hxc
    · exact hxa.symm
    · exact absurd hyz (H.loopless.irrefl _)
    · exact hac hyz
    · exact hxc.symm
    · exact (hac hyz.symm).symm
    · exact absurd hyz (H.loopless.irrefl _)
  · intro y hy hyc
    exact hh.five y hy (by simpa using hyc)

/-- Colouring one more outer vertex and extending with a known extension. -/
theorem extends_of_update {H : SimpleGraph V} {S : Finset V} {c c' : List V} {L : V → Finset C}
    {g : V → C} {v : V} {col : C} (hcol : col ∈ L v) (hv : v ∉ c) (hvc' : v ∈ c')
    (hc : ∀ y ∈ c', y ∈ c ∨ y = v) (hc' : ∀ y ∈ c, y ∈ c')
    (h : Extends H S c' L (Function.update g v col)) : Extends H S c L g := by
  obtain ⟨f, hf1, hf2, hf3⟩ := h
  refine ⟨f, fun y hy => ?_, fun y hy hyc => ?_, hf3⟩
  · rw [hf1 y (hc' y hy), Function.update_of_ne (fun e => hv (by rw [← e]; exact hy))]
  · by_cases hyv : y = v
    · subst hyv; rw [hf1 y hvc', Function.update_self]; exact hcol
    · exact hf2 y hy (fun h => (hc y h).elim hyc hyv)

/-- Properness after colouring one more vertex. -/
theorem prop_update {H : SimpleGraph V} {l : List V} {g : V → C} {v : V} {col : C}
    (hg : ∀ y ∈ l, y ≠ v → ∀ z ∈ l, z ≠ v → H.Adj y z → g y ≠ g z)
    (hv : ∀ y ∈ l, y ≠ v → H.Adj v y → g y ≠ col) :
    ∀ y ∈ l, ∀ z ∈ l, H.Adj y z → Function.update g v col y ≠ Function.update g v col z := by
  intro y hy z hz hyz
  by_cases hyv : y = v
  · subst hyv
    have hzy : z ≠ y := fun e => H.loopless.irrefl _ (e ▸ hyz)
    rw [Function.update_self, Function.update_of_ne hzy]
    exact (hv z hz hzy hyz).symm
  · by_cases hzv : z = v
    · subst hzv
      rw [Function.update_self, Function.update_of_ne hyv]
      exact hv y hy hyv hyz.symm
    · rw [Function.update_of_ne hyv, Function.update_of_ne hzv]
      exact hg y hy hyv z hz hzv hyz

theorem pathOK_prop {H : SimpleGraph V} {x a c : V} {g : V → C} (h : PathOK H x a c g) :
    ∀ y ∈ [x, a, c], ∀ z ∈ [x, a, c], H.Adj y z → g y ≠ g z := by
  intro y hy z hz hyz
  obtain ⟨hxa, hxc, hac⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy hz
  rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
  · exact absurd hyz (H.loopless.irrefl _)
  · exact hxa
  · exact hxc
  · exact hxa.symm
  · exact absurd hyz (H.loopless.irrefl _)
  · exact hac hyz
  · exact hxc.symm
  · exact (hac hyz.symm).symm
  · exact absurd hyz (H.loopless.irrefl _)

/-- **Theorem 3, quadrilaterals.** -/
theorem thm3_four (H : SimpleGraph V) {S : Finset V} {x a v c : V} (hNT : T.NT H S [x, a, v, c])
    (L : V → Finset C) (g : V → C) (hh : Thm3Hyp H S x [a, v, c] a c L g) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x [a, v, c] a c L := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hxa_ne, hxv_ne, hxc_ne⟩, ⟨hav_ne, hac_ne⟩, hvc_ne, -⟩ := hnd
  have hxa : H.Adj x a := T.adj_cons hNT
  have hav : H.Adj a v := T.adj_cons (by simpa using T.rotate hNT)
  have hvc : H.Adj v c := T.adj_cons (by simpa using T.rotate (T.rotate hNT))
  have hcx : H.Adj c x := T.adj_cons (by simpa using T.rotate (T.rotate (T.rotate hNT)))
  have h3v : 3 ≤ (L v).card := hh.three v (by simp) (Ne.symm hav_ne) hvc_ne
  have hgp := pathOK_prop hh.ok
  have fin : ∀ col ∈ L v, col ≠ g a → col ≠ g c → (H.Adj x v → col ≠ g x) →
      Extends H S [c, x, a] L g := by
    intro col hcol h1 h2 h3
    refine extends_of_update (c' := [x, a, v, c]) hcol
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hvc_ne, fun e => hxv_ne e.symm, fun e => hav_ne e.symm⟩) (by simp)
      (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
      (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto) ?_
    refine T.thm2_four H _ S rfl x a v c hNT L (Function.update g v col) ?_ ?_
    · refine prop_update ?_ ?_
      · intro y hy hyv z hz hzv hyz
        exact hgp y (by simp at hy ⊢; tauto) z (by simp at hz ⊢; tauto) hyz
      · intro y hy hyv hvy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact (h3 hvy.symm).symm
        · exact h1.symm
        · exact absurd rfl hyv
        · exact h2.symm
    · intro y hy hyc
      exact hh.five y hy (by simpa using hyc)
  by_cases hxv : H.Adj x v
  · by_cases hex : ∃ col ∈ L v, col ≠ g x ∧ col ≠ g a ∧ col ≠ g c
    · obtain ⟨col, hcol, h1, h2, h3⟩ := hex
      exact Or.inl (fin col hcol h2 h3 (fun _ => h1))
    · right
      push_neg at hex
      have hsub : L v ⊆ {g x, g a, g c} := by
        intro col hcol
        by_cases h1 : col = g x
        · simp [h1]
        by_cases h2 : col = g a
        · simp [h2]
        simp [hex col hcol h1 h2]
      have hcard : (L v).card = 3 :=
        le_antisymm ((Finset.card_le_card hsub).trans Finset.card_le_three) h3v
      refine ⟨[a, v, c], ∅, ?_, by simp [hav_ne, hac_ne, hvc_ne], rfl, rfl, fun y hy => hy, by simp, ?_⟩
      · have := GW.cons (m := 2) (P := [a]) (b := v) (Q := [c]) (Block.tri hxa hxv hav)
          (GW.one (Block.tri hxv hcx.symm hvc))
        simpa using this
      · intro y hy hya hyc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact absurd rfl hya
        · exact hcard
        · exact absurd rfl hyc
  · obtain ⟨col, hcol, h1, h2⟩ := exists_avoid2 (L v) h3v (g a) (g c)
    exact Or.inl (fin col hcol h1 h2 (fun h => absurd h hxv))

set_option maxHeartbeats 2000000 in
/-- Theorem 3 for pentagons, once colours for `v, w` are chosen. -/
theorem fin5 (H : SimpleGraph V) {S : Finset V} {x a v w c : V}
    (hNT : T.NT H S [x, a, v, w, c]) (L : V → Finset C) (g : V → C)
    (hh : Thm3Hyp H S x [a, v, w, c] a c L g) {cv cw : C} (hcv : cv ∈ L v) (hcw : cw ∈ L w)
    (h1 : cv ≠ g a) (h2 : H.Adj x v → cv ≠ g x) (h3 : H.Adj v c → cv ≠ g c) (h4 : cw ≠ g c)
    (h5 : H.Adj x w → cw ≠ g x) (h6 : H.Adj a w → cw ≠ g a) (h7 : cv ≠ cw)
    (hhub : NoHubExc H S [x, a, v, w, c] L
      (Function.update (Function.update g v cv) w cw)) :
    Extends H S [c, x, a] L g := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hxa, hxv, hxw, hxc⟩, ⟨hav, haw, hac⟩, ⟨hvw, hvc⟩, hwc, -⟩ := hnd
  have hgp := pathOK_prop hh.ok
  have hp1 : ∀ y ∈ [x, a, v, c], ∀ z ∈ [x, a, v, c], H.Adj y z →
      Function.update g v cv y ≠ Function.update g v cv z := by
    refine prop_update ?_ ?_
    · intro y hy hyv z hz hzv hyz
      exact hgp y (by simp at hy ⊢; tauto) z (by simp at hz ⊢; tauto) hyz
    · intro y hy hyv hvy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact (h2 hvy.symm).symm
      · exact h1.symm
      · exact absurd rfl hyv
      · exact (h3 hvy).symm
  have hp2 : ∀ y ∈ [x, a, v, w, c], ∀ z ∈ [x, a, v, w, c], H.Adj y z →
      Function.update (Function.update g v cv) w cw y ≠
        Function.update (Function.update g v cv) w cw z := by
    refine prop_update ?_ ?_
    · intro y hy hyw z hz hzw hyz
      exact hp1 y (by simp at hy ⊢; tauto) z (by simp at hz ⊢; tauto) hyz
    · intro y hy hyw hwy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · rw [Function.update_of_ne hxv]; exact (h5 hwy.symm).symm
      · rw [Function.update_of_ne hav]; exact (h6 hwy.symm).symm
      · rw [Function.update_self]; exact h7
      · exact absurd rfl hyw
      · rw [Function.update_of_ne (Ne.symm hvc)]; exact h4.symm
  have hE := T.thm2_five H _ S rfl x a v w c hNT L _ hp2
    (fun y hy hyc => hh.five y hy (by simpa using hyc)) hhub
  refine extends_of_update (c' := [x, a, v, c]) hcv
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hvc, fun e => hxv e.symm, fun e => hav e.symm⟩) (by simp)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto) ?_
  refine extends_of_update (c' := [x, a, v, w, c]) hcw
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hxw e.symm, fun e => haw e.symm, fun e => hvw e.symm, hwc⟩) (by simp)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto) hE

set_option maxHeartbeats 2000000 in
/-- **Theorem 3, pentagons with the chord `x v`.** -/
theorem thm3_five_xv (H : SimpleGraph V) {S : Finset V} {x a v w c : V}
    (hNT : T.NT H S [x, a, v, w, c]) (L : V → Finset C) (g : V → C)
    (hh : Thm3Hyp H S x [a, v, w, c] a c L g) (hxv : H.Adj x v) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x [a, v, w, c] a c L := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hxa_ne, hxv_ne, hxw_ne, hxc_ne⟩, ⟨hav_ne, haw_ne, hac_ne⟩, ⟨hvw_ne, hvc_ne⟩,
    hwc_ne, -⟩ := hnd
  have r1 : T.NT H S [a, v, w, c, x] := by simpa using T.rotate hNT
  have r2 : T.NT H S [v, w, c, x, a] := by simpa using T.rotate r1
  have r3 : T.NT H S [w, c, x, a, v] := by simpa using T.rotate r2
  have r4 : T.NT H S [c, x, a, v, w] := by simpa using T.rotate r3
  have hxa : H.Adj x a := T.adj_cons hNT
  have hav : H.Adj a v := T.adj_cons r1
  have hvw : H.Adj v w := T.adj_cons r2
  have hwc : H.Adj w c := T.adj_cons r3
  have hcx : H.Adj c x := T.adj_cons r4
  have h3v : 3 ≤ (L v).card := hh.three v (by simp) (Ne.symm hav_ne) hvc_ne
  have h3w : 3 ≤ (L w).card := hh.three w (by simp) (Ne.symm haw_ne) hwc_ne
  -- no hub
  have hnohub : ∀ g' : V → C, NoHubExc H S [x, a, v, w, c] L g' := by
    intro g' u huS hu hall
    exfalso
    exact T.no_chord_of_hub (x := x) (l₁ := [a]) (y := v) (l₂ := [w, c]) (by simpa using hNT)
      (by simp) (by simp) huS (by simpa using hu) (fun z hz => hall z (by simpa using hz)) hxv
  -- `a w` is not an edge
  have haw : ¬ H.Adj a w :=
    T.no_chord_of_crossing (y := a) (l₁ := [v]) (z := w) (l₂ := [c, x]) (by simpa using r1)
      (by simp) (by simp) (p := v) (q := x) (by simp) (by simp) (Or.inl hxv.symm)
  by_cases hxw : H.Adj x w
  · have hvc : ¬ H.Adj v c :=
      T.no_chord_of_crossing (y := v) (l₁ := [w]) (z := c) (l₂ := [x, a]) (by simpa using r2)
        (by simp) (by simp) (p := w) (q := x) (by simp) (by simp) (Or.inl hxw.symm)
    set A := ((L v).erase (g x)).erase (g a) with hA
    have hA1 : 1 ≤ A.card := by
      have h1 := Finset.pred_card_le_card_erase (s := L v) (a := g x)
      have h2 := Finset.pred_card_le_card_erase (s := (L v).erase (g x)) (a := g a)
      rw [← hA] at h2; omega
    have hmemA : ∀ col ∈ A, col ∈ L v ∧ col ≠ g x ∧ col ≠ g a := fun col h =>
      ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h),
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
    -- try a colour `cv ∈ A` and a colour for `w`
    have attempt : ∀ cv ∈ A, (∃ cw ∈ L w, cw ≠ g x ∧ cw ≠ g c ∧ cw ≠ cv) →
        Extends H S [c, x, a] L g := by
      intro cv hcv ⟨cw, hcw, hw1, hw2, hw3⟩
      obtain ⟨hcvL, hcvx, hcva⟩ := hmemA cv hcv
      exact T.fin5 H hNT L g hh hcvL hcw hcva (fun _ => hcvx) (fun h => absurd h hvc) hw2
        (fun _ => hw1) (fun h => absurd h haw) (fun e => hw3 e.symm) (hnohub _)
    by_cases hA2 : 2 ≤ A.card
    · left
      obtain ⟨c1, hc1, c2, hc2, hc12⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      by_contra hne
      have hw1 : ∀ cw ∈ L w, cw = g x ∨ cw = g c ∨ cw = c1 := by
        intro cw hcw
        by_contra h; push_neg at h
        exact hne (attempt c1 hc1 ⟨cw, hcw, h.1, h.2.1, h.2.2⟩)
      have hw2 : ∀ cw ∈ L w, cw = g x ∨ cw = g c ∨ cw = c2 := by
        intro cw hcw
        by_contra h; push_neg at h
        exact hne (attempt c2 hc2 ⟨cw, hcw, h.1, h.2.1, h.2.2⟩)
      have hsub : L w ⊆ {g x, g c} := by
        intro cw hcw
        rcases hw1 cw hcw with h | h | h
        · simp [h]
        · simp [h]
        · rcases hw2 cw hcw with h' | h' | h'
          · simp [h']
          · simp [h']
          · exact absurd (h.symm.trans h') hc12
      have := (Finset.card_le_card hsub).trans Finset.card_le_two
      omega
    · obtain ⟨β, hAβ⟩ := Finset.card_eq_one.mp (by omega : A.card = 1)
      have hβ : β ∈ A := by rw [hAβ]; simp
      by_cases hwex : ∃ cw ∈ L w, cw ≠ g x ∧ cw ≠ g c ∧ cw ≠ β
      · exact Or.inl (attempt β hβ hwex)
      · right
        push_neg at hwex
        have hsubv : L v ⊆ {g x, g a, β} := by
          intro col hcol
          by_cases h1 : col = g x
          · simp [h1]
          by_cases h2 : col = g a
          · simp [h2]
          have : col ∈ A := Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hcol⟩⟩
          rw [hAβ] at this; simp at this; simp [this]
        have hsubw : L w ⊆ {g x, g c, β} := by
          intro col hcol
          by_cases h1 : col = g x
          · simp [h1]
          by_cases h2 : col = g c
          · simp [h2]
          simp [hwex col hcol h1 h2]
        have hcv3 : (L v).card = 3 :=
          le_antisymm ((Finset.card_le_card hsubv).trans Finset.card_le_three) h3v
        have hcw3 : (L w).card = 3 :=
          le_antisymm ((Finset.card_le_card hsubw).trans Finset.card_le_three) h3w
        refine ⟨[a, v, w, c], ∅, ?_, by simp [hav_ne, haw_ne, hac_ne, hvw_ne, hvc_ne, hwc_ne], rfl,
          rfl, fun y hy => hy, by simp, ?_⟩
        · have h1 : GW H 2 x (v :: [w, c]) ∅ := by
            have := GW.cons (m := 2) (P := [v]) (b := w) (Q := [c]) (Block.tri hxv hxw hvw)
              (GW.one (Block.tri hxw hcx.symm hwc))
            simpa using this
          have := GW.cons (m := 2) (P := [a]) (b := v) (Q := [w, c]) (Block.tri hxa hxv hav) h1
          simpa using this
        · intro y hy hya hyc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact absurd rfl hya
          · exact hcv3
          · exact hcw3
          · exact absurd rfl hyc
  · by_cases hvex : ∃ cv ∈ L v, cv ≠ g x ∧ cv ≠ g a ∧ (H.Adj v c → cv ≠ g c)
    · left
      obtain ⟨cv, hcv, h1, h2, h3⟩ := hvex
      obtain ⟨cw, hcw, hw1, hw2⟩ := exists_avoid2 (L w) h3w (g c) cv
      exact T.fin5 H hNT L g hh hcv hcw h2 (fun _ => h1) h3 hw1 (fun h => absurd h hxw)
        (fun h => absurd h haw) (fun e => hw2 e.symm) (hnohub _)
    · right
      push_neg at hvex
      have hvc : H.Adj v c := by
        by_contra hvc
        have hsub : L v ⊆ {g x, g a} := by
          intro col hcol
          by_cases h1 : col = g x
          · simp [h1]
          by_cases h2 : col = g a
          · simp [h2]
          exact absurd (hvex col hcol h1 h2).1 hvc
        have := (Finset.card_le_card hsub).trans Finset.card_le_two
        omega
      have hsubv : L v ⊆ {g x, g a, g c} := by
        intro col hcol
        by_cases h1 : col = g x
        · simp [h1]
        by_cases h2 : col = g a
        · simp [h2]
        simp [(hvex col hcol h1 h2).2]
      have hcv3 : (L v).card = 3 :=
        le_antisymm ((Finset.card_le_card hsubv).trans Finset.card_le_three) h3v
      refine ⟨[a, v, c], ∅, ?_, by simp [hav_ne, hac_ne, hvc_ne], rfl, rfl, by simp, by simp, ?_⟩
      · have := GW.cons (m := 2) (P := [a]) (b := v) (Q := [c]) (Block.tri hxa hxv hav)
          (GW.one (Block.tri hxv hcx.symm hvc))
        simpa using this
      · intro y hy hya hyc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact absurd rfl hya
        · exact hcv3
        · exact absurd rfl hyc

theorem exc3_reverse {H : SimpleGraph V} {S : Finset V} {x a c : V} {P Q : List V}
    {L : V → Finset C} (hPQ : ∀ y, y ∈ Q ↔ y ∈ P) (h : Exc3 H S x Q c a L) :
    Exc3 H S x P a c L := by
  obtain ⟨P', U, hGW, hnd, hh, hl, hsub, hU, hL⟩ := h
  refine ⟨P'.reverse, U, hGW.reverse, List.nodup_reverse.mpr hnd,
    by rw [List.head?_reverse]; exact hl,
    by rw [List.getLast?_reverse]; exact hh, fun y hy => (hPQ y).1 (hsub y (by simpa using hy)),
    fun u hu => ⟨(hU u hu).1, fun h => (hU u hu).2 ?_⟩,
    fun y hy hya hyc => hL y (by simpa using hy) hyc hya⟩
  rcases List.mem_cons.mp h with h | h
  · exact List.mem_cons.mpr (Or.inl h)
  · exact List.mem_cons_of_mem _ ((hPQ u).2 h)

/-- Two vertices joined to the whole pentagon cannot both be interior. -/
theorem hub_unique (H : SimpleGraph V) {S : Finset V} {x a v w c u₁ u₂ : V}
    (hNT : T.NT H S [x, a, v, w, c]) (hu₁S : u₁ ∈ S) (hu₁ : u₁ ∉ [x, a, v, w, c])
    (h₁ : ∀ y ∈ [x, a, v, w, c], H.Adj u₁ y) (hu₂S : u₂ ∈ S) (hu₂ : u₂ ∉ [x, a, v, w, c])
    (h₂ : ∀ y ∈ [x, a, v, w, c], H.Adj u₂ y) : u₁ = u₂ := by
  by_contra hne
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hu₁ hu₂
  obtain ⟨⟨hxa, hxv, hxw, hxc⟩, ⟨hav, haw, hac⟩, ⟨hvw, hvc⟩, hwc, -⟩ := hnd
  obtain ⟨S₁, S₂, hA, hB, hU, hI, hX⟩ :=
    T.cut (x := x) (l₁ := [a]) (y := v) (l₂ := [w, c]) (u := u₁) (by simpa using hNT) hu₁S
      (by simp; tauto) (h₁ x (by simp)) (h₁ v (by simp))
      (T.no_chord_of_hub (x := x) (l₁ := [a]) (y := v) (l₂ := [w, c]) (by simpa using hNT)
        (by simp) (by simp) hu₁S (by simp; tauto) (fun z hz => h₁ z (by simp at hz ⊢; tauto)))
  have hmem : ∀ z, z ∈ S₁ → z ∈ S₂ → z = x ∨ z = v ∨ z = u₁ := by
    intro z hz1 hz2
    have : z ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hz1, hz2⟩
    rw [hI] at this; simpa using this
  have haS₁ : a ∈ S₁ := T.subset hA a (by simp)
  have hwS₂ : w ∈ S₂ := T.subset hB w (by simp)
  have haS₂ : a ∉ S₂ := fun h => by
    rcases hmem a haS₁ h with e | e | e
    · exact hxa e.symm
    · exact hav e
    · exact hu₁.2.1 e.symm
  have hwS₁ : w ∉ S₁ := fun h => by
    rcases hmem w h hwS₂ with e | e | e
    · exact hxw e.symm
    · exact hvw e.symm
    · exact hu₁.2.2.2.1 e.symm
  have hu₂' : u₂ ∈ S₁ ∪ S₂ := hU ▸ hu₂S
  have hnot : ¬ (u₂ = x ∨ u₂ = v ∨ u₂ = u₁) := by
    rintro (e | e | e)
    · exact hu₂.1 e
    · exact hu₂.2.2.1 e
    · exact hne e.symm
  rcases Finset.mem_union.mp hu₂' with h1 | h2
  · rcases hX u₂ h1 w hwS₂ (h₂ w (by simp)) with h | h
    · exact hnot (hmem u₂ h1 h)
    · exact hwS₁ h
  · rcases hX a haS₁ u₂ h2 (h₂ a (by simp)).symm with h | h
    · exact haS₂ h
    · exact hnot (hmem u₂ h h2)

set_option maxHeartbeats 2000000 in
/-- **Theorem 3, pentagons without chords at `x`.** -/
theorem thm3_five_nox (H : SimpleGraph V) {S : Finset V} {x a v w c : V}
    (hNT : T.NT H S [x, a, v, w, c]) (L : V → Finset C) (g : V → C)
    (hh : Thm3Hyp H S x [a, v, w, c] a c L g) (hxv : ¬ H.Adj x v) (hxw : ¬ H.Adj x w) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x [a, v, w, c] a c L := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hxa_ne, hxv_ne, hxw_ne, hxc_ne⟩, ⟨hav_ne, haw_ne, hac_ne⟩, ⟨hvw_ne, hvc_ne⟩,
    hwc_ne, -⟩ := hnd
  have r1 : T.NT H S [a, v, w, c, x] := by simpa using T.rotate hNT
  have r2 : T.NT H S [v, w, c, x, a] := by simpa using T.rotate r1
  have r3 : T.NT H S [w, c, x, a, v] := by simpa using T.rotate r2
  have r4 : T.NT H S [c, x, a, v, w] := by simpa using T.rotate r3
  have hxa : H.Adj x a := T.adj_cons hNT
  have hav : H.Adj a v := T.adj_cons r1
  have hvw : H.Adj v w := T.adj_cons r2
  have hwc : H.Adj w c := T.adj_cons r3
  have hcx : H.Adj c x := T.adj_cons r4
  have h3v : 3 ≤ (L v).card := hh.three v (by simp) (Ne.symm hav_ne) hvc_ne
  have h3w : 3 ≤ (L w).card := hh.three w (by simp) (Ne.symm haw_ne) hwc_ne
  by_cases hhub : ∃ u ∈ S, u ∉ [x, a, v, w, c] ∧ ∀ y ∈ [x, a, v, w, c], H.Adj u y
  · obtain ⟨u, huS, hu, hall⟩ := hhub
    have huniq : ∀ u', u' ∈ S → u' ∉ [x, a, v, w, c] → (∀ y ∈ [x, a, v, w, c], H.Adj u' y) →
        u = u' := fun u' hu'S hu' hall' => T.hub_unique H hNT huS hu hall hu'S hu' hall'
    have haw : ¬ H.Adj a w := T.no_chord_of_hub (x := a) (l₁ := [v]) (y := w) (l₂ := [c, x])
      (by simpa using r1) (by simp) (by simp) huS (by simp at hu ⊢; tauto)
      (fun z hz => hall z (by simp at hz ⊢; tauto))
    have hvc : ¬ H.Adj v c := T.no_chord_of_hub (x := v) (l₁ := [w]) (y := c) (l₂ := [x, a])
      (by simpa using r2) (by simp) (by simp) huS (by simp at hu ⊢; tauto)
      (fun z hz => hall z (by simp at hz ⊢; tauto))
    set D := (L u) \ {g x, g a, g c} with hD
    have hL5 : 5 ≤ (L u).card := hh.five u huS (by simpa using hu)
    have hD2 : 2 ≤ D.card := by
      have := Finset.le_card_sdiff ({g x, g a, g c} : Finset C) (L u)
      have h3 : ({g x, g a, g c} : Finset C).card ≤ 3 := Finset.card_le_three
      rw [← hD] at this; omega
    set Lv := (L v).erase (g a) with hLv
    set Lw := (L w).erase (g c) with hLw
    have hLv2 : 2 ≤ Lv.card := by
      have := Finset.pred_card_le_card_erase (s := L v) (a := g a); rw [← hLv] at this; omega
    have hLw2 : 2 ≤ Lw.card := by
      have := Finset.pred_card_le_card_erase (s := L w) (a := g c); rw [← hLw] at this; omega
    by_cases hgood : ∃ cv ∈ Lv, ∃ cw ∈ Lw, cv ≠ cw ∧ ∃ d ∈ D, d ≠ cv ∧ d ≠ cw
    · left
      obtain ⟨cv, hcv, cw, hcw, hne, d, hd, hd1, hd2⟩ := hgood
      refine T.fin5 H hNT L g hh (Finset.mem_of_mem_erase hcv) (Finset.mem_of_mem_erase hcw)
        (Finset.ne_of_mem_erase hcv) (fun h => absurd h hxv) (fun h => absurd h hvc)
        (Finset.ne_of_mem_erase hcw) (fun h => absurd h hxw) (fun h => absurd h haw) hne ?_
      intro u' hu'S hu' hall'
      obtain rfl := huniq u' hu'S hu' hall'
      rw [hD, Finset.mem_sdiff] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
      refine ⟨d, hd.1, ?_⟩
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · rw [Function.update_of_ne hxw_ne, Function.update_of_ne hxv_ne]; exact fun e => hd.2.1 e.symm
      · rw [Function.update_of_ne haw_ne, Function.update_of_ne hav_ne]
        exact fun e => hd.2.2.1 e.symm
      · rw [Function.update_of_ne hvw_ne, Function.update_self]; exact fun e => hd1 e.symm
      · rw [Function.update_self]; exact fun e => hd2 e.symm
      · rw [Function.update_of_ne (Ne.symm hwc_ne), Function.update_of_ne (Ne.symm hvc_ne)]
        exact fun e => hd.2.2.2 e.symm
    · right
      push_neg at hgood
      have hsubD : ∀ cv ∈ Lv, ∀ cw ∈ Lw, cv ≠ cw → D ⊆ {cv, cw} := by
        intro cv hcv cw hcw hne d hd
        by_contra hdn
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdn
        exact hdn.2 (hgood cv hcv cw hcw hne d hd hdn.1)
      have hother : ∀ (s : Finset C) (col : C), 2 ≤ s.card → ∃ col' ∈ s, col' ≠ col := by
        intro s col hs
        have := Finset.pred_card_le_card_erase (s := s) (a := col)
        obtain ⟨col', hcol'⟩ := Finset.card_pos.mp (by omega : 0 < (s.erase col).card)
        exact ⟨col', Finset.mem_of_mem_erase hcol', Finset.ne_of_mem_erase hcol'⟩
      have hDeq : ∀ cv ∈ Lv, ∀ cw ∈ Lw, cv ≠ cw → D = {cv, cw} := by
        intro cv hcv cw hcw hne
        exact Finset.eq_of_subset_of_card_le (hsubD cv hcv cw hcw hne)
          (by rw [Finset.card_pair hne]; exact hD2)
      have hLvD : Lv ⊆ D := by
        intro cv hcv
        obtain ⟨cw, hcw, hne⟩ := hother Lw cv hLw2
        rw [hDeq cv hcv cw hcw (Ne.symm hne)]; simp
      have hLwD : Lw ⊆ D := by
        intro cw hcw
        obtain ⟨cv, hcv, hne⟩ := hother Lv cw hLv2
        rw [hDeq cv hcv cw hcw hne]; simp
      have hDc : D.card = 2 := by
        obtain ⟨cv, hcv⟩ := Finset.card_pos.mp (by omega : 0 < Lv.card)
        obtain ⟨cw, hcw, hne⟩ := hother Lw cv hLw2
        rw [hDeq cv hcv cw hcw (Ne.symm hne), Finset.card_pair (Ne.symm hne)]
      have hcard : ∀ (s : Finset C) (col : C), 3 ≤ s.card → s.erase col ⊆ D → s.card = 3 := by
        intro s col hs hsub
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.pred_card_le_card_erase (s := s) (a := col)
        omega
      have hcv3 := hcard (L v) (g a) h3v hLvD
      have hcw3 := hcard (L w) (g c) h3w hLwD
      refine ⟨[a, v, w, c], {u}, ?_, by simp [hav_ne, haw_ne, hac_ne, hvw_ne, hvc_ne, hwc_ne],
        rfl, rfl, fun y hy => hy, ?_, ?_⟩
      · refine GW.one (Block.wheel (by simp) (by simp) ?_ (fun y hy => hall y (by simp [hy]))
          (hall x (by simp)) (by simp [hxa]) (by simp [hcx.symm]))
        unfold IsPathL
        simp [hav, hvw, hwc]
      · intro u' hu'
        simp only [Finset.mem_singleton] at hu'; subst hu'
        exact ⟨huS, hu⟩
      · intro y hy hya hyc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact absurd rfl hya
        · exact hcv3
        · exact hcw3
        · exact absurd rfl hyc
  · left
    push_neg at hhub
    have hnohub : ∀ g' : V → C, NoHubExc H S [x, a, v, w, c] L g' := by
      intro g' u huS hu hall
      obtain ⟨y, hy, hny⟩ := hhub u huS hu
      exact absurd (hall y hy) hny
    by_cases haw : H.Adj a w
    · have hvc : ¬ H.Adj v c :=
        T.no_chord_of_crossing (y := v) (l₁ := [w]) (z := c) (l₂ := [x, a]) (by simpa using r2)
          (by simp) (by simp) (p := w) (q := a) (by simp) (by simp) (Or.inl haw.symm)
      obtain ⟨cw, hcw, hw1, hw2⟩ := exists_avoid2 (L w) h3w (g a) (g c)
      obtain ⟨cv, hcv, hv1, hv2⟩ := exists_avoid2 (L v) h3v (g a) cw
      exact T.fin5 H hNT L g hh hcv hcw hv1 (fun h => absurd h hxv) (fun h => absurd h hvc) hw2
        (fun h => absurd h hxw) (fun _ => hw1) hv2 (hnohub _)
    · obtain ⟨cv, hcv, hv1, hv2⟩ := exists_avoid2 (L v) h3v (g a) (g c)
      obtain ⟨cw, hcw, hw1, hw2⟩ := exists_avoid2 (L w) h3w (g c) cv
      exact T.fin5 H hNT L g hh hcv hcw hv1 (fun h => absurd h hxv) (fun _ => hv2) hw1
        (fun h => absurd h hxw) (fun h => absurd h haw) (fun e => hw2 e.symm) (hnohub _)

/-- **Theorem 3, pentagons.** -/
theorem thm3_five (H : SimpleGraph V) {S : Finset V} {x a v w c : V}
    (hNT : T.NT H S [x, a, v, w, c]) (L : V → Finset C) (g : V → C)
    (hh : Thm3Hyp H S x [a, v, w, c] a c L g) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x [a, v, w, c] a c L := by
  by_cases hxv : H.Adj x v
  · exact T.thm3_five_xv H hNT L g hh hxv
  by_cases hxw : H.Adj x w
  · have hNTr : T.NT H S [x, c, w, v, a] := by
      have h1 := T.reverse hNT
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.singleton_append] at h1
      exact T.rotate_back (by simpa using h1)
    have hmem : ∀ y, y ∈ [c, w, v, a] ↔ y ∈ [a, v, w, c] := by intro y; simp; tauto
    have hhr : Thm3Hyp H S x [c, w, v, a] c a L g :=
      ⟨by simp, by simp, by simp, ⟨hh.ok.2.1, hh.ok.1, fun h => (hh.ok.2.2 h.symm).symm⟩,
        fun y hy hyc hya => hh.three y ((hmem y).1 hy) hya hyc,
        fun y hy hyc => hh.five y hy (fun h => hyc (by
          rcases List.mem_cons.mp h with h | h
          · exact List.mem_cons.mpr (Or.inl h)
          · exact List.mem_cons_of_mem _ ((hmem y).2 h)))⟩
    rcases T.thm3_five_xv H hNTr L g hhr hxw with h | h
    · left
      exact extends_of_mem_iff (by intro y; simp; tauto) h
    · right
      exact exc3_reverse hmem h
  · exact T.thm3_five_nox H hNT L g hh hxv hxw

end NTCalc

end ThomassenManyColourings
