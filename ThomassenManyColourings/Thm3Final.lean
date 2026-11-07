/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Claim7

/-!
# Theorem 3: the final step

Helpers: gluing extensions along a separation, and Claims 5/6 in the form "an interior vertex
joined to three consecutive outer vertices at an end of the path".
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] [DecidableEq C] in
/-- Extensions only depend on the precolouring on the cycle. -/
theorem extends_congr {H : SimpleGraph V} {S : Finset V} {c : List V} {L : V → Finset C}
    {f₀ f₀' : V → C} (h : ∀ z ∈ c, f₀ z = f₀' z) (he : Extends H S c L f₀) :
    Extends H S c L f₀' := by
  obtain ⟨f, h1, h2, h3⟩ := he
  exact ⟨f, fun z hz => (h1 z hz).trans (h z hz), h2, h3⟩

/-- Gluing two extensions of the same precolouring along a separation. -/
theorem extends_glue {H : SimpleGraph V} {S S₁ S₂ : Finset V} {c c₁ c₂ : List V}
    {L : V → Finset C} {f₀ : V → C} (hU : S₁ ∪ S₂ = S)
    (hX : ∀ p ∈ S₁, ∀ q ∈ S₂, H.Adj p q → p ∈ S₂ ∨ q ∈ S₁)
    (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ c₁ ∧ z ∈ c₂)
    (hc : ∀ z ∈ c, (z ∈ S₁ → z ∈ c₁) ∧ (z ∈ S₂ → z ∈ c₂)) (hcS : ∀ z ∈ c, z ∈ S)
    (hl₁ : ∀ z ∈ c₁, z ∉ c → f₀ z ∈ L z) (hl₂ : ∀ z ∈ c₂, z ∉ c → f₀ z ∈ L z)
    (h₁ : Extends H S₁ c₁ L f₀) (h₂ : Extends H S₂ c₂ L f₀) : Extends H S c L f₀ := by
  classical
  obtain ⟨f₁, a1, b1, p1⟩ := h₁
  obtain ⟨f₂, a2, b2, p2⟩ := h₂
  have hside : ∀ z ∈ S, z ∉ S₁ → z ∈ S₂ := fun z hz h1 =>
    (Finset.mem_union.mp (hU ▸ hz)).resolve_left h1
  refine ⟨fun z => if z ∈ S₁ then f₁ z else f₂ z, ?_, ?_, ?_⟩
  · intro z hz
    by_cases h1 : z ∈ S₁
    · simp only [h1, ite_true]; exact a1 z ((hc z hz).1 h1)
    · simp only [h1, ite_false]; exact a2 z ((hc z hz).2 (hside z (hcS z hz) h1))
  · intro z hz hzc
    by_cases h1 : z ∈ S₁
    · simp only [h1, ite_true]
      by_cases hz1 : z ∈ c₁
      · rw [a1 z hz1]; exact hl₁ z hz1 hzc
      · exact b1 z h1 hz1
    · simp only [h1, ite_false]
      have h2 := hside z hz h1
      by_cases hz2 : z ∈ c₂
      · rw [a2 z hz2]; exact hl₂ z hz2 hzc
      · exact b2 z h2 hz2
  · refine isProperOn_glue hU hX p1 p2 (fun z h1 h2 => ?_)
    rw [a2 z (hI z h1 h2).2, a1 z (hI z h1 h2).1]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Claim 6 with a centre**: an interior vertex joined to `v_{k-2}, v_{k-1}, v_k` leaves
`v_{k-1}` of degree three (no separating triangles), so Claim 6 applies. -/
theorem claim6_of_centre (H : SimpleGraph V) {S : Finset V} {x a w₄ w₃ c z0 : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: (M ++ [w₄, w₃, c])))
    (hh : Thm3Hyp H S x (a :: (M ++ [w₄, w₃, c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: (M ++ [w₄, w₃, c]) → z ∈ a :: (M ++ [w₄, w₃, c]) →
      H.Adj y z → ConsecIn (a :: (M ++ [w₄, w₃, c])) y z)
    (hxc : ∀ y ∈ a :: (M ++ [w₄, w₃, c]), H.Adj x y → y = a ∨ y = c)
    (hN : T.NoSepTri H S (x :: a :: (M ++ [w₄, w₃, c])))
    (ih : T.Thm3Below S.card C)
    (hz0S : z0 ∈ S) (hz0n : z0 ∉ x :: a :: (M ++ [w₄, w₃, c]))
    (hz0w₄ : H.Adj z0 w₄) (hz0w₃ : H.Adj z0 w₃) (hz0c : H.Adj z0 c) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: (M ++ [w₄, w₃, c])) a c L := by
  classical
  have hPnd : (a :: (M ++ [w₄, w₃, c])).Nodup := (List.nodup_cons.mp (T.nodup hNT)).2
  have hw₃P : w₃ ∈ a :: (M ++ [w₄, w₃, c]) := by simp
  have hrot4 : T.NT H S (w₄ :: ([w₃] ++ c :: (x :: a :: M))) := by
    have := T.rotate_append (A := x :: a :: M) (B := [w₄, w₃, c]) (by simpa using hNT)
    simpa using this
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := w₄) (y := c) (u := z0) (l₁ := [w₃])
    (l₂ := x :: a :: M) hrot4 hz0S
    (by
      intro h; apply hz0n
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto)
    hz0w₄ hz0c (fun h => ConsecIn.not_gap (A := a :: M) (M := [w₃]) (B := []) (by simp)
      (by simpa using hPnd) (by simpa using hPc w₄ c (by simp) (by simp) h))
  have hmem1 : ∀ v, v ∈ S₁ → v ∈ S₂ → v = w₄ ∨ v = c ∨ v = z0 := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hR1 : Region H S (x :: a :: (M ++ [w₄, w₃, c])) S₁ [w₄, w₃, c, z0] := by
    refine (Region.refl H S _).piece (c₂ := c :: (x :: a :: M ++ [w₄, z0])) hU ?_ hX ?_
      (fun v hv => T.subset h₂ v hv)
    · intro v h1 h2; rcases hmem1 v h1 h2 with e | e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hS1r : T.NT H S₁ (z0 :: ([w₄] ++ w₃ :: [c])) := T.rotate_back (by simpa using h₁)
  obtain ⟨T₁, T₂, ht₁, ht₂, hUT, hIT, hXT⟩ := T.chord hS1r (by simp) (by simp) hz0w₃
  have hmemT : ∀ v, v ∈ T₁ → v ∈ T₂ → v = z0 ∨ v = w₃ := by
    intro v h1 h2
    have : v ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hIT] at this; simpa using this
  have hRT₁ : Region H S (x :: a :: (M ++ [w₄, w₃, c])) T₁ [z0, w₄, w₃] := by
    refine hR1.piece (c₂ := [w₃, c, z0]) hUT ?_ hXT ?_
      (fun v hv => T.subset ht₂ v (by simpa using hv))
    · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hRT₂ : Region H S (x :: a :: (M ++ [w₄, w₃, c])) T₂ [w₃, c, z0] := by
    refine hR1.piece' (c₁ := [z0, w₄, w₃]) hUT ?_ hXT ?_
      (fun v hv => T.subset ht₁ v (by simpa using hv))
    · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hF₁ := hN T₁ z0 w₄ w₃ (by simpa using ht₁) hRT₁
  have hF₂ := hN T₂ w₃ c z0 (by simpa using ht₂) hRT₂
  have hw₃S₁ : w₃ ∈ S₁ := T.subset h₁ w₃ (by simp)
  have hw₃S₂ : w₃ ∉ S₂ := by
    intro h
    rcases hmem1 w₃ hw₃S₁ h with e | e | e
    · have := (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.1
      rw [e] at this; simp at this
    · have := (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.1
      rw [e] at this; simp at this
    · exact hz0n (e ▸ List.mem_cons_of_mem _ hw₃P)
  have hdeg : ∀ z ∈ S, H.Adj w₃ z → z = c ∨ z = w₄ ∨ z = z0 := by
    intro z hz hwz
    have hzS₁ : z ∈ S₁ := by
      by_contra hn
      have hz2 : z ∈ S₂ := (Finset.mem_union.mp (hU ▸ hz)).resolve_left hn
      rcases hX w₃ hw₃S₁ z hz2 hwz with h | h
      · exact hw₃S₂ h
      · exact hn h
    rcases Finset.mem_union.mp (hUT ▸ hzS₁) with h | h
    · rcases hF₁ z h with e | e | e
      · exact Or.inr (Or.inr e)
      · exact Or.inr (Or.inl e)
      · rw [e] at hwz; exact absurd hwz (H.loopless.irrefl _)
    · rcases hF₂ z h with e | e | e
      · rw [e] at hwz; exact absurd hwz (H.loopless.irrefl _)
      · exact Or.inl e
      · exact Or.inr (Or.inr e)
  exact T.claim6 H (u := z0) hNT hh hPc hxc hdeg hN ih

/-- **Claim 5 with a centre** (mirror image): an interior vertex joined to `v₂, v₃, v₄`. -/
theorem claim5_of_centre (H : SimpleGraph V) {S : Finset V} {x a v₃ v₄ c z0 : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: v₃ :: v₄ :: (M ++ [c])))
    (hh : Thm3Hyp H S x (a :: v₃ :: v₄ :: (M ++ [c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: v₃ :: v₄ :: (M ++ [c]) → z ∈ a :: v₃ :: v₄ :: (M ++ [c]) →
      H.Adj y z → ConsecIn (a :: v₃ :: v₄ :: (M ++ [c])) y z)
    (hxc : ∀ y ∈ a :: v₃ :: v₄ :: (M ++ [c]), H.Adj x y → y = a ∨ y = c)
    (hN : T.NoSepTri H S (x :: a :: v₃ :: v₄ :: (M ++ [c])))
    (ih : T.Thm3Below S.card C)
    (hz0S : z0 ∈ S) (hz0n : z0 ∉ x :: a :: v₃ :: v₄ :: (M ++ [c]))
    (hz0a : H.Adj z0 a) (hz0v₃ : H.Adj z0 v₃) (hz0v₄ : H.Adj z0 v₄) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: v₃ :: v₄ :: (M ++ [c])) a c L := by
  have hrev : (a :: v₃ :: v₄ :: (M ++ [c])).reverse = c :: (M.reverse ++ [v₄, v₃, a]) := by simp
  have hmem : ∀ y, y ∈ c :: (M.reverse ++ [v₄, v₃, a]) ↔ y ∈ a :: v₃ :: v₄ :: (M ++ [c]) := by
    intro y; rw [← hrev, List.mem_reverse]
  have hNT' : T.NT H S (x :: c :: (M.reverse ++ [v₄, v₃, a])) := by
    rw [← hrev]
    exact T.rotate_back (by simpa using T.reverse hNT)
  have hh' : Thm3Hyp H S x (c :: (M.reverse ++ [v₄, v₃, a])) c a L g := by
    refine ⟨rfl, by simpa using getLast?_cons_append_singleton c a (M.reverse ++ [v₄, v₃]),
      by simp, ⟨hh.ok.2.1, hh.ok.1, fun h => (hh.ok.2.2 h.symm).symm⟩, ?_, ?_⟩
    · intro y hy hyc hya
      exact hh.three y ((hmem y).1 hy) hya hyc
    · intro y hy hyc
      exact hh.five y hy (fun h => hyc (by
        rcases List.mem_cons.mp h with e | h
        · exact e ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((hmem y).2 h)))
  have hcyc : ∀ v, v ∈ x :: a :: v₃ :: v₄ :: (M ++ [c]) ↔
      v ∈ x :: c :: (M.reverse ++ [v₄, v₃, a]) := by
    intro v
    simp only [List.mem_cons (b := x)]
    rw [hmem v]
  rcases T.claim6_of_centre H hNT' hh'
    (by
      intro y z hy hz hyz
      rw [← hrev]
      exact (hPc y z ((hmem y).1 hy) ((hmem z).1 hz) hyz).reverse)
    (fun y hy hxy => (hxc y ((hmem y).1 hy) hxy).symm)
    (T.noSepTri_congr hcyc hN) ih hz0S (fun h => hz0n ((hcyc z0).2 h)) hz0v₄ hz0v₃ hz0a
    with h | h
  · exact Or.inl (extends_of_mem_iff (fun v => by simp; tauto) h)
  · exact Or.inr (exc3_reverse hmem h)

set_option maxHeartbeats 32000000 in
/-- **The final configuration is colourable**: a hub `u` over `v₃ … v_{k-1}` and a vertex `w`
joined to `u, v_{k-1}, v_k, v₁`. Colour the skeleton, then extend into the quadrilateral
`u v_{k-1} v_k w`, the triangle `w v_k v₁` and the pentagon `v₁ v₂ v₃ u w` (Theorem 2; if the
pentagon has a hub `h`, cut it along `v₂ h u` and colour as in the paper). -/
theorem final_colour (H : SimpleGraph V) {S : Finset V} {x a v₃ w₄ w₃ c u w : V} {R : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])))
    (hh : Thm3Hyp H S x (a :: v₃ :: (R ++ [w₄, w₃, c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) → z ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) →
      H.Adj y z → ConsecIn (a :: v₃ :: (R ++ [w₄, w₃, c])) y z)
    (hxc : ∀ y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]), H.Adj x y → y = a ∨ y = c)
    (hN : T.NoSepTri H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])))
    (huS : u ∈ S) (hu : u ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]))
    (hwS : w ∈ S) (hw : w ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c])) (hwu : w ≠ u)
    (hub : ∀ y ∈ v₃ :: (R ++ [w₄, w₃]), H.Adj u y)
    (hwu' : H.Adj w u) (hwc : H.Adj w c) (hwx : H.Adj w x)
    (hnuc : ¬ H.Adj u c) (hnua : ¬ H.Adj u a) (hnwa : ¬ H.Adj w a) (hnwv₃ : ¬ H.Adj w v₃) :
    Extends H S [c, x, a] L g := by
  classical
  -- repetition-freeness
  have hnd := T.nodup hNT
  have hPnd : (a :: v₃ :: (R ++ [w₄, w₃, c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: v₃ :: (R ++ [w₄, w₃, c]) := (List.nodup_cons.mp hnd).1
  have hPnd' : ((a :: v₃ :: (R ++ [w₄])) ++ [w₃, c]).Nodup := by simpa using hPnd
  obtain ⟨hA, hB, hAB⟩ := List.nodup_append.mp hPnd'
  have haQ : a ∉ v₃ :: (R ++ [w₄]) := (List.nodup_cons.mp hA).1
  have hv₃Q : v₃ ∉ R ++ [w₄] := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).1
  have hQnd : (R ++ [w₄]).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).2
  have hw₃c : w₃ ≠ c := by intro e; rw [e] at hB; simp at hB
  have hdis : ∀ p ∈ a :: v₃ :: (R ++ [w₄]), p ≠ w₃ ∧ p ≠ c := fun p hp =>
    ⟨hAB p hp w₃ (by simp), hAB p hp c (by simp)⟩
  have hav₃ : a ≠ v₃ := fun e => haQ (by simp [e])
  have haw₃ := (hdis a (by simp)).1
  have hac := (hdis a (by simp)).2
  have hv₃w₃ := (hdis v₃ (by simp)).1
  have hv₃c := (hdis v₃ (by simp)).2
  have hQw₃ : ∀ y ∈ R ++ [w₄], y ≠ w₃ := fun y hy =>
    (hdis y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))).1
  have hQc : ∀ y ∈ R ++ [w₄], y ≠ c := fun y hy =>
    (hdis y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))).2
  have hQP : ∀ y ∈ R ++ [w₄], y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := fun y hy => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto
  have hQa : ∀ y ∈ R ++ [w₄], y ≠ a := fun y hy e => haQ (e ▸ List.mem_cons_of_mem _ hy)
  have hQv₃ : ∀ y ∈ R ++ [w₄], y ≠ v₃ := fun y hy e => hv₃Q (e ▸ hy)
  have hxa : x ≠ a := fun e => hxP (by simp [e])
  have hxv₃ : x ≠ v₃ := fun e => hxP (by simp [e])
  have hxw₃ : x ≠ w₃ := fun e => hxP (by simp [e])
  have hxc' : x ≠ c := fun e => hxP (by simp [e])
  have hxQ : ∀ y ∈ R ++ [w₄], y ≠ x := fun y hy e => hxP (e ▸ hQP y hy)
  have hux : u ≠ x := fun e => hu (by simp [e])
  have hua : u ≠ a := fun e => hu (by simp [e])
  have huv₃ : u ≠ v₃ := fun e => hu (by simp [e])
  have huw₃ : u ≠ w₃ := fun e => hu (by simp [e])
  have huc : u ≠ c := fun e => hu (by simp [e])
  have huQ : ∀ y ∈ R ++ [w₄], y ≠ u := fun y hy e => hu (e ▸ List.mem_cons_of_mem _ (hQP y hy))
  have hwxn : w ≠ x := fun e => hw (by simp [e])
  have hwa : w ≠ a := fun e => hw (by simp [e])
  have hwv₃ : w ≠ v₃ := fun e => hw (by simp [e])
  have hww₃' : w ≠ w₃ := fun e => hw (by simp [e])
  have hwc' : w ≠ c := fun e => hw (by simp [e])
  have hwQ : ∀ y ∈ R ++ [w₄], y ≠ w := fun y hy e => hw (e ▸ List.mem_cons_of_mem _ (hQP y hy))
  -- cut A along `v₃ u w₃`
  have hrotA : T.NT H S (v₃ :: ((R ++ [w₄]) ++ w₃ :: [c, x, a])) := by
    have := T.rotate_append (A := [x, a]) (B := v₃ :: (R ++ [w₄, w₃, c])) (by simpa using hNT)
    simpa using this
  obtain ⟨Fu, D, hF, hD, hUA, hIA, hXA⟩ := T.cut (x := v₃) (y := w₃) (u := u)
    (l₁ := R ++ [w₄]) (l₂ := [c, x, a]) hrotA huS
    (by
      intro h; apply hu
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto)
    (hub v₃ (by simp)) (hub w₃ (by simp))
    (fun h => ConsecIn.not_gap (A := [a]) (M := R ++ [w₄]) (B := [c]) (by simp)
      (by simpa using hPnd) (by simpa using hPc v₃ w₃ (by simp) (by simp) h))
  have hmemA : ∀ v, v ∈ Fu → v ∈ D → v = v₃ ∨ v = w₃ ∨ v = u := by
    intro v h1 h2
    have : v ∈ Fu ∩ D := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hIA] at this; simpa using this
  have hD' : T.NT H D [w₃, c, x, a, v₃, u] := by simpa using hD
  have hF' : T.NT H Fu (u :: (v₃ :: (R ++ [w₄, w₃]))) := T.rotate_back (by simpa using hF)
  have hRF : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) Fu (u :: (v₃ :: (R ++ [w₄, w₃]))) := by
    refine (Region.refl H S _).piece (c₂ := [w₃, c, x, a, v₃, u]) hUA ?_ hXA ?_
      (fun v hv => T.subset hD' v hv)
    · intro v h1 h2; rcases hmemA v h1 h2 with e | e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hRD : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) D [w₃, c, x, a, v₃, u] := by
    refine (Region.refl H S _).piece' (c₁ := u :: (v₃ :: (R ++ [w₄, w₃]))) hUA ?_ hXA ?_
      (fun v hv => T.subset hF' v hv)
    · intro v h1 h2; rcases hmemA v h1 h2 with e | e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hfillF := fan_fill hN u _ (v₃ :: (R ++ [w₄, w₃])) Fu rfl hF' hRF
    (List.IsChain.tail (NT_chain hF')) hub
  have hwD : w ∈ D := by
    rcases Finset.mem_union.mp (hUA ▸ hwS) with h | h
    · rcases hfillF w h with e | e
      · exact absurd e hwu
      · exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at e ⊢
          tauto))) hw
    · exact h
  -- cut B along `u w c`
  have hrotB : T.NT H D (u :: ([w₃] ++ c :: [x, a, v₃])) := T.rotate_back (by simpa using hD')
  obtain ⟨D1, D2, h1, h2, hUB, hIB, hXB⟩ := T.cut (x := u) (y := c) (u := w) (l₁ := [w₃])
    (l₂ := [x, a, v₃]) hrotB hwD
    (by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
      exact ⟨hwu, hww₃', hwc', hwxn, hwa, hwv₃⟩)
    hwu' hwc hnuc
  have hmemB : ∀ v, v ∈ D1 → v ∈ D2 → v = u ∨ v = c ∨ v = w := by
    intro v h1 h2
    have : v ∈ D1 ∩ D2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hIB] at this; simpa using this
  have h1' : T.NT H D1 [u, w₃, c, w] := by simpa using h1
  have h2' : T.NT H D2 [c, x, a, v₃, u, w] := by simpa using h2
  have hR1 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) D1 [u, w₃, c, w] := by
    refine hRD.piece (c₂ := [c, x, a, v₃, u, w]) hUB ?_ hXB ?_ (fun v hv => T.subset h2' v hv)
    · intro v h1 h2; rcases hmemB v h1 h2 with e | e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hR2 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) D2 [c, x, a, v₃, u, w] := by
    refine hRD.piece' (c₁ := [u, w₃, c, w]) hUB ?_ hXB ?_ (fun v hv => T.subset h1' v hv)
    · intro v h1 h2; rcases hmemB v h1 h2 with e | e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  -- chord C: `x w`
  have hrotC : T.NT H D2 (x :: ([a, v₃, u] ++ w :: [c])) := by simpa using T.rotate h2'
  obtain ⟨D3, D4, h3, h4, hUC, hIC, hXC⟩ := T.chord hrotC (by simp) (by simp) hwx.symm
  have hmemC : ∀ v, v ∈ D3 → v ∈ D4 → v = x ∨ v = w := by
    intro v h1 h2
    have : v ∈ D3 ∩ D4 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hIC] at this; simpa using this
  have h3' : T.NT H D3 [x, a, v₃, u, w] := by simpa using h3
  have h4' : T.NT H D4 [w, c, x] := by simpa using h4
  have hR3 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) D3 [x, a, v₃, u, w] := by
    refine hR2.piece (c₂ := [w, c, x]) hUC ?_ hXC ?_ (fun v hv => T.subset h4' v hv)
    · intro v h1 h2; rcases hmemC v h1 h2 with e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hR4 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) D4 [w, c, x] := by
    refine hR2.piece' (c₁ := [x, a, v₃, u, w]) hUC ?_ hXC ?_ (fun v hv => T.subset h3' v hv)
    · intro v h1 h2; rcases hmemC v h1 h2 with e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  -- interior vertices of the pieces have five colours
  have h5of : ∀ (D' : Finset V) (c' : List V),
      Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) D' c' →
      ∀ z ∈ D', z ∉ c' → 5 ≤ (L z).card := fun D' c' hR z hz hzc =>
    hh.five z (hR.1 hz) (hR.2 z hz hzc).1
  -- the skeleton colouring
  let skel : C → C → C → C → (V → C) → V → C := fun β γ ε δ φ z =>
    if z = u then β else if z = w then γ else if z = w₃ then ε else if z = v₃ then δ
    else if z ∈ R ++ [w₄] then φ z else g z
  have hxQ' : x ∉ R ++ [w₄] := fun h => hxQ x h rfl
  have haQ' : a ∉ R ++ [w₄] := fun h => hQa a h rfl
  have hcQ' : c ∉ R ++ [w₄] := fun h => hQc c h rfl
  have hw₃Q' : w₃ ∉ R ++ [w₄] := fun h => hQw₃ w₃ h rfl
  have hchordQ : ∀ y z, y ∈ v₃ :: (R ++ [w₄, w₃]) → z ∈ v₃ :: (R ++ [w₄, w₃]) → H.Adj y z →
      ConsecIn (v₃ :: (R ++ [w₄, w₃])) y z := by
    have eP : a :: v₃ :: (R ++ [w₄, w₃, c]) = [a] ++ (v₃ :: (R ++ [w₄, w₃])) ++ [c] := by simp
    intro y z hy hz hyz
    have hy' : y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
      rw [eP]; exact List.mem_append_left _ (List.mem_append_right _ hy)
    have hz' : z ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
      rw [eP]; exact List.mem_append_left _ (List.mem_append_right _ hz)
    have h := hPc y z hy' hz' hyz
    rw [eP] at h
    exact ConsecIn.infix (by rw [← eP]; exact hPnd) hy hz h
  obtain ⟨v₄, rest, hv₄⟩ : ∃ v₄ rest, R ++ [w₄] = v₄ :: rest :=
    List.exists_cons_of_ne_nil (by simp)
  have hcQp : c ∉ v₃ :: (R ++ [w₄, w₃]) := by
    intro h
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
    rcases h with e | e | e | e
    · exact hv₃c e.symm
    · exact hcQ' (List.mem_append_left _ e)
    · exact hcQ' (by simp [e])
    · exact hw₃c e.symm
  have hxQp : x ∉ v₃ :: (R ++ [w₄, w₃]) := fun h => hxP (by
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto)
  have haQp : a ∉ v₃ :: (R ++ [w₄, w₃]) := by
    intro h
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
    rcases h with e | e | e | e
    · exact hav₃ e
    · exact haQ' (List.mem_append_left _ e)
    · exact haQ' (by simp [e])
    · exact haw₃ e
  have finish : ∀ (β γ ε δ : C) (φ : V → C), β ∈ L u → γ ∈ L w → ε ∈ L w₃ → δ ∈ L v₃ →
      (∀ y ∈ R ++ [w₄], φ y ∈ L y ∧ φ y ≠ β) → (R ++ [w₄]).IsChain (fun y z => φ y ≠ φ z) →
      (∀ z ∈ (R ++ [w₄]).getLast?, φ z ≠ ε) → φ v₄ ≠ δ →
      δ ≠ β → ε ≠ β → γ ≠ β → ε ≠ g c → ε ≠ γ → γ ≠ g c → γ ≠ g x →
      Extends H D3 [x, a, v₃, u, w] L (skel β γ ε δ φ) → Extends H S [c, x, a] L g := by
    intro β γ ε δ φ hβ hγ hε hδ hφ hφc hφe hφs hδβ hεβ hγβ hεc hεγ hγc hγx hD3
    obtain ⟨f₀, hf₀⟩ : ∃ f₀, f₀ = skel β γ ε δ φ := ⟨_, rfl⟩
    rw [← hf₀] at hD3
    have e_u : f₀ u = β := by rw [hf₀]; simp [skel]
    have e_w : f₀ w = γ := by rw [hf₀]; simp [skel, hwu]
    have e_w₃ : f₀ w₃ = ε := by rw [hf₀]; simp [skel, huw₃.symm, hww₃'.symm]
    have e_v₃ : f₀ v₃ = δ := by rw [hf₀]; simp [skel, huv₃.symm, hwv₃.symm, hv₃w₃]
    have e_Q : ∀ y ∈ R ++ [w₄], f₀ y = φ y := by
      intro y hy; rw [hf₀]
      simp only [skel, huQ y hy, hwQ y hy, hQw₃ y hy, hQv₃ y hy, hy, ite_true, ite_false]
    have e_x : f₀ x = g x := by
      rw [hf₀]; simp only [skel, hux.symm, hwxn.symm, hxw₃, hxv₃, hxQ', ite_false]
    have e_a : f₀ a = g a := by
      rw [hf₀]; simp only [skel, hua.symm, hwa.symm, haw₃, hav₃, haQ', ite_false]
    have e_c : f₀ c = g c := by
      rw [hf₀]
      simp only [skel, huc.symm, hwc'.symm, hw₃c.symm, hv₃c.symm, hcQ', ite_false]
    have hskL : ∀ z, z ∈ u :: w :: v₃ :: (R ++ [w₄, w₃]) → f₀ z ∈ L z := by
      intro z hz
      have hcl : z = u ∨ z = w ∨ z = v₃ ∨ z ∈ R ++ [w₄] ∨ z = w₃ := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz ⊢; tauto
      rcases hcl with h | h | h | h | h
      · rw [h, e_u]; exact hβ
      · rw [h, e_w]; exact hγ
      · rw [h, e_v₃]; exact hδ
      · rw [e_Q z h]; exact (hφ z h).1
      · rw [h, e_w₃]; exact hε
    -- the fan
    have hneβ : ∀ y ∈ v₃ :: (R ++ [w₄, w₃]), f₀ y ≠ β := by
      intro y hy
      have hcl : y = v₃ ∨ y ∈ R ++ [w₄] ∨ y = w₃ := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
      rcases hcl with h | h | h
      · rw [h, e_v₃]; exact hδβ
      · rw [e_Q y h]; exact (hφ y h).2
      · rw [h, e_w₃]; exact hεβ
    have hchF : (v₃ :: (R ++ [w₄, w₃])).IsChain (fun y z => f₀ y ≠ f₀ z) := by
      have e1 : v₃ :: (R ++ [w₄, w₃]) = v₃ :: ((v₄ :: rest) ++ [w₃]) := by
        rw [← hv₄]; simp
      rw [e1]
      refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
      · rw [e_v₃, e_Q v₄ (by rw [hv₄]; simp)]; exact Ne.symm hφs
      · show List.IsChain _ ((v₄ :: rest) ++ [w₃])
        rw [List.isChain_append]
        refine ⟨isChain_congr (fun p hp q hq hpq => by
            rw [e_Q p (by rw [hv₄]; exact hp), e_Q q (by rw [hv₄]; exact hq)]; exact hpq)
            (hv₄ ▸ hφc), by simp, ?_⟩
        intro p hp q hq
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
        rw [← hq, e_w₃, e_Q p (by rw [hv₄]; exact List.mem_of_mem_getLast? hp)]
        exact hφe p (by rw [hv₄]; exact hp)
    have eF : Extends H Fu (u :: (v₃ :: (R ++ [w₄, w₃]))) L f₀ := by
      refine ⟨f₀, fun _ _ => rfl, ?_, ?_⟩
      · intro z hz hzc
        rcases hfillF z hz with h | h
        · exact absurd (by simp [h]) hzc
        · exact absurd (List.mem_cons_of_mem _ h) hzc
      · intro p hp q hq hpq
        rcases hfillF p hp with h1 | h1 <;> rcases hfillF q hq with h2 | h2
        · rw [h1, h2] at hpq; exact absurd hpq (H.loopless.irrefl _)
        · rw [h1, e_u]; exact (hneβ q h2).symm
        · rw [h2, e_u]; exact hneβ p h1
        · rcases (hchordQ p q h1 h2 hpq).chain hchF with h | h
          · exact h
          · exact Ne.symm h
    -- the quadrilateral `u w₃ c w` and the triangle `w c x`
    obtain ⟨hxa', hxc'', -⟩ := hh.ok
    have eD1 : Extends H D1 [u, w₃, c, w] L f₀ := by
      refine T.thm2_four H _ D1 rfl u w₃ c w h1' L f₀ ?_ (h5of D1 _ hR1)
      intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;> simp only [e_u, e_w₃, e_c, e_w] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact absurd hpq hnuc | exact absurd hpq.symm hnuc
        | exact hεβ.symm | exact hεβ | exact hγβ.symm | exact hγβ
        | exact hεc | exact hεc.symm | exact hεγ | exact hεγ.symm
        | exact hγc | exact hγc.symm
    have eD4 : Extends H D4 [w, c, x] L f₀ := by
      refine T.thm2_three H h4' L f₀ ?_ (h5of D4 _ hR4)
      intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;> simp only [e_c, e_w, e_x] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact hγc | exact hγc.symm | exact hγx | exact hγx.symm
        | exact hxc'' | exact hxc''.symm
    -- gluing
    have hx3 : x ∈ D3 := T.subset h3' x (by simp)
    have hw3 : w ∈ D3 := T.subset h3' w (by simp)
    have eD2 : Extends H D2 [c, x, a, v₃, u, w] L f₀ := by
      refine extends_glue hUC hXC ?_ ?_ (fun z hz => T.subset h2' z hz) ?_ ?_ hD3 eD4
      · intro z h1 h2; rcases hmemC z h1 h2 with e | e <;> simp [e]
      · intro z hz
        refine ⟨fun h => ?_, fun h => ?_⟩
        · by_cases hzc : z = c
          · exact absurd (hmemC z h (hzc ▸ T.subset h4' c (by simp))) (by
              rw [hzc]; rintro (e | e); exact hxc' e.symm; exact hwc' e.symm)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto
        · have hz3 : z ∈ D3 → z = x ∨ z = w := fun h3 => hmemC z h3 h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e | e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
          · rcases hz3 (e ▸ T.subset h3' a (by simp)) with e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm hxa)
            · exact absurd (e.symm.trans e') (Ne.symm hwa)
          · rcases hz3 (e ▸ T.subset h3' v₃ (by simp)) with e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm hxv₃)
            · exact absurd (e.symm.trans e') (Ne.symm hwv₃)
          · rcases hz3 (e ▸ T.subset h3' u (by simp)) with e' | e'
            · exact absurd (e.symm.trans e') hux
            · exact absurd (e.symm.trans e') (Ne.symm hwu)
          · exact Or.inl e
      · intro z hz hzc; exfalso; apply hzc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto
      · intro z hz hzc; exfalso; apply hzc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto
    have eD : Extends H D [w₃, c, x, a, v₃, u] L f₀ := by
      refine extends_glue hUB hXB ?_ ?_ (fun z hz => T.subset hD' z hz) ?_ ?_ eD1 eD2
      · intro z h1 h2; rcases hmemB z h1 h2 with e | e | e <;> simp [e]
      · intro z hz
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have hz2 : z ∈ D2 → z = u ∨ z = c ∨ z = w := fun h2 => hmemB z h h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e | e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
          · rcases hz2 (e ▸ T.subset h2' x (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm hux)
            · exact absurd (e.symm.trans e') hxc'
            · exact absurd (e.symm.trans e') (Ne.symm hwxn)
          · rcases hz2 (e ▸ T.subset h2' a (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm hua)
            · exact absurd (e.symm.trans e') hac
            · exact absurd (e.symm.trans e') (Ne.symm hwa)
          · rcases hz2 (e ▸ T.subset h2' v₃ (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm huv₃)
            · exact absurd (e.symm.trans e') hv₃c
            · exact absurd (e.symm.trans e') (Ne.symm hwv₃)
          · exact Or.inl e
        · have hz1 : z ∈ D1 → z = u ∨ z = c ∨ z = w := fun h1 => hmemB z h1 h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e | e
          · rcases hz1 (e ▸ T.subset h1' w₃ (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm huw₃)
            · exact absurd (e.symm.trans e') hw₃c
            · exact absurd (e.symm.trans e') (Ne.symm hww₃')
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · intro z hz hzc; apply hskL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hzc ⊢; tauto
      · intro z hz hzc; apply hskL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hzc ⊢; tauto
    have eS : Extends H S [c, x, a] L f₀ := by
      refine extends_glue hUA hXA ?_ ?_ (fun z hz => T.subset hNT z (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz ⊢; tauto))
        ?_ ?_ eF eD
      · intro z h1 h2; rcases hmemA z h1 h2 with e | e | e <;> simp [e]
      · intro z hz
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases hfillF z h with e | e
          · exfalso
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with e' | e' | e' <;> rw [e'] at e
            · exact huc e.symm
            · exact hux e.symm
            · exact hua e.symm
          · exfalso
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with e' | e' | e' <;> rw [e'] at e
            · exact hcQp e
            · exact hxQp e
            · exact haQp e
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto
      · intro z hz hzc; apply hskL
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz hzc ⊢; tauto
      · intro z hz hzc; apply hskL
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz hzc ⊢; tauto
    refine extends_congr (fun z hz => ?_) eS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h <;> rw [h]
    · exact e_c
    · exact e_x
    · exact e_a
  -- skeleton values
  have sk_u : ∀ β γ ε δ φ, skel β γ ε δ φ u = β := fun _ _ _ _ _ => by simp [skel]
  have sk_w : ∀ β γ ε δ φ, skel β γ ε δ φ w = γ := fun _ _ _ _ _ => by simp [skel, hwu]
  have sk_v₃ : ∀ β γ ε δ φ, skel β γ ε δ φ v₃ = δ := fun _ _ _ _ _ => by
    simp [skel, huv₃.symm, hwv₃.symm, hv₃w₃]
  have sk_x : ∀ β γ ε δ φ, skel β γ ε δ φ x = g x := fun _ _ _ _ _ => by
    simp only [skel, hux.symm, hwxn.symm, hxw₃, hxv₃, hxQ', ite_false]
  have sk_a : ∀ β γ ε δ φ, skel β γ ε δ φ a = g a := fun _ _ _ _ _ => by
    simp only [skel, hua.symm, hwa.symm, haw₃, hav₃, haQ', ite_false]
  have h3v₃ : 3 ≤ (L v₃).card := hh.three v₃ (by simp) (Ne.symm hav₃) hv₃c
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  have h5w : 5 ≤ (L w).card := hh.five w hwS hw
  have h3w₃ : 3 ≤ (L w₃).card := hh.three w₃ (by simp) (Ne.symm haw₃) hw₃c
  have h3Q : ∀ y ∈ R ++ [w₄], 3 ≤ (L y).card := fun y hy =>
    hh.three y (hQP y hy) (hQa y hy) (hQc y hy)
  obtain ⟨hxa', hxc'', -⟩ := hh.ok
  have hv₄Q : v₄ ∈ R ++ [w₄] := by rw [hv₄]; simp
  have hnxv₃ : ¬ H.Adj x v₃ := fun h => by
    rcases hxc v₃ (by simp) h with e | e
    · exact hav₃ e.symm
    · exact hv₃c e
  -- `γ` for `w`
  have pickγ : ∀ β ε : C, ∃ γ ∈ L w, γ ≠ β ∧ γ ≠ ε ∧ γ ≠ g c ∧ γ ≠ g x := by
    intro β ε
    have h1 := Finset.pred_card_le_card_erase (s := L w) (a := β)
    have h2 := Finset.pred_card_le_card_erase (s := (L w).erase β) (a := ε)
    have h3 := Finset.pred_card_le_card_erase (s := ((L w).erase β).erase ε) (a := g c)
    have h4 := Finset.pred_card_le_card_erase (s := (((L w).erase β).erase ε).erase (g c))
      (a := g x)
    obtain ⟨γ, hγ⟩ : ((((L w).erase β).erase ε).erase (g c)).erase (g x) |>.Nonempty :=
      Finset.card_pos.mp (by omega)
    simp only [Finset.mem_erase] at hγ
    exact ⟨γ, hγ.2.2.2.2, hγ.2.2.2.1, hγ.2.2.1, hγ.2.1, hγ.1⟩
  by_cases hhub : ∃ t ∈ D3, t ∉ [x, a, v₃, u, w] ∧ ∀ y ∈ [x, a, v₃, u, w], H.Adj t y
  · -- a hub `t` of the pentagon: cut along `a t u`, then along the chord `t w`
    obtain ⟨t, htD, htn, htall⟩ := hhub
    have htx : H.Adj t x := htall x (by simp)
    have hta : H.Adj t a := htall a (by simp)
    have htv₃ : H.Adj t v₃ := htall v₃ (by simp)
    have htu : H.Adj t u := htall u (by simp)
    have htw : H.Adj t w := htall w (by simp)
    have htS : t ∈ S := hR3.1 htD
    have htP : t ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]) := (hR3.2 t htD htn).1
    have h5t : 5 ≤ (L t).card := hh.five t htS htP
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htn
    obtain ⟨htxn, htan, htv₃n, htun, htwn⟩ := htn
    have hrotD : T.NT H D3 (a :: ([v₃] ++ u :: [w, x])) := by simpa using T.rotate h3'
    obtain ⟨Q1, Q2, hq1, hq2, hUD, hID, hXD⟩ := T.cut (x := a) (y := u) (u := t) (l₁ := [v₃])
      (l₂ := [w, x]) hrotD htD
      (by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
        exact ⟨htan, htv₃n, htun, htwn, htxn⟩)
      hta htu (fun h => hnua h.symm)
    have hmemD : ∀ v, v ∈ Q1 → v ∈ Q2 → v = a ∨ v = u ∨ v = t := by
      intro v h1 h2
      have : v ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hID] at this; simpa using this
    have hq1' : T.NT H Q1 [a, v₃, u, t] := by simpa using hq1
    have hq2' : T.NT H Q2 [u, w, x, a, t] := by simpa using hq2
    have hRQ1 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) Q1 [a, v₃, u, t] := by
      refine hR3.piece (c₂ := [u, w, x, a, t]) hUD ?_ hXD ?_ (fun v hv => T.subset hq2' v hv)
      · intro v h1 h2; rcases hmemD v h1 h2 with e | e | e <;> simp [e]
      · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
    have hRQ2 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) Q2 [u, w, x, a, t] := by
      refine hR3.piece' (c₁ := [a, v₃, u, t]) hUD ?_ hXD ?_ (fun v hv => T.subset hq1' v hv)
      · intro v h1 h2; rcases hmemD v h1 h2 with e | e | e <;> simp [e]
      · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
    have hrotQ : T.NT H Q2 (t :: ([u] ++ w :: [x, a])) := T.rotate_back (by simpa using hq2')
    obtain ⟨T₁, T₂, ht₁, ht₂, hUT, hIT, hXT⟩ := T.chord hrotQ (by simp) (by simp) htw
    have hmemT : ∀ v, v ∈ T₁ → v ∈ T₂ → v = t ∨ v = w := by
      intro v h1 h2
      have : v ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hIT] at this; simpa using this
    have ht₁' : T.NT H T₁ [t, u, w] := by simpa using ht₁
    have ht₂' : T.NT H T₂ [w, x, a, t] := by simpa using ht₂
    have hRT₁ : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) T₁ [t, u, w] := by
      refine hRQ2.piece (c₂ := [w, x, a, t]) hUT ?_ hXT ?_ (fun v hv => T.subset ht₂' v hv)
      · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
      · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
    have hRT₂ : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) T₂ [w, x, a, t] := by
      refine hRQ2.piece' (c₁ := [t, u, w]) hUT ?_ hXT ?_ (fun v hv => T.subset ht₁' v hv)
      · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
      · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
    -- the colours (paper): two colours at `v₃`, three at `v₄`
    obtain ⟨A3, hA3s, hA3c⟩ := Finset.exists_subset_card_eq (s := (L v₃).erase (g a)) (n := 2)
      (by have := Finset.pred_card_le_card_erase (s := L v₃) (a := g a); omega)
    obtain ⟨L4, hL4s, hL4c⟩ := Finset.exists_subset_card_eq (s := L v₄) (n := 3) (h3Q v₄ hv₄Q)
    obtain ⟨β, hβL, hβA, hβ4⟩ : ∃ β ∈ L u, β ∉ A3 ∧ ((A3 ∩ L4).Nonempty → β ∉ L4) := by
      by_cases hint : (A3 ∩ L4).Nonempty
      · have hcu : (A3 ∪ L4).card ≤ 4 := by
          have := Finset.card_union_add_card_inter A3 L4
          have := Finset.card_pos.mpr hint; omega
        have := Finset.le_card_sdiff (A3 ∪ L4) (L u)
        obtain ⟨β, hβ⟩ : (L u \ (A3 ∪ L4)).Nonempty := Finset.card_pos.mp (by omega)
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hβ
        exact ⟨β, hβ.1, hβ.2.1, fun _ => hβ.2.2⟩
      · have := Finset.le_card_sdiff A3 (L u)
        obtain ⟨β, hβ⟩ : (L u \ A3).Nonempty := Finset.card_pos.mp (by omega)
        simp only [Finset.mem_sdiff] at hβ
        exact ⟨β, hβ.1, hβ.2, fun h => absurd h hint⟩
    obtain ⟨ε, hεL, hεβ, hεc⟩ := three_pick h3w₃ β (g c)
    obtain ⟨γ, hγL, hγβ, hγε, hγc, hγx⟩ := pickγ β ε
    obtain ⟨η, hηL, hηx, hηa, hηβ, hηγ⟩ : ∃ η ∈ L t, η ≠ g x ∧ η ≠ g a ∧ η ≠ β ∧ η ≠ γ := by
      have h1 := Finset.pred_card_le_card_erase (s := L t) (a := g x)
      have h2 := Finset.pred_card_le_card_erase (s := (L t).erase (g x)) (a := g a)
      have h3 := Finset.pred_card_le_card_erase (s := ((L t).erase (g x)).erase (g a)) (a := β)
      have h4 := Finset.pred_card_le_card_erase (s := (((L t).erase (g x)).erase (g a)).erase β)
        (a := γ)
      obtain ⟨η, hη⟩ : ((((L t).erase (g x)).erase (g a)).erase β).erase γ |>.Nonempty :=
        Finset.card_pos.mp (by omega)
      simp only [Finset.mem_erase] at hη
      exact ⟨η, hη.2.2.2.2, hη.2.2.2.1, hη.2.2.1, hη.2.1, hη.1⟩
    obtain ⟨δ, hδA, hδη⟩ : ∃ δ ∈ A3, δ ≠ η := by
      obtain ⟨c1, h1, c2, h2', hne⟩ := Finset.one_lt_card.mp (show 1 < A3.card by omega)
      by_cases hc1 : c1 = η
      · exact ⟨c2, h2', fun h => hne (hc1.trans h.symm)⟩
      · exact ⟨c1, h1, hc1⟩
    have hδL : δ ∈ L v₃ := Finset.mem_of_mem_erase (hA3s hδA)
    have hδa : δ ≠ g a := Finset.ne_of_mem_erase (hA3s hδA)
    have hδβ : δ ≠ β := fun e => hβA (e ▸ hδA)
    -- the inner path, with the three colours `L4` at `v₄`
    let L'' : V → Finset C := Function.update L v₄ L4
    have hvr : (v₄ :: rest).Nodup := hv₄ ▸ hQnd
    have hv₄r : v₄ ∉ rest := (List.nodup_cons.mp hvr).1
    have hflex : 2 ≤ (((L'' v₄).erase δ).erase β).card := by
      simp only [L'', Function.update_self]
      by_cases hint : (A3 ∩ L4).Nonempty
      · rw [Finset.erase_eq_of_notMem (fun h => hβ4 hint (Finset.mem_of_mem_erase h))]
        have := Finset.pred_card_le_card_erase (s := L4) (a := δ); omega
      · have hδ4 : δ ∉ L4 := fun h => hint ⟨δ, Finset.mem_inter.mpr ⟨hδA, h⟩⟩
        rw [Finset.erase_eq_of_notMem hδ4]
        have := Finset.pred_card_le_card_erase (s := L4) (a := β); omega
    obtain ⟨φ, hφ, hφδ, hφe, hφc⟩ := side_flex L'' δ β ε hvr hflex (fun y hy => by
      have hy4 : y ≠ v₄ := fun e => hv₄r (e ▸ hy)
      simp only [L'', Function.update_of_ne hy4]
      exact h3Q y (by rw [hv₄]; exact List.mem_cons_of_mem _ hy))
    have hφ' : ∀ y ∈ R ++ [w₄], φ y ∈ L y ∧ φ y ≠ β := by
      intro y hy
      rw [hv₄] at hy
      obtain ⟨h1, h2⟩ := hφ y hy
      refine ⟨?_, h2⟩
      by_cases hy4 : y = v₄
      · rw [hy4] at h1 ⊢; simp only [L'', Function.update_self] at h1; exact hL4s h1
      · simp only [L'', Function.update_of_ne hy4] at h1; exact h1
    refine finish β γ ε δ φ hβL hγL hεL hδL hφ' (hv₄ ▸ hφc) (hv₄ ▸ hφe) hφδ hδβ hεβ hγβ hεc
      (Ne.symm hγε) hγc hγx ?_
    -- the pentagon, with `t` coloured `η`
    let f₁ := Function.update (skel β γ ε δ φ) t η
    have g_t : f₁ t = η := Function.update_self ..
    have g_ne : ∀ z, z ≠ t → f₁ z = skel β γ ε δ φ z := fun z hz => Function.update_of_ne hz ..
    have g_x : f₁ x = g x := by rw [g_ne x (Ne.symm htxn), sk_x]
    have g_a : f₁ a = g a := by rw [g_ne a (Ne.symm htan), sk_a]
    have g_v₃ : f₁ v₃ = δ := by rw [g_ne v₃ (Ne.symm htv₃n), sk_v₃]
    have g_u : f₁ u = β := by rw [g_ne u (Ne.symm htun), sk_u]
    have g_w : f₁ w = γ := by rw [g_ne w (Ne.symm htwn), sk_w]
    have eQ1 : Extends H Q1 [a, v₃, u, t] L f₁ := by
      refine T.thm2_four H _ Q1 rfl a v₃ u t hq1' L f₁ ?_ (h5of Q1 _ hRQ1)
      intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;> simp only [g_a, g_v₃, g_u, g_t] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact absurd hpq hnua | exact absurd hpq.symm hnua
        | exact hδa | exact hδa.symm | exact hηa | exact hηa.symm
        | exact hδβ | exact hδβ.symm | exact hδη | exact hδη.symm
        | exact hηβ | exact hηβ.symm
    have eT1 : Extends H T₁ [t, u, w] L f₁ := by
      refine T.thm2_three H ht₁' L f₁ ?_ (h5of T₁ _ hRT₁)
      intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;> simp only [g_t, g_u, g_w] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact hηβ | exact hηβ.symm | exact hηγ | exact hηγ.symm
        | exact hγβ | exact hγβ.symm
    have eT2 : Extends H T₂ [w, x, a, t] L f₁ := by
      refine T.thm2_four H _ T₂ rfl w x a t ht₂' L f₁ ?_ (h5of T₂ _ hRT₂)
      intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;> simp only [g_w, g_x, g_a, g_t] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact absurd hpq hnwa | exact absurd hpq.symm hnwa
        | exact hγx | exact hγx.symm | exact hηγ | exact hηγ.symm
        | exact hxa' | exact hxa'.symm | exact hηx | exact hηx.symm
        | exact hηa | exact hηa.symm
    have eQ2 : Extends H Q2 [u, w, x, a, t] L f₁ := by
      refine extends_glue hUT hXT ?_ ?_ (fun z hz => T.subset hq2' z hz) ?_ ?_ eT1 eT2
      · intro z h1 h2; rcases hmemT z h1 h2 with e | e <;> simp [e]
      · intro z hz
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have h2 : z ∈ T₂ → z = t ∨ z = w := fun h2 => hmemT z h h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
          · rcases h2 (e ▸ T.subset ht₂' x (by simp)) with e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm htxn)
            · exact absurd (e.symm.trans e') (Ne.symm hwxn)
          · rcases h2 (e ▸ T.subset ht₂' a (by simp)) with e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm htan)
            · exact absurd (e.symm.trans e') (Ne.symm hwa)
          · exact Or.inl e
        · have h1 : z ∈ T₁ → z = t ∨ z = w := fun h1 => hmemT z h1 h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e
          · rcases h1 (e ▸ T.subset ht₁' u (by simp)) with e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm htun)
            · exact absurd (e.symm.trans e') (Ne.symm hwu)
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr e))
      · intro z hz hzc; exfalso; apply hzc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto
      · intro z hz hzc; exfalso; apply hzc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢; tauto
    have eD3 : Extends H D3 [x, a, v₃, u, w] L f₁ := by
      refine extends_glue hUD hXD ?_ ?_ (fun z hz => T.subset h3' z hz) ?_ ?_ eQ1 eQ2
      · intro z h1 h2; rcases hmemD z h1 h2 with e | e | e <;> simp [e]
      · intro z hz
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have h2 : z ∈ Q2 → z = a ∨ z = u ∨ z = t := fun h2 => hmemD z h h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e
          · rcases h2 (e ▸ T.subset hq2' x (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') hxa
            · exact absurd (e.symm.trans e') (Ne.symm hux)
            · exact absurd (e.symm.trans e') (Ne.symm htxn)
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
          · rcases h2 (e ▸ T.subset hq2' w (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') hwa
            · exact absurd (e.symm.trans e') hwu
            · exact absurd (e.symm.trans e') (Ne.symm htwn)
        · have h1 : z ∈ Q1 → z = a ∨ z = u ∨ z = t := fun h1 => hmemD z h1 h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with e | e | e | e | e
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
          · rcases h1 (e ▸ T.subset hq1' v₃ (by simp)) with e' | e' | e'
            · exact absurd (e.symm.trans e') (Ne.symm hav₃)
            · exact absurd (e.symm.trans e') (Ne.symm huv₃)
            · exact absurd (e.symm.trans e') (Ne.symm htv₃n)
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
      · intro z hz hzc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hzc
        have hzt : z = t := by tauto
        rw [hzt, g_t]; exact hηL
      · intro z hz hzc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hzc
        have hzt : z = t := by tauto
        rw [hzt, g_t]; exact hηL
    refine extends_congr (fun z hz => ?_) eD3
    have hzt : z ≠ t := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with e | e | e | e | e <;> rw [e]
      · exact Ne.symm htxn
      · exact Ne.symm htan
      · exact Ne.symm htv₃n
      · exact Ne.symm htun
      · exact Ne.symm htwn
    exact g_ne z hzt
  · -- no hub: Theorem 2 for the pentagon
    push Not at hhub
    obtain ⟨β, hβAu, hflex⟩ := exists_flex (A := ((L u).erase (g x)).erase (g a))
      (by
        have := Finset.pred_card_le_card_erase (s := L u) (a := g x)
        have := Finset.pred_card_le_card_erase (s := (L u).erase (g x)) (a := g a); omega)
      (L v₃) (g a) h3v₃
    have hβL : β ∈ L u := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hβAu)
    have hβx : β ≠ g x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hβAu)
    have hβa : β ≠ g a := Finset.ne_of_mem_erase hβAu
    obtain ⟨ε, hεL, hεβ, hεc⟩ := three_pick h3w₃ β (g c)
    obtain ⟨φ, hφ, hφe, hφc⟩ := path_colour L β (R ++ [w₄]) ε hQnd (fun y hy => by
      have := Finset.pred_card_le_card_erase (s := L y) (a := β)
      have := h3Q y hy; omega)
    obtain ⟨δ, hδ, hδφ⟩ : ∃ δ ∈ ((L v₃).erase (g a)).erase β, δ ≠ φ v₄ := by
      obtain ⟨c1, h1, c2, h2', hne⟩ := Finset.one_lt_card.mp
        (show 1 < (((L v₃).erase (g a)).erase β).card by omega)
      by_cases hc1 : c1 = φ v₄
      · exact ⟨c2, h2', fun h => hne (hc1.trans h.symm)⟩
      · exact ⟨c1, h1, hc1⟩
    have hδL : δ ∈ L v₃ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hδ)
    have hδa : δ ≠ g a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hδ)
    have hδβ : δ ≠ β := Finset.ne_of_mem_erase hδ
    obtain ⟨γ, hγL, hγβ, hγε, hγc, hγx⟩ := pickγ β ε
    refine finish β γ ε δ φ hβL hγL hεL hδL hφ hφc hφe (Ne.symm hδφ) hδβ hεβ hγβ hεc
      (Ne.symm hγε) hγc hγx ?_
    refine T.thm2_five H _ D3 rfl x a v₃ u w h3' L _ ?_ (h5of D3 _ hR3) ?_
    · intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with hp | hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq | hq <;>
        rw [hp, hq] at hpq ⊢ <;>
        simp only [sk_x, sk_a, sk_v₃, sk_u, sk_w] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact absurd hpq hnxv₃ | exact absurd hpq.symm hnxv₃
        | exact absurd hpq hnua | exact absurd hpq.symm hnua
        | exact absurd hpq hnwa | exact absurd hpq.symm hnwa
        | exact absurd hpq hnwv₃ | exact absurd hpq.symm hnwv₃
        | exact hxa' | exact hxa'.symm | exact hβx | exact hβx.symm
        | exact hγx | exact hγx.symm | exact hδa | exact hδa.symm
        | exact hβa | exact hβa.symm | exact hδβ | exact hδβ.symm
        | exact hγβ | exact hγβ.symm
    · intro t ht htn hall
      obtain ⟨y, hy, hny⟩ := hhub t ht htn
      exact absurd (hall y hy) hny

set_option maxHeartbeats 16000000 in
/-- **The final step of Theorem 3** (for `k ≥ 6`, no chords, no separating triangles): the
conclusion of Theorem 3 holds. Delete `v₃` as in Claim 7; an exceptional `G − v₃` ends in a wheel
block whose centre `z0` is joined to `z, v_{k-1}, v_k, v₁`; `z = v_{k-2}` is Claim 6, otherwise `z`
is a common neighbour of `v₃, v_{k-1}`, a hub over `v₃ … v_{k-1}` (Claim 3), and the configuration
is coloured by `final_colour` (Claims 4, 5, 6 exclude the remaining adjacencies). -/
theorem thm3_final (H : SimpleGraph V) {S : Finset V} {x a v₃ w₄ w₃ c : V} {R : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])))
    (hh : Thm3Hyp H S x (a :: v₃ :: (R ++ [w₄, w₃, c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) → z ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) →
      H.Adj y z → ConsecIn (a :: v₃ :: (R ++ [w₄, w₃, c])) y z)
    (hxc : ∀ y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]), H.Adj x y → y = a ∨ y = c)
    (hN : T.NoSepTri H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])))
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: v₃ :: (R ++ [w₄, w₃, c])) a c L := by
  classical
  have hnd := T.nodup hNT
  have hPnd : (a :: v₃ :: (R ++ [w₄, w₃, c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: v₃ :: (R ++ [w₄, w₃, c]) := (List.nodup_cons.mp hnd).1
  have hav₃ : a ≠ v₃ := by rintro rfl; simp at hPnd
  have hv₃c : v₃ ≠ c := by rintro rfl; simp at hPnd
  have haw₃ : a ≠ w₃ := by rintro rfl; simp at hPnd
  have hac : a ≠ c := by rintro rfl; simp at hPnd
  have hw₃c : w₃ ≠ c := by
    intro e
    have := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp hPnd).2).2).2.1
    rw [e] at this; simp at this
  have hv₃P : v₃ ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by simp
  -- delete `v₃`
  have hrot : T.NT H S (v₃ :: (R ++ [w₄, w₃, c, x, a])) := by
    have := T.rotate_append (A := [x, a]) (B := v₃ :: (R ++ [w₄, w₃, c])) (by simpa using hNT)
    simpa using this
  have hlastl : (R ++ [w₄, w₃, c, x, a]).getLast? = some a := by
    rw [show R ++ [w₄, w₃, c, x, a] = (R ++ [w₄, w₃, c, x]) ++ [a] by simp]
    exact List.getLast?_concat ..
  have hheadl : (R ++ [w₄, w₃, c, x, a]).head? = (R ++ [w₄, w₃, c]).head? := by
    rcases R with _ | ⟨r, R'⟩ <;> simp
  obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp) (by
    intro z hz hv₃z
    by_cases hzx : z = x
    · rw [hzx] at hv₃z
      rcases hxc v₃ hv₃P hv₃z.symm with h | h
      · exact absurd h hav₃.symm
      · exact absurd h hv₃c
    · have hzP : z ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz ⊢; tauto
      rcases ConsecIn.nbr (A := [a]) (B := R ++ [w₄, w₃, c]) hPnd (hPc v₃ z hv₃P hzP hv₃z)
        with h | h
      · simp only [List.getLast?_singleton, Option.some.injEq] at h
        right; rw [hlastl, h]
      · left; rw [hheadl]; exact h)
  have hcyc : ∀ w, w ∉ v₃ :: (R ++ [w₄, w₃, c, x, a]) →
      w ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]) := by
    intro w hw h; apply hw
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  have hv₃S : v₃ ∈ S := T.subset hNT v₃ (by simp)
  -- lists without two colours of `L(v₃) ∖ {c(v₂)}` at the interior neighbours of `v₃`
  have h3v₃ : 3 ≤ (L v₃).card := hh.three v₃ hv₃P (Ne.symm hav₃) hv₃c
  obtain ⟨α₁, hα₁, α₂, hα₂, hα₁₂⟩ := Finset.one_lt_card.mp
    (show 1 < ((L v₃).erase (g a)).card by
      have := Finset.pred_card_le_card_erase (s := L v₃) (a := g a); omega)
  let L' : V → Finset C := fun z => if z ∈ us then ((L z).erase α₁).erase α₂ else L z
  have hL'in : ∀ z ∈ us, L' z = ((L z).erase α₁).erase α₂ := fun z hz => by simp [L', hz]
  have hL'out : ∀ z, z ∉ us → L' z = L z := fun z hz => by simp [L', hz]
  have hus3 : ∀ z ∈ us, 3 ≤ (L' z).card := by
    intro z hz
    rw [hL'in z hz]
    have h5 := hh.five z (hus z hz).1 (hcyc z (hus z hz).2)
    have := Finset.pred_card_le_card_erase (s := L z) (a := α₁)
    have := Finset.pred_card_le_card_erase (s := (L z).erase α₁) (a := α₂); omega
  have hG' : T.NT H (S.erase v₃) (x :: a :: (us ++ (R ++ [w₄, w₃, c]))) := by
    have := T.rotate_append (A := R ++ [w₄, w₃, c]) (B := x :: a :: us) (by simpa using hNT')
    simpa using this
  have hlast' : (a :: (us ++ (R ++ [w₄, w₃, c]))).getLast? = some c := by
    rw [show a :: (us ++ (R ++ [w₄, w₃, c])) = a :: ((us ++ R ++ [w₄, w₃]) ++ [c]) by simp]
    exact getLast?_cons_append_singleton a c _
  have hcl : ∀ y ∈ a :: (us ++ (R ++ [w₄, w₃, c])), y ∈ us ∨ y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
    intro y hy
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
  have hh' : Thm3Hyp H (S.erase v₃) x (a :: (us ++ (R ++ [w₄, w₃, c]))) a c L' g := by
    refine ⟨rfl, hlast', by simp; omega, hh.ok, ?_, ?_⟩
    · intro y hy hya hyc
      by_cases hyu : y ∈ us
      · exact hus3 y hyu
      · rw [hL'out y hyu]
        rcases hcl y hy with h | h
        · exact absurd h hyu
        · exact hh.three y h hya hyc
    · intro y hy hyc
      have hyu : y ∉ us := fun h => hyc (by simp [h])
      rw [hL'out y hyu]
      have hyv : y ≠ v₃ := Finset.ne_of_mem_erase hy
      apply hh.five y (Finset.mem_of_mem_erase hy)
      intro h; apply hyc
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  have hcard : (S.erase v₃).card < S.card := Finset.card_erase_lt_of_mem hv₃S
  rcases ih H (S.erase v₃) hcard x _ a c L' g hG' hh' with hE | hE
  · -- a colouring of `G − v₃` extends to `v₃`
    left
    obtain ⟨f, hfc, hfL, hfp⟩ := hE
    obtain ⟨v₄, hv₄⟩ : ∃ v₄, (R ++ [w₄, w₃, c, x, a]).head? = some v₄ := by
      rcases R with _ | ⟨r, R'⟩ <;> exact ⟨_, rfl⟩
    have hfa : f a = g a := hfc a (by simp)
    have hfu : ∀ z ∈ us, f z ≠ α₁ ∧ f z ≠ α₂ := by
      intro z hz
      have hzn := hcyc z (hus z hz).2
      have h := hfL z (Finset.mem_erase.mpr ⟨fun e => (hus z hz).2 (by simp [e]), (hus z hz).1⟩)
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun e => hzn (by simp [e]), fun e => hzn (by simp [e]),
            fun e => hzn (by simp [e])⟩)
      rw [hL'in z hz] at h
      exact ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
    obtain ⟨col, hcolL, hcola, hcolv₄, hcolu⟩ : ∃ col, col ∈ L v₃ ∧ col ≠ g a ∧ col ≠ f v₄ ∧
        ∀ z ∈ us, f z ≠ col := by
      by_cases h : α₁ = f v₄
      · exact ⟨α₂, Finset.mem_of_mem_erase hα₂, Finset.ne_of_mem_erase hα₂,
          fun e => hα₁₂ (h.trans e.symm), fun z hz e => (hfu z hz).2 e⟩
      · exact ⟨α₁, Finset.mem_of_mem_erase hα₁, Finset.ne_of_mem_erase hα₁, h,
          fun z hz e => (hfu z hz).1 e⟩
    refine ⟨Function.update f v₃ col, ?_, ?_, isProperOn_update hfp ?_⟩
    · intro z hz
      have hzv : z ≠ v₃ := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h | h <;> rw [h]
        · exact hv₃c.symm
        · exact fun e => hxP (e ▸ hv₃P)
        · exact hav₃
      rw [Function.update_of_ne hzv]; exact hfc z hz
    · intro z hz hzc
      by_cases hzv : z = v₃
      · rw [hzv, Function.update_self]; exact hcolL
      · rw [Function.update_of_ne hzv]
        have h := hfL z (Finset.mem_erase.mpr ⟨hzv, hz⟩) hzc
        by_cases hzu : z ∈ us
        · rw [hL'in z hzu] at h
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
        · rwa [hL'out z hzu] at h
    · intro w hw hvw
      rcases hnb w hw hvw with h | h | h
      · rw [hv₄] at h; simp only [Option.some.injEq] at h; rw [← h]; exact Ne.symm hcolv₄
      · rw [hlastl] at h; simp only [Option.some.injEq] at h; rw [← h, hfa]; exact Ne.symm hcola
      · exact hcolu w h
  -- `G − v₃` is exceptional
  by_cases hyc : ∃ y ∈ us, H.Adj y c
  · -- an interior neighbour of `v₃` joined to `v_k` is joined to `v_{k-1}` (Claim 3)
    obtain ⟨y, hyus, hyc'⟩ := hyc
    have hyS := (hus y hyus).1
    have hyn := hcyc y (hus y hyus).2
    have hNT0 := hNT
    have hh0 := hh
    have hPc0 := hPc
    have hxc0 := hxc
    have hN0 := hN
    have hyn0 := hyn
    have e : a :: v₃ :: (R ++ [w₄, w₃, c]) = [a] ++ v₃ :: ((R ++ [w₄, w₃]) ++ c :: []) := by
      simp
    have hPnd' := hPnd
    rw [e] at hNT hh hPc hxc hN hyn hPnd' ⊢
    rcases T.claim3 H (P₀ := [a]) (vi := v₃) (M := R ++ [w₄, w₃]) (vj := c) (P₁ := []) hNT hh
      (by simp) hyS hyn (hadj y hyus).symm hyc'
      (by
        intro p q hp hq hpq
        have h := hPc p q (List.mem_append_right _ hp) (List.mem_append_right _ hq) hpq
        exact ConsecIn.of_append_left hPnd' hp hq h)
      hN ih with h | h | hall
    · exact Or.inl h
    · exact Or.inr h
    · rw [← e]
      exact T.claim6_of_centre H (M := v₃ :: R) hNT0 hh0 hPc0 hxc0 hN0 ih hyS hyn0
        (hall w₄ (by simp)) (hall w₃ (by simp)) hyc'
  push Not at hyc
  obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, -⟩ := hE
  have hcP : c ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by simp
  have hw₃P : w₃ ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by simp
  -- the neighbours of `v_k` and `v_{k-1}` on the new outer path
  have A1 : ∀ y ∈ PW, H.Adj y c → y = w₃ := by
    intro y hy hyc'
    rcases hcl y (hsubW y hy) with h | h
    · exact absurd hyc' (hyc y h)
    · have e2 : a :: v₃ :: (R ++ [w₄, w₃, c]) = (a :: v₃ :: (R ++ [w₄, w₃])) ++ c :: [] := by
        simp
      have h' := (hPc y c h hcP hyc').symm
      rw [e2] at h'
      rcases ConsecIn.nbr (by rw [← e2]; exact hPnd) h' with h1 | h1
      · rw [show a :: v₃ :: (R ++ [w₄, w₃]) = (a :: v₃ :: (R ++ [w₄])) ++ [w₃] by simp,
          List.getLast?_concat] at h1
        simp only [Option.some.injEq] at h1; exact h1.symm
      · simp at h1
  have A2 : ∀ y ∈ PW, H.Adj y w₃ → y = w₄ ∨ y = c ∨ y ∈ us := by
    intro y hy hyw
    rcases hcl y (hsubW y hy) with h | h
    · exact Or.inr (Or.inr h)
    · have e2 : a :: v₃ :: (R ++ [w₄, w₃, c]) = (a :: v₃ :: (R ++ [w₄])) ++ w₃ :: [c] := by
        simp
      have h' := (hPc y w₃ h hw₃P hyw).symm
      rw [e2] at h'
      rcases ConsecIn.nbr (by rw [← e2]; exact hPnd) h' with h1 | h1
      · rw [show a :: v₃ :: (R ++ [w₄]) = (a :: v₃ :: R) ++ [w₄] by simp,
          List.getLast?_concat] at h1
        simp only [Option.some.injEq] at h1; exact Or.inl h1.symm
      · simp only [List.head?_cons, Option.some.injEq] at h1; exact Or.inr (Or.inl h1.symm)
  have hch := hGW.isPath
  -- the path of the wheel ends with `z, v_{k-1}, v_k`, where `z = v_{k-2}` or `z ∈ us`
  obtain ⟨R3, z, hR3, hz, hzw₃⟩ : ∃ R3 z, PW = R3 ++ [z, w₃, c] ∧ (z = w₄ ∨ z ∈ us) ∧
      H.Adj z w₃ := by
    rcases PW.eq_nil_or_concat with h | ⟨P1, t, h⟩
    · subst h; simp at hhW
    rw [List.concat_eq_append] at h
    have ht : t = c := by rw [h, List.getLast?_concat] at hlW; simpa using hlW
    subst ht
    rcases P1.eq_nil_or_concat with h1 | ⟨P2, y, h1⟩
    · subst h1; rw [h] at hhW; simp at hhW; exact absurd hhW.symm hac
    rw [List.concat_eq_append] at h1
    subst h1
    have hyc' : H.Adj y t := by
      rw [h] at hch
      exact (List.isChain_append.mp hch).2.2 y (by simp) t rfl
    have hyw : y = w₃ := A1 y (by rw [h]; simp) hyc'
    subst hyw
    rcases P2.eq_nil_or_concat with h2 | ⟨P3, z, h2⟩
    · subst h2; rw [h] at hhW; simp at hhW; exact absurd hhW.symm haw₃
    rw [List.concat_eq_append] at h2
    subst h2
    have hzy : H.Adj z y := by
      rw [h] at hch
      have := (List.isChain_append.mp hch).1
      exact (List.isChain_append.mp this).2.2 z (by simp) y rfl
    rcases A2 z (by rw [h]; simp) hzy with hz | hz | hz
    · exact ⟨P3, z, by rw [h]; simp, Or.inl hz, hzy⟩
    · subst hz; rw [h] at hndW
      exact absurd rfl ((List.nodup_append.mp hndW).2.2 z (by simp) z (by simp))
    · exact ⟨P3, z, by rw [h]; simp, Or.inr hz, hzy⟩
  have hC3 : Consec3 PW z w₃ c := hR3 ▸ Consec3.of_append R3 z w₃ c
  have hxw₃ : ¬ H.Adj x w₃ := fun h => by
    rcases hxc w₃ hw₃P h with e | e
    · exact haw₃ e.symm
    · exact hw₃c e
  obtain ⟨z0, hz0U, hz0z, hz0w₃, hz0c, hz0x⟩ := hGW.centre_of_inner hC3 hxw₃
  have hz0S : z0 ∈ S := Finset.mem_of_mem_erase (hUW z0 hz0U).1
  have hz0v : z0 ≠ v₃ := Finset.ne_of_mem_erase (hUW z0 hz0U).1
  have hz0n : z0 ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]) := by
    intro h; apply (hUW z0 hz0U).2
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  have hz0us : z0 ∉ us := fun h => (hUW z0 hz0U).2 (by simp [h])
  rcases hz with hz | hzus
  · rw [hz] at hz0z
    exact T.claim6_of_centre H (M := v₃ :: R) hNT hh hPc hxc hN ih hz0S hz0n hz0z hz0w₃ hz0c
  -- `z` is a hub over `v₃ … v_{k-1}` (Claim 3)
  have hzS := (hus z hzus).1
  have hzn := hcyc z (hus z hzus).2
  have hzv₃ : H.Adj z v₃ := (hadj z hzus).symm
  have eQ : a :: v₃ :: (R ++ [w₄, w₃, c]) = [a] ++ (v₃ :: ((R ++ [w₄]) ++ [w₃])) ++ [c] := by
    simp
  have hchordQ : ∀ p q, p ∈ v₃ :: ((R ++ [w₄]) ++ [w₃]) → q ∈ v₃ :: ((R ++ [w₄]) ++ [w₃]) →
      H.Adj p q → ConsecIn (v₃ :: ((R ++ [w₄]) ++ [w₃])) p q := by
    intro p q hp hq hpq
    have hp' : p ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
      rw [eQ]; exact List.mem_append_left _ (List.mem_append_right _ hp)
    have hq' : q ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
      rw [eQ]; exact List.mem_append_left _ (List.mem_append_right _ hq)
    have h := hPc p q hp' hq' hpq
    rw [eQ] at h
    exact ConsecIn.infix (by rw [← eQ]; exact hPnd) hp hq h
  have hhub3 : (Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: v₃ :: (R ++ [w₄, w₃, c])) a c L) ∨
      ∀ m ∈ R ++ [w₄], H.Adj z m := by
    have e2 : a :: v₃ :: (R ++ [w₄, w₃, c]) = [a] ++ v₃ :: ((R ++ [w₄]) ++ w₃ :: [c]) := by simp
    have hNT2 := hNT
    have hh2 := hh
    have hN2 := hN
    have hzn2 := hzn
    rw [e2] at hNT2 hh2 hN2 hzn2
    rcases T.claim3 H (P₀ := [a]) (vi := v₃) (M := R ++ [w₄]) (vj := w₃) (P₁ := [c]) hNT2 hh2
      (by simp) hzS hzn2 hzv₃ hzw₃ hchordQ hN2 ih with h | h | h
    · exact Or.inl (Or.inl h)
    · left; right; rw [e2]; exact h
    · exact Or.inr h
  rcases hhub3 with h | hall
  · exact h
  have hub : ∀ y ∈ v₃ :: (R ++ [w₄, w₃]), H.Adj z y := by
    intro y hy
    have hcl : y = v₃ ∨ y ∈ R ++ [w₄] ∨ y = w₃ := by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
    rcases hcl with e | e | e
    · rw [e]; exact hzv₃
    · exact hall y e
    · rw [e]; exact hzw₃
  have hz0zne : z0 ≠ z := fun e => hz0us (e ▸ hzus)
  -- `z` not joined to `v_k` (Claim 6) nor to `v₂` (Claim 5)
  by_cases hzc : H.Adj z c
  · exact T.claim6_of_centre H (M := v₃ :: R) hNT hh hPc hxc hN ih hzS hzn
      (hub w₄ (by simp)) hzw₃ hzc
  obtain ⟨v₄, M', hv₄⟩ : ∃ v₄ M', R ++ [w₄, w₃] = v₄ :: M' :=
    List.exists_cons_of_ne_nil (by simp)
  by_cases hza : H.Adj z a
  · have e5 : a :: v₃ :: (R ++ [w₄, w₃, c]) = a :: v₃ :: v₄ :: (M' ++ [c]) := by
      rw [show R ++ [w₄, w₃, c] = (R ++ [w₄, w₃]) ++ [c] by simp, hv₄]; rfl
    have hzv₄ : H.Adj z v₄ := hub v₄ (by rw [hv₄]; simp)
    rw [e5] at hNT hh hPc hxc hN hzn ⊢
    exact T.claim5_of_centre H hNT hh hPc hxc hN ih hzS hzn hza hzv₃ hzv₄
  -- `z0` not joined to `v₂` (Claim 4) nor to `v₃`
  by_cases hz0a : H.Adj z0 a
  · have e4 : a :: v₃ :: (R ++ [w₄, w₃, c]) = a :: ((v₃ :: (R ++ [w₄, w₃])) ++ [c]) := by simp
    rw [e4] at hNT hh hPc hxc hN hz0n ⊢
    exact T.claim4 H hNT hh (by simp) hz0S hz0n hz0a hz0c hPc hxc hN ih
  have hnz0v₃ : ¬ H.Adj z0 v₃ := by
    intro h
    rcases hnb z0 hz0S h.symm with h1 | h1 | h1
    · rw [hheadl] at h1
      exact hz0n (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_of_mem_head? h1))))
    · rw [hlastl] at h1; simp only [Option.some.injEq] at h1
      exact hz0n (by simp [← h1])
    · exact hz0us h1
  exact Or.inl (T.final_colour H hNT hh hPc hxc hN hzS hzn hz0S hz0n hz0zne hub hz0z hz0c hz0x
    hzc hza hz0a hnz0v₃)

end NTCalc

end ThomassenManyColourings
