/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlanePiece

/-!
# The two sides of a chord (layer B, part 4)

For `PNT H S (x :: (l₁ ++ y :: l₂))` with a chord `x y` and a separation `S₁ ∪ S₂ = S`,
`S₁ ∩ S₂ = {x, y}` without crossing edges, with the arc `x l₁ y` in `S₁` and `l₂` outside `S₁`,
the piece `S₁` is a plane near-triangulation with outer cycle `x l₁ y` (`chord_side`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A cyclic successor pair avoiding `l₂` lies on the arc `x l₁ y`. -/
theorem cycSucc_arc {x y : V} {l₁ l₂ : List V} (hnd : (x :: (l₁ ++ y :: l₂)).Nodup)
    (hl₂ : l₂ ≠ []) {a b : V} (h : CycSucc (x :: (l₁ ++ y :: l₂)) a b) (ha : a ∉ l₂)
    (hb : b ∉ l₂) : CycSucc (x :: (l₁ ++ [y])) a b := by
  have hbig : x :: (l₁ ++ y :: l₂) = (x :: (l₁ ++ [y])) ++ l₂ := by simp
  have haP : a ∈ x :: (l₁ ++ [y]) := by
    have := h.mem.1
    rw [hbig, List.mem_append] at this
    exact this.resolve_right ha
  obtain ⟨A₀, B₀, hAB⟩ := List.append_of_mem haP
  rcases B₀ with _ | ⟨b', B₁⟩
  · -- `a` is the last vertex `y`, followed by the first vertex of `l₂`
    obtain ⟨z, l₂', rfl⟩ := List.exists_cons_of_ne_nil hl₂
    have h1 : CycSucc (x :: (l₁ ++ y :: z :: l₂')) a z :=
      Or.inl ⟨A₀, l₂', by rw [hbig, hAB]; simp⟩
    rw [CycSucc.unique hnd h h1] at hb
    exact absurd (by simp) hb
  · have h1 : CycSucc (x :: (l₁ ++ y :: l₂)) a b' :=
      Or.inl ⟨A₀, B₁ ++ l₂, by rw [hbig, hAB]; simp⟩
    rw [CycSucc.unique hnd h h1]
    exact Or.inl ⟨A₀, B₁, hAB⟩

variable [Fintype V] {H : SimpleGraph V} {S : Finset V}

omit [DecidableEq V] [Fintype V] in
/-- The third vertex of the inner triangle at a dart. -/
theorem tri_adj {c : List V} {M : PlaneMap (indG H S)} (hM : IsNTMap c M) (d : (indG H S).Dart)
    (hd : ¬ IsOuter c d) :
    H.Adj d.snd (M.facePerm d).snd ∧ H.Adj (M.facePerm d).snd d.fst ∧
      (M.facePerm d).snd ∈ S := by
  have h1 := (M.facePerm d).adj
  rw [face_fst'] at h1
  have h2 := (M.facePerm (M.facePerm d)).adj
  rw [face_fst'] at h2
  have h3 := face_fst' M (M.facePerm (M.facePerm d))
  rw [← facePerm_pow_three, hM.2 d hd] at h3
  rw [← h3] at h2
  exact ⟨h1.1, h2.1, Finset.mem_coe.mp h1.2.2⟩

set_option maxHeartbeats 8000000 in
/-- **One side of a chord.** -/
theorem chord_side {x y : V} {l₁ l₂ : List V} (hP : PNT H S (x :: (l₁ ++ y :: l₂)))
    {M : PlaneMap (indG H S)} (hM : IsNTMap (x :: (l₁ ++ y :: l₂)) M) (hl₁ : l₁ ≠ [])
    (hl₂ : l₂ ≠ []) (hxy : H.Adj x y) {S₁ S₂ : Finset V} (hS₁ : S₁ ⊆ S)
    (hcov : S₁ ∪ S₂ = S) (hint : S₁ ∩ S₂ = {x, y})
    (hcross : ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁)
    (hL : ∀ v ∈ x :: (l₁ ++ [y]), v ∈ S₁) (hl₂out : ∀ v ∈ l₂, v ∉ S₁)
    (hreach : ∀ u ∈ S₁, ∀ v ∈ S₁, (indG H S₁).Reachable u v) :
    PNT H S₁ (x :: (l₁ ++ [y])) := by
  classical
  have hnd := hP.nodup
  have hbig : x :: (l₁ ++ y :: l₂) = (x :: (l₁ ++ [y])) ++ l₂ := by simp
  have hndL : (x :: (l₁ ++ [y])).Nodup := by
    have := hnd; rw [hbig] at this; exact (List.nodup_append.mp this).1
  have h3 : 3 ≤ (x :: (l₁ ++ [y])).length := by
    obtain ⟨z, l₁', rfl⟩ := List.exists_cons_of_ne_nil hl₁; simp
  -- consecutive vertices of the arc are adjacent; so is the closing pair `y x`
  have hadjL : ∀ u v, CycSucc (x :: (l₁ ++ [y])) u v → H.Adj u v := by
    intro u v huv
    rcases huv with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
    · exact hP.adj (Or.inl ⟨A, B ++ l₂, by rw [hbig, hAB]; simp⟩)
    · simp only [List.cons.injEq] at hMm
      obtain ⟨rfl, hM'⟩ := hMm
      have : l₁ ++ [y] = Mm ++ [u] := hM'
      obtain ⟨-, hu⟩ := List.append_inj' this rfl
      simp only [List.cons.injEq, and_true] at hu
      rw [← hu]
      exact hxy.symm
  -- an inner triangle leaving `S₁` has both base vertices in `{x, y}`
  have hleave : ∀ d : (indG H S).Dart, ¬ IsOuter (x :: (l₁ ++ y :: l₂)) d → d.fst ∈ S₁ →
      d.snd ∈ S₁ → (M.facePerm d).snd ∉ S₁ → (d.fst = x ∨ d.fst = y) ∧ (d.snd = x ∨ d.snd = y) := by
    intro d hd hfS hsS hz
    obtain ⟨hbz, hza, hzS⟩ := tri_adj hM d hd
    have hz2 : (M.facePerm d).snd ∈ S₂ := by
      have h := Finset.ext_iff.mp hcov ((M.facePerm d).snd)
      rw [Finset.mem_union] at h
      exact (h.mpr hzS).resolve_left hz
    have hb2 : d.snd ∈ S₂ := (hcross _ hsS _ hz2 hbz).resolve_right hz
    have ha2 : d.fst ∈ S₂ := (hcross _ hfS _ hz2 hza.symm).resolve_right hz
    have hb : d.snd ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hsS, hb2⟩
    have ha : d.fst ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨hfS, ha2⟩
    rw [hint] at ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    exact ⟨ha, hb⟩
  set td := Grotzsch.toDart (restrict_mono (H := H) hS₁) with htd
  obtain ⟨z, l₁', rfl⟩ := List.exists_cons_of_ne_nil hl₁
  have hxz : CycSucc (x :: (z :: l₁' ++ [y])) x z := Or.inl ⟨[], l₁' ++ [y], by simp⟩
  have hzx_not : ¬ CycSucc (x :: (z :: l₁' ++ y :: l₂)) z x := by
    intro h
    obtain ⟨w, l₂', rfl⟩ := List.exists_cons_of_ne_nil hl₂
    -- the predecessor of `x` is the last vertex of `l₂`
    have hlast : CycSucc (x :: (z :: l₁' ++ y :: w :: l₂'))
        ((w :: l₂').getLast (by simp)) x :=
      Or.inr ⟨z :: l₁' ++ y :: (w :: l₂').dropLast, by
        rw [show z :: l₁' ++ y :: w :: l₂' =
          (z :: l₁' ++ [y]) ++ ((w :: l₂').dropLast ++ [(w :: l₂').getLast (by simp)]) by
          rw [List.dropLast_append_getLast]; simp]
        simp⟩
    have := CycSucc.unique_left hnd h hlast
    have hzl : z ∈ w :: l₂' := this ▸ List.getLast_mem _
    exact hl₂out z hzl (hL z (by simp))
  refine piece_PNT hP hM hS₁ hndL h3 hL hadjL hreach ?_ ?_ ?_
  · -- the first arc dart is an outer dart of `M`
    refine ⟨⟨(x, z), indG_adj_of (hadjL x z hxz) (hL x (by simp)) (hL z (by simp))⟩, hxz, ?_⟩
    left
    exact Or.inl ⟨[], l₁' ++ y :: l₂, by simp⟩
  · -- the darts of `R`
    intro d hd
    by_cases ho : IsOuter (x :: (z :: l₁' ++ y :: l₂)) (td d)
    · left
      exact cycSucc_arc hnd hl₂ ho (fun h => hl₂out _ h (Finset.mem_coe.mp d.adj.2.1))
        (fun h => hl₂out _ h (Finset.mem_coe.mp d.adj.2.2))
    · have hz := hd.resolve_left ho
      obtain ⟨ha, hb⟩ := hleave (td d) ho (Finset.mem_coe.mp d.adj.2.1)
        (Finset.mem_coe.mp d.adj.2.2) hz
      have hne : d.fst ≠ d.snd := d.adj.1.ne
      change d.fst = x ∨ d.fst = y at ha
      change d.snd = x ∨ d.snd = y at hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hne
      · right; rw [ha, hb]; exact Or.inr ⟨z :: l₁', rfl⟩
      · left; rw [ha, hb]; exact Or.inr ⟨z :: l₁', rfl⟩
      · exact absurd (ha.trans hb.symm) hne
  · -- the backward dart `(z, x)` is missing
    refine ⟨x, z, hxz, fun d hd hdz hdx => ?_⟩
    have hout : ∀ h : IsOuter (x :: (z :: l₁' ++ y :: l₂)) (td d), False := by
      intro h
      have h' : CycSucc (x :: (z :: l₁' ++ y :: l₂)) d.fst d.snd := h
      rw [hdz, hdx] at h'
      exact hzx_not h'
    rcases hd with ho | hz
    · exact hout ho
    · have ho : ¬ IsOuter (x :: (z :: l₁' ++ y :: l₂)) (td d) := hout
      obtain ⟨ha, -⟩ := hleave (td d) ho (Finset.mem_coe.mp d.adj.2.1)
        (Finset.mem_coe.mp d.adj.2.2) hz
      change d.fst = x ∨ d.fst = y at ha
      rw [hdz] at ha
      have hz1 : (z :: (l₁' ++ [y])).Nodup := (List.nodup_cons.mp hndL).2
      rcases ha with h | h
      · exact (List.nodup_cons.mp hndL).1 (by simp [h])
      · exact (List.nodup_cons.mp hz1).1 (by simp [h])

end ThomassenManyColourings
