/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneChordSep

/-!
# The two sides of a cut along `x u y` (layer B, part 6)

For `PNT H S (x :: (l₁ ++ y :: l₂))`, an interior vertex `u` joined to `x` and `y` (with `x ≁ y`)
and a separation `S₁ ∪ S₂ = S`, `S₁ ∩ S₂ = {x, y, u}` without crossing edges, with the arc
`x l₁ y` and `u` in `S₁` and `l₂` outside `S₁`, the piece `S₁` is a plane near-triangulation
with outer cycle `x l₁ y u` (`cut_side`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A consecutive pair of `L ++ [w]` not ending at `w` is consecutive in `L`. -/
theorem consec_of_append_single {A B L : List V} {a b w : V}
    (h : A ++ a :: b :: B = L ++ [w]) (hb : b ≠ w) : ∃ B', L = A ++ a :: b :: B' := by
  rcases B.eq_nil_or_concat with rfl | ⟨B', c, rfl⟩
  · have h' : (A ++ [a]) ++ [b] = L ++ [w] := by rw [← h]; simp
    obtain ⟨-, hbw⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at hbw
    exact absurd hbw hb
  · have h' : (A ++ a :: b :: B') ++ [c] = L ++ [w] := by rw [← h]; simp
    obtain ⟨hL, -⟩ := List.append_inj' h' rfl
    exact ⟨B', hL.symm⟩

omit [DecidableEq V] in
/-- An outer pair of `x l₁ y l₂` avoiding `l₂` is consecutive on `x l₁ y`. -/
theorem consec_arc {x y : V} {l₁ l₂ : List V} (hnd : (x :: (l₁ ++ y :: l₂)).Nodup)
    (hl₂ : l₂ ≠ []) {a b : V} (h : CycSucc (x :: (l₁ ++ y :: l₂)) a b) (ha : a ∉ l₂)
    (hb : b ∉ l₂) : ∃ A B, x :: (l₁ ++ [y]) = A ++ a :: b :: B := by
  rcases cycSucc_arc hnd hl₂ h ha hb with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
  · exact ⟨A, B, hAB⟩
  · exfalso
    simp only [List.cons.injEq] at hMm
    obtain ⟨-, hM'⟩ := hMm
    obtain ⟨-, hya⟩ := List.append_inj' hM' rfl
    simp only [List.cons.injEq, and_true] at hya
    -- the successor of `y` is the first vertex of `l₂`
    obtain ⟨w, l₂', rfl⟩ := List.exists_cons_of_ne_nil hl₂
    have h1 : CycSucc (x :: (l₁ ++ y :: w :: l₂')) y w := Or.inl ⟨x :: l₁, l₂', by simp⟩
    rw [← hya] at h
    have := CycSucc.unique hnd h h1
    exact hb (this ▸ List.mem_cons_self)

variable [Fintype V] {H : SimpleGraph V} {S : Finset V}

-- `piece_PNT` and the case analysis on the separator exceed the default heartbeat budget.
set_option maxHeartbeats 8000000 in
/-- **One side of a cut along `x u y`.** -/
theorem cut_side {x y u : V} {l₁ l₂ : List V} (hP : PNT H S (x :: (l₁ ++ y :: l₂)))
    {M : PlaneMap (indG H S)} (hM : IsNTMap (x :: (l₁ ++ y :: l₂)) M) (hl₁ : l₁ ≠ [])
    (hl₂ : l₂ ≠ []) (hu : u ∉ x :: (l₁ ++ y :: l₂)) (hux : H.Adj u x) (huy : H.Adj u y)
    (hxy : ¬ H.Adj x y) {S₁ S₂ : Finset V} (hS₁ : S₁ ⊆ S)
    (hcov : S₁ ∪ S₂ = S) (hint : S₁ ∩ S₂ = {x, y, u})
    (hcross : ∀ a ∈ S₁, ∀ w ∈ S₂, H.Adj a w → a ∈ S₂ ∨ w ∈ S₁)
    (hL : ∀ v ∈ x :: (l₁ ++ [y, u]), v ∈ S₁) (hl₂out : ∀ v ∈ l₂, v ∉ S₁)
    (hreach : ∀ a ∈ S₁, ∀ v ∈ S₁, (indG H S₁).Reachable a v) :
    PNT H S₁ (x :: (l₁ ++ [y, u])) := by
  classical
  have hnd := hP.nodup
  have hbig : x :: (l₁ ++ y :: l₂) = (x :: (l₁ ++ [y])) ++ l₂ := by simp
  have hndA : (x :: (l₁ ++ [y])).Nodup := by
    have := hnd; rw [hbig] at this; exact (List.nodup_append.mp this).1
  have hC : x :: (l₁ ++ [y, u]) = (x :: (l₁ ++ [y])) ++ [u] := by simp
  have huA : u ∉ x :: (l₁ ++ [y]) := fun h => hu (by rw [hbig]; exact List.mem_append_left _ h)
  have hndL : (x :: (l₁ ++ [y, u])).Nodup := by
    rw [hC, List.nodup_append]
    exact ⟨hndA, List.nodup_singleton u, fun a ha b hb hab => huA (by
      simp only [List.mem_singleton] at hb; rw [← hb, ← hab]; exact ha)⟩
  have h4 : 3 ≤ (x :: (l₁ ++ [y, u])).length := by simp
  -- consecutive vertices of the new cycle are adjacent
  have hadjL : ∀ a b, CycSucc (x :: (l₁ ++ [y, u])) a b → H.Adj a b := by
    intro a b hab
    rcases hab with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
    · by_cases hbu : b = u
      · -- `a` precedes `u`, so `a = y`
        subst hbu
        have h1 : CycSucc (x :: (l₁ ++ [y, b])) y b := Or.inl ⟨x :: l₁, [], by simp⟩
        have := CycSucc.unique_left hndL (Or.inl ⟨A, B, hAB⟩) h1
        rw [this]; exact huy.symm
      · rw [hC] at hAB
        obtain ⟨B', hB'⟩ := consec_of_append_single hAB.symm hbu
        exact hP.adj (Or.inl ⟨A, B' ++ l₂, by rw [hbig, hB']; simp⟩)
    · rw [hC] at hMm
      simp only [List.cons_append, List.cons.injEq] at hMm
      obtain ⟨rfl, hM'⟩ := hMm
      obtain ⟨-, hau⟩ := List.append_inj' (show (l₁ ++ [y]) ++ [u] = Mm ++ [a] by
        simpa using hM') rfl
      simp only [List.cons.injEq, and_true] at hau
      rw [← hau]; exact hux
  -- an inner triangle leaving `S₁` has its base on the separator
  have hleave : ∀ d : (indG H S).Dart, ¬ IsOuter (x :: (l₁ ++ y :: l₂)) d → d.fst ∈ S₁ →
      d.snd ∈ S₁ → (M.facePerm d).snd ∉ S₁ →
      (d.fst = x ∨ d.fst = y ∨ d.fst = u) ∧ (d.snd = x ∨ d.snd = y ∨ d.snd = u) := by
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
  have hxz : CycSucc (x :: (z :: l₁' ++ [y, u])) x z := Or.inl ⟨[], l₁' ++ [y, u], by simp⟩
  have hzx_not : ¬ CycSucc (x :: (z :: l₁' ++ y :: l₂)) z x := by
    intro h
    obtain ⟨w, l₂', rfl⟩ := List.exists_cons_of_ne_nil hl₂
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
  have hux' : ¬ H.Adj x y := hxy
  refine piece_PNT hP hM hS₁ hndL h4 hL hadjL hreach ?_ ?_ ?_
  · refine ⟨⟨(x, z), indG_adj_of (hadjL x z hxz) (hL x (by simp)) (hL z (by simp))⟩, hxz, ?_⟩
    left
    exact Or.inl ⟨[], l₁' ++ y :: l₂, by simp⟩
  · intro d hd
    by_cases ho : IsOuter (x :: (z :: l₁' ++ y :: l₂)) (td d)
    · left
      have ho' : CycSucc (x :: (z :: l₁' ++ y :: l₂)) d.fst d.snd := ho
      obtain ⟨A, B, hAB⟩ := consec_arc hnd hl₂ ho'
        (fun h => hl₂out _ h (Finset.mem_coe.mp d.adj.2.1))
        (fun h => hl₂out _ h (Finset.mem_coe.mp d.adj.2.2))
      exact Or.inl ⟨A, B ++ [u], by
        rw [show x :: (z :: l₁' ++ [y, u]) = (x :: (z :: l₁' ++ [y])) ++ [u] by simp, hAB]
        simp⟩
    · have hz := hd.resolve_left ho
      obtain ⟨ha, hb⟩ := hleave (td d) ho (Finset.mem_coe.mp d.adj.2.1)
        (Finset.mem_coe.mp d.adj.2.2) hz
      have hne : d.fst ≠ d.snd := d.adj.1.ne
      have hadj : H.Adj d.fst d.snd := d.adj.1
      change d.fst = x ∨ d.fst = y ∨ d.fst = u at ha
      change d.snd = x ∨ d.snd = y ∨ d.snd = u at hb
      have hwrap : CycSucc (x :: (z :: l₁' ++ [y, u])) u x :=
        Or.inr ⟨z :: l₁' ++ [y], by simp⟩
      have hyu : CycSucc (x :: (z :: l₁' ++ [y, u])) y u := Or.inl ⟨x :: z :: l₁', [], by simp⟩
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
      · exact absurd (ha.trans hb.symm) hne
      · exact absurd (by rw [ha, hb] at hadj; exact hadj) hux'
      · right; rw [ha, hb]; exact hwrap
      · exact absurd (by rw [ha, hb] at hadj; exact hadj.symm) hux'
      · exact absurd (ha.trans hb.symm) hne
      · left; rw [ha, hb]; exact hyu
      · left; rw [ha, hb]; exact hwrap
      · right; rw [ha, hb]; exact hyu
      · exact absurd (ha.trans hb.symm) hne
  · refine ⟨x, z, hxz, fun d hd hdz hdx => ?_⟩
    have hout : ∀ h : IsOuter (x :: (z :: l₁' ++ y :: l₂)) (td d), False := by
      intro h
      have h' : CycSucc (x :: (z :: l₁' ++ y :: l₂)) d.fst d.snd := h
      rw [hdz, hdx] at h'
      exact hzx_not h'
    rcases hd with ho | hz
    · exact hout ho
    · obtain ⟨ha, -⟩ := hleave (td d) hout (Finset.mem_coe.mp d.adj.2.1)
        (Finset.mem_coe.mp d.adj.2.2) hz
      change d.fst = x ∨ d.fst = y ∨ d.fst = u at ha
      rw [hdz] at ha
      have hz1 : (z :: (l₁' ++ [y])).Nodup := (List.nodup_cons.mp hndA).2
      rcases ha with h | h | h
      · exact (List.nodup_cons.mp hndA).1 (by simp [h])
      · exact (List.nodup_cons.mp hz1).1 (by simp [h])
      · exact huA (by rw [← h]; simp)

end ThomassenManyColourings
