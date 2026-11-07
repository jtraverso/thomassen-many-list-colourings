/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Claim4
public import ThomassenManyColourings.Lemma3
public import ThomassenManyColourings.ListFacts

/-!
# Theorem 3, Claim 5: `v₃` has degree at least four

If the only neighbours of `v₃` are `v₂`, `v₄` and one more vertex `u`, delete `v₃`: `u` is an
interior vertex joined to `v₂` and `v₄`. Let `v_i` be the last vertex of the outer path joined to
`u`; `v_i = v_k` is Claim 4, and Claim 3 makes the inside of `v₂ u v_i` a fan. Deleting two colours
of `L(v₃) ∖ {c(v₂)}` from `L(u)`, a colouring of the outside `G₁` of `v₂ u v_i` extends to `G`
(colour the fan greedily, then `v₃`); otherwise `G₁` is a generalized wheel whose only junction is
`u`, with one wheel centre `w`, and Lemma 3 (`dfan`) colours `G`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
/-- A block on two path vertices with `m ≥ 3` is a triangle. -/
theorem Block.empty_of_two {H : SimpleGraph V} {m : ℕ} {x : V} {P : List V} {U : Finset V}
    (h : Block H m x P U) (hm : 3 ≤ m) (hP : P.length ≤ 2) : U = ∅ := by
  cases h with
  | tri => rfl
  | wheel _ hm' => omega

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 16000000 in
/-- **Claim 5**, as a reduction: if `v₃` has at most one neighbour off the outer cycle, the
conclusion of Theorem 3 holds. -/
theorem claim5 (H : SimpleGraph V) {S : Finset V} {x a v₃ v₄ c u : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: v₃ :: v₄ :: (M ++ [c])))
    (hh : Thm3Hyp H S x (a :: v₃ :: v₄ :: (M ++ [c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: v₃ :: v₄ :: (M ++ [c]) → z ∈ a :: v₃ :: v₄ :: (M ++ [c]) →
      H.Adj y z → ConsecIn (a :: v₃ :: v₄ :: (M ++ [c])) y z)
    (hxc : ∀ y ∈ a :: v₃ :: v₄ :: (M ++ [c]), H.Adj x y → y = a ∨ y = c)
    (hdeg : ∀ z ∈ S, H.Adj v₃ z → z = a ∨ z = v₄ ∨ z = u)
    (hN : T.NoSepTri H S (x :: a :: v₃ :: v₄ :: (M ++ [c])))
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: v₃ :: v₄ :: (M ++ [c])) a c L := by
  classical
  have hnd := T.nodup hNT
  have hPnd : (a :: v₃ :: v₄ :: (M ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: v₃ :: v₄ :: (M ++ [c]) := (List.nodup_cons.mp hnd).1
  have hav₃ : a ≠ v₃ := by rintro rfl; simp at hPnd
  have hav₄ : a ≠ v₄ := by rintro rfl; simp at hPnd
  have hv₃v₄ : v₃ ≠ v₄ := by rintro rfl; simp at hPnd
  have hv₃c : v₃ ≠ c := by rintro rfl; simp at hPnd
  have hv₃M : v₃ ∉ M := fun h => by simp [h] at hPnd
  have hv₃P : v₃ ∈ a :: v₃ :: v₄ :: (M ++ [c]) := by simp
  -- delete `v₃`
  have hrot : T.NT H S (v₃ :: v₄ :: (M ++ [c, x, a])) := by
    have := T.rotate_append (A := [x, a]) (B := v₃ :: v₄ :: (M ++ [c])) (by simpa using hNT)
    simpa using this
  have hlastl : (v₄ :: (M ++ [c, x, a])).getLast? = some a := by
    rw [show v₄ :: (M ++ [c, x, a]) = (v₄ :: M ++ [c, x]) ++ [a] by simp]
    exact List.getLast?_concat ..
  obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp) (by
    intro z hz hv₃z
    have hz' : z = a ∨ z = v₄ := by
      by_cases hzx : z = x
      · subst hzx
        rcases hxc v₃ hv₃P hv₃z.symm with h | h
        · exact absurd h hav₃.symm
        · exact absurd h hv₃c
      · have hzP : z ∈ a :: v₃ :: v₄ :: (M ++ [c]) := by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz ⊢; tauto
        have hcons := hPc v₃ z hv₃P hzP hv₃z
        rcases ConsecIn.nbr (A := [a]) (B := v₄ :: (M ++ [c])) hPnd hcons with h | h
        · simp at h; exact Or.inl h.symm
        · simp at h; exact Or.inr h.symm
    rcases hz' with rfl | rfl
    · exact Or.inr hlastl
    · exact Or.inl rfl)
  have hcyc : ∀ w, w ∉ v₃ :: v₄ :: (M ++ [c, x, a]) → w ∉ x :: a :: v₃ :: v₄ :: (M ++ [c]) := by
    intro w hw h; apply hw
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  have hus_u : ∀ w ∈ us, w = u := by
    intro w hw
    obtain ⟨hwS, hwn⟩ := hus w hw
    rcases hdeg w hwS (hadj w hw) with h | h | h
    · exact absurd (by simp [h]) hwn
    · exact absurd (by simp [h]) hwn
    · exact h
  have hus1 : us = [u] := by
    rcases us with _ | ⟨w, us'⟩
    · exfalso
      have h1 : T.NT H (S.erase v₃) ((M ++ [c, x, a]) ++ [v₄]) := T.rotate (by simpa using hNT')
      have h2 := (List.isChain_append.mp (NT_chain h1)).2.2 a
        (by rw [show M ++ [c, x, a] = (M ++ [c, x]) ++ [a] by simp]; exact List.getLast?_concat ..)
        v₄ rfl
      rcases hPc a v₄ (by simp) (by simp) h2 with ⟨-, e⟩ | ⟨e, -⟩ | h'
      · exact hv₃v₄ e.symm
      · exact hav₃ e
      · exact (List.nodup_cons.mp hPnd).1 (ConsecIn.mem h').1
    · have hw := hus_u w (by simp)
      subst hw
      rcases us' with _ | ⟨w', us''⟩
      · rfl
      · have := hus_u w' (by simp)
        subst this
        have hnd' := (List.nodup_append.mp (T.nodup hNT')).2.1
        simp at hnd'
  rw [hus1] at hNT' hnb hus hadj
  have huS : u ∈ S := (hus u (by simp)).1
  have hu : u ∉ x :: a :: v₃ :: v₄ :: (M ++ [c]) := hcyc u (hus u (by simp)).2
  have hv₃u : H.Adj v₃ u := hadj u (by simp)
  have hG' : T.NT H (S.erase v₃) (x :: a :: u :: v₄ :: (M ++ [c])) := by
    have := T.rotate_append (A := v₄ :: (M ++ [c])) (B := [x, a, u]) (by simpa using hNT')
    simpa using this
  have hchG := NT_chain hG'
  have hau : H.Adj a u := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchG).2).1
  have huv₄ : H.Adj u v₄ := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp
    (List.isChain_cons_cons.mp hchG).2).2).1
  -- `S − v₃` is a region of `G`
  have hRegE : Region H S (x :: a :: v₃ :: v₄ :: (M ++ [c])) (S.erase v₃)
      (x :: a :: u :: v₄ :: (M ++ [c])) := by
    refine ⟨Finset.erase_subset _ _, fun z hz hzc => ⟨?_, ?_⟩⟩
    · have hzv : z ≠ v₃ := Finset.ne_of_mem_erase hz
      intro h; apply hzc
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
    · intro w hw hzw
      refine Finset.mem_erase.mpr ⟨fun e => ?_, hw⟩
      subst e
      rcases hdeg z (Finset.mem_of_mem_erase hz) hzw.symm with h | h | h <;> exact hzc (by simp [h])
  -- the last neighbour `v_i` of `u` on the path
  obtain ⟨A, vi, B, hQ, huvi, hB⟩ := exists_last_mem (H.Adj u) (v₄ :: (M ++ [c]))
    ⟨v₄, by simp, huv₄⟩
  by_cases huc : H.Adj u c
  · exact T.claim4 H (M := v₃ :: v₄ :: M) hNT hh (by simp) huS hu hau.symm huc hPc hxc hN ih
  obtain ⟨B', rfl⟩ : ∃ B', B = B' ++ [c] := by
    rcases B.eq_nil_or_concat with rfl | ⟨B', b, rfl⟩
    · exfalso
      have hl := congrArg List.getLast? hQ
      rw [show v₄ :: (M ++ [c]) = (v₄ :: M) ++ [c] by simp, List.getLast?_concat,
        List.getLast?_concat] at hl
      simp only [Option.some.injEq] at hl
      exact huc (hl ▸ huvi)
    · have hl := congrArg List.getLast? hQ
      rw [show v₄ :: (M ++ [c]) = (v₄ :: M) ++ [c] by simp, List.getLast?_concat,
        show A ++ vi :: B'.concat b = (A ++ vi :: B') ++ [b] by simp, List.getLast?_concat] at hl
      simp only [Option.some.injEq] at hl
      exact ⟨B', by rw [hl]; simp⟩
  have hv₄mem : v₄ ∈ A ++ vi :: (B' ++ [c]) := hQ ▸ List.mem_cons_self
  rw [hQ] at hNT hh hPc hxc hN hG' hRegE hu hPnd hxP hv₃P ⊢
  -- Claim 3 on `a … v_i`
  have hP1 : a :: v₃ :: (A ++ vi :: (B' ++ [c])) = (a :: (v₃ :: A ++ [vi])) ++ (B' ++ [c]) := by
    simp
  rcases T.claim3 H (P₀ := []) (vi := a) (vj := vi) (M := v₃ :: A) (P₁ := B' ++ [c]) hNT hh
    (by simp) huS hu hau.symm huvi
    (by
      intro y z hy hz hyz
      have hy' : y ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
        rw [hP1]; exact List.mem_append_left _ hy
      have hz' : z ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
        rw [hP1]; exact List.mem_append_left _ hz
      have h := hPc y z hy' hz' hyz
      rw [hP1] at h
      exact ConsecIn.of_append_right (by rw [← hP1]; exact hPnd) hy hz h)
    hN ih with h | h | hall
  · exact Or.inl h
  · exact Or.inr h
  -- lists without two colours of `L(v₃) ∖ {c(v₂)}` at `u`
  have h3v₃ : 3 ≤ (L v₃).card := hh.three v₃ hv₃P (Ne.symm hav₃) hv₃c
  obtain ⟨α₁, hα₁, α₂, hα₂, hα₁₂⟩ := Finset.one_lt_card.mp
    (show 1 < ((L v₃).erase (g a)).card by
      have := Finset.pred_card_le_card_erase (s := L v₃) (a := g a); omega)
  let L' : V → Finset C := fun z => if z = u then ((L u).erase α₁).erase α₂ else L z
  have hL'u : L' u = ((L u).erase α₁).erase α₂ := by simp [L']
  have hL'ne : ∀ z, z ≠ u → L' z = L z := fun z hz => by simp [L', hz]
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  have h3u : 3 ≤ (L' u).card := by
    rw [hL'u]
    have := Finset.pred_card_le_card_erase (s := L u) (a := α₁)
    have := Finset.pred_card_le_card_erase (s := (L u).erase α₁) (a := α₂); omega
  -- split `G − v₃` along `u v_i` into the outside `S₁g` and the fan `S₂f`
  have hhuA : ∀ z ∈ A ++ [vi], H.Adj u z := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact hall z (List.mem_cons_of_mem _ h)
    · simp at h; subst h; exact huvi
  have hAP : ∀ z ∈ A, z ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := fun z hz => by simp [hz]
  have hviA : vi ∉ A := by
    intro h
    have : (A ++ vi :: (B' ++ [c])).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hPnd).2).2
    exact (List.nodup_append.mp this).2.2 vi h vi (by simp) rfl
  have huA : u ∉ A := fun h => hu (by simp [h])
  obtain ⟨S₁g, S₂f, h1g, hUg, hIg, hXg, hfill2, hReg1, hA1⟩ : ∃ S₁g S₂f : Finset V,
      T.NT H S₁g (x :: a :: u :: vi :: (B' ++ [c])) ∧ S₁g ∪ S₂f = S.erase v₃ ∧
      (∀ z, z ∈ S₁g → z ∈ S₂f → z = u ∨ z = vi) ∧
      (∀ p ∈ S₁g, ∀ q ∈ S₂f, H.Adj p q → p ∈ S₂f ∨ q ∈ S₁g) ∧
      (∀ z ∈ S₂f, z = u ∨ z ∈ A ∨ z = vi) ∧
      Region H S (x :: a :: v₃ :: (A ++ vi :: (B' ++ [c]))) S₁g
        (x :: a :: u :: vi :: (B' ++ [c])) ∧ (∀ z ∈ A, z ∉ S₁g) := by
    rcases A with _ | ⟨a₁, A'⟩
    · have huE : u ∈ S.erase v₃ := T.subset hG' u (by simp)
      have hviE : vi ∈ S.erase v₃ := T.subset hG' vi (by simp)
      refine ⟨S.erase v₃, {u, vi}, by simpa using hG', ?_, ?_, ?_, ?_, by simpa using hRegE,
        by simp⟩
      · apply Finset.union_eq_left.mpr
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact huE
        · exact hviE
      · intro z _ hz; simpa using hz
      · intro p _ q hq _
        right; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact huE
        · exact hviE
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · have hrotu : T.NT H (S.erase v₃) (u :: (a₁ :: A' ++ vi :: (B' ++ [c, x, a]))) := by
        have := T.rotate_append (A := [x, a]) (B := u :: (a₁ :: A' ++ vi :: (B' ++ [c])))
          (by simpa using hG')
        simpa using this
      obtain ⟨S₂f, S₁g, hf, h1, hU, hI, hX⟩ := T.chord (x := u) (y := vi) (l₁ := a₁ :: A')
        (l₂ := B' ++ [c, x, a]) hrotu (by simp) (by simp) huvi
      have h1' : T.NT H S₁g (x :: a :: u :: vi :: (B' ++ [c])) := by
        have := T.rotate_append (A := vi :: (B' ++ [c])) (B := [x, a, u]) (by simpa using h1)
        simpa using this
      have hmem : ∀ z, z ∈ S₂f → z ∈ S₁g → z = u ∨ z = vi := by
        intro z h2 h1
        have : z ∈ S₂f ∩ S₁g := Finset.mem_inter.mpr ⟨h2, h1⟩
        rw [hI] at this; simpa using this
      have hRf : Region H S (x :: a :: v₃ :: (a₁ :: A' ++ vi :: (B' ++ [c]))) S₂f
          (u :: (a₁ :: A' ++ [vi])) := by
        refine hRegE.piece (c₂ := x :: a :: u :: vi :: (B' ++ [c])) hU ?_ hX ?_
          (fun v hv => T.subset h1' v hv)
        · intro v h2 h1; rcases hmem v h2 h1 with rfl | rfl <;> simp
        · intro v hv
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
      have hRg : Region H S (x :: a :: v₃ :: (a₁ :: A' ++ vi :: (B' ++ [c]))) S₁g
          (x :: a :: u :: vi :: (B' ++ [c])) := by
        refine hRegE.piece' (c₁ := u :: (a₁ :: A' ++ [vi])) hU ?_ hX ?_
          (fun v hv => T.subset hf v hv)
        · intro v h2 h1; rcases hmem v h2 h1 with rfl | rfl <;> simp
        · intro v hv
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
      have hfill := fan_fill hN u _ (a₁ :: A' ++ [vi]) S₂f rfl hf hRf
        (List.IsChain.tail (NT_chain hf)) hhuA
      refine ⟨S₁g, S₂f, h1', by rw [Finset.union_comm]; exact hU, fun z h1 h2 => hmem z h2 h1,
        fun p hp q hq hpq => (hX q hq p hp hpq.symm).symm, ?_, hRg, ?_⟩
      · intro z hz
        rcases hfill z hz with h | h
        · exact Or.inl h
        · right
          simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr h
      · intro z hz h1
        rcases hmem z (T.subset hf z (List.mem_cons_of_mem _ (List.mem_append_left _ hz))) h1 with
          rfl | rfl
        · exact huA hz
        · exact hviA hz
  have hS1sub : S₁g ⊆ S.erase v₃ := hUg ▸ Finset.subset_union_left
  have hS2sub : S₂f ⊆ S.erase v₃ := hUg ▸ Finset.subset_union_right
  have hv₃S : v₃ ∈ S := T.subset hNT v₃ (by simp)
  have hcard : S₁g.card < S.card :=
    lt_of_le_of_lt (Finset.card_le_card hS1sub) (Finset.card_erase_lt_of_mem hv₃S)
  have hlast1 : (a :: u :: vi :: (B' ++ [c])).getLast? = some c :=
    getLast?_cons_append_singleton a c (u :: vi :: B')
  have hP' : ∀ y ∈ a :: u :: vi :: (B' ++ [c]), y ≠ u →
      y ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
    intro y hy hyu
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
  have hh1 : Thm3Hyp H S₁g x (a :: u :: vi :: (B' ++ [c])) a c L' g := by
    refine ⟨rfl, hlast1, by simp, hh.ok, ?_, ?_⟩
    · intro y hy hya hyc
      by_cases hyu : y = u
      · rw [hyu]; exact h3u
      · rw [hL'ne y hyu]; exact hh.three y (hP' y hy hyu) hya hyc
    · intro y hy hyc
      have hyu : y ≠ u := fun e => hyc (by simp [e])
      rw [hL'ne y hyu]
      exact hh.five y (Finset.mem_of_mem_erase (hS1sub hy)) (hReg1.2 y hy hyc).1
  have huS1 : u ∈ S₁g := T.subset h1g u (by simp)
  have hviS1 : vi ∈ S₁g := T.subset h1g vi (by simp)
  rcases ih H S₁g hcard x _ a c L' g h1g hh1 with hE | hE
  · left
    obtain ⟨f₁, h1c, h1L, h1p⟩ := hE
    have hAP' : (A ++ vi :: (B' ++ [c])).Nodup :=
      (List.nodup_cons.mp (List.nodup_cons.mp hPnd).2).2
    have hAnd : A.Nodup := (List.nodup_append.mp hAP').1
    have haA : a ∉ A := fun h => (List.nodup_cons.mp hPnd).1 (by simp [h])
    have hcA : c ∉ A := fun h => (List.nodup_append.mp hAP').2.2 c h c (by simp) rfl
    have h3A : ∀ y ∈ A, 3 ≤ (L y).card := fun y hy =>
      hh.three y (hAP y hy) (fun e => haA (e ▸ hy)) (fun e => hcA (e ▸ hy))
    obtain ⟨φ, hφ, hφe, hφc⟩ := path_colour L (f₁ u) A (f₁ vi) hAnd (fun y hy => by
      have := Finset.pred_card_le_card_erase (s := L y) (a := f₁ u)
      have := h3A y hy; omega)
    let F : V → C := fun z => if z ∈ A then φ z else f₁ z
    have FA : ∀ z ∈ A, F z = φ z := fun z hz => by simp only [F, hz, ite_true]
    have Fn : ∀ z, z ∉ A → F z = f₁ z := fun z hz => by simp only [F, hz, ite_false]
    -- the fan is properly coloured
    have eP : a :: v₃ :: (A ++ vi :: (B' ++ [c])) = [a, v₃] ++ (A ++ [vi]) ++ (B' ++ [c]) := by
      simp
    have hcAvi : ∀ y z, y ∈ A ++ [vi] → z ∈ A ++ [vi] → H.Adj y z → ConsecIn (A ++ [vi]) y z := by
      intro y z hy hz hyz
      have hy' : y ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
        rw [eP]; exact List.mem_append_left _ (List.mem_append_right _ hy)
      have hz' : z ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
        rw [eP]; exact List.mem_append_left _ (List.mem_append_right _ hz)
      have h := hPc y z hy' hz' hyz
      rw [eP] at h
      exact ConsecIn.infix (by rw [← eP]; exact hPnd) hy hz h
    have hchF : (A ++ [vi]).IsChain (fun y z => F y ≠ F z) := by
      rw [List.isChain_append]
      refine ⟨isChain_congr (fun p hp q hq hpq => by rw [FA p hp, FA q hq]; exact hpq) hφc,
        by simp, ?_⟩
      intro p hp q hq
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      rw [FA p (List.mem_of_mem_getLast? hp), Fn vi hviA]; exact hφe p hp
    have hFu : ∀ q ∈ S₂f, q ≠ u → H.Adj u q → F u ≠ F q := by
      intro q hq hqu huq
      rw [Fn u huA]
      rcases hfill2 q hq with h | h | h
      · exact absurd h hqu
      · rw [FA q h]; exact (hφ q h).2.symm
      · subst h; rw [Fn q hviA]; exact h1p u huS1 q hviS1 huq
    have hF2 : IsProperOn H S₂f F := by
      intro p hp q hq hpq
      by_cases hpu : p = u
      · subst hpu
        exact hFu q hq (fun e => H.loopless.irrefl _ (e ▸ hpq)) hpq
      by_cases hqu : q = u
      · subst hqu
        exact (hFu p hp hpu hpq.symm).symm
      have hp' : p ∈ A ++ [vi] := by
        rcases hfill2 p hp with h | h | h
        · exact absurd h hpu
        · exact List.mem_append_left _ h
        · simp [h]
      have hq' : q ∈ A ++ [vi] := by
        rcases hfill2 q hq with h | h | h
        · exact absurd h hqu
        · exact List.mem_append_left _ h
        · simp [h]
      rcases (hcAvi p q hp' hq' hpq).chain hchF with h | h
      · exact h
      · exact Ne.symm h
    have hGp := isProperOn_glue hUg hXg h1p hF2 (fun z h1 h2 => by
      rcases hIg z h1 h2 with rfl | rfl
      · exact Fn z huA
      · exact Fn z hviA)
    set G : V → C := fun z => if z ∈ S₁g then f₁ z else F z with hGdef
    have G1 : ∀ z ∈ S₁g, G z = f₁ z := fun z hz => by simp only [hGdef, hz, ite_true]
    -- colour `v₃`
    have hGu : G u ∈ L' u := by
      rw [G1 u huS1]
      exact h1L u huS1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hu (by simp [e]), fun e => hu (by simp [e]), fun e => hu (by simp [e])⟩)
    have hGuα : G u ≠ α₁ ∧ G u ≠ α₂ := by
      rw [hL'u] at hGu
      exact ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hGu), Finset.ne_of_mem_erase hGu⟩
    have haS1 : a ∈ S₁g := T.subset h1g a (by simp)
    have hGa : G a = g a := by rw [G1 a haS1]; exact h1c a (by simp)
    obtain ⟨col, hcolL, hcola, hcolu, hcolv₄⟩ :
        ∃ col, col ∈ L v₃ ∧ col ≠ g a ∧ col ≠ G u ∧ col ≠ G v₄ := by
      by_cases h : α₁ = G v₄
      · exact ⟨α₂, Finset.mem_of_mem_erase hα₂, Finset.ne_of_mem_erase hα₂,
          fun e => hGuα.2 e.symm, fun e => hα₁₂ (h.trans e.symm)⟩
      · exact ⟨α₁, Finset.mem_of_mem_erase hα₁, Finset.ne_of_mem_erase hα₁,
          fun e => hGuα.1 e.symm, h⟩
    refine ⟨Function.update G v₃ col, ?_, ?_, isProperOn_update hGp ?_⟩
    · intro z hz
      have hzS1 : z ∈ S₁g := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h | h <;> rw [h] <;> exact T.subset h1g _ (by simp)
      have hzv : z ≠ v₃ := fun e => Finset.ne_of_mem_erase (hS1sub hzS1) e
      rw [Function.update_of_ne hzv, G1 z hzS1]; exact h1c z hz
    · intro z hz hzc
      by_cases hzv : z = v₃
      · rw [hzv, Function.update_self]; exact hcolL
      · rw [Function.update_of_ne hzv]
        have hzE : z ∈ S.erase v₃ := Finset.mem_erase.mpr ⟨hzv, hz⟩
        by_cases hz1 : z ∈ S₁g
        · rw [G1 z hz1]
          have := h1L z hz1 hzc
          by_cases hzu : z = u
          · rw [hzu, hL'u] at this; rw [hzu]
            exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
          · rwa [hL'ne z hzu] at this
        · have hz2 : z ∈ S₂f := (Finset.mem_union.mp (hUg ▸ hzE)).resolve_left hz1
          have hzA : z ∈ A := by
            rcases hfill2 z hz2 with h | h | h
            · exact absurd (h ▸ huS1) hz1
            · exact h
            · exact absurd (h ▸ hviS1) hz1
          simp only [hGdef, hz1, ite_false]; rw [FA z hzA]; exact (hφ z hzA).1
    · intro w hw hvw
      rcases hdeg w hw hvw with h | h | h
      · rw [h, hGa]; exact Ne.symm hcola
      · rw [h]; exact Ne.symm hcolv₄
      · rw [h]; exact Ne.symm hcolu
  · -- the outside is exceptional: it is a generalized wheel
    obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, -⟩ := hE
    have hQ1nd : (a :: u :: vi :: (B' ++ [c])).Nodup := (List.nodup_cons.mp (T.nodup h1g)).2
    have eP2 : a :: v₃ :: (A ++ vi :: (B' ++ [c])) = (a :: v₃ :: A) ++ (vi :: (B' ++ [c])) := by
      simp
    have hRP : ∀ z ∈ vi :: (B' ++ [c]), z ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
      intro z hz; rw [eP2]; exact List.mem_append_right _ hz
    have hsuf : ∀ y z, y ∈ vi :: (B' ++ [c]) → z ∈ vi :: (B' ++ [c]) → H.Adj y z →
        ConsecIn (vi :: (B' ++ [c])) y z := by
      intro y z hy hz hyz
      have h := hPc y z (hRP y hy) (hRP z hz) hyz
      rw [eP2] at h
      exact ConsecIn.of_append_left (by rw [← eP2]; exact hPnd) hy hz h
    have hv₃R : v₃ ∉ vi :: (B' ++ [c]) := by
      intro h
      have := (List.nodup_cons.mp (List.nodup_cons.mp hPnd).2).1
      exact this (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
    have hnota : ∀ z ∈ vi :: (B' ++ [c]), ¬ H.Adj a z := by
      intro z hz haz
      have h := hPc a z (by simp) (hRP z hz) haz
      rcases ConsecIn.nbr (A := []) (B := v₃ :: (A ++ vi :: (B' ++ [c]))) hPnd h with h1 | h1
      · simp at h1
      · simp only [List.head?_cons, Option.some.injEq] at h1
        exact hv₃R (h1 ▸ hz)
    have hcls : ∀ w ∈ a :: u :: vi :: (B' ++ [c]), w = a ∨ w = u ∨ w ∈ vi :: (B' ++ [c]) := by
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (List.mem_cons.mpr h))
    have hQ1c : ∀ y z, y ∈ a :: u :: vi :: (B' ++ [c]) → z ∈ a :: u :: vi :: (B' ++ [c]) →
        H.Adj y z → ConsecIn (a :: u :: vi :: (B' ++ [c])) y z := by
      intro y z hy hz hyz
      rcases hcls y hy with h1 | h1 | h1 <;> rcases hcls z hz with h2 | h2 | h2
      · rw [h1, h2] at hyz; exact absurd hyz (H.loopless.irrefl _)
      · exact Or.inl ⟨h1, h2⟩
      · rw [h1] at hyz; exact absurd hyz (hnota z h2)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · rw [h1, h2] at hyz; exact absurd hyz (H.loopless.irrefl _)
      · rcases List.mem_cons.mp h2 with h3 | h3
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h3⟩))
        · rw [h1] at hyz; exact absurd hyz (hB z h3)
      · rw [h2] at hyz; exact absurd hyz.symm (hnota y h1)
      · rcases List.mem_cons.mp h1 with h3 | h3
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h2⟩)))
        · rw [h2] at hyz; exact absurd hyz.symm (hB y h3)
      · exact ConsecIn.append_left (A := [a, u]) (hsuf y z h1 h2 hyz)
    have hPW : PW = a :: u :: vi :: (B' ++ [c]) :=
      path_eq_of_chordless _ _ hQ1nd hndW hsubW (by rw [hhW]; rfl) (by rw [hlW, hlast1])
        hGW.isPath hQ1c
    subst hPW
    obtain ⟨hfill1, hGW3⟩ := gw_fill hN hGW h1g hReg1 hUW
    have hwP : ∀ w ∈ U, w ∈ S ∧ w ∉ x :: a :: v₃ :: (A ++ vi :: (B' ++ [c])) := fun w hw =>
      ⟨Finset.mem_of_mem_erase (hS1sub (hUW w hw).1), (hReg1.2 w (hUW w hw).1 (hUW w hw).2).1⟩
    have hxQ1 : ∀ b ∈ a :: u :: vi :: (B' ++ [c]), H.Adj x b → b = a ∨ b = u ∨ b = c := by
      intro b hb hxb
      by_cases hbu : b = u
      · exact Or.inr (Or.inl hbu)
      · rcases hxc b (hP' b hb hbu) hxb with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    -- the generalized wheel has one junction, at `u`
    have hstruct : (∃ w ∈ U, H.Adj w a ∧ H.Adj w c) ∨
        (∃ w, U = {w} ∧ ∀ y ∈ u :: vi :: (B' ++ [c]), H.Adj w y) := by
      generalize hQg : a :: u :: vi :: (B' ++ [c]) = Q at hGW3
      cases hGW3 with
      | one hB =>
        cases hB with
        | tri => simp at hQg
        | wheel _ _ _ hwall _ _ _ =>
          left
          exact ⟨_, Finset.mem_singleton_self _, hwall a (by rw [← hQg]; simp),
            hwall c (by rw [← hQg]; simp)⟩
      | @cons P₁ Q₂ b U₁ U₂ hB hrest =>
        have hP₁ : P₁ ≠ [] := fun h => by subst h; have := hB.two_le; simp at this
        have hQ₂ : Q₂ ≠ [] := fun h => by subst h; have := hrest.two_le; simp at this
        have hxb : H.Adj x b := hB.adj_last b (by simp)
        have hbQ : b ∈ a :: u :: vi :: (B' ++ [c]) := by rw [hQg]; simp
        have hnd' : (P₁ ++ b :: Q₂).Nodup := hQg ▸ hQ1nd
        obtain ⟨hba, hbc⟩ := junction_inner hnd' hP₁ hQ₂ (by rw [← hQg]; rfl)
          (by rw [← hQg]; exact hlast1)
        have hbu : b = u := by
          rcases hxQ1 b hbQ hxb with h | h | h
          · exact absurd h hba
          · exact h
          · exact absurd h hbc
        obtain ⟨p, P₁', rfl⟩ := List.exists_cons_of_ne_nil hP₁
        simp only [List.cons_append, List.cons.injEq] at hQg
        obtain ⟨hap, hQg'⟩ := hQg
        have hP₁' : P₁' = [] := by
          rcases P₁' with _ | ⟨q, P₁''⟩
          · rfl
          · exfalso
            simp only [List.cons_append, List.cons.injEq] at hQg'
            have : b ∈ vi :: (B' ++ [c]) := by rw [hQg'.2]; simp
            rw [hbu] at this
            exact (List.nodup_cons.mp (List.nodup_cons.mp hQ1nd).2).1 this
        subst hP₁'
        simp only [List.nil_append, List.cons.injEq] at hQg'
        obtain ⟨-, hQ₂eq⟩ := hQg'
        subst hQ₂eq
        have hU₁ : U₁ = ∅ := hB.empty_of_two (le_refl 3) (by simp)
        rw [hbu] at hrest
        generalize hQr : u :: vi :: (B' ++ [c]) = Qr at hrest
        cases hrest with
        | one hB' =>
          cases hB' with
          | tri => simp at hQr
          | wheel _ _ _ hwall _ _ _ =>
            right
            exact ⟨_, by simp [hU₁], fun y hy => hwall y (hQr ▸ hy)⟩
        | @cons P₂ Q₃ b' U₃ U₄ hB'' hrest' =>
          exfalso
          have hP₂ : P₂ ≠ [] := fun h => by subst h; have := hB''.two_le; simp at this
          have hQ₃ : Q₃ ≠ [] := fun h => by subst h; have := hrest'.two_le; simp at this
          have hxb' : H.Adj x b' := hB''.adj_last b' (by simp)
          have hnd'' : (P₂ ++ b' :: Q₃).Nodup := hQr ▸ (List.nodup_cons.mp hQ1nd).2
          obtain ⟨hbh, hbl⟩ := junction_inner hnd'' hP₂ hQ₃ (by rw [← hQr]; rfl)
            (by rw [← hQr]; exact getLast?_cons_append_singleton u c (vi :: B'))
          have hb'R : b' ∈ u :: vi :: (B' ++ [c]) := by rw [hQr]; simp
          rcases hxQ1 b' (List.mem_cons_of_mem _ hb'R) hxb' with h | h | h
          · rw [h] at hb'R; exact (List.nodup_cons.mp hQ1nd).1 hb'R
          · exact hbh h
          · exact hbl h
    have claim4w : ∀ w, w ∈ S → w ∉ x :: a :: v₃ :: (A ++ vi :: (B' ++ [c])) → H.Adj w a →
        H.Adj w c → Extends H S [c, x, a] L g ∨
          Exc3 H S x (a :: v₃ :: (A ++ vi :: (B' ++ [c]))) a c L := by
      intro w hwS hwn hwa hwc
      have e : a :: v₃ :: (A ++ vi :: (B' ++ [c])) = a :: ((v₃ :: (A ++ vi :: B')) ++ [c]) := by
        simp
      rw [e] at hNT hh hPc hxc hN hwn ⊢
      exact T.claim4 H hNT hh (by simp) hwS hwn hwa hwc hPc hxc hN ih
    rcases hstruct with ⟨w, hwU, hwa, hwc⟩ | ⟨w, hUw, hwall⟩
    · exact claim4w w (hwP w hwU).1 (hwP w hwU).2 hwa hwc
    subst hUw
    have hwS := (hwP w (by simp)).1
    have hwnP := (hwP w (by simp)).2
    by_cases hwa : H.Adj w a
    · exact claim4w w hwS hwnP hwa (hwall c (by simp))
    left
    have hwS1 : w ∈ S₁g := (hUW w (by simp)).1
    have hwQ1 : w ∉ x :: a :: u :: vi :: (B' ++ [c]) := (hUW w (by simp)).2
    have hwS2 : w ∉ S₂f := fun h => by
      rcases hIg w hwS1 h with e | e <;> exact hwQ1 (by simp [e])
    have hv₄P : v₄ ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv₄mem)
    have hPnd2 : ((a :: (v₃ :: A ++ vi :: B')) ++ [c]).Nodup := by simpa using hPnd
    have h3' : ∀ y ∈ v₃ :: A ++ vi :: B', 3 ≤ (L y).card := by
      intro y hy
      have hyP : y ∈ a :: v₃ :: (A ++ vi :: (B' ++ [c])) := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
      apply hh.three y hyP
      · intro e
        exact (List.nodup_cons.mp (List.nodup_append.mp hPnd2).1).1 (e ▸ hy)
      · intro e
        exact (List.nodup_append.mp hPnd2).2.2 y (List.mem_cons_of_mem _ hy) c (by simp) e
    refine dfan H (m₁ := v₃) (RL := A) (PR := B') ?_ ?_ hPc hxc hB ?_ L g hh.ok.1 hh.ok.2.1 h3'
      h5u (hh.five w hwS hwnP)
    · intro z hz
      by_cases hzv : z = v₃
      · right; right; right; rw [hzv]; simp
      have hzE : z ∈ S.erase v₃ := Finset.mem_erase.mpr ⟨hzv, hz⟩
      rcases Finset.mem_union.mp (hUg ▸ hzE) with h1 | h2
      · rcases hfill1 z h1 with h | h | h
        · exact Or.inl h
        · by_cases hzu : z = u
          · exact Or.inr (Or.inl hzu)
          · exact Or.inr (Or.inr (Or.inr (hP' z h hzu)))
        · simp only [Finset.mem_singleton] at h
          exact Or.inr (Or.inr (Or.inl h))
      · rcases hfill2 z h2 with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (by simp [h])))
        · exact Or.inr (Or.inr (Or.inr (by simp [h])))
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hPnd⟩⟩⟩
      · intro h
        rcases List.mem_cons.mp h with e | h
        · exact hu (by simp [← e])
        · rcases List.mem_cons.mp h with e | h
          · exact hwQ1 (by simp [← e])
          · exact hxP h
      · intro h
        rcases List.mem_cons.mp h with e | h
        · exact hwQ1 (by simp [← e])
        · exact hu (List.mem_cons_of_mem _ h)
      · intro h; exact hwnP (List.mem_cons_of_mem _ h)
    · intro z hz hwz
      simp only [List.mem_cons] at hz
      rcases hz with h | h | h
      · rw [h] at hwz; exact hwa hwz
      · rw [h] at hwz
        rcases hdeg w hwS hwz.symm with e | e | e
        · exact hwQ1 (by simp [e])
        · exact hwnP (by rw [e]; exact List.mem_cons_of_mem _ hv₄P)
        · exact hwQ1 (by simp [e])
      · have hzE : z ∈ S.erase v₃ := T.subset hG' z (by simp [h])
        have hz2 : z ∈ S₂f := (Finset.mem_union.mp (hUg ▸ hzE)).resolve_left (hA1 z h)
        rcases hXg w hwS1 z hz2 hwz with h' | h'
        · exact hwS2 h'
        · exact hA1 z h h'

omit [DecidableEq V] in
/-- Regions only depend on the vertex set of the outer cycle of `G`. -/
theorem region_congr {H : SimpleGraph V} {S₀ S : Finset V} {C₀ C₀' c : List V}
    (hC : ∀ v, v ∈ C₀ ↔ v ∈ C₀') (h : Region H S₀ C₀ S c) : Region H S₀ C₀' S c :=
  ⟨h.1, fun u hu huc => ⟨fun h' => (h.2 u hu huc).1 ((hC u).2 h'), (h.2 u hu huc).2⟩⟩

theorem noSepTri_congr {H : SimpleGraph V} {S : Finset V} {C₀ C₀' : List V}
    (hC : ∀ v, v ∈ C₀ ↔ v ∈ C₀') (h : T.NoSepTri H S C₀) : T.NoSepTri H S C₀' :=
  fun S₁ p q r h1 hR => h S₁ p q r h1 (region_congr (fun v => (hC v).symm) hR)

/-- **Claim 6** (the mirror image of Claim 5): if `v_{k-1}` has at most one neighbour off the
outer cycle, the conclusion of Theorem 3 holds. -/
theorem claim6 (H : SimpleGraph V) {S : Finset V} {x a w₃ w₄ c u : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: (M ++ [w₄, w₃, c])))
    (hh : Thm3Hyp H S x (a :: (M ++ [w₄, w₃, c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: (M ++ [w₄, w₃, c]) → z ∈ a :: (M ++ [w₄, w₃, c]) →
      H.Adj y z → ConsecIn (a :: (M ++ [w₄, w₃, c])) y z)
    (hxc : ∀ y ∈ a :: (M ++ [w₄, w₃, c]), H.Adj x y → y = a ∨ y = c)
    (hdeg : ∀ z ∈ S, H.Adj w₃ z → z = c ∨ z = w₄ ∨ z = u)
    (hN : T.NoSepTri H S (x :: a :: (M ++ [w₄, w₃, c])))
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: (M ++ [w₄, w₃, c])) a c L := by
  have hrev : (a :: (M ++ [w₄, w₃, c])).reverse = c :: w₃ :: w₄ :: (M.reverse ++ [a]) := by simp
  have hmem : ∀ y, y ∈ c :: w₃ :: w₄ :: (M.reverse ++ [a]) ↔ y ∈ a :: (M ++ [w₄, w₃, c]) := by
    intro y; rw [← hrev, List.mem_reverse]
  have hNT' : T.NT H S (x :: c :: w₃ :: w₄ :: (M.reverse ++ [a])) := by
    rw [← hrev]
    exact T.rotate_back (by simpa using T.reverse hNT)
  have hh' : Thm3Hyp H S x (c :: w₃ :: w₄ :: (M.reverse ++ [a])) c a L g := by
    refine ⟨rfl, getLast?_cons_append_singleton c a (w₃ :: w₄ :: M.reverse), by simp,
      ⟨hh.ok.2.1, hh.ok.1, fun h => (hh.ok.2.2 h.symm).symm⟩, ?_, ?_⟩
    · intro y hy hyc hya
      exact hh.three y ((hmem y).1 hy) hya hyc
    · intro y hy hyc
      exact hh.five y hy (fun h => hyc (by
        rcases List.mem_cons.mp h with e | h
        · exact e ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((hmem y).2 h)))
  have hPc' : ∀ y z, y ∈ c :: w₃ :: w₄ :: (M.reverse ++ [a]) →
      z ∈ c :: w₃ :: w₄ :: (M.reverse ++ [a]) → H.Adj y z →
      ConsecIn (c :: w₃ :: w₄ :: (M.reverse ++ [a])) y z := by
    intro y z hy hz hyz
    rw [← hrev]
    exact (hPc y z ((hmem y).1 hy) ((hmem z).1 hz) hyz).reverse
  have hxc' : ∀ y ∈ c :: w₃ :: w₄ :: (M.reverse ++ [a]), H.Adj x y → y = c ∨ y = a := by
    intro y hy hxy
    exact (hxc y ((hmem y).1 hy) hxy).symm
  have hcyc : ∀ v, v ∈ x :: a :: (M ++ [w₄, w₃, c]) ↔ v ∈ x :: c :: w₃ :: w₄ :: (M.reverse ++ [a]) := by
    intro v
    simp only [List.mem_cons (b := x)]
    rw [hmem v]
  rcases T.claim5 H hNT' hh' hPc' hxc' hdeg (T.noSepTri_congr hcyc hN) ih with h | h
  · exact Or.inl (extends_of_mem_iff (fun v => by simp; tauto) h)
  · exact Or.inr (exc3_reverse hmem h)

end NTCalc

end ThomassenManyColourings
