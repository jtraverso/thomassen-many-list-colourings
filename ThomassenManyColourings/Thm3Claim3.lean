/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Fill

/-!
# Theorem 3, Claim 3: a vertex joined to `v_i, v_j` is joined to everything between

If an interior vertex `u` is joined to `v_i` and `v_j` (with at least one vertex between them on
the outer path), cut along `v_i u v_j`. The inside `Int` has at most one bad precolouring of
`v_j u v_i` unless it is a broken wheel (Lemma 1, after `gw_fill`), so deleting that colour from
`L(u)` and applying the induction hypothesis to the outside gives the conclusion of Theorem 3.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Claim 3**, as a reduction: either the conclusion of Theorem 3 holds, or `u` is joined to
every vertex strictly between `v_i` and `v_j`. -/
theorem claim3 (H : SimpleGraph V) {S : Finset V} {x u vi vj : V} {P₀ M P₁ : List V} {a c : V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (P₀ ++ vi :: (M ++ vj :: P₁))))
    (hh : Thm3Hyp H S x (P₀ ++ vi :: (M ++ vj :: P₁)) a c L g) (hM : M ≠ [])
    (huS : u ∈ S) (hu : u ∉ x :: (P₀ ++ vi :: (M ++ vj :: P₁)))
    (hui : H.Adj u vi) (huj : H.Adj u vj)
    (hQc : ∀ y z, y ∈ vi :: (M ++ [vj]) → z ∈ vi :: (M ++ [vj]) → H.Adj y z →
      ConsecIn (vi :: (M ++ [vj])) y z)
    (hN : T.NoSepTri H S (x :: (P₀ ++ vi :: (M ++ vj :: P₁))))
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (P₀ ++ vi :: (M ++ vj :: P₁)) a c L ∨
      ∀ m ∈ M, H.Adj u m := by
  classical
  -- cutting along `vi u vj`
  have hrot : T.NT H S (vi :: (M ++ vj :: (P₁ ++ x :: P₀))) := by
    have := T.rotate_append (A := x :: P₀) (B := vi :: (M ++ vj :: P₁)) (by simpa using hNT)
    simpa using this
  have hQnd0 : (vi :: (M ++ [vj])).Nodup := (T.nodup hrot).sublist
    (by simpa using List.Sublist.cons₂ vi (List.Sublist.append_left
      (List.singleton_sublist.mpr (List.mem_cons_self (a := vj) (l := P₁ ++ x :: P₀))) M))
  have hvivj : ¬ H.Adj vi vj := fun h =>
    ConsecIn.not_ends hM hQnd0 (hQc vi vj (by simp) (by simp) h)
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := vi) (y := vj) (u := u) (l₁ := M)
    (l₂ := P₁ ++ x :: P₀) hrot huS
    (by simp only [List.mem_cons, List.mem_append, not_or] at hu ⊢; tauto) hui huj hvivj
  have hInt : T.NT H S₁ (u :: (vi :: (M ++ [vj]))) := T.rotate_back (by simpa using h₁)
  have hExt : T.NT H S₂ (x :: (P₀ ++ vi :: u :: vj :: P₁)) := by
    have := T.rotate_append (A := vj :: P₁) (B := x :: (P₀ ++ [vi, u])) (by simpa using h₂)
    simpa using this
  have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = vi ∨ v = vj ∨ v = u := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : ∀ v ∈ S₁, v ∈ S := fun v hv => hU ▸ Finset.mem_union_left _ hv
  have hS₂ : ∀ v ∈ S₂, v ∈ S := fun v hv => hU ▸ Finset.mem_union_right _ hv
  have hside : ∀ v ∈ S, v ∉ S₂ → v ∈ S₁ := fun v hv h2 =>
    (Finset.mem_union.mp (hU ▸ hv)).resolve_right h2
  -- repetition-freeness of the outer cycle
  have hnd := T.nodup hNT
  have hnd0 := List.nodup_cons.mp hnd
  have hA := List.nodup_append.mp hnd0.2
  have hB := List.nodup_cons.mp hA.2.1
  have hC := List.nodup_append.mp hB.2
  have hviM : vi ∉ M := fun h => hB.1 (List.mem_append_left _ h)
  have hvjM : vj ∉ M := fun h => hC.2.2 vj h vj (by simp) rfl
  have huM : u ∉ M := fun h => hu (by simp [h])
  have hxM : x ∉ M := fun h => hnd0.1 (by simp [h])
  have hxvi : x ≠ vi := fun h => hnd0.1 (by simp [h])
  have hxvj : x ≠ vj := fun h => hnd0.1 (by simp [h])
  have hxu : x ≠ u := fun h => hu (by simp [h])
  have haP : a ∈ P₀ ++ [vi] := by
    have := hh.head
    rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ [vi]) ++ (M ++ vj :: P₁) by simp,
      List.head?_append_of_ne_nil _ (by simp)] at this
    exact List.mem_of_mem_head? this
  have hcP : c ∈ vj :: P₁ := by
    have := hh.last
    rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ vi :: M) ++ (vj :: P₁) by simp,
      List.getLast?_append_of_ne_nil _ (by simp)] at this
    exact List.mem_of_mem_getLast? this
  have haM : a ∉ M := by
    intro h
    rcases List.mem_append.mp haP with h' | h'
    · exact hA.2.2 a h' a (by simp [h]) rfl
    · simp at h'; exact hviM (h' ▸ h)
  have hcM : c ∉ M := fun h => hC.2.2 c h c hcP rfl
  have hua : u ≠ a := fun h => hu (by
    rcases List.mem_append.mp haP with h' | h'
    · simp [h ▸ h']
    · simp at h'; simp [h, h'])
  have huc : u ≠ c := fun h => hu (by
    rcases List.mem_cons.mp hcP with h' | h'
    · simp [h, h']
    · simp [h ▸ h'])
  have hMside : ∀ m ∈ M, m ∈ S₁ ∧ m ∉ S₂ := by
    intro m hm
    have h1 : m ∈ S₁ := T.subset hInt m (by simp [hm])
    refine ⟨h1, fun h2 => ?_⟩
    rcases hmem m h1 h2 with rfl | rfl | rfl
    · exact hviM hm
    · exact hvjM hm
    · exact huM hm
  have hxS₂ : x ∈ S₂ := T.subset hExt x (by simp)
  have huS₂ : u ∈ S₂ := T.subset hExt u (by simp)
  have hviS₂ : vi ∈ S₂ := T.subset hExt vi (by simp)
  have hvjS₂ : vj ∈ S₂ := T.subset hExt vj (by simp)
  have hxS₁ : x ∉ S₁ := fun h1 => by
    rcases hmem x h1 hxS₂ with h | h | h
    · exact hxvi h
    · exact hxvj h
    · exact hxu h
  have hcard₁ : S₁.card < S.card :=
    Finset.card_lt_card ⟨fun v hv => hS₁ v hv, fun h => hxS₁ (h (hS₂ x hxS₂))⟩
  obtain ⟨m₀, hm₀⟩ := List.exists_mem_of_ne_nil M hM
  have hcard₂ : S₂.card < S.card :=
    Finset.card_lt_card ⟨fun v hv => hS₂ v hv, fun h => (hMside m₀ hm₀).2 (h (hS₁ m₀ (hMside m₀ hm₀).1))⟩
  -- vertices of the inside off its outer cycle are interior vertices of `G`
  have hInt_out : ∀ w ∈ S₁, w ∉ u :: (vi :: (M ++ [vj])) →
      w ∉ x :: (P₀ ++ vi :: (M ++ vj :: P₁)) := by
    intro w hw hwc hwP
    by_cases hwM : w ∈ M
    · exact hwc (by simp [hwM])
    · have h2 : w ∈ S₂ := T.subset hExt w (by
        simp only [List.mem_cons, List.mem_append] at hwP ⊢; tauto)
      rcases hmem w hw h2 with rfl | rfl | rfl <;> simp at hwc
  have hExt_out : ∀ w ∈ S₂, w ∉ x :: (P₀ ++ vi :: u :: vj :: P₁) →
      w ∉ x :: (P₀ ++ vi :: (M ++ vj :: P₁)) := by
    intro w hw hwc hwP
    by_cases hwM : w ∈ M
    · exact (hMside w hwM).2 hw
    · apply hwc
      simp only [List.mem_cons, List.mem_append] at hwP ⊢; tauto
  have hthreeM : ∀ y ∈ M, 3 ≤ (L y).card := fun y hy =>
    hh.three y (by simp [hy]) (fun h => haM (h ▸ hy)) (fun h => hcM (h ▸ hy))
  have hQl : (vi :: (M ++ [vj])).getLast? = some vj := by
    rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  have hypInt : ∀ h : V → C, PathOK H u vi vj h →
      Thm3Hyp H S₁ u (vi :: (M ++ [vj])) vi vj L h := by
    intro h hok
    refine ⟨rfl, hQl, by simp, hok, ?_, ?_⟩
    · intro y hy hyi hyj
      have hyM : y ∈ M := by simp only [List.mem_cons, List.mem_append] at hy; tauto
      exact hthreeM y hyM
    · intro y hy hyc
      exact hh.five y (hS₁ y hy) (hInt_out y hy hyc)
  -- the inside is a region of `G`
  have hRegInt : Region H S (x :: (P₀ ++ vi :: (M ++ vj :: P₁))) S₁ (u :: (vi :: (M ++ [vj]))) := by
    refine (Region.refl H S _).piece (c₂ := x :: (P₀ ++ vi :: u :: vj :: P₁)) hU ?_ hX ?_
      (fun v hv => T.subset hExt v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
  -- at most one bad colour at `u`, unless `u` is joined to all of `M`
  have hcol : (∀ m ∈ M, H.Adj u m) ∨ ∃ col : C, ∀ h : V → C, PathOK H u vi vj h →
      ¬ Extends H S₁ [vj, u, vi] L h → h u = col := by
    by_cases hE3 : Exc3 H S₁ u (vi :: (M ++ [vj])) vi vj L
    · obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := hE3
      have hQnd : (vi :: (M ++ [vj])).Nodup := (List.nodup_cons.mp (T.nodup hInt)).2
      have hPW : PW = vi :: (M ++ [vj]) :=
        path_eq_of_chordless _ _ hQnd hndW hsubW (by rw [hhW]; rfl) (by rw [hlW, hQl])
          hGW.isPath hQc
      subst hPW
      by_cases hU0 : U = ∅
      · left; intro m hm; exact hGW.broken_adj hU0 m (by simp [hm])
      · right
        have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU0
        obtain ⟨hfill, hGW3⟩ := gw_fill hN hGW hInt hRegInt hUW
        have hBU := T.lemma1 H u _ _ U rfl hGW3 hUne S₁ vi vj rfl hQl hInt hfill hUW L
          (fun w hw => hh.five w (hS₁ w (hUW w hw).1) (hInt_out w (hUW w hw).1 (hUW w hw).2))
          (fun y hy hyi hyj => hthreeM y (by
            simp only [List.mem_cons, List.mem_append] at hy; tauto))
        by_cases hex : ∃ h₀ : V → C, PathOK H u vi vj h₀ ∧ ¬ Extends H S₁ [vj, u, vi] L h₀
        · obtain ⟨h₀, hok₀, hne₀⟩ := hex
          exact ⟨h₀ u, fun h hok hne => (hBU h h₀ hok hok₀ hne hne₀).1⟩
        · push Not at hex
          exact ⟨g u, fun h hok hne => absurd (hex h hok) hne⟩
    · right
      refine ⟨g u, fun h hok hne => ?_⟩
      exfalso
      rcases ih H S₁ hcard₁ u _ vi vj L h hInt (hypInt h hok) with hE | hE
      · exact hne hE
      · exact hE3 hE
  rcases hcol with hall | ⟨col, hbad⟩
  · exact Or.inr (Or.inr hall)
  -- delete the bad colour from `L u` and apply the induction hypothesis to the outside
  let L' : V → Finset C := fun w => if w = u then (L u).erase col else L w
  have hL'u : L' u = (L u).erase col := by simp [L']
  have hL'ne : ∀ w, w ≠ u → L' w = L w := fun w hw => by simp [L', hw]
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  have h4u : 4 ≤ (L' u).card := by
    rw [hL'u]; have := Finset.pred_card_le_card_erase (s := L u) (a := col); omega
  have hh' : Thm3Hyp H S₂ x (P₀ ++ vi :: u :: vj :: P₁) a c L' g := by
    refine ⟨?_, ?_, by simp; omega, hh.ok, ?_, ?_⟩
    · have := hh.head
      rcases P₀ with _ | ⟨p, P₀'⟩ <;> simpa using this
    · have e1 : ∀ R : List V, (R ++ vj :: P₁).getLast? = (vj :: P₁).getLast? := fun R =>
        List.getLast?_append_of_ne_nil _ (by simp)
      have := hh.last
      rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ vi :: M) ++ vj :: P₁ by simp, e1] at this
      rw [show P₀ ++ vi :: u :: vj :: P₁ = (P₀ ++ [vi, u]) ++ vj :: P₁ by simp, e1]
      exact this
    · intro y hy hya hyc
      by_cases hyu : y = u
      · rw [hyu]; omega
      · rw [hL'ne y hyu]
        exact hh.three y (by simp only [List.mem_cons, List.mem_append] at hy ⊢; tauto) hya hyc
    · intro y hy hyc
      have hyu : y ≠ u := fun h => hyc (by simp [h])
      rw [hL'ne y hyu]
      exact hh.five y (hS₂ y hy) (hExt_out y hy hyc)
  have haS₂ : a ∈ S₂ := T.subset hExt a (List.mem_cons_of_mem _ (List.mem_of_mem_head? hh'.head))
  have hcS₂ : c ∈ S₂ := T.subset hExt c
    (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hh'.last))
  rcases ih H S₂ hcard₂ x _ a c L' g hExt hh' with hE | hE
  · left
    obtain ⟨f, hfc, hfL, hfp⟩ := hE
    have hfu : f u ∈ (L u).erase col := by
      rw [← hL'u]
      exact hfL u huS₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨huc, fun h => hxu h.symm, hua⟩)
    have hokf : PathOK H u vi vj f :=
      ⟨hfp u huS₂ vi hviS₂ hui, hfp u huS₂ vj hvjS₂ huj, fun h => hfp vi hviS₂ vj hvjS₂ h⟩
    have hext : Extends H S₁ [vj, u, vi] L f := by
      by_contra hne
      exact Finset.ne_of_mem_erase hfu (hbad f hokf hne)
    obtain ⟨f₁, h1c, h1L, h1p⟩ := hext
    refine ⟨fun w => if w ∈ S₂ then f w else f₁ w, ?_, ?_, ?_⟩
    · intro w hw
      have hw2 : w ∈ S₂ := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact hcS₂
        · exact hxS₂
        · exact haS₂
      simp only [hw2, ite_true]; exact hfc w hw
    · intro w hw hwc
      by_cases h2 : w ∈ S₂
      · simp only [h2, ite_true]
        have := hfL w h2 hwc
        by_cases hwu : w = u
        · rw [hwu] at this ⊢; rw [hL'u] at this; exact Finset.mem_of_mem_erase this
        · rwa [hL'ne w hwu] at this
      · simp only [h2, ite_false]
        refine h1L w (hside w hw h2) ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl | rfl)
        · exact h2 hvjS₂
        · exact h2 huS₂
        · exact h2 hviS₂
    · refine isProperOn_glue (S₁ := S₂) (S₂ := S₁) (by rw [Finset.union_comm]; exact hU)
        (fun p hp w hw hpw => (hX w hw p hp hpw.symm).symm) hfp h1p ?_
      intro w h2 h1
      rcases hmem w h1 h2 with rfl | rfl | rfl <;> exact h1c w (by simp)
  · right; left
    obtain ⟨P'', U, hGW, hnd'', hh'', hl'', hsub, hUc, hL⟩ := hE
    have hnu : ∀ y ∈ P'', y ≠ u := by
      intro y hy hyu
      have h3 := hL y hy (hyu ▸ hua) (hyu ▸ huc)
      rw [hyu] at h3
      omega
    refine ⟨P'', U, hGW, hnd'', hh'', hl'', ?_, ?_, ?_⟩
    · intro y hy
      have h1 := hsub y hy
      have h2 := hnu y hy
      simp only [List.mem_cons, List.mem_append] at h1 ⊢; tauto
    · intro w hw
      obtain ⟨h1, h2⟩ := hUc w hw
      exact ⟨hS₂ w h1, hExt_out w h1 h2⟩
    · intro y hy hya hyc
      have := hL y hy hya hyc
      rwa [hL'ne y (hnu y hy)] at this

end NTCalc

end ThomassenManyColourings
