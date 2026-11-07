/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim9d

/-!
# Theorem 4: an interior vertex joined to `v_k, v₁, v₂`

(After Claims 8–10.) The triangles `v₁ v₂ v` and `v₁ v v_k` are faces, so `G − v₁` is the
near-triangulation with outer cycle `v v₂ … v_k`. Colour `v` in two ways and apply induction to
`G − v₁` with `v_k, v, v₂` precoloured (`n − 1`, same `r`), unless `G − v₁` is a generalized
wheel, in which case `n ≤ 3r`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 32000000 in
/-- **An interior vertex joined to `v_k, v₁, v₂`.** -/
theorem thm4_hub (H : SimpleGraph V) {S : Finset V} {x : V} {M : List V} {a c v : V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: (M ++ [c]))) (hh : Thm4Hyp H S x (a :: (M ++ [c])) a c L g true)
    (hM : M ≠ [])
    (hPc : ∀ u w, u ∈ a :: (M ++ [c]) → w ∈ a :: (M ++ [c]) → H.Adj u w →
      ConsecIn (a :: (M ++ [c])) u w)
    (h10 : ∀ y ∈ M, (L y).card = 3) (hN : T.NoSepTri H S (x :: a :: (M ++ [c])))
    (hvS : v ∈ S) (hvn : v ∉ x :: a :: (M ++ [c])) (hva : H.Adj v a) (hvx : H.Adj v x)
    (hvc : H.Adj v c)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hpc : pcList true x a c = [c, x, a] := rfl
  intro hne hexc
  rw [hpc] at hne ⊢
  have hnd := T.nodup hNT
  have hxP := (List.nodup_cons.mp hnd).1
  have hPnd := (List.nodup_cons.mp hnd).2
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at hvn
  obtain ⟨hvx', hva', hvM, hvc'⟩ := hvn
  have hxa : x ≠ a := fun e => hxP (by simp [e])
  have hxc : x ≠ c := fun e => hxP (by simp [e])
  have hac : a ≠ c := fun e => (List.nodup_cons.mp hPnd).1 (by simp [e])
  have hcM : c ∉ M := fun h => (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.2 c h c
    (by simp) rfl
  have haM : a ∉ M := fun h => (List.nodup_cons.mp hPnd).1 (by simp [h])
  have hxM : x ∉ M := fun h => hxP (by simp [h])
  -- cut along `a v c`
  have hrot : T.NT H S (a :: (M ++ c :: [x])) := by simpa using T.rotate hNT
  have hvnot : v ∉ a :: (M ++ c :: [x]) := by
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
    exact ⟨hva', hvM, hvc', hvx'⟩
  obtain ⟨Si, So, hi, ho, hU, hI, hX⟩ := T.cut (x := a) (y := c) (u := v) (l₁ := M) (l₂ := [x])
    hrot hvS hvnot hva hvc (fun h => ConsecIn.not_ends hM hPnd (hPc a c (by simp) (by simp) h))
  have hmem : ∀ u, u ∈ Si → u ∈ So → u = a ∨ u = c ∨ u = v := by
    intro u h1 h2
    have : u ∈ Si ∩ So := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have ho' : T.NT H So [c, x, a, v] := by simpa using ho
  have hi' : T.NT H Si (v :: a :: (M ++ [c])) := T.rotate_back (by simpa using hi)
  have hRo : Region H S (x :: a :: (M ++ [c])) So [c, x, a, v] := by
    refine (Region.refl H S _).piece' (c₁ := v :: a :: (M ++ [c])) hU ?_ hX ?_
      (fun u hu => T.subset hi' u hu)
    · intro u h1 h2; rcases hmem u h1 h2 with e | e | e <;> simp [e]
    · intro u hu
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hu ⊢; tauto
  have hRi : Region H S (x :: a :: (M ++ [c])) Si (v :: a :: (M ++ [c])) := by
    refine (Region.refl H S _).piece (c₂ := [c, x, a, v]) hU ?_ hX ?_
      (fun u hu => T.subset ho' u hu)
    · intro u h1 h2; rcases hmem u h1 h2 with e | e | e <;> simp [e]
    · intro u hu
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hu ⊢; tauto
  -- the quadrilateral `c x a v` with the chord `x v` consists of two empty triangles
  have hoR : T.NT H So (x :: ([a] ++ v :: [c])) := by simpa using T.rotate ho'
  obtain ⟨T₁, T₂, ht₁, ht₂, hUT, hIT, hXT⟩ := T.chord hoR (by simp) (by simp) hvx.symm
  have hmemT : ∀ u, u ∈ T₁ → u ∈ T₂ → u = x ∨ u = v := by
    intro u h1 h2
    have : u ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hIT] at this; simpa using this
  have ht₁' : T.NT H T₁ [x, a, v] := by simpa using ht₁
  have ht₂' : T.NT H T₂ [v, c, x] := by simpa using ht₂
  have hRT₁ : Region H S (x :: a :: (M ++ [c])) T₁ [x, a, v] := by
    refine hRo.piece (c₂ := [v, c, x]) hUT ?_ hXT ?_ (fun u hu => T.subset ht₂' u hu)
    · intro u h1 h2; rcases hmemT u h1 h2 with e | e <;> simp [e]
    · intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢; tauto
  have hRT₂ : Region H S (x :: a :: (M ++ [c])) T₂ [v, c, x] := by
    refine hRo.piece' (c₁ := [x, a, v]) hUT ?_ hXT ?_ (fun u hu => T.subset ht₁' u hu)
    · intro u h1 h2; rcases hmemT u h1 h2 with e | e <;> simp [e]
    · intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢; tauto
  have hF₁ := hN T₁ x a v ht₁' hRT₁
  have hF₂ := hN T₂ v c x ht₂' hRT₂
  have hSo : ∀ u ∈ So, u = x ∨ u = a ∨ u = v ∨ u = c := by
    intro u hu
    rcases Finset.mem_union.mp (hUT ▸ hu) with h | h
    · rcases hF₁ u h with e | e | e <;> simp [e]
    · rcases hF₂ u h with e | e | e <;> simp [e]
  have hxSo : x ∈ So := T.subset ho' x (by simp)
  have hxSi : x ∉ Si := fun h => by
    rcases hmem x h hxSo with e | e | e
    · exact hxa e
    · exact hxc e
    · exact hvx' e.symm
  have hS : ∀ u ∈ S, u ∈ Si ∨ u = x := by
    intro u hu
    rcases Finset.mem_union.mp (hU ▸ hu) with h | h
    · exact Or.inl h
    · rcases hSo u h with e | e | e | e
      · exact Or.inr e
      · exact Or.inl (e ▸ T.subset hi' a (by simp))
      · exact Or.inl (e ▸ T.subset hi' v (by simp))
      · exact Or.inl (e ▸ T.subset hi' c (by simp))
  have hSiS : Si ⊆ S := fun u hu => hU ▸ Finset.mem_union_left _ hu
  have hvSi : v ∈ Si := T.subset hi' v (by simp)
  -- counts
  have hn : nCount S [c, x, a] = nCount Si [c, v, a] + 1 := by
    unfold nCount
    rw [← Finset.card_insert_of_notMem (a := v) (by simp)]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_insert, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    constructor
    · rintro ⟨hu, huc, hux, hua⟩
      rcases hS u hu with h | h
      · by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr ⟨h, huc, huv, hua⟩
      · exact absurd h hux
    · rintro (rfl | ⟨hu, huc, huv, hua⟩)
      · exact ⟨hvS, hvc', hvx', hva'⟩
      · exact ⟨hSiS hu, huc, fun e => hxSi (e ▸ hu), hua⟩
  have h5v : 5 ≤ (L v).card := hh.five v hvS (by
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
    exact ⟨hvx', hva', hvM, hvc'⟩)
  have hr : rCount S [c, x, a] L = rCount Si [c, v, a] L := by
    unfold rCount
    congr 1
    ext u
    simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · rintro ⟨hu, ⟨huc, hux, hua⟩, h3⟩
      rcases hS u hu with h | h
      · exact ⟨h, ⟨huc, fun e => by rw [e] at h3; omega, hua⟩, h3⟩
      · exact absurd h hux
    · rintro ⟨hu, ⟨huc, huv, hua⟩, h3⟩
      exact ⟨hSiS hu, ⟨huc, fun e => hxSi (e ▸ hu), hua⟩, h3⟩
  have h3P : ∀ y ∈ a :: (M ++ [c]), y ≠ a → y ≠ c → 3 ≤ (L y).card := by
    intro y hy hya hyc
    have : y ∈ M := by simp at hy; tauto
    rw [h10 y this]
  have h5i : ∀ u ∈ Si, u ∉ v :: a :: (M ++ [c]) → 5 ≤ (L u).card := fun u hu huc =>
    hh.five u (hSiS hu) (hRi.2 u hu huc).1
  by_cases hE : Exc3 H Si v (a :: (M ++ [c])) a c L
  · -- `G − v₁` is a generalized wheel: `n ≤ 3r`
    obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := hE
    have hPW : PW = a :: (M ++ [c]) := path_eq_of_chordless _ _ hPnd hndW hsubW (by rw [hhW]; rfl)
      (by rw [hlW]; exact (getLast?_cons_append_singleton a c M).symm) hGW.isPath hPc
    subst hPW
    obtain ⟨hfill, hG3⟩ := gw_fill hN hGW hi' hRi hUW
    have hcU := hG3.card_add_two_le
    simp only [List.length_cons, List.length_append, List.length_nil] at hcU
    have hMnd : M.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).1
    have hn' : nCount Si [c, v, a] ≤ M.length + U.card := by
      unfold nCount
      calc (Si.filter (· ∉ [c, v, a])).card ≤ (M.toFinset ∪ U).card := by
            apply Finset.card_le_card
            intro u hu
            simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
              not_or] at hu
            simp only [Finset.mem_union, List.mem_toFinset]
            rcases hfill u hu.1 with e | e | e
            · exact absurd e hu.2.2.1
            · left; simp only [List.mem_cons, List.mem_append] at e; tauto
            · exact Or.inr e
        _ ≤ M.toFinset.card + U.card := Finset.card_union_le _ _
        _ = _ := by rw [List.toFinset_card_of_nodup hMnd]
    have hr' : M.length ≤ rCount Si [c, v, a] L := by
      unfold rCount
      rw [← List.toFinset_card_of_nodup hMnd]
      apply Finset.card_le_card
      intro u hu
      rw [List.mem_toFinset] at hu
      simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨T.subset hi' u (by simp [hu]), ⟨fun e => hcM (e ▸ hu), fun e => hvM (e ▸ hu),
        fun e => haM (e ▸ hu)⟩, h10 u hu⟩
    have hMpos : 1 ≤ M.length := List.length_pos_iff.mpr hM
    exact bound4_of_le (ncard_extSet_pos hne) (by omega)
  -- two colours for `v`, then induction
  have key : ∀ β, β ∈ L v → β ≠ g x → β ≠ g a → β ≠ g c →
      Bound4 (ExtSet H Si [c, v, a] L (Function.update g v β)).ncard (nCount Si [c, v, a])
        (rCount Si [c, v, a] L) ∧
      ExtSet H Si [c, v, a] L (Function.update g v β) ⊆ ExtSet H S [c, x, a] L g := by
    intro β hβL hβx hβa hβc
    set gβ := Function.update g v β with hgβ
    have gv : gβ v = β := Function.update_self ..
    have gne : ∀ u, u ≠ v → gβ u = g u := fun u hu => Function.update_of_ne hu ..
    have hh₁ : Thm4Hyp H Si v (a :: (M ++ [c])) a c L gβ true :=
      ⟨rfl, getLast?_cons_append_singleton a c M, by simp,
        by rw [gv, gne a (Ne.symm hva')]; exact hβa, fun _ => by rw [gv, gne c (Ne.symm hvc')]; exact hβc,
        fun _ h => by rw [gne a (Ne.symm hva'), gne c (Ne.symm hvc')]; exact hh.ac rfl h,
        fun y hy hyn => h3P y hy (fun e => hyn (by simp [pcList, e]))
          (fun e => hyn (by simp [pcList, e])), h5i⟩
    have hsub : ExtSet H Si [c, v, a] L gβ ⊆ ExtSet H S [c, x, a] L g := by
      rintro f ⟨h1, h2, h3⟩
      have hfv : f v = β := by rw [h1 v (Or.inr (by simp)), gv]
      have hfx : f x = g x := by rw [h1 x (Or.inl hxSi), gne x (Ne.symm hvx')]
      have hfa : f a = g a := by rw [h1 a (Or.inr (by simp)), gne a (Ne.symm hva')]
      refine ⟨fun u hu => ?_, fun u hu hun => ?_, fun p hp q hq hpq => ?_⟩
      · rcases hu with hu | hu
        · have hu1 : u ∉ Si := fun h => hu (hSiS h)
          rw [h1 u (Or.inl hu1), gne u (fun e => hu (e ▸ hvS))]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with e | e | e
          · rw [e, h1 c (Or.inr (by simp)), gne c (Ne.symm hvc')]
          · rw [e]; exact hfx
          · rw [e, h1 a (Or.inr (by simp)), gne a (Ne.symm hva')]
      · rcases hS u hu with h | h
        · by_cases huv : u = v
          · rw [huv, hfv]; exact hβL
          · exact h2 u h (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun ⊢
              exact ⟨hun.1, huv, hun.2.2⟩)
        · exact absurd (by simp [h]) hun
      · -- edges at `x` go to `a, c, v`
        have hxnb : ∀ z ∈ S, H.Adj x z → z = a ∨ z = c ∨ z = v := by
          intro z hz hxz
          rcases hS z hz with h | h
          · rcases hX z h x hxSo hxz.symm with h' | h'
            · rcases hmem z h h' with e | e | e
              · exact Or.inl e
              · exact Or.inr (Or.inl e)
              · exact Or.inr (Or.inr e)
            · exact absurd h' hxSi
          · rw [h] at hxz; exact absurd hxz (H.loopless.irrefl _)
        have hfc : f c = g c := by rw [h1 c (Or.inr (by simp)), gne c (Ne.symm hvc')]
        have hfa' : f a = g a := by rw [h1 a (Or.inr (by simp)), gne a (Ne.symm hva')]
        have hxval : ∀ z ∈ S, H.Adj x z → f x ≠ f z := by
          intro z hz hxz
          rw [hfx]
          rcases hxnb z hz hxz with e | e | e
          · rw [e, hfa']; exact hh.xa
          · rw [e, hfc]; exact hh.xc rfl
          · rw [e, hfv]; exact Ne.symm hβx
        rcases hS p hp with hp1 | hp1 <;> rcases hS q hq with hq1 | hq1
        · exact h3 p hp1 q hq1 hpq
        · rw [hq1] at hpq ⊢; exact (hxval p hp hpq.symm).symm
        · rw [hp1] at hpq ⊢; exact hxval q hq hpq
        · rw [hp1, hq1] at hpq; exact absurd hpq (H.loopless.irrefl _)
    refine ⟨?_, hsub⟩
    have hh3 : Thm3Hyp H Si v (a :: (M ++ [c])) a c L gβ :=
      ⟨rfl, getLast?_cons_append_singleton a c M, by simp,
        ⟨hh₁.xa, hh₁.xc rfl, hh₁.ac rfl⟩, h3P, h5i⟩
    have hne₁ : (ExtSet H Si [c, v, a] L gβ).Nonempty := by
      rcases T.thm3 H hi' hh3 with h | h
      · exact extSet_nonempty_iff.mpr h
      · exact absurd h hE
    exact ih H Si v (a :: (M ++ [c])) a c L gβ true hi' hh₁ (by
      left; show nCount Si [c, v, a] < nCount S [c, x, a]; omega) hne₁ (by
      rintro ⟨-, u, hu, hun, h4, -, -, -, -⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
      by_cases huM : u ∈ M
      · rw [h10 u huM] at h4; omega
      · have := h5i u hu (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
          exact ⟨hun.2.1, hun.2.2, huM, hun.1⟩)
        omega)
  obtain ⟨β₁, h1, β₂, h2, h12⟩ := Finset.one_lt_card.mp
    (show 1 < ((((L v).erase (g x)).erase (g a)).erase (g c)).card by
      have := Finset.pred_card_le_card_erase (s := L v) (a := g x)
      have := Finset.pred_card_le_card_erase (s := (L v).erase (g x)) (a := g a)
      have := Finset.pred_card_le_card_erase (s := ((L v).erase (g x)).erase (g a)) (a := g c)
      omega)
  simp only [Finset.mem_erase] at h1 h2
  obtain ⟨hB1, hsub1⟩ := key β₁ h1.2.2.2 h1.2.2.1 h1.2.1 h1.1
  obtain ⟨hB2, hsub2⟩ := key β₂ h2.2.2.2 h2.2.2.1 h2.2.1 h2.1
  set M8 := minM8 (nCount Si [c, v, a]) (rCount Si [c, v, a] L)
  have hM1 := minM8_le hB1
  have hM2 := minM8_le hB2
  have hdisj : Disjoint (ExtSet H Si [c, v, a] L (Function.update g v β₁))
      (ExtSet H Si [c, v, a] L (Function.update g v β₂)) := by
    rw [Set.disjoint_left]
    intro f hf1 hf2
    have e1 := hf1.1 v (Or.inr (by simp))
    have e2 := hf2.1 v (Or.inr (by simp))
    rw [Function.update_self] at e1 e2
    exact h12 (e1.symm.trans e2)
  have hsum : (ExtSet H Si [c, v, a] L (Function.update g v β₁)).ncard +
      (ExtSet H Si [c, v, a] L (Function.update g v β₂)).ncard ≤
        (ExtSet H S [c, x, a] L g).ncard := by
    rw [← Set.ncard_union_eq hdisj (extSet_finite _ _ _ _ _) (extSet_finite _ _ _ _ _)]
    exact Set.ncard_le_ncard (Set.union_subset hsub1 hsub2) (extSet_finite H S [c, x, a] L g)
  have hspecM := minM8_spec (nCount Si [c, v, a]) (rCount Si [c, v, a] L)
  unfold Bound4
  rw [hn, hr, pow_succ]
  calc 2 ^ nCount Si [c, v, a] * 2 ≤ M8 ^ 9 * 8 ^ rCount Si [c, v, a] L * 2 :=
        Nat.mul_le_mul_right _ hspecM
    _ ≤ (2 * M8) ^ 9 * 8 ^ rCount Si [c, v, a] L := by
        rw [mul_pow]
        calc M8 ^ 9 * 8 ^ rCount Si [c, v, a] L * 2 = 2 * (M8 ^ 9 * 8 ^ rCount Si [c, v, a] L) :=
              by ring
          _ ≤ 2 ^ 9 * (M8 ^ 9 * 8 ^ rCount Si [c, v, a] L) :=
              Nat.mul_le_mul_right _ (by norm_num)
          _ = _ := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 9)

end NTCalc

end ThomassenManyColourings
