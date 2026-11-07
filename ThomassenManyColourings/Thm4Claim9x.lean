/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Sym

/-!
# Theorem 4, Claim 9: chords at `v₁` with three precoloured vertices

A chord `v₁ y` with at least one outer vertex strictly on each side. If the side of `v_k` is not
exceptional (Theorem 3), colour the side of `v₂` first and extend; symmetrically; if both sides
are generalized wheels, there are at most `|P| - 2` non-path vertices besides the path's inner
vertices, all of which have three colours, so `n ≤ 3r`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 32000000 in
/-- **Claim 9, chords at `v₁`, three precoloured vertices.** -/
theorem thm4_claim9_x3 (H : SimpleGraph V) {S : Finset V} {x y : V} {P₀ P₁ : List V}
    {a c : V} {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (P₀ ++ y :: P₁))) (hh : Thm4Hyp H S x (P₀ ++ y :: P₁) a c L g true)
    (hP₀ : 2 ≤ P₀.length) (hP₁ : 2 ≤ P₁.length) (hxy : H.Adj x y)
    (hPc : ∀ u v, u ∈ P₀ ++ y :: P₁ → v ∈ P₀ ++ y :: P₁ → H.Adj u v →
      ConsecIn (P₀ ++ y :: P₁) u v)
    (hN : T.NoSepTri H S (x :: (P₀ ++ y :: P₁)))
    (hno4₁ : ∀ u ∈ S, u ∉ [a, x, y] → (L u).card = 4 → H.Adj u a → H.Adj u x → H.Adj u y →
      False)
    (hno4₂ : ∀ u ∈ S, u ∉ [c, x, y] → (L u).card = 4 → H.Adj u c → H.Adj u x → H.Adj u y →
      False)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hnd := T.nodup hNT
  have hxP := (List.nodup_cons.mp hnd).1
  have hPnd := (List.nodup_cons.mp hnd).2
  have hP := List.nodup_append.mp hPnd
  have hyP₁ : y ∉ P₁ := (List.nodup_cons.mp hP.2.1).1
  have hyP₀ : y ∉ P₀ := fun h => hP.2.2 y h y List.mem_cons_self rfl
  have hP₀ne : P₀ ≠ [] := by intro h; rw [h] at hP₀; simp at hP₀
  have hP₁ne : P₁ ≠ [] := by intro h; rw [h] at hP₁; simp at hP₁
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hNT hP₀ne hP₁ne hxy
  have h₂' : T.NT H S₂ (x :: y :: P₁) := T.rotate_back (by simpa using h₂)
  have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = y := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hP₀side : ∀ v ∈ P₀, v ∉ S₂ := by
    intro v hv h2
    rcases hmem v (T.subset h₁ v (by simp [hv])) h2 with rfl | rfl
    · exact hxP (List.mem_append_left _ hv)
    · exact hyP₀ hv
  have hP₁side : ∀ v ∈ P₁, v ∉ S₁ := by
    intro v hv h1
    rcases hmem v h1 (T.subset h₂' v (by simp [hv])) with rfl | rfl
    · exact hxP (by simp [hv])
    · exact hyP₁ hv
  have hhead : P₀.head? = some a := by
    have := hh.head; rwa [List.head?_append_of_ne_nil _ hP₀ne] at this
  have hlast : P₁.getLast? = some c := by
    have := hh.last
    rwa [show P₀ ++ y :: P₁ = (P₀ ++ [y]) ++ P₁ by simp,
      List.getLast?_append_of_ne_nil _ hP₁ne] at this
  have haP₀ : a ∈ P₀ := List.mem_of_mem_head? hhead
  have hcP₁ : c ∈ P₁ := List.mem_of_mem_getLast? hlast
  have hya : y ≠ a := fun e => hyP₀ (e ▸ haP₀)
  have hyc : y ≠ c := fun e => hyP₁ (e ▸ hcP₁)
  have haS₂ : a ∉ S₂ := hP₀side a haP₀
  have hcS₁ : c ∉ S₁ := hP₁side c hcP₁
  have hxa : x ≠ a := fun e => hxP (by rw [e]; simp [haP₀])
  have hxc : x ≠ c := fun e => hxP (by rw [e]; simp [hcP₁])
  -- `y` is not adjacent to `c` nor to `a` (no chords)
  have hnyc : ¬ H.Adj y c := by
    intro h
    rcases ConsecIn.nbr hPnd (hPc y c (by simp) (by simp [hcP₁]) h) with h1 | h1
    · exact hP.2.2 c (List.mem_of_mem_getLast? h1) c (List.mem_cons_of_mem _ hcP₁) rfl
    · have := eq_single_of_head_last (List.nodup_cons.mp hP.2.1).2 h1 hlast
      rw [this] at hP₁; simp at hP₁
  have hnya : ¬ H.Adj y a := by
    intro h
    rcases ConsecIn.nbr hPnd (hPc y a (by simp) (by simp [haP₀]) h) with h1 | h1
    · have := eq_single_of_head_last hP.1 hhead h1
      rw [this] at hP₀; simp at hP₀
    · exact hP.2.2 a haP₀ a (List.mem_cons_of_mem _ (List.mem_of_mem_head? h1)) rfl
  have hyS₁ : y ∈ S₁ := T.subset h₁ y (by simp)
  have hxS₁ : x ∈ S₁ := T.subset h₁ x (by simp)
  -- lists of the two sides
  have hh₁ : Thm4Hyp H S₁ x (P₀ ++ [y]) a y L g false := by
    refine ⟨by rw [List.head?_append_of_ne_nil _ hP₀ne]; exact hhead, List.getLast?_concat ..,
      by simp; omega, hh.xa, by simp, by simp,
      fun v hv hvn => hh.three v (by simp only [List.mem_append, List.mem_cons] at hv ⊢; tauto) ?_,
      fun v hv hvc => hh.five v (hU ▸ Finset.mem_union_left _ hv) ?_⟩
    · have hvc : v ≠ c := fun e => hcS₁ (e ▸ T.subset h₁ v (List.mem_cons_of_mem _ hv))
      simp only [pcList, ite_true, Bool.false_eq_true, ite_false, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hvn ⊢
      exact ⟨hvc, hvn⟩
    · intro h; apply hvc
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd hv (hP₁side v h)
  have h3₂ : ∀ v ∈ y :: P₁, v ≠ y → v ≠ c → 3 ≤ (L v).card := by
    intro v hv hvy hvc
    have hvP₁ : v ∈ P₁ := by simpa [hvy] using hv
    apply hh.three v (by simp [hvP₁])
    simp only [pcList, ite_true, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hvc, fun e => hxP (by simp [← e, hvP₁]),
      fun e => hP₁side v hvP₁ (e ▸ T.subset h₁ a (by simp [haP₀]))⟩
  have h5₂ : ∀ v ∈ S₂, v ∉ x :: y :: P₁ → 5 ≤ (L v).card := by
    intro v hv hvc
    apply hh.five v (hU ▸ Finset.mem_union_right _ hv)
    intro h; apply hvc
    simp only [List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact absurd hv (hP₀side v h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨m₂, hm₂, hm₂c⟩ : ∃ m ∈ P₁, m ≠ c := by
    obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP₁ne
    have hP' : P' ≠ [] := by intro h; rw [h] at hP₁; simp at hP₁
    refine ⟨p, by simp, fun e => ?_⟩
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hP'] at hlast
    simp only [Option.getD_some, Option.some.injEq] at hlast
    exact (List.nodup_cons.mp (List.nodup_cons.mp hP.2.1).2).1 (e ▸ hlast ▸ List.getLast_mem hP')
  obtain ⟨m₁, hm₁, hm₁a⟩ : ∃ m ∈ P₀, m ≠ a := by
    obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP₀ne
    have hP' : P' ≠ [] := by intro h; rw [h] at hP₀; simp at hP₀
    obtain ⟨q, P'', rfl⟩ := List.exists_cons_of_ne_nil hP'
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    refine ⟨q, by simp, fun e => ?_⟩
    rw [e] at hP; simp at hP
  by_cases hE2 : Exc3 H S₂ x (y :: P₁) y c L
  swap
  · -- colour the side of `v₂` first
    refine T.thm4_glue_three H h₁ hh₁ h₂' rfl (by rw [List.getLast?_cons, hlast]; rfl)
      (by simp; omega) h3₂ h5₂ hU hX hmem hcS₁ haS₂ hya hxy (hh.xc rfl) hnyc hE2
      (fun u hu hun h4 huc hux huy => hno4₂ u (hU ▸ Finset.mem_union_right _ hu) hun h4 huc hux
        huy) ?_ ih
    unfold nCount
    refine Finset.card_pos.mpr ⟨m₂, Finset.mem_filter.mpr ⟨T.subset h₂' m₂ (by simp [hm₂]), ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hm₂c, fun e => hxP (by simp [← e, hm₂]), fun e => hyP₁ (e ▸ hm₂)⟩
  by_cases hE1 : Exc3 H S₁ x (P₀ ++ [y]) a y L
  swap
  · -- colour the side of `v_k` first (reverse the orientation)
    apply thm4concl_swap
    have hrev : (P₀ ++ y :: P₁).reverse = P₁.reverse ++ y :: P₀.reverse := by simp
    have h₁r : T.NT H S₁ (x :: y :: P₀.reverse) := by
      have := T.rotate_back (by simpa using T.reverse h₁) (x := x) (l := (P₀ ++ [y]).reverse)
      simpa using this
    have h₂r : T.NT H S₂ (x :: (P₁.reverse ++ [y])) := by
      have := T.rotate_back (by simpa using T.reverse h₂') (x := x) (l := (y :: P₁).reverse)
      simpa using this
    have hhr : (P₁.reverse ++ [y]).head? = some c := by
      rw [List.head?_append_of_ne_nil _ (by simpa using hP₁ne), List.head?_reverse]
      exact hlast
    have hh₂r : Thm4Hyp H S₂ x (P₁.reverse ++ [y]) c y L g false := by
      refine ⟨hhr, List.getLast?_concat ..,  by simp; omega, fun e => hh.xc rfl e, by simp,
        by simp, fun v hv hvn => ?_, fun v hv hvc => h5₂ v hv (fun h => hvc (by
          simp only [List.mem_cons, List.mem_append, List.mem_reverse, List.not_mem_nil,
            or_false] at h ⊢
          tauto))⟩
      have hv' : v ∈ y :: P₁ := by
        simp only [List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil,
          or_false] at hv ⊢
        tauto
      by_cases hvy : v = y
      · rw [hvy]
        apply hh.three y (by simp)
        simp only [pcList, ite_true, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hyc, fun e => hxP (by simp [← e]), hya⟩
      · exact h3₂ v hv' hvy (fun e => hvn (by simp [pcList, e]))
    have hnoE1 : ¬ Exc3 H S₁ x (y :: P₀.reverse) y a L := by
      intro h
      apply hE1
      exact exc3_reverse (fun v => by
        simp only [List.mem_cons, List.mem_append, List.mem_reverse, List.not_mem_nil,
          or_false]; tauto) h
    have hn : nCount S (pcList true x c a) = nCount S (pcList true x a c) :=
      nCount_congr (pc3_swap x a c)
    have hr : rCount S (pcList true x c a) L = rCount S (pcList true x a c) L :=
      rCount_congr (pc3_swap x a c)
    refine T.thm4_glue_three H h₂r hh₂r h₁r rfl (by
        rw [List.getLast?_cons, List.getLast?_reverse, hhead]; rfl)
      (by simp; omega) (fun v hv hvy hva => hh.three v (by
        simp only [List.mem_cons, List.mem_reverse] at hv; simp; tauto) (by
        have hvP₀ : v ∈ P₀ := by simpa [hvy] using hv
        simp only [pcList, ite_true, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hcS₁ (e ▸ T.subset h₁ v (by simp [hvP₀])),
          fun e => hxP (by simp [← e, hvP₀]), hva⟩))
      (fun v hv hvc => hh.five v (hU ▸ Finset.mem_union_left _ hv) (by
        intro h; apply hvc
        simp only [List.mem_cons, List.mem_append, List.mem_reverse]
          at h ⊢
        rcases h with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
        · exact absurd hv (hP₁side v h)))
      (by rw [Finset.union_comm]; exact hU) (fun p hp q hq hpq => (hX q hq p hp hpq.symm).symm)
      (fun v h2 h1 => hmem v h1 h2) haS₂ hcS₁ hyc hxy (hh.xa) hnya hnoE1
      (fun u hu hun h4 hua hux huy => hno4₁ u (hU ▸ Finset.mem_union_left _ hu) hun h4 hua hux
        huy) ?_ (by rw [hn, hr]; exact ih)
    unfold nCount
    refine Finset.card_pos.mpr ⟨m₁, Finset.mem_filter.mpr ⟨T.subset h₁ m₁ (by simp [hm₁]), ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hm₁a, fun e => hxP (by simp [← e, hm₁]), fun e => hyP₀ (e ▸ hm₁)⟩
  -- both sides are generalized wheels: `n ≤ 3r`
  have hR₁ : Region H S (x :: (P₀ ++ y :: P₁)) S₁ (x :: (P₀ ++ [y])) := by
    refine (Region.refl H S _).piece (c₂ := x :: y :: P₁) hU ?_ hX ?_
      (fun v hv => T.subset h₂' v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hR₂ : Region H S (x :: (P₀ ++ y :: P₁)) S₂ (x :: y :: P₁) := by
    refine (Region.refl H S _).piece' (c₁ := x :: (P₀ ++ [y])) hU ?_ hX ?_
      (fun v hv => T.subset h₁ v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have eP : P₀ ++ y :: P₁ = (P₀ ++ [y]) ++ P₁ := by simp
  have hnd₁ : (P₀ ++ [y]).Nodup := (List.nodup_append.mp (eP ▸ hPnd)).1
  have hc₁ : ∀ u v, u ∈ P₀ ++ [y] → v ∈ P₀ ++ [y] → H.Adj u v → ConsecIn (P₀ ++ [y]) u v := by
    intro u v hu hv huv
    have h := hPc u v (by rw [eP]; exact List.mem_append_left _ hu)
      (by rw [eP]; exact List.mem_append_left _ hv) huv
    rw [eP] at h
    exact ConsecIn.of_append_right (eP ▸ hPnd) hu hv h
  have hc₂ : ∀ u v, u ∈ y :: P₁ → v ∈ y :: P₁ → H.Adj u v → ConsecIn (y :: P₁) u v := by
    intro u v hu hv huv
    exact ConsecIn.of_append_left hPnd hu hv
      (hPc u v (List.mem_append_right _ hu) (List.mem_append_right _ hv) huv)
  obtain ⟨PW1, U1, hGW1, hndW1, hhW1, hlW1, hsubW1, hUW1, hLW1⟩ := hE1
  have hPW1 : PW1 = P₀ ++ [y] := path_eq_of_chordless _ _ hnd₁ hndW1 hsubW1
    (by rw [hhW1, List.head?_append_of_ne_nil _ hP₀ne, hhead])
    (by rw [hlW1, List.getLast?_concat]) hGW1.isPath hc₁
  subst hPW1
  obtain ⟨hfill1, hG1⟩ := gw_fill hN hGW1 h₁ hR₁ hUW1
  obtain ⟨PW2, U2, hGW2, hndW2, hhW2, hlW2, hsubW2, hUW2, hLW2⟩ := hE2
  have hPW2 : PW2 = y :: P₁ := path_eq_of_chordless _ _ hP.2.1 hndW2 hsubW2 (by rw [hhW2]; rfl)
    (by rw [hlW2, List.getLast?_cons, hlast]; rfl) hGW2.isPath hc₂
  subst hPW2
  obtain ⟨hfill2, hG2⟩ := gw_fill hN hGW2 h₂' hR₂ hUW2
  have hcU1 := hG1.card_add_two_le
  have hcU2 := hG2.card_add_two_le
  apply thm4_of_le
  show nCount S [c, x, a] ≤ 3 * rCount S [c, x, a] L
  have hPc' : (P₀ ++ y :: P₁).toFinset.card = P₀.length + P₁.length + 1 := by
    rw [List.toFinset_card_of_nodup hPnd]; simp; omega
  have haP : a ∈ (P₀ ++ y :: P₁).toFinset := by simp [haP₀]
  have hcP : c ∈ ((P₀ ++ y :: P₁).toFinset.erase a) := by
    simp only [Finset.mem_erase, List.mem_toFinset]
    exact ⟨fun e => hxa (by
      exact absurd (e ▸ haS₂) (fun h => h (T.subset h₂' c (by simp [hcP₁])))), by simp [hcP₁]⟩
  have hyP : y ∈ (((P₀ ++ y :: P₁).toFinset.erase a).erase c) := by
    simp only [Finset.mem_erase, List.mem_toFinset]
    exact ⟨hyc, hya, by simp⟩
  have hn : nCount S [c, x, a] ≤ (P₀.length + P₁.length - 1) + U1.card + U2.card := by
    unfold nCount
    calc (S.filter (· ∉ [c, x, a])).card
        ≤ ((((P₀ ++ y :: P₁).toFinset.erase a).erase c) ∪ U1 ∪ U2).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          obtain ⟨hzS, hzc, hzx, hza⟩ := hz
          simp only [Finset.mem_union, Finset.mem_erase, List.mem_toFinset]
          rcases Finset.mem_union.mp (hU ▸ hzS) with h | h
          · rcases hfill1 z h with e | e | e
            · exact absurd e hzx
            · left; left
              refine ⟨hzc, hza, ?_⟩
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at e ⊢
              tauto
            · exact Or.inl (Or.inr e)
          · rcases hfill2 z h with e | e | e
            · exact absurd e hzx
            · left; left
              refine ⟨hzc, hza, ?_⟩
              simp only [List.mem_append, List.mem_cons] at e ⊢
              tauto
            · exact Or.inr e
      _ ≤ (((P₀ ++ y :: P₁).toFinset.erase a).erase c).card + U1.card + U2.card := by
          refine (Finset.card_union_le _ _).trans ?_
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = (P₀.length + P₁.length - 1) + U1.card + U2.card := by
          rw [Finset.card_erase_of_mem hcP, Finset.card_erase_of_mem haP, hPc']; omega
  have hr : P₀.length + P₁.length - 2 ≤ rCount S [c, x, a] L := by
    unfold rCount
    calc P₀.length + P₁.length - 2
        = ((((P₀ ++ y :: P₁).toFinset.erase a).erase c).erase y).card := by
          rw [Finset.card_erase_of_mem hyP, Finset.card_erase_of_mem hcP,
            Finset.card_erase_of_mem haP, hPc']; omega
      _ ≤ _ := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_erase, List.mem_toFinset] at hz
          obtain ⟨hzy, hzc, hza, hzP⟩ := hz
          simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨T.subset hNT z (List.mem_cons_of_mem _ hzP),
            ⟨hzc, fun e => hxP (e ▸ hzP), hza⟩, ?_⟩
          rcases List.mem_append.mp hzP with h | h
          · exact hLW1 z (List.mem_append_left _ h) hza hzy
          · exact hLW2 z h hzy hzc
  simp only [List.length_append, List.length_cons, List.length_nil] at hcU1 hcU2
  omega

end NTCalc

end ThomassenManyColourings
