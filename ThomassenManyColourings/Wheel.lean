/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.GW

/-!
# Extending colourings of wheels

`x a v₃ … b` is the outer cycle of a wheel with centre `u`; `b, x, a` are precoloured. If `u` gets
a colour `γ` off the three precolours and `v₃` has a list `L₃` of at least three colours whose
members other than `γ` are available at `v₃` and distinct from the colour of `a`, the colouring
extends (Theorem 1 applied to the wheel minus `x` and `a`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

/-- In a wheel, the only outer neighbours of the first outer vertex are its two neighbours on the
cycle. -/
theorem wheel_nbr {H : SimpleGraph V} {S : Finset V} {x : V} {P : List V}
    (hNT : T.NT H S (x :: P)) {u : V} (huS : u ∈ S) (hu : u ∉ x :: P)
    (hhub : ∀ z ∈ x :: P, H.Adj u z) :
    ∀ z ∈ P, H.Adj x z → P.head? = some z ∨ P.getLast? = some z := by
  intro z hz hxz
  by_contra hne
  push_neg at hne
  obtain ⟨l₁, l₂, hP⟩ := List.append_of_mem hz
  have hl₁ : l₁ ≠ [] := by rintro rfl; apply hne.1; simp [hP]
  have hl₂ : l₂ ≠ [] := by
    rintro rfl; apply hne.2; rw [hP, List.getLast?_append]; simp
  subst hP
  exact T.no_chord_of_hub hNT hl₁ hl₂ huS hu hhub hxz

/-- **Wheel extension.** -/
theorem wheel_ext (H : SimpleGraph V) {S : Finset V} {x a v₃ b u : V} {M : List V}
    (hNT : T.NT H S (x :: a :: v₃ :: (M ++ [b])))
    (hS : ∀ y ∈ S, y ∈ x :: a :: v₃ :: (M ++ [b]) ∨ y = u)
    (huS : u ∈ S) (hu : u ∉ x :: a :: v₃ :: (M ++ [b]))
    (hhub : ∀ z ∈ x :: a :: v₃ :: (M ++ [b]), H.Adj u z)
    (L : V → Finset C) (g : V → C) (hxa : g x ≠ g a) (hxb : g x ≠ g b)
    (γ : C) (hγ : γ ∈ L u) (hγx : γ ≠ g x) (hγa : γ ≠ g a) (hγb : γ ≠ g b)
    (L₃ : Finset C) (hL₃ : 3 ≤ L₃.card) (hL₃s : ∀ c ∈ L₃, c ≠ γ → c ∈ L v₃ ∧ c ≠ g a)
    (hM : ∀ y ∈ M, 3 ≤ (L y).card) :
    Extends H S [b, x, a] L g := by
  classical
  set P := a :: v₃ :: (M ++ [b]) with hPdef
  have hnd := T.nodup hNT
  have hndP : P.Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ P := (List.nodup_cons.mp hnd).1
  have hux : u ≠ x := fun e => hu (by simp [hPdef, e])
  have huP : u ∉ P := fun h => hu (List.mem_cons_of_mem _ h)
  have hab : a ≠ b := by
    intro e; rw [hPdef, e] at hndP; simp at hndP
  have hav : a ≠ v₃ := by
    intro e; rw [hPdef, e] at hndP; simp at hndP
  have haM : a ∉ M := by
    intro h; rw [hPdef] at hndP; simp [h] at hndP
  have hvM : v₃ ∉ M := by
    intro h; rw [hPdef] at hndP; simp [h] at hndP
  have hvb : v₃ ≠ b := by
    intro e; rw [hPdef, e] at hndP; simp at hndP
  have hbM : b ∉ M := by
    intro h
    have h1 : (M ++ [b]).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hndP).2).2
    exact (List.nodup_append.mp h1).2.2 b h b (by simp) rfl
  have hxS : x ∈ S := T.subset hNT x (by simp [hPdef])
  have haS : a ∈ S := T.subset hNT a (by simp [hPdef])
  have hbS : b ∈ S := T.subset hNT b (by simp [hPdef])
  have hvS : v₃ ∈ S := T.subset hNT v₃ (by simp [hPdef])
  -- delete `x`
  have hx_nb := T.wheel_nbr hNT huS hu hhub
  obtain ⟨us, hus, hnb, hNT1, -⟩ := T.delete hNT (by simp [hPdef]) hx_nb
  have hus_eq : us = [u] := by
    have hall : ∀ w ∈ us, w = u := by
      intro w hw
      rcases hS w (hus w hw).1 with h | h
      · exact absurd h (hus w hw).2
      · exact h
    have hmem : u ∈ us := by
      rcases hnb u huS (hhub x (by simp)).symm with h | h | h
      · exact absurd (List.mem_of_mem_head? h) huP
      · exact absurd (List.mem_of_mem_getLast? h) huP
      · exact h
    have hndus : us.Nodup := (List.nodup_append.mp (T.nodup hNT1)).2.1
    rcases us with _ | ⟨w, us'⟩
    · simp at hmem
    · have hw := hall w (by simp)
      subst hw
      have : us' = [] := by
        rcases us' with _ | ⟨w', us''⟩
        · rfl
        · have := hall w' (by simp)
          subst this
          simp at hndus
      rw [this]
  subst hus_eq
  have hNT1' : T.NT H (S.erase x) (a :: (v₃ :: (M ++ [b] ++ [u]))) := by
    simpa [hPdef] using hNT1
  -- delete `a`
  have hrotx : T.NT H S (a :: (v₃ :: (M ++ [b] ++ [x]))) := by
    simpa [hPdef] using T.rotate hNT
  have ha_nb0 := T.wheel_nbr hrotx huS (fun h => hu (by
      simp only [hPdef, List.mem_cons, List.mem_append, List.mem_singleton] at h ⊢; tauto))
    (fun z hz => hhub z (by simp [hPdef] at hz ⊢; tauto))
  have ha_nb : ∀ z ∈ v₃ :: (M ++ [b] ++ [u]), H.Adj a z →
      (v₃ :: (M ++ [b] ++ [u])).head? = some z ∨ (v₃ :: (M ++ [b] ++ [u])).getLast? = some z := by
    intro z hz haz
    by_cases hzu : z = u
    · right; subst hzu
      rw [List.getLast?_cons, List.getLast?_append]; simp
    · have hz' : z ∈ v₃ :: (M ++ [b] ++ [x]) := by
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hz ⊢
        tauto
      rcases ha_nb0 z hz' haz with h | h
      · left; simpa using h
      · have hl : (v₃ :: (M ++ [b] ++ [x])).getLast? = some x := by
          rw [List.getLast?_cons, List.getLast?_append]; simp
        rw [hl, Option.some.injEq] at h
        subst h
        exfalso
        have hx' : x ∈ P ∨ x = u := by
          simp only [hPdef, List.mem_cons, List.mem_append, List.mem_singleton,
            List.not_mem_nil, or_false] at hz ⊢
          tauto
        rcases hx' with h | h
        · exact hxP h
        · exact hux h.symm
  obtain ⟨us', hus', hnb', hNT2, -⟩ := T.delete hNT1' (by simp) ha_nb
  have hus'_eq : us' = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro w hw
    obtain ⟨hwS, hwn⟩ := hus' w hw
    have hwx : w ≠ x := Finset.ne_of_mem_erase hwS
    rcases hS w (Finset.mem_of_mem_erase hwS) with h | h
    · apply hwn
      simp only [hPdef, List.mem_cons, List.mem_append, List.mem_singleton] at h ⊢
      tauto
    · apply hwn; simp [h]
  subst hus'_eq
  set S₂ := (S.erase x).erase a with hS₂
  have hNT3 : T.NT H S₂ (b :: u :: v₃ :: M) := by
    have h0 : T.NT H S₂ ((v₃ :: M) ++ [b, u]) := by simpa using hNT2
    simpa using T.rotate_append h0
  let L' : V → Finset C := fun y => if y = v₃ then L₃ else L y
  have hub : Function.update g u γ b ≠ Function.update g u γ u := by
    rw [Function.update_self, Function.update_of_ne (fun e => hu (by simp [hPdef, e]))]
    exact hγb.symm
  obtain ⟨f, hfb, hfu, hfL, hfp⟩ := T.thm1 H _ S₂ rfl b u (v₃ :: M) hNT3 L'
    (Function.update g u γ) hub
    (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simp only [L', if_true]; exact hL₃
      · have : y ≠ v₃ := fun e => hvM (e ▸ hy)
        simp only [L', this, if_false]; exact hM y hy)
    (by
      intro y hy hyc
      exfalso
      have hyx : y ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hya : y ≠ a := Finset.ne_of_mem_erase hy
      rcases hS y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)) with h | h
      · apply hyc
        simp only [hPdef, List.mem_cons, List.mem_append, List.mem_singleton] at h ⊢
        tauto
      · apply hyc; simp [h])
  rw [Function.update_of_ne (fun e => hu (by simp [hPdef, e]))] at hfb
  rw [Function.update_self] at hfu
  have huS₂ : u ∈ S₂ := T.subset hNT3 u (by simp)
  have hvS₂ : v₃ ∈ S₂ := T.subset hNT3 v₃ (by simp)
  have hfv : f v₃ ∈ L v₃ ∧ f v₃ ≠ g a := by
    have h1 := hfL v₃ hvS₂ hvb (fun e => hu (by simp [hPdef, ← e]))
    simp only [L', if_true] at h1
    exact hL₃s _ h1 (by rw [← hfu]; exact hfp v₃ hvS₂ u huS₂ (hhub v₃ (by simp [hPdef])).symm)
  set F₁ := Function.update f x (g x) with hF₁
  have hF₁p : IsProperOn H (S.erase a) F₁ := by
    apply isProperOn_update
    · rw [Finset.erase_right_comm]; exact hfp
    · intro w hw hxw
      have hwa : w ≠ a := Finset.ne_of_mem_erase hw
      rcases hnb w (Finset.mem_of_mem_erase hw) hxw with h | h | h
      · simp [hPdef] at h; exact absurd h.symm hwa
      · simp [hPdef, List.getLast?_cons, List.getLast?_append] at h; subst h; rw [hfb]; exact hxb.symm
      · simp at h; subst h; rw [hfu]; exact hγx
  refine ⟨Function.update F₁ a (g a), ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · rw [Function.update_of_ne (Ne.symm hab), hF₁, Function.update_of_ne
        (fun e => hxP (by simp [hPdef, e]))]
      exact hfb
    · rw [Function.update_of_ne (fun e => hxP (by simp [hPdef, ← e])), hF₁,
        Function.update_self]
    · simp
  · intro y hy hyc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc
    rw [Function.update_of_ne hyc.2.2, hF₁, Function.update_of_ne hyc.2.1]
    by_cases hyu : y = u
    · subst hyu; rw [hfu]; exact hγ
    by_cases hyv : y = v₃
    · subst hyv; exact hfv.1
    · have hyS₂ : y ∈ S₂ := Finset.mem_erase.mpr ⟨hyc.2.2, Finset.mem_erase.mpr ⟨hyc.2.1, hy⟩⟩
      have h1 := hfL y hyS₂ hyc.1 hyu
      simp only [L', hyv, if_false] at h1
      exact h1
  · apply isProperOn_update hF₁p
    intro w hw haw
    by_cases hwx : w = x
    · subst hwx; rw [hF₁, Function.update_self]; exact hxa
    · rw [hF₁, Function.update_of_ne hwx]
      rcases hnb' w (Finset.mem_erase.mpr ⟨hwx, hw⟩) haw with h | h | h
      · simp at h; subst h; exact hfv.2
      · have hl : (v₃ :: (M ++ [b] ++ [u])).getLast? = some u := by
          rw [List.getLast?_cons, List.getLast?_append]; simp
        rw [hl, Option.some.injEq] at h
        subst h; rw [hfu]; exact hγa
      · simp at h

/-- Lists of a wheel forced by a non-extendable precolouring of the principal path. -/
theorem wheel_bad (H : SimpleGraph V) {S : Finset V} {x a v₃ b u : V} {M : List V}
    (hNT : T.NT H S (x :: a :: v₃ :: (M ++ [b])))
    (hS : ∀ y ∈ S, y ∈ x :: a :: v₃ :: (M ++ [b]) ∨ y = u)
    (huS : u ∈ S) (hu : u ∉ x :: a :: v₃ :: (M ++ [b]))
    (hhub : ∀ z ∈ x :: a :: v₃ :: (M ++ [b]), H.Adj u z)
    (L : V → Finset C) (g : V → C) (hxa : g x ≠ g a) (hxb : g x ≠ g b)
    (h5 : 5 ≤ (L u).card) (h3 : 3 ≤ (L v₃).card) (hM : ∀ y ∈ M, 3 ≤ (L y).card)
    (hbad : ¬ Extends H S [b, x, a] L g) :
    ((L v₃).erase (g a)).card = 2 ∧ (L u) \ {g x, g a, g b} = (L v₃).erase (g a) ∧
      g a ≠ g b ∧ g x ∈ L u ∧ g a ∈ L u ∧ g b ∈ L u := by
  classical
  set A := (L v₃).erase (g a) with hA
  set G3 : Finset C := {g x, g a, g b} with hG3
  set Lu := (L u) \ G3 with hLu
  have hG3c : G3.card ≤ 3 := Finset.card_le_three
  have hA2 : 2 ≤ A.card := by
    have := Finset.pred_card_le_card_erase (s := L v₃) (a := g a)
    rw [← hA] at this; omega
  have hLu2 : 2 ≤ Lu.card := by
    have := Finset.le_card_sdiff G3 (L u)
    rw [← hLu] at this; omega
  have hmemLu : ∀ γ ∈ Lu, γ ∈ L u ∧ γ ≠ g x ∧ γ ≠ g a ∧ γ ≠ g b := by
    intro γ hγ
    simp only [hLu, hG3, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hγ
    exact ⟨hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2⟩
  -- (1) `A` has exactly two colours
  have hA_le : A.card ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨γ, hγ⟩ := Finset.card_pos.mp (by omega : 0 < Lu.card)
    obtain ⟨hγL, hγx, hγa, hγb⟩ := hmemLu γ hγ
    apply hbad
    exact T.wheel_ext H hNT hS huS hu hhub L g hxa hxb γ hγL hγx hγa hγb A (by omega)
      (fun c hc _ => ⟨Finset.mem_of_mem_erase hc, Finset.ne_of_mem_erase hc⟩) hM
  have hA2' : A.card = 2 := le_antisymm hA_le hA2
  -- (2) every colour left at `u` lies in `A`
  have hsub : Lu ⊆ A := by
    intro γ hγ
    by_contra hγA
    obtain ⟨hγL, hγx, hγa, hγb⟩ := hmemLu γ hγ
    apply hbad
    refine T.wheel_ext H hNT hS huS hu hhub L g hxa hxb γ hγL hγx hγa hγb (insert γ A) ?_ ?_ hM
    · rw [Finset.card_insert_of_notMem hγA]; omega
    · intro c hc hcγ
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact absurd rfl hcγ
      · exact ⟨Finset.mem_of_mem_erase hc, Finset.ne_of_mem_erase hc⟩
  have hLuA : Lu = A := Finset.eq_of_subset_of_card_le hsub (by omega)
  -- the three precolours are distinct members of `L u`
  have hinter : (L u ∩ G3).card = 3 := by
    have h1 := Finset.card_sdiff_add_card_inter (L u) G3
    have h2 : (L u ∩ G3).card ≤ G3.card := Finset.card_le_card Finset.inter_subset_right
    rw [← hLu, hLuA, hA2'] at h1
    omega
  have hG3eq : L u ∩ G3 = G3 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    (by omega)
  have hG3sub : G3 ⊆ L u := by rw [← hG3eq]; exact Finset.inter_subset_left
  have hab : g a ≠ g b := by
    intro e
    have : G3.card ≤ 2 := by
      rw [hG3, e]; simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.mem_insert,
        true_or]
      exact Finset.card_le_two
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := L u) (s₂ := G3))
    omega
  exact ⟨hA2', hLuA, hab, hG3sub (by simp [hG3]), hG3sub (by simp [hG3]),
    hG3sub (by simp [hG3])⟩

/-- **Lemma 1, wheels.** Two non-extendable precolourings of the principal path agree. -/
theorem wheel_unique (H : SimpleGraph V) {S : Finset V} {x a v₃ b u : V} {M : List V}
    (hNT : T.NT H S (x :: a :: v₃ :: (M ++ [b])))
    (hS : ∀ y ∈ S, y ∈ x :: a :: v₃ :: (M ++ [b]) ∨ y = u)
    (huS : u ∈ S) (hu : u ∉ x :: a :: v₃ :: (M ++ [b]))
    (hhub : ∀ z ∈ x :: a :: v₃ :: (M ++ [b]), H.Adj u z)
    (L : V → Finset C) (h5 : 5 ≤ (L u).card) (h3 : ∀ y ∈ v₃ :: M, 3 ≤ (L y).card)
    {g g' : V → C} (hxa : g x ≠ g a) (hxb : g x ≠ g b) (hxa' : g' x ≠ g' a)
    (hxb' : g' x ≠ g' b) (hbad : ¬ Extends H S [b, x, a] L g)
    (hbad' : ¬ Extends H S [b, x, a] L g') :
    g x = g' x ∧ g a = g' a ∧ g b = g' b := by
  classical
  have hnd := T.nodup hNT
  -- the mirror image
  obtain ⟨w, M', hwM⟩ : ∃ w M', M.reverse ++ [v₃] = w :: M' :=
    List.exists_cons_of_ne_nil (by simp)
  have hmemw : ∀ y, y ∈ w :: M' ↔ y ∈ M ∨ y = v₃ := by
    intro y; rw [← hwM]; simp
  have hcyc : ∀ y, y ∈ x :: b :: w :: (M' ++ [a]) ↔ y ∈ x :: a :: v₃ :: (M ++ [b]) := by
    intro y
    have := hmemw y
    simp only [List.mem_cons, List.mem_append, List.mem_singleton] at this ⊢
    tauto
  have hNTr : T.NT H S (x :: b :: w :: (M' ++ [a])) := by
    have h1 := T.reverse hNT
    have h2 : (x :: a :: v₃ :: (M ++ [b])).reverse = (b :: (w :: M') ++ [a]) ++ [x] := by
      rw [← hwM]; simp
    rw [h2] at h1
    simpa using T.rotate_back h1
  have hSr : ∀ y ∈ S, y ∈ x :: b :: w :: (M' ++ [a]) ∨ y = u := fun y hy =>
    (hS y hy).imp (hcyc y).2 id
  have hur : u ∉ x :: b :: w :: (M' ++ [a]) := fun h => hu ((hcyc u).1 h)
  have hhubr : ∀ z ∈ x :: b :: w :: (M' ++ [a]), H.Adj u z := fun z hz => hhub z ((hcyc z).1 hz)
  have hperm : ∀ y, y ∈ [a, x, b] ↔ y ∈ [b, x, a] := by intro y; simp; tauto
  have h3w : 3 ≤ (L w).card := h3 w (by
    have := (hmemw w).1 (by simp); simp only [List.mem_cons]; tauto)
  have hM' : ∀ y ∈ M', 3 ≤ (L y).card := fun y hy => h3 y (by
    have := (hmemw y).1 (by simp [hy]); simp only [List.mem_cons]; tauto)
  have hM : ∀ y ∈ M, 3 ≤ (L y).card := fun y hy => h3 y (by simp [hy])
  have hv3 : 3 ≤ (L v₃).card := h3 v₃ (by simp)
  have badr : ∀ {g : V → C}, ¬ Extends H S [b, x, a] L g → ¬ Extends H S [a, x, b] L g :=
    fun hb he => hb (extends_of_mem_iff hperm he)
  obtain ⟨hA, hLuA, hab, hgx, hga, hgb⟩ :=
    T.wheel_bad H hNT hS huS hu hhub L g hxa hxb h5 hv3 hM hbad
  obtain ⟨hB, hLuB, -, -, -, -⟩ :=
    T.wheel_bad H hNTr hSr huS hur hhubr L g hxb hxa h5 h3w hM' (badr hbad)
  obtain ⟨hA', hLuA', hab', hgx', hga', hgb'⟩ :=
    T.wheel_bad H hNT hS huS hu hhub L g' hxa' hxb' h5 hv3 hM hbad'
  obtain ⟨hB', hLuB', -, -, -, -⟩ :=
    T.wheel_bad H hNTr hSr huS hur hhubr L g' hxb' hxa' h5 h3w hM' (badr hbad')
  have hG : ∀ (g : V → C), ({g x, g b, g a} : Finset C) = {g x, g a, g b} := by
    intro g; ext; simp; tauto
  rw [hG] at hLuB hLuB'
  have hAB : (L v₃).erase (g a) = (L w).erase (g b) := hLuA.symm.trans hLuB
  have hAB' : (L v₃).erase (g' a) = (L w).erase (g' b) := hLuA'.symm.trans hLuB'
  -- a member of a list whose erasure has two elements but the list has at least three
  have hmem_of : ∀ (s : Finset C) (c : C), 3 ≤ s.card → (s.erase c).card = 2 → c ∈ s := by
    intro s c hs he
    by_contra hc
    rw [Finset.erase_eq_of_notMem hc] at he; omega
  have hgav : g a ∈ L v₃ := hmem_of _ _ hv3 hA
  have hg'av : g' a ∈ L v₃ := hmem_of _ _ hv3 hA'
  have hgbw : g b ∈ L w := hmem_of _ _ h3w hB
  have hg'bw : g' b ∈ L w := hmem_of _ _ h3w hB'
  by_cases hM0 : M = []
  · -- four outer vertices: no bad colouring at all
    subst hM0
    simp only [List.reverse_nil, List.nil_append, List.cons.injEq] at hwM
    obtain ⟨hw, -⟩ := hwM
    subst hw
    exfalso
    have : g b ∈ (L v₃).erase (g a) := Finset.mem_erase.mpr ⟨hab.symm, hgbw⟩
    rw [hAB] at this
    exact (Finset.ne_of_mem_erase this) rfl
  · have haa : g a = g' a := by
      by_contra hne
      have h1 : g' a ∈ (L v₃).erase (g a) := Finset.mem_erase.mpr ⟨fun e => hne e.symm, hg'av⟩
      rw [hAB] at h1
      have h2 : g' a ∈ (L w).erase (g' b) :=
        Finset.mem_erase.mpr ⟨hab', Finset.mem_of_mem_erase h1⟩
      rw [← hAB'] at h2
      exact (Finset.ne_of_mem_erase h2) rfl
    have hbb : g b = g' b := by
      by_contra hne
      have h1 : g' b ∈ (L w).erase (g b) := Finset.mem_erase.mpr ⟨fun e => hne e.symm, hg'bw⟩
      rw [← hAB] at h1
      have h2 : g' b ∈ (L v₃).erase (g' a) :=
        Finset.mem_erase.mpr ⟨fun e => hab' e.symm, Finset.mem_of_mem_erase h1⟩
      rw [hAB'] at h2
      exact (Finset.ne_of_mem_erase h2) rfl
    refine ⟨?_, haa, hbb⟩
    by_contra hne
    have h1 : g x ∈ (L u) \ {g' x, g' a, g' b} := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hgx, hne, haa ▸ hxa, hbb ▸ hxb⟩
    rw [hLuA', ← haa, ← hLuA] at h1
    simp at h1

end NTCalc

end ThomassenManyColourings
