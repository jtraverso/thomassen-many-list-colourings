/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Interface

/-!
# Theorem 1 (Thomassen 1994): near-triangulations are 2-extendable

Let `H` on `S` be a near-triangulation with outer cycle `a b v₃ … v_k`. If `a, b` are precoloured
with distinct colours, the other outer vertices have lists of size at least three and the interior
vertices lists of size at least five, then the precolouring extends to a proper list colouring.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- `f` is proper on `S`. -/
def IsProperOn (H : SimpleGraph V) (S : Finset V) (f : V → C) : Prop :=
  ∀ u ∈ S, ∀ w ∈ S, H.Adj u w → f u ≠ f w

namespace NTCalc

variable (T : NTCalc V)

theorem mem_of_mem_cycle {H : SimpleGraph V} {S : Finset V} {c : List V} (h : T.NT H S c)
    {v : V} (hv : v ∈ c) : v ∈ S := T.subset h v hv

/-- **Theorem 1.** -/
theorem thm1 (H : SimpleGraph V) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∀ (a b : V) (l : List V),
    T.NT H S (a :: b :: l) → ∀ (L : V → Finset C) (f₀ : V → C), f₀ a ≠ f₀ b →
    (∀ v ∈ l, 3 ≤ (L v).card) → (∀ v ∈ S, v ∉ a :: b :: l → 5 ≤ (L v).card) →
    ∃ f : V → C, f a = f₀ a ∧ f b = f₀ b ∧ (∀ v ∈ S, v ≠ a → v ≠ b → f v ∈ L v) ∧
      IsProperOn H S f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS a b l hNT L f₀ hab h3 h5
  have hnd := T.nodup hNT
  rcases l.eq_nil_or_concat with rfl | ⟨init, v, rfl⟩
  · -- a single edge
    have hS2 := T.two hNT
    refine ⟨f₀, rfl, rfl, ?_, ?_⟩
    · intro x hx hxa hxb
      rw [hS2] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> contradiction
    · intro u hu w hw huw
      rw [hS2] at hu hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact absurd huw (H.loopless.irrefl _)
      · exact hab
      · exact hab.symm
      · exact absurd huw (H.loopless.irrefl _)
  · simp only [List.concat_eq_append] at hNT h3 h5 hnd ⊢
    have hrot : T.NT H S (v :: a :: b :: init) := by
      apply T.rotate_back
      simpa using hNT
    have hvS : v ∈ S := T.subset hNT v (by simp)
    by_cases hch : ∃ z ∈ b :: init, z ≠ (b :: init).getLast (List.cons_ne_nil _ _) ∧ H.Adj v z
    · -- a chord at `v`
      obtain ⟨z, hz, hzl, hvz⟩ := hch
      obtain ⟨s, t, hst⟩ := List.append_of_mem hz
      have ht : t ≠ [] := by
        rintro rfl
        apply hzl
        simp [hst]
      obtain ⟨m, hm⟩ : ∃ m, s ++ [z] = b :: m := by
        rcases s with _ | ⟨x, s'⟩
        · simp only [List.nil_append, List.cons.injEq] at hst
          exact ⟨[], by simp [hst.1]⟩
        · simp only [List.cons_append, List.cons.injEq] at hst
          exact ⟨s' ++ [z], by simp [hst.1]⟩
      have hinit : init = m ++ t := by
        have : b :: init = b :: (m ++ t) := by
          rw [hst, ← List.cons_append, ← hm]; simp
        simpa using this
      have hrot' : T.NT H S (v :: ((a :: s) ++ z :: t)) := by
        have : v :: a :: b :: init = v :: ((a :: s) ++ z :: t) := by rw [hst]; rfl
        rwa [this] at hrot
      have hR := T.nodup hrot'
      obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hrot' (List.cons_ne_nil _ _) ht hvz
      have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
      have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
      have hmem₁₂ : ∀ x, x ∈ S₁ → x ∈ S₂ → x = v ∨ x = z := by
        intro x h1 h2
        have : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
        rw [hI] at this
        simpa using this
      -- the shape of the rotated cycle
      have hR' : (v :: (a :: (b :: (m ++ t)))).Nodup ∧ z ∈ b :: m ∧ z ∉ t := by
        refine ⟨?_, ?_, ?_⟩
        · have := T.nodup hrot; rwa [hinit] at this
        · rw [← hm]; simp
        · intro hzt
          have h' : (s ++ z :: t).Nodup := by
            have := hR; simp only [List.nodup_cons, List.cons_append] at this; exact this.2.2
          rw [List.nodup_append] at h'
          exact (List.nodup_cons.mp h'.2.1).1 hzt
      obtain ⟨hnd', hzbm, hzt⟩ := hR'
      simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hnd'
      obtain ⟨⟨hva, hvb, hvm, hvt⟩, ⟨hab', ham, hat⟩, ⟨hbm, hbt⟩, hmt⟩ := hnd'
      have hmt' := List.nodup_append.mp hmt
      have h₁' : T.NT H S₁ (a :: b :: (m ++ [v])) := by
        have := T.rotate h₁
        simpa [hm] using this
      have h₂' : T.NT H S₂ (v :: z :: t) := by
        apply T.rotate_back
        simpa using h₂
      have hvS₁ : v ∈ S₁ := T.subset h₁ v (by simp)
      have hzS₁ : z ∈ S₁ := T.subset h₁ z (by simp)
      have haS₁ : a ∈ S₁ := T.subset h₁ a (by simp)
      have hbS₁ : b ∈ S₁ := T.subset h₁' b (by simp)
      have ht_not : ∀ x ∈ t, x ∉ S₁ := by
        intro x hx hx1
        rcases hmem₁₂ x hx1 (T.subset h₂ x (by simp [hx])) with rfl | rfl
        · exact hvt hx
        · exact hzt hx
      have hcard₁ : S₁.card < n := by
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil t ht
        rw [← hS]
        refine Finset.card_lt_card ⟨hS₁, fun h => ht_not w hw (h ?_)⟩
        exact T.subset hNT w (by simp [hinit, hw])
      have ha_not : a ∉ S₂ := by
        intro h2
        rcases hmem₁₂ a haS₁ h2 with h | h
        · exact hva h.symm
        · rw [h] at ham hab'
          rcases List.mem_cons.mp hzbm with h' | h'
          · exact hab' h'
          · exact ham h'
      have hcard₂ : S₂.card < n := by
        rw [← hS]
        exact Finset.card_lt_card ⟨hS₂, fun h => ha_not (h (T.subset hNT a (by simp)))⟩
      -- colour the piece containing `a b`
      obtain ⟨f₁, hf₁a, hf₁b, hf₁L, hf₁P⟩ := ih _ hcard₁ S₁ rfl a b (m ++ [v]) h₁' L f₀ hab
        (by
          intro x hx
          apply h3
          simp only [List.mem_append, List.mem_singleton] at hx ⊢
          rcases hx with hx | hx
          · left; rw [hinit]; exact List.mem_append_left _ hx
          · right; exact hx)
        (by
          intro x hx hxc
          apply h5 x (hS₁ hx)
          intro hxc'
          apply hxc
          simp only [List.mem_cons, List.mem_append, List.mem_singleton, hinit] at hxc' ⊢
          rcases hxc' with h | h | (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact absurd hx (ht_not x h)
          · exact Or.inr (Or.inr (Or.inr h)))
      -- colour the other piece with `v z` precoloured
      obtain ⟨f₂, hf₂v, hf₂z, hf₂L, hf₂P⟩ := ih _ hcard₂ S₂ rfl v z t h₂' L f₁
        (hf₁P v hvS₁ z hzS₁ hvz)
        (by
          intro x hx
          apply h3
          simp [hinit, hx])
        (by
          intro x hx hxc
          apply h5 x (hS₂ hx)
          intro hxc'
          apply hxc
          simp only [List.mem_cons, List.mem_append, List.mem_singleton, hinit] at hxc' ⊢
          have hS1 : ∀ y ∈ a :: b :: (m ++ [v]), y ∈ S₂ → y = v ∨ y = z := fun y hy h2 =>
            hmem₁₂ y (T.subset h₁' y hy) h2
          rcases hxc' with h | h | (h | h) | h
          · rcases hS1 x (by simp [h]) hx with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inl h')
          · rcases hS1 x (by simp [h]) hx with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inl h')
          · rcases hS1 x (by simp [h]) hx with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h)
          · exact Or.inl (by simpa using h))
      refine ⟨fun x => if x ∈ S₁ then f₁ x else f₂ x, by simp [haS₁, hf₁a],
        by simp [hbS₁, hf₁b], ?_, ?_⟩
      · intro x hx hxa hxb
        by_cases h1 : x ∈ S₁
        · simp only [h1, if_true]; exact hf₁L x h1 hxa hxb
        · simp only [h1, if_false]
          have h2 : x ∈ S₂ := by
            have : x ∈ S₁ ∪ S₂ := hU ▸ hx
            exact (Finset.mem_union.mp this).resolve_left h1
          exact hf₂L x h2 (fun e => h1 (e ▸ hvS₁)) (fun e => h1 (e ▸ hzS₁))
      · have hagree : ∀ x ∈ S₁, x ∈ S₂ → f₂ x = f₁ x := by
          intro x h1 h2
          rcases hmem₁₂ x h1 h2 with rfl | rfl
          · exact hf₂v
          · exact hf₂z
        have hside : ∀ x ∈ S, x ∉ S₁ → x ∈ S₂ := by
          intro x hx h1
          have : x ∈ S₁ ∪ S₂ := hU ▸ hx
          exact (Finset.mem_union.mp this).resolve_left h1
        intro u hu w hw huw
        by_cases hu1 : u ∈ S₁ <;> by_cases hw1 : w ∈ S₁
        · simp only [hu1, hw1, if_true]; exact hf₁P u hu1 w hw1 huw
        · simp only [hu1, hw1, if_true, if_false]
          have hw2 := hside w hw hw1
          have hu2 : u ∈ S₂ := (hX u hu1 w hw2 huw).resolve_right hw1
          rw [← hagree u hu1 hu2]
          exact hf₂P u hu2 w hw2 huw
        · simp only [hu1, hw1, if_true, if_false]
          have hu2 := hside u hu hu1
          have hw2 : w ∈ S₂ := (hX w hw1 u hu2 huw.symm).resolve_right hu1
          rw [← hagree w hw1 hw2]
          exact hf₂P u hu2 w hw2 huw
        · simp only [hu1, hw1, if_false]
          exact hf₂P u (hside u hu hu1) w (hside w hw hw1) huw
    · -- no chord at `v`: delete it
      push_neg at hch
      set p := (b :: init).getLast (List.cons_ne_nil _ _) with hp
      have hlast : (a :: b :: init).getLast? = some p := by
        rw [List.getLast?_cons_cons, List.getLast?_eq_getLast (List.cons_ne_nil _ _)]
      obtain ⟨us, hus, hnb, hNT', -⟩ := T.delete hrot (by simp) (by
        intro z hz hvz
        rcases List.mem_cons.mp hz with rfl | hz'
        · left; rfl
        · right; rw [hlast]
          by_contra hne
          exact (hch z hz' (fun e => hne (by rw [e]))) hvz)
      have hndr := T.nodup hrot
      have hva : v ≠ a := by
        intro e; simp [e] at hndr
      have hvb : v ≠ b := by
        intro e; simp [e] at hndr
      have hLv : 3 ≤ (L v).card := h3 v (by simp)
      have h2 : 1 < ((L v).erase (f₀ a)).card := by
        have := Finset.pred_card_le_card_erase (s := L v) (a := f₀ a)
        omega
      obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.mp h2
      let L' : V → Finset C := fun x => if x ∈ us then ((L x).erase α).erase β else L x
      have hus_int : ∀ u ∈ us, 5 ≤ (L u).card := by
        intro u hu
        obtain ⟨huS, hunot⟩ := hus u hu
        apply h5 u huS
        intro hc
        apply hunot
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hc ⊢
        tauto
      have hcard' : (S.erase v).card < n := by
        rw [← hS]; exact Finset.card_erase_lt_of_mem hvS
      have hNT'' : T.NT H (S.erase v) (a :: b :: (init ++ us)) := by simpa using hNT'
      obtain ⟨f', hf'a, hf'b, hf'L, hf'P⟩ := ih _ hcard' (S.erase v) rfl a b (init ++ us) hNT''
        L' f₀ hab
        (by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · have hxu : x ∉ us := by
              intro hxu
              exact (hus x hxu).2 (by simp [hx])
            simp only [L', hxu, if_false]
            exact h3 x (by simp [hx])
          · simp only [L', hx, if_true]
            have h1 := Finset.pred_card_le_card_erase (s := (L x).erase α) (a := β)
            have h2 := Finset.pred_card_le_card_erase (s := L x) (a := α)
            have := hus_int x hx
            omega)
        (by
          intro x hx hxc
          have hxu : x ∉ us := fun h => hxc (by simp [h])
          simp only [L', hxu, if_false]
          apply h5 x (Finset.mem_of_mem_erase hx)
          intro hc
          have hxv : x ≠ v := Finset.ne_of_mem_erase hx
          apply hxc
          simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hc ⊢
          tauto)
      set γ : C := if α ≠ f' p then α else β with hγ
      have hγL : γ ∈ L v := by
        rw [hγ]; split_ifs
        · exact Finset.mem_of_mem_erase hα
        · exact Finset.mem_of_mem_erase hβ
      have hγa : γ ≠ f₀ a := by
        rw [hγ]; split_ifs
        · exact Finset.ne_of_mem_erase hα
        · exact Finset.ne_of_mem_erase hβ
      have hγp : γ ≠ f' p := by
        rw [hγ]; split_ifs with h
        · exact h
        · push_neg at h; rw [← h]; exact hαβ.symm
      have hγu : ∀ u ∈ us, f' u ≠ γ := by
        intro u hu
        have huS : u ∈ S.erase v := Finset.mem_erase.mpr
          ⟨fun e => (hus u hu).2 (by simp [e]), (hus u hu).1⟩
        have hua : u ≠ a := fun e => (hus u hu).2 (by simp [e])
        have hub : u ≠ b := fun e => (hus u hu).2 (by simp [e])
        have hm := hf'L u huS hua hub
        simp only [L', hu, if_true] at hm
        have h1 := Finset.ne_of_mem_erase hm
        have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
        rw [hγ]; split_ifs
        · exact h2
        · exact h1
      refine ⟨Function.update f' v γ, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne hva.symm]; exact hf'a
      · rw [Function.update_of_ne hvb.symm]; exact hf'b
      · intro x hx hxa hxb
        by_cases hxv : x = v
        · subst hxv; rw [Function.update_self]; exact hγL
        · rw [Function.update_of_ne hxv]
          have hm := hf'L x (Finset.mem_erase.mpr ⟨hxv, hx⟩) hxa hxb
          by_cases hxu : x ∈ us
          · simp only [L', hxu, if_true] at hm
            exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)
          · simpa [L', hxu] using hm
      · -- neighbours of `v`
        have hnbv : ∀ w ∈ S, H.Adj v w → w ≠ v → Function.update f' v γ w ≠ γ := by
          intro w hw hvw hwv
          rw [Function.update_of_ne hwv]
          rcases hnb w hw hvw with h | h | h
          · simp only [List.head?_cons, Option.some.injEq] at h
            subst h
            rw [hf'a]; exact hγa.symm
          · rw [hlast, Option.some.injEq] at h
            subst h
            exact hγp.symm
          · exact hγu w h
        intro u hu w hw huw
        by_cases hu' : u = v
        · subst hu'
          have hwv : w ≠ u := fun e => H.loopless.irrefl _ (e ▸ huw)
          rw [Function.update_self]
          exact (hnbv w hw huw hwv).symm
        · by_cases hw' : w = v
          · subst hw'
            rw [Function.update_self]
            exact hnbv u hu huw.symm hu'
          · rw [Function.update_of_ne hu', Function.update_of_ne hw']
            exact hf'P u (Finset.mem_erase.mpr ⟨hu', hu⟩) w (Finset.mem_erase.mpr ⟨hw', hw⟩) huw

end NTCalc

end ThomassenManyColourings
