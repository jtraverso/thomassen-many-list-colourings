/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Defs

/-!
# Theorem 3, Claim 1: chords of the outer cycle

Each claim of the paper's minimal-counterexample argument is stated here as a reduction: under
the induction hypothesis (Theorem 3 for smaller vertex sets), a configuration yields the
conclusion of Theorem 3.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

/-- Theorem 3 for all vertex sets of size less than `n` (and all graphs). -/
def Thm3Below (n : ℕ) (C : Type*) [DecidableEq C] : Prop :=
  ∀ (H : SimpleGraph V) (S : Finset V), S.card < n → ∀ (x : V) (P : List V) (a c : V)
    (L : V → Finset C) (g : V → C), T.NT H S (x :: P) → Thm3Hyp H S x P a c L g →
    Extends H S [c, x, a] L g ∨ Exc3 H S x P a c L

/-- An exceptional configuration of a piece is one of the whole graph. -/
theorem exc3_mono {H : SimpleGraph V} {S S₂ : Finset V} {x a c : V} {Q Q₂ : List V}
    {L : V → Finset C} (h : Exc3 H S₂ x Q₂ a c L) (hS : S₂ ⊆ S) (hQ : ∀ y ∈ Q₂, y ∈ Q)
    (hout : ∀ u ∈ S₂, u ∉ x :: Q₂ → u ∉ x :: Q) : Exc3 H S x Q a c L := by
  obtain ⟨P', U, hGW, hnd, hh, hl, hsub, hU, hL⟩ := h
  exact ⟨P', U, hGW, hnd, hh, hl, fun y hy => hQ y (hsub y hy),
    fun u hu => ⟨hS (hU u hu).1, hout u (hU u hu).1 (hU u hu).2⟩, hL⟩

/-- **Claim 1, chords avoiding `x`.** -/
theorem claim1_nox (H : SimpleGraph V) {S : Finset V} {x y z : V} {P₀ M P₁ : List V}
    {a c : V} {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (P₀ ++ y :: M ++ z :: P₁)))
    (hh : Thm3Hyp H S x (P₀ ++ y :: M ++ z :: P₁) a c L g) (hM : M ≠ []) (hyz : H.Adj y z)
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (P₀ ++ y :: M ++ z :: P₁) a c L := by
  classical
  have hnd := T.nodup hNT
  have hrot : T.NT H S (y :: (M ++ z :: (P₁ ++ x :: P₀))) := by
    have := T.rotate_append (A := x :: P₀) (B := y :: M ++ z :: P₁) (by simpa using hNT)
    simpa using this
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hrot hM (by simp) hyz
  have h₂' : T.NT H S₂ (x :: (P₀ ++ y :: z :: P₁)) := by
    have := T.rotate_append (A := z :: P₁) (B := x :: P₀ ++ [y]) (by simpa using h₂)
    simpa using this
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = y ∨ w = z := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
  have hndr := T.nodup hrot
  simp only [List.nodup_cons, List.mem_append, List.mem_cons, not_or, List.nodup_append]
    at hndr
  have hMy : ∀ m ∈ M, m ≠ y := fun m hm e => hndr.1.1 (e ▸ hm)
  have hMz : ∀ m ∈ M, m ≠ z := fun m hm e => hndr.2.2.2 m hm z (by simp) e
  have hMS : ∀ m ∈ M, m ∈ S₁ ∧ m ∉ S₂ := by
    intro m hm
    have h1 : m ∈ S₁ := T.subset h₁ m (by simp [hm])
    exact ⟨h1, fun h2 => (hmem m h1 h2).elim (hMy m hm) (hMz m hm)⟩
  have hcard : S₂.card < S.card := by
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hM
    exact Finset.card_lt_card ⟨hS₂, fun h => (hMS m hm).2 (h (hS₁ (hMS m hm).1))⟩
  have hsubQ : ∀ w ∈ P₀ ++ y :: z :: P₁, w ∈ P₀ ++ y :: M ++ z :: P₁ := by
    intro w hw
    simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto
  have hout : ∀ u ∈ S₂, u ∉ x :: (P₀ ++ y :: z :: P₁) → u ∉ x :: (P₀ ++ y :: M ++ z :: P₁) := by
    intro u hu hun h
    apply hun
    have huM : u ∉ M := fun hm => (hMS u hm).2 hu
    simp only [List.mem_cons, List.mem_append] at h ⊢
    tauto
  have hh₂ : Thm3Hyp H S₂ x (P₀ ++ y :: z :: P₁) a c L g := by
    refine ⟨?_, ?_, by simp; omega, hh.ok, fun w hw hwa hwc => hh.three w (hsubQ w hw) hwa hwc,
      fun w hw hwc => hh.five w (hS₂ hw) (hout w hw hwc)⟩
    · have := hh.head
      rcases P₀ with _ | ⟨p, P₀'⟩
      · simp only [List.nil_append, List.cons_append, List.head?_cons] at this ⊢; exact this
      · simp only [List.cons_append, List.head?_cons] at this ⊢; exact this
    · have := hh.last
      have key : ∀ A : List V, (A ++ z :: P₁).getLast? = (z :: P₁).getLast? :=
        fun A => List.getLast?_append_of_ne_nil _ (by simp)
      have e1 : P₀ ++ y :: M ++ z :: P₁ = (P₀ ++ y :: M) ++ z :: P₁ := by simp
      have e2 : P₀ ++ y :: z :: P₁ = (P₀ ++ [y]) ++ z :: P₁ := by simp
      rw [e1, key] at this
      rw [e2, key]; exact this
  have hS₁c : ∀ w ∈ S₁, w ∈ x :: (P₀ ++ y :: z :: P₁) → w = y ∨ w = z := fun w hw h =>
    hmem w hw (T.subset h₂' w h)
  have haS₂ : a ∈ S₂ := T.subset h₂' a (List.mem_cons_of_mem _ (List.mem_of_mem_head? hh₂.head))
  have hcS₂ : c ∈ S₂ := T.subset h₂' c (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hh₂.last))
  rcases ih H S₂ hcard x _ a c L g h₂' hh₂ with hE | hX3
  · left
    obtain ⟨f₂, hf₂c, hf₂L, hf₂p⟩ := hE
    have hyS₂ : y ∈ S₂ := T.subset h₂' y (by simp)
    have hzS₂ : z ∈ S₂ := T.subset h₂' z (by simp)
    have h₁' : T.NT H S₁ (z :: y :: M) := T.rotate_back (by simpa using h₁)
    obtain ⟨f₁, hf₁z, hf₁y, hf₁L, hf₁p⟩ := T.thm1 H _ S₁ rfl z y M h₁' L f₂
      (hf₂p z hzS₂ y hyS₂ hyz.symm)
      (by
        intro m hm
        apply hh.three m (by simp [hm])
        · intro e; subst e; exact (hMS m hm).2 haS₂
        · intro e; subst e; exact (hMS m hm).2 hcS₂)
      (by
        intro w hw hwc
        apply hh.five w (hS₁ hw)
        intro h
        by_cases hwM : w ∈ M
        · exact hwc (by simp [hwM])
        · have h' : w ∈ x :: (P₀ ++ y :: z :: P₁) := by
            simp only [List.mem_cons, List.mem_append] at h ⊢; tauto
          rcases hS₁c w hw h' with rfl | rfl
          · exact hwc (by simp)
          · exact hwc (by simp))
    refine ⟨fun w => if w ∈ S₂ then f₂ w else f₁ w, ?_, ?_, ?_⟩
    · intro w hw
      have hw2 : w ∈ S₂ := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact hcS₂
        · exact T.subset h₂' w (by simp)
        · exact haS₂
      simp only [hw2, if_true]; exact hf₂c w hw
    · intro w hw hwc
      by_cases h2 : w ∈ S₂
      · simp only [h2, if_true]; exact hf₂L w h2 hwc
      · simp only [h2, if_false]
        have h1 : w ∈ S₁ := (Finset.mem_union.mp (hU ▸ hw)).resolve_right h2
        exact hf₁L w h1 (fun e => h2 (e ▸ hzS₂)) (fun e => h2 (e ▸ hyS₂))
    · refine isProperOn_glue (S₁ := S₂) (S₂ := S₁) (by rw [Finset.union_comm]; exact hU)
        (fun u hu w hw huw => (hX w hw u hu huw.symm).symm) hf₂p hf₁p ?_
      intro w h2 h1
      rcases hmem w h1 h2 with rfl | rfl
      · exact hf₁y
      · exact hf₁z
  · exact Or.inr (exc3_mono hX3 hS₂ hsubQ hout)

/-- Gluing two exceptional configurations along the principal edge `x y`. -/
theorem exc3_glue {H : SimpleGraph V} {S S₁ S₂ : Finset V} {x a y c : V} {P₀ P₁ : List V}
    {L : V → Finset C} (h₁ : Exc3 H S₁ x (P₀ ++ [y]) a y L) (h₂ : Exc3 H S₂ x (y :: P₁) y c L)
    (hS₁ : S₁ ⊆ S) (hS₂ : S₂ ⊆ S) (hy : (L y).card = 3) (hP : (P₀ ++ y :: P₁).Nodup)
    (hout₁ : ∀ u ∈ S₁, u ∉ x :: (P₀ ++ [y]) → u ∉ x :: (P₀ ++ y :: P₁))
    (hout₂ : ∀ u ∈ S₂, u ∉ x :: y :: P₁ → u ∉ x :: (P₀ ++ y :: P₁)) :
    Exc3 H S x (P₀ ++ y :: P₁) a c L := by
  obtain ⟨Q₁, U₁, hG₁, hnd₁, hh₁, hl₁, hsub₁, hU₁, hL₁⟩ := h₁
  obtain ⟨Q₂, U₂, hG₂, hnd₂, hh₂, hl₂, hsub₂, hU₂, hL₂⟩ := h₂
  obtain ⟨Q₁', rfl⟩ : ∃ Q₁', Q₁ = Q₁' ++ [y] := by
    rcases Q₁.eq_nil_or_concat with h | ⟨Q₁', z, h⟩
    · subst h; simp at hl₁
    · subst h; rw [List.concat_eq_append, List.getLast?_append] at hl₁
      simp at hl₁; subst hl₁; exact ⟨Q₁', by simp⟩
  obtain ⟨Q₂', rfl⟩ : ∃ Q₂', Q₂ = y :: Q₂' := by
    rcases Q₂ with _ | ⟨z, Q₂'⟩
    · simp at hh₂
    · simp at hh₂; subst hh₂; exact ⟨Q₂', rfl⟩
  refine ⟨Q₁' ++ y :: Q₂', U₁ ∪ U₂, GW.append hG₁ hG₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the glued path has no repetition
    have hy1 : y ∉ Q₁' := fun h => (List.nodup_append.mp hnd₁).2.2 y h y (by simp) rfl
    have hy2 : y ∉ Q₂' := (List.nodup_cons.mp hnd₂).1
    have hQ₁P : ∀ w ∈ Q₁', w ∈ P₀ := by
      intro w hw
      have := hsub₁ w (List.mem_append_left _ hw)
      rcases List.mem_append.mp this with h | h
      · exact h
      · simp at h; subst h; exact absurd hw hy1
    have hQ₂P : ∀ w ∈ Q₂', w ∈ P₁ := by
      intro w hw
      have := hsub₂ w (List.mem_cons_of_mem _ hw)
      rcases List.mem_cons.mp this with h | h
      · subst h; exact absurd hw hy2
      · exact h
    have hPd := List.nodup_append.mp hP
    rw [List.nodup_append]
    refine ⟨(List.nodup_append.mp hnd₁).1, List.nodup_cons.mpr ⟨hy2, (List.nodup_cons.mp hnd₂).2⟩, ?_⟩
    intro w hw w' hw' e
    subst e
    rcases List.mem_cons.mp hw' with h | h
    · subst h; exact hy1 hw
    · exact hPd.2.2 w (hQ₁P w hw) w (List.mem_cons_of_mem _ (hQ₂P w h)) rfl
  · rcases Q₁' with _ | ⟨q, Q₁''⟩
    · simp at hh₁ ⊢; exact hh₁
    · simpa using hh₁
  · have key : ∀ A : List V, (A ++ y :: Q₂').getLast? = (y :: Q₂').getLast? :=
      fun A => List.getLast?_append_of_ne_nil _ (by simp)
    rw [key]; exact hl₂
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · have := hsub₁ w (List.mem_append_left _ h)
      simp only [List.mem_append, List.mem_cons, List.mem_singleton] at this ⊢; tauto
    · have := hsub₂ w h
      simp only [List.mem_append, List.mem_cons] at this ⊢; tauto
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact ⟨hS₁ (hU₁ u h).1, hout₁ u (hU₁ u h).1 (hU₁ u h).2⟩
    · exact ⟨hS₂ (hU₂ u h).1, hout₂ u (hU₂ u h).1 (hU₂ u h).2⟩
  · intro w hw hwa hwc
    by_cases hwy : w = y
    · subst hwy; exact hy
    rcases List.mem_append.mp hw with h | h
    · exact hL₁ w (List.mem_append_left _ h) hwa hwy
    · exact hL₂ w h hwy hwc

set_option maxHeartbeats 8000000 in
/-- **Claim 1, chords at `x`.** -/
theorem claim1_x (H : SimpleGraph V) {S : Finset V} {x y : V} {P₀ P₁ : List V} {a c : V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (P₀ ++ y :: P₁))) (hh : Thm3Hyp H S x (P₀ ++ y :: P₁) a c L g)
    (hP₀ : P₀ ≠ []) (hP₁ : P₁ ≠ []) (hxy : H.Adj x y)
    (hya : P₀ = [a] ∨ ¬ H.Adj a y) (hyc : P₁ = [c] ∨ ¬ H.Adj y c)
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (P₀ ++ y :: P₁) a c L := by
  classical
  obtain ⟨P₀', rfl⟩ : ∃ P₀', P₀ = a :: P₀' := by
    obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP₀
    have := hh.head; simp at this; subst this; exact ⟨P', rfl⟩
  obtain ⟨P₁', rfl⟩ : ∃ P₁', P₁ = P₁' ++ [c] := by
    rcases P₁.eq_nil_or_concat with h | ⟨P₁', z, h⟩
    · exact absurd h hP₁
    · subst h
      have := hh.last
      rw [List.concat_eq_append, List.getLast?_append_of_ne_nil _ (by simp)] at this
      have e : y :: (P₁' ++ [z]) = (y :: P₁') ++ [z] := by simp
      rw [e, List.getLast?_append_of_ne_nil _ (by simp)] at this
      have hzc : z = c := by simpa using this
      subst hzc; exact ⟨P₁', by simp⟩
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hNT (by simp) (by simp) hxy
  have h₁' : T.NT H S₁ (x :: a :: (P₀' ++ [y])) := by simpa using h₁
  have h₂' : T.NT H S₂ (x :: y :: (P₁' ++ [c])) := T.rotate_back (by simpa using h₂)
  have h₂'' : T.NT H S₂ (c :: x :: y :: P₁') := T.rotate_back (by simpa using h₂')
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = x ∨ w = y := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
  have hside : ∀ w ∈ S, w ∉ S₁ → w ∈ S₂ := fun w hw h1 =>
    (Finset.mem_union.mp (hU ▸ hw)).resolve_left h1
  have hnd := T.nodup hNT
  simp only [List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or,
    List.nodup_append] at hnd
  have hxS₁ : x ∈ S₁ := T.subset h₁' x (by simp)
  have hyS₁ : y ∈ S₁ := T.subset h₁' y (by simp)
  have hxS₂ : x ∈ S₂ := T.subset h₂' x (by simp)
  have hyS₂ : y ∈ S₂ := T.subset h₂' y (by simp)
  have hP₀side : ∀ w ∈ a :: P₀', w ∈ S₁ ∧ w ∉ S₂ := by
    intro w hw
    have h1 : w ∈ S₁ := T.subset h₁' w (by simp only [List.mem_cons, List.mem_append] at hw ⊢; tauto)
    refine ⟨h1, fun h2 => ?_⟩
    rcases hmem w h1 h2 with rfl | rfl
    · simp only [List.mem_cons] at hw; tauto
    · simp only [List.mem_cons] at hw; tauto
  have hP₁side : ∀ w ∈ P₁' ++ [c], w ∈ S₂ ∧ w ∉ S₁ := by
    intro w hw
    have h2 : w ∈ S₂ := T.subset h₂' w (by simp only [List.mem_cons, List.mem_append] at hw ⊢; tauto)
    refine ⟨h2, fun h1 => ?_⟩
    rcases hmem w h1 h2 with rfl | rfl
    · simp only [List.mem_append, List.mem_cons] at hw; tauto
    · simp only [List.mem_append, List.mem_cons] at hw; tauto
  have haS₁ := (hP₀side a (by simp)).1
  have haS₂ := (hP₀side a (by simp)).2
  have hcS₂ := (hP₁side c (by simp)).1
  have hcS₁ := (hP₁side c (by simp)).2
  have hya_ne : y ≠ a := fun e => haS₂ (e ▸ hyS₂)
  have hyc_ne : y ≠ c := fun e => hcS₁ (e ▸ hyS₁)
  have hxa_ne : x ≠ a := fun e => haS₂ (e ▸ hxS₂)
  have hxc_ne : x ≠ c := fun e => hcS₁ (e ▸ hxS₁)
  have hxy_ne : x ≠ y := fun e => H.loopless.irrefl x (e ▸ hxy)
  have h3y : 3 ≤ (L y).card := hh.three y (by simp) hya_ne hyc_ne
  have hok := hh.ok
  have haP₀' : a ∉ P₀' := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp (T.nodup h₁')).2).1 (List.mem_append_left _ h)
  have hcP₁' : c ∉ P₁' := fun h => (List.nodup_cons.mp (T.nodup h₂'')).1 (by simp [h])
  -- the extension predicates of the two sides
  let E1 : C → Prop := fun β => Extends H S₁ [y, x, a] L (Function.update g y β)
  let E2 : C → Prop := fun β => Extends H S₂ [c, x, y] L (Function.update g y β)
  have glueE : ∀ β ∈ L y, E1 β → E2 β → Extends H S [c, x, a] L g := by
    intro β hβ ⟨f₁, h1c, h1L, h1p⟩ ⟨f₂, h2c, h2L, h2p⟩
    refine ⟨fun w => if w ∈ S₁ then f₁ w else f₂ w, ?_, ?_, ?_⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · simp [hcS₁, h2c w (by simp), Function.update_of_ne (Ne.symm hyc_ne)]
      · simp [hxS₁, h1c w (by simp), Function.update_of_ne hxy_ne]
      · simp [haS₁, h1c w (by simp), Function.update_of_ne (Ne.symm hya_ne)]
    · intro w hw hwc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwc
      by_cases hwy : w = y
      · subst hwy; simp [hyS₁, h1c w (by simp), hβ]
      by_cases h1 : w ∈ S₁
      · simp only [h1, if_true]; exact h1L w h1 (by simp [hwy, hwc.2.1, hwc.2.2])
      · simp only [h1, if_false]; exact h2L w (hside w hw h1) (by simp [hwy, hwc.1, hwc.2.1])
    · refine isProperOn_glue hU hX h1p h2p ?_
      intro w hw1 hw2
      rcases hmem w hw1 hw2 with rfl | rfl
      · rw [h2c w (by simp), h1c w (by simp)]
      · rw [h2c w (by simp), h1c w (by simp)]
  -- Theorem 1 on each side, with a three-element list at `y`
  have hint₁ : ∀ w ∈ S₁, w ∉ x :: a :: (P₀' ++ [y]) → w ∉ x :: (a :: P₀' ++ y :: (P₁' ++ [c])) := by
    intro w hw hwc h
    apply hwc
    by_cases hwP : w ∈ P₁' ++ [c]
    · exact absurd hw (hP₁side w hwP).2
    · simp only [List.cons_append, List.mem_cons, List.mem_append] at h hwP ⊢; tauto
  have hint₂ : ∀ w ∈ S₂, w ∉ c :: x :: y :: P₁' → w ∉ x :: (a :: P₀' ++ y :: (P₁' ++ [c])) := by
    intro w hw hwc h
    apply hwc
    by_cases hwP : w ∈ a :: P₀'
    · exact absurd hw (hP₀side w hwP).2
    · simp only [List.cons_append, List.mem_cons, List.mem_append] at h hwP ⊢; tauto
  have T1 : ∀ L₃ : Finset C, 3 ≤ L₃.card → ∃ β ∈ L₃, β ≠ g x ∧ E1 β := by
    intro L₃ hL₃
    let L' : V → Finset C := fun w => if w = y then L₃ else L w
    obtain ⟨f, hfx, hfa, hfL, hfp⟩ := T.thm1 H _ S₁ rfl x a (P₀' ++ [y]) h₁' L' g hok.1
      (by
        intro w hw
        by_cases hwy : w = y
        · simp only [L', hwy, if_true]; exact hL₃
        · simp only [L', hwy, if_false]
          have hwP : w ∈ P₀' := by simpa [hwy] using hw
          apply hh.three w (by simp [hwP])
          · intro e; subst e; exact haP₀' hwP
          · intro e; subst e; exact hcS₁ (T.subset h₁' w (by simp [hwP])))
      (by
        intro w hw hwc
        have hwy : w ≠ y := fun e => hwc (by simp [e])
        simp only [L', hwy, if_false]
        exact hh.five w (hS₁ hw) (hint₁ w hw hwc))
    have hfy : f y ∈ L₃ := by
      have := hfL y hyS₁ (Ne.symm hxy_ne) hya_ne
      simpa [L'] using this
    have hfyx : f y ≠ g x := by rw [← hfx]; exact (hfp x hxS₁ y hyS₁ hxy).symm
    refine ⟨f y, hfy, hfyx, f, ?_, ?_, hfp⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · simp
      · rw [Function.update_of_ne hxy_ne]; exact hfx
      · rw [Function.update_of_ne (Ne.symm hya_ne)]; exact hfa
    · intro w hw hwc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwc
      have := hfL w hw hwc.2.1 hwc.2.2
      simpa [L', hwc.1] using this
  have T2 : ∀ L₃ : Finset C, 3 ≤ L₃.card → ∃ β ∈ L₃, β ≠ g x ∧ E2 β := by
    intro L₃ hL₃
    let L' : V → Finset C := fun w => if w = y then L₃ else L w
    obtain ⟨f, hfc, hfx, hfL, hfp⟩ := T.thm1 H _ S₂ rfl c x (y :: P₁') h₂'' L' g
      (fun e => hok.2.1 e.symm)
      (by
        intro w hw
        by_cases hwy : w = y
        · simp only [L', hwy, if_true]; exact hL₃
        · simp only [L', hwy, if_false]
          have hwP : w ∈ P₁' := by simpa [hwy] using hw
          apply hh.three w (by simp [hwP])
          · intro e; subst e; exact haS₂ (T.subset h₂' w (by simp [hwP]))
          · intro e; subst e; exact hcP₁' hwP)
      (by
        intro w hw hwc
        have hwy : w ≠ y := fun e => hwc (by simp [e])
        simp only [L', hwy, if_false]
        exact hh.five w (hS₂ hw) (hint₂ w hw hwc))
    have hfy : f y ∈ L₃ := by
      have := hfL y hyS₂ hyc_ne (Ne.symm hxy_ne)
      simpa [L'] using this
    have hfyx : f y ≠ g x := by rw [← hfx]; exact (hfp x hxS₂ y hyS₂ hxy).symm
    refine ⟨f y, hfy, hfyx, f, ?_, ?_, hfp⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · rw [Function.update_of_ne (Ne.symm hyc_ne)]; exact hfc
      · rw [Function.update_of_ne hxy_ne]; exact hfx
      · simp
    · intro w hw hwc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwc
      have := hfL w hw hwc.1 hwc.2.1
      simpa [L', hwc.2.2] using this
  have pair : ∀ (E : C → Prop), (∀ L₃ : Finset C, 3 ≤ L₃.card → ∃ β ∈ L₃, β ≠ g x ∧ E β) →
      ∀ p q : C, p ≠ g x → q ≠ g x → p ≠ q → E p ∨ E q := by
    intro E hT p q hp hq hpq
    have hc : ({g x, p, q} : Finset C).card = 3 :=
      Finset.card_eq_three.mpr ⟨g x, p, q, Ne.symm hp, Ne.symm hq, hpq, rfl⟩
    obtain ⟨β, hβ, hβx, hE⟩ := hT _ (le_of_eq hc.symm)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl
    · exact absurd rfl hβx
    · exact Or.inl hE
    · exact Or.inr hE
  have hcS : S₂.card < S.card :=
    Finset.card_lt_card ⟨hS₂, fun h => haS₂ (h (hS₁ haS₁))⟩
  have hcS' : S₁.card < S.card :=
    Finset.card_lt_card ⟨hS₁, fun h => hcS₁ (h (hS₂ hcS₂))⟩
  have hout₁ : ∀ u ∈ S₁, u ∉ x :: (a :: P₀' ++ [y]) →
      u ∉ x :: (a :: P₀' ++ y :: (P₁' ++ [c])) := by
    intro u hu hun h
    apply hun
    by_cases huP : u ∈ P₁' ++ [c]
    · exact absurd hu (hP₁side u huP).2
    · simp only [List.cons_append, List.mem_cons, List.mem_append] at h huP ⊢; tauto
  have hout₂ : ∀ u ∈ S₂, u ∉ x :: y :: (P₁' ++ [c]) →
      u ∉ x :: (a :: P₀' ++ y :: (P₁' ++ [c])) := by
    intro u hu hun h
    apply hun
    by_cases huP : u ∈ a :: P₀'
    · exact absurd hu (hP₀side u huP).2
    · simp only [List.cons_append, List.mem_cons, List.mem_append] at h huP ⊢; tauto
  by_cases hbig : 3 ≤ ((L y).erase (g x)).card
  · left
    have h2lt : 2 < ((L y).erase (g x)).card := by omega
    obtain ⟨α₁, h1, α₂, h2, α₃, h3, h12, h13, h23⟩ := Finset.two_lt_card.mp h2lt
    have hx1 := Finset.ne_of_mem_erase h1
    have hx2 := Finset.ne_of_mem_erase h2
    have hx3 := Finset.ne_of_mem_erase h3
    have a12 := pair E1 T1 α₁ α₂ hx1 hx2 h12
    have a13 := pair E1 T1 α₁ α₃ hx1 hx3 h13
    have a23 := pair E1 T1 α₂ α₃ hx2 hx3 h23
    have b12 := pair E2 T2 α₁ α₂ hx1 hx2 h12
    have b13 := pair E2 T2 α₁ α₃ hx1 hx3 h13
    have b23 := pair E2 T2 α₂ α₃ hx2 hx3 h23
    have hcom : (E1 α₁ ∧ E2 α₁) ∨ (E1 α₂ ∧ E2 α₂) ∨ (E1 α₃ ∧ E2 α₃) := by tauto
    rcases hcom with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact glueE α₁ (Finset.mem_of_mem_erase h1) e1 e2
    · exact glueE α₂ (Finset.mem_of_mem_erase h2) e1 e2
    · exact glueE α₃ (Finset.mem_of_mem_erase h3) e1 e2
  · have hpred := Finset.pred_card_le_card_erase (s := L y) (a := g x)
    have hgxL : g x ∈ L y := by
      by_contra h
      rw [Finset.erase_eq_of_notMem h] at hbig; omega
    have hLy3 : (L y).card = 3 := by
      have := Finset.card_erase_of_mem hgxL; omega
    by_cases hcom : ∃ β ∈ L y, E1 β ∧ E2 β
    · obtain ⟨β, hβ, e1, e2⟩ := hcom
      exact Or.inl (glueE β hβ e1 e2)
    right
    push_neg at hcom
    have hxa' : H.Adj x a := T.adj_cons h₁'
    have hrc : T.NT H S₂ (y :: (P₁' ++ [c]) ++ [x]) := by simpa using T.rotate h₂'
    have X2 : Exc3 H S₂ x (y :: (P₁' ++ [c])) y c L := by
      rcases hyc with hP | hnyc
      · have hP' : P₁' = [] := by simpa using hP
        subst hP'
        have hyc' : H.Adj y c := T.adj_cons (by simpa using hrc)
        have hcx : H.Adj c x := T.adj_cons (by simpa using T.rotate hrc)
        exact ⟨[y, c], ∅, GW.one (Block.tri hxy hcx.symm hyc'), by simp [hyc_ne], rfl, rfl,
          fun w hw => hw,
          by simp, by intro w hw hwy hwc; simp at hw; tauto⟩
      · obtain ⟨β₁, hβ₁, hβ₁x, hE1⟩ := T1 (L y) h3y
        have hnE2 := hcom β₁ hβ₁ hE1
        have hh₂ : Thm3Hyp H S₂ x (y :: (P₁' ++ [c])) y c L (Function.update g y β₁) := by
          refine ⟨rfl, ?_, by simp, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
          · rw [List.getLast?_cons, List.getLast?_append_of_ne_nil _ (by simp)]; simp
          · rw [Function.update_of_ne hxy_ne, Function.update_self]; exact hβ₁x.symm
          · rw [Function.update_of_ne hxy_ne, Function.update_of_ne (Ne.symm hyc_ne)]
            exact hok.2.1
          · intro h; exact absurd h hnyc
          · intro w hw hwy hwc
            have hwP : w ∈ P₁' := by
              simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hw; tauto
            apply hh.three w (by simp [hwP])
            · intro e; subst e; exact haS₂ (T.subset h₂' w (by simp [hwP]))
            · exact hwc
          · intro w hw hwc
            exact hh.five w (hS₂ hw) (hout₂ w hw hwc)
        rcases ih H S₂ hcS x _ y c L _ h₂' hh₂ with h | h
        · exact absurd h hnE2
        · exact h
    have X1 : Exc3 H S₁ x (a :: P₀' ++ [y]) a y L := by
      rcases hya with hP | hnya
      · have hP' : P₀' = [] := by simpa using hP
        subst hP'
        have hay : H.Adj a y := T.adj_cons (by simpa using T.rotate h₁')
        exact ⟨[a, y], ∅, GW.one (Block.tri hxa' hxy hay), by simp [Ne.symm hya_ne], rfl, rfl,
          fun w hw => by simpa using hw,
          by simp, by intro w hw hwa hwy; simp at hw; tauto⟩
      · obtain ⟨β₂, hβ₂, hβ₂x, hE2⟩ := T2 (L y) h3y
        have hnE1 : ¬ E1 β₂ := fun h => hcom β₂ hβ₂ h hE2
        have hh₁ : Thm3Hyp H S₁ x (a :: P₀' ++ [y]) a y L (Function.update g y β₂) := by
          refine ⟨by simp, ?_, by simp, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
          · rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp
          · rw [Function.update_of_ne hxy_ne, Function.update_of_ne (Ne.symm hya_ne)]
            exact hok.1
          · rw [Function.update_of_ne hxy_ne, Function.update_self]; exact hβ₂x.symm
          · intro h; exact absurd h hnya
          · intro w hw hwa hwy
            have hwP : w ∈ P₀' := by
              simp only [List.cons_append, List.mem_cons, List.mem_append,
                List.mem_singleton] at hw; tauto
            apply hh.three w (by simp [hwP]) hwa
            intro e; subst e; exact hcS₁ (T.subset h₁' w (by simp [hwP]))
          · intro w hw hwc
            exact hh.five w (hS₁ hw) (hout₁ w hw hwc)
        rcases ih H S₁ hcS' x _ a y L _ (by simpa using h₁') hh₁ with h | h
        · exact absurd h hnE1
        · exact h
    exact exc3_glue (P₀ := a :: P₀') (P₁ := P₁' ++ [c]) X1 X2 hS₁ hS₂ hLy3
      (List.nodup_cons.mp (T.nodup hNT)).2 hout₁ hout₂

/-- **Claim 2, separating triangles.** If the inside of a triangle `p q r` has a vertex, the
conclusion of Theorem 3 follows from the induction hypothesis on the outside. -/
theorem claim2_tri (H : SimpleGraph V) {S Sin Sout : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} {p q r : V}
    (hh : Thm3Hyp H S x P a c L g) (hin : T.NT H Sin [p, q, r]) (hout : T.NT H Sout (x :: P))
    (hU : Sin ∪ Sout = S) (hI : Sin ∩ Sout = {p, q, r})
    (hX : ∀ u ∈ Sin, ∀ w ∈ Sout, H.Adj u w → u ∈ Sout ∨ w ∈ Sin)
    (hsep : ∃ z ∈ Sin, z ∉ ({p, q, r} : Finset V)) (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x P a c L := by
  classical
  obtain ⟨z, hzin, hzn⟩ := hsep
  have hSin : Sin ⊆ S := hU ▸ Finset.subset_union_left
  have hSout : Sout ⊆ S := hU ▸ Finset.subset_union_right
  have hmem : ∀ w, w ∈ Sin → w ∈ Sout → w = p ∨ w = q ∨ w = r := by
    intro w h1 h2
    have : w ∈ Sin ∩ Sout := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hzout : z ∉ Sout := fun h => hzn (by rcases hmem z hzin h with rfl | rfl | rfl <;> simp)
  have hcard : Sout.card < S.card := Finset.card_lt_card ⟨hSout, fun h => hzout (h (hSin hzin))⟩
  have hh' : Thm3Hyp H Sout x P a c L g :=
    ⟨hh.head, hh.last, hh.two_le, hh.ok, hh.three, fun w hw hwc => hh.five w (hSout hw) hwc⟩
  rcases ih H Sout hcard x P a c L g hout hh' with hE | hX3
  · left
    obtain ⟨f, hfc, hfL, hfp⟩ := hE
    have hpS : p ∈ Sout := (Finset.mem_inter.mp (hI ▸ (by simp : p ∈ ({p, q, r} : Finset V)))).2
    have hqS : q ∈ Sout := (Finset.mem_inter.mp (hI ▸ (by simp : q ∈ ({p, q, r} : Finset V)))).2
    have hrS : r ∈ Sout := (Finset.mem_inter.mp (hI ▸ (by simp : r ∈ ({p, q, r} : Finset V)))).2
    -- the outer cycle avoids the inside
    have hcyc : ∀ w ∈ x :: P, w ∈ Sout := fun w hw => T.subset hout w hw
    obtain ⟨f', hf'c, hf'L, hf'p⟩ := T.thm2_three H hin L f
      (fun u hu w hw huw => hfp u (by simp at hu; rcases hu with rfl | rfl | rfl <;> assumption)
        w (by simp at hw; rcases hw with rfl | rfl | rfl <;> assumption) huw)
      (by
        intro w hw hwc
        apply hh.five w (hSin hw)
        intro h
        have hw2 := hcyc w h
        rcases hmem w hw hw2 with rfl | rfl | rfl <;> simp at hwc)
    refine ⟨fun w => if w ∈ Sout then f w else f' w, ?_, ?_, ?_⟩
    · intro w hw
      have hw' : w ∈ x :: P := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hh.last)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_of_mem_head? hh.head)
      simp only [hcyc w hw', if_true]; exact hfc w hw
    · intro w hw hwc
      by_cases h2 : w ∈ Sout
      · simp only [h2, if_true]; exact hfL w h2 hwc
      · simp only [h2, if_false]
        have h1 : w ∈ Sin := (Finset.mem_union.mp (hU ▸ hw)).resolve_right h2
        exact hf'L w h1 (by
          intro h; simp at h
          rcases h with rfl | rfl | rfl
          · exact h2 hpS
          · exact h2 hqS
          · exact h2 hrS)
    · refine isProperOn_glue (S₁ := Sout) (S₂ := Sin) (by rw [Finset.union_comm]; exact hU)
        (fun u hu w hw huw => (hX w hw u hu huw.symm).symm) hfp hf'p ?_
      intro w h2 h1
      rcases hmem w h1 h2 with rfl | rfl | rfl <;> exact hf'c w (by simp)
  · exact Or.inr (exc3_mono hX3 hSout (fun w hw => hw) (fun u _ h => h))

/-- **Claim 2, separating triangles**, in excision form: a triangle piece `S₁` with a vertex
strictly inside yields the conclusion of Theorem 3. -/
theorem claim2_ex (H : SimpleGraph V) {S S₁ : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} {p q r : V}
    (hNT : T.NT H S (x :: P)) (hh : Thm3Hyp H S x P a c L g) (h₁ : T.NT H S₁ [p, q, r])
    (hsub : S₁ ⊆ S)
    (hstrict : ∀ u ∈ S₁, u ∉ [p, q, r] → u ∉ x :: P ∧ ∀ w ∈ S, H.Adj u w → w ∈ S₁)
    (hsep : ∃ z ∈ S₁, z ∉ ({p, q, r} : Finset V)) (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x P a c L := by
  classical
  have hout := T.excise3 hNT h₁ hsub hstrict
  have hp : p ∈ S₁ := T.subset h₁ p (by simp)
  have hq : q ∈ S₁ := T.subset h₁ q (by simp)
  have hr : r ∈ S₁ := T.subset h₁ r (by simp)
  refine T.claim2_tri H hh h₁ hout ?_ ?_ ?_ hsep ih
  · ext w
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | ⟨h, -⟩ | rfl | rfl | rfl)
      · exact hsub h
      · exact h
      · exact hsub hp
      · exact hsub hq
      · exact hsub hr
    · intro hw
      by_cases h : w ∈ S₁
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hw, h⟩)
  · ext w
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, ⟨-, h⟩ | h⟩
      · exact absurd h1 h
      · exact h
    · rintro (rfl | rfl | rfl)
      · exact ⟨hp, Or.inr (Or.inl rfl)⟩
      · exact ⟨hq, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨hr, Or.inr (Or.inr (Or.inr rfl))⟩
  · intro u hu w hw huw
    by_cases hut : u ∈ [p, q, r]
    · left
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hut
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · right
      have hwS : w ∈ S := by
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨h, -⟩ | rfl | rfl | rfl
        · exact h
        · exact hsub hp
        · exact hsub hq
        · exact hsub hr
      exact (hstrict u hu hut).2 w hwS huw

end NTCalc

end ThomassenManyColourings
