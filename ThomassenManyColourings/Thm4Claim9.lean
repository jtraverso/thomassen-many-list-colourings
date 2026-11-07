/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Glue

/-!
# Theorem 4, Claim 9: chords

A chord avoiding `v₁` (or a chord at `v₁` when only `v₁, v₂` are precoloured) has a side with no
precoloured vertex besides its ends: glue (`thm4_glue_free`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
theorem pcList_sub {t3 : Bool} {x a c : V} {z : V} (hz : z ∈ pcList t3 x a c) :
    z = x ∨ z = a ∨ z = c := by
  cases t3 <;> simp [pcList] at hz <;> tauto

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Claim 9, chords avoiding `v₁`.** -/
theorem thm4_claim9_path (H : SimpleGraph V) {S : Finset V} {x y z : V} {P₀ M P₁ : List V}
    {a c : V} {L : V → Finset C} {g : V → C} {t3 : Bool}
    (hNT : T.NT H S (x :: (P₀ ++ y :: M ++ z :: P₁)))
    (hh : Thm4Hyp H S x (P₀ ++ y :: M ++ z :: P₁) a c L g t3) (hM : M ≠ []) (hyz : H.Adj y z)
    (ih : T.Thm4Lt C (nCount S (pcList t3 x a c))
      (nCount S (pcList t3 x a c) - rCount S (pcList t3 x a c) L) t3) :
    Thm4Concl H S x a c L g t3 := by
  classical
  have hnd := T.nodup hNT
  have hrot : T.NT H S (y :: (M ++ z :: (P₁ ++ x :: P₀))) := by
    have := T.rotate_append (A := x :: P₀) (B := y :: M ++ z :: P₁) (by simpa using hNT)
    simpa using this
  obtain ⟨Sin, Sout, h₁, h₂, hU, hI, hX⟩ := T.chord hrot hM (by simp) hyz
  have hOut : T.NT H Sout (x :: (P₀ ++ y :: z :: P₁)) := by
    have := T.rotate_append (A := z :: P₁) (B := x :: (P₀ ++ [y])) (by simpa using h₂)
    simpa using this
  have hIn : T.NT H Sin (z :: (y :: M)) := T.rotate_back (by simpa using h₁)
  have hmem : ∀ v, v ∈ Sin → v ∈ Sout → v = y ∨ v = z := by
    intro v h1 h2
    have : v ∈ Sin ∩ Sout := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  -- positions on the outer cycle
  have hMside : ∀ m ∈ M, m ∉ Sout := by
    intro m hm h2
    have h1 : m ∈ Sin := T.subset h₁ m (by simp [hm])
    have hP := List.nodup_append.mp (List.nodup_cons.mp hnd).2
    have hyM := (List.nodup_cons.mp (List.nodup_append.mp hP.1).2.1).1
    rcases hmem m h1 h2 with rfl | rfl
    · exact hyM hm
    · exact hP.2.2 m (by simp [hm]) m List.mem_cons_self rfl
  have hcycP : ∀ v, v ∈ x :: (P₀ ++ y :: M ++ z :: P₁) → v ∉ M →
      v ∈ x :: (P₀ ++ y :: z :: P₁) := by
    intro v hv hvM
    simp only [List.mem_cons, List.mem_append] at hv hvM ⊢; tauto
  obtain ⟨m₀, hm₀⟩ := List.exists_mem_of_ne_nil M hM
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, (y :: M).getLast? = some c₂ :=
    ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
  have hhead : (P₀ ++ y :: z :: P₁).head? = some a := by
    have := hh.head
    rcases P₀ with _ | ⟨p, P₀'⟩ <;> simpa using this
  have hlast : (P₀ ++ y :: z :: P₁).getLast? = some c := by
    have := hh.last
    rw [show P₀ ++ y :: M ++ z :: P₁ = (P₀ ++ y :: M) ++ z :: P₁ by simp,
      List.getLast?_append_of_ne_nil _ (by simp)] at this
    rw [show P₀ ++ y :: z :: P₁ = (P₀ ++ [y]) ++ z :: P₁ by simp,
      List.getLast?_append_of_ne_nil _ (by simp)]
    exact this
  have hh₁ : Thm4Hyp H Sout x (P₀ ++ y :: z :: P₁) a c L g t3 := by
    refine ⟨hhead, hlast, by simp; omega, hh.xa, hh.xc, hh.ac, fun v hv hvn => hh.three v (by
      simp only [List.mem_append, List.mem_cons] at hv ⊢; tauto) hvn, fun v hv hvc => ?_⟩
    apply hh.five v (hU ▸ Finset.mem_union_right _ hv)
    intro h
    by_cases hvM : v ∈ M
    · exact hMside v hvM hv
    · exact hvc (hcycP v h hvM)
  have hpcP : ∀ v ∈ pcList t3 x a c, v ∈ x :: (P₀ ++ y :: z :: P₁) := by
    intro v hv
    rcases pcList_sub hv with rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_of_mem_head? hhead)
    · exact List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hlast)
  refine T.thm4_glue_free H (S₁ := Sout) (S₂ := Sin) (x₂ := z) (P₂ := y :: M) (a₂ := y)
    (c₂ := c₂) hOut hh₁ (fun _ => rfl) hIn rfl hc₂ (by
      obtain ⟨m, M', rfl⟩ := List.exists_cons_of_ne_nil hM; simp)
    (fun v hv hvy => ?_) (fun v hv hvc => ?_) (by rw [Finset.union_comm]; exact hU)
    (fun p hp q hq hpq => (hX q hq p hp hpq.symm).symm)
    (fun v h1 h2 => (hmem v h2 h1).symm) (T.subset hOut z (by simp))
    (T.subset hOut y (by simp)) hyz.symm
    (fun v hv h2 => (hmem v h2 (T.subset hOut v (hpcP v hv))).symm) ?_ ?_ ih
  · -- inner path vertices have three colours
    have hvM : v ∈ M := by simpa [hvy] using hv
    apply hh.three v (by simp [hvM])
    intro hpc
    have := T.subset hOut v (hpcP v hpc)
    exact hMside v hvM this
  · -- inner interior vertices have five colours
    apply hh.five v (hU ▸ Finset.mem_union_left _ hv)
    intro h
    by_cases hvM : v ∈ M
    · exact hvc (by simp [hvM])
    · have h2 := T.subset hOut v (hcycP v h hvM)
      rcases hmem v hv h2 with rfl | rfl
      · exact hvc (by simp)
      · exact hvc (by simp)
  · -- a vertex of `M` is free in the inner piece
    unfold nCount
    refine Finset.card_pos.mpr ⟨m₀, Finset.mem_filter.mpr ⟨T.subset h₁ m₀ (by simp [hm₀]), ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨fun e => hMside m₀ hm₀ (e ▸ T.subset hOut z (by simp)),
      fun e => hMside m₀ hm₀ (e ▸ T.subset hOut y (by simp))⟩
  · -- with two precoloured vertices, `v_k` is free in the outer piece
    cases t3 with
    | true => exact Or.inr rfl
    | false =>
      left
      unfold nCount
      refine Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨T.subset hOut c
        (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hlast)), ?_⟩⟩
      simp only [pcList, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      have hnd' := T.nodup hOut
      have hcP := List.mem_of_mem_getLast? hlast
      refine ⟨fun e => (List.nodup_cons.mp hnd').1 (e ▸ hcP), fun e => ?_⟩
      have h1 := eq_single_of_head_last (List.nodup_cons.mp hnd').2 hhead (e ▸ hlast)
      have := congrArg List.length h1
      simp at this; omega

set_option maxHeartbeats 8000000 in
/-- **Claim 9, chords at `v₁` with two precoloured vertices**: the side containing `v_k` is
free. -/
theorem thm4_claim9_x2 (H : SimpleGraph V) {S : Finset V} {x y : V} {P₀ P₁ : List V}
    {a c : V} {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (P₀ ++ y :: P₁))) (hh : Thm4Hyp H S x (P₀ ++ y :: P₁) a c L g false)
    (hP₀ : P₀ ≠ []) (hP₁ : P₁ ≠ []) (hxy : H.Adj x y)
    (ih : T.Thm4Lt C (nCount S (pcList false x a c))
      (nCount S (pcList false x a c) - rCount S (pcList false x a c) L) false) :
    Thm4Concl H S x a c L g false := by
  classical
  have hnd := T.nodup hNT
  have hxP := (List.nodup_cons.mp hnd).1
  have hP := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  have hyP₁ : y ∉ P₁ := (List.nodup_cons.mp hP.2.1).1
  have hyP₀ : y ∉ P₀ := fun h => hP.2.2 y h y List.mem_cons_self rfl
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hNT hP₀ hP₁ hxy
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
    have := hh.head; rwa [List.head?_append_of_ne_nil _ hP₀] at this
  have hlast : P₁.getLast? = some c := by
    have := hh.last
    rwa [show P₀ ++ y :: P₁ = (P₀ ++ [y]) ++ P₁ by simp,
      List.getLast?_append_of_ne_nil _ hP₁] at this
  have haP₀ : a ∈ P₀ := List.mem_of_mem_head? hhead
  have hcP₁ : c ∈ P₁ := List.mem_of_mem_getLast? hlast
  have hh₁ : Thm4Hyp H S₁ x (P₀ ++ [y]) a y L g false := by
    refine ⟨by rw [List.head?_append_of_ne_nil _ hP₀]; exact hhead, List.getLast?_concat ..,
      by have := List.length_pos_iff.mpr hP₀; simp; omega, hh.xa, by simp, by simp,
      fun v hv hvn => hh.three v (by simp only [List.mem_append, List.mem_cons] at hv ⊢; tauto)
        hvn, fun v hv hvc => hh.five v (hU ▸ Finset.mem_union_left _ hv) ?_⟩
    intro h; apply hvc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hv (hP₁side v h)
  refine T.thm4_glue_free H (S₁ := S₁) (S₂ := S₂) (x₂ := x) (P₂ := y :: P₁) (a₂ := y)
    (c₂ := c) h₁ hh₁ (by simp) h₂' rfl (by
      rw [List.getLast?_cons, hlast]; rfl)
    (by have := List.length_pos_iff.mpr hP₁; simp; omega)
    (fun v hv hvy => hh.three v (by simp at hv ⊢; tauto) (by
      have hvP₁ : v ∈ P₁ := by simpa [hvy] using hv
      simp only [pcList, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨fun e => hxP (by simp [← e, hvP₁]),
        fun e => hP₁side v hvP₁ (e ▸ T.subset h₁ a (by simp [haP₀]))⟩))
    (fun v hv hvc => hh.five v (hU ▸ Finset.mem_union_right _ hv) (by
      intro h; apply hvc
      simp only [List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact absurd hv (hP₀side v h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)))
    hU hX hmem (T.subset h₁ x (by simp)) (T.subset h₁ y (by simp)) hxy
    (fun v hv h2 => hmem v (by
      simp only [pcList, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl
      · exact T.subset h₁ _ (by simp)
      · exact T.subset h₁ _ (by simp [haP₀])) h2)
    ?_ (Or.inl ?_) ih
  · unfold nCount
    refine Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨T.subset h₂' c (by simp [hcP₁]), ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hxP (by simp [← e, hcP₁]), fun e => hyP₁ (e ▸ hcP₁)⟩
  · unfold nCount
    refine Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨T.subset h₁ y (by simp), ?_⟩⟩
    simp only [pcList, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    exact ⟨fun e => hxP (by simp [← e]), fun e => hyP₀ (e ▸ haP₀)⟩

end NTCalc

end ThomassenManyColourings
