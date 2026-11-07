/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Final

/-!
# Theorem 3

Let `G` be a near-triangulation with outer cycle `v₁ v₂ … v_k`, `v_k, v₁, v₂` precoloured, three
colours at the other outer vertices and five inside. Then `G` is coloured, unless it contains a
generalized wheel with principal path `v_k v₁ v₂` whose outer vertices are on `C` and have exactly
three colours (`Exc3`).

The proof is by strong induction on the number of vertices: `k ≤ 5` is Theorem 2; for `k ≥ 6`,
a separating triangle is Claim 2, a chord is Claim 1, and otherwise `thm3_final` applies.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
theorem exists_append_three : ∀ (l : List V), 3 ≤ l.length → ∃ R p q r, l = R ++ [p, q, r] := by
  intro l hl
  rcases hrev : l.reverse with _ | ⟨r, _ | ⟨q, _ | ⟨p, R'⟩⟩⟩
  · have := congrArg List.length hrev
    simp only [List.length_reverse, List.length_nil] at this; omega
  · have := congrArg List.length hrev
    simp only [List.length_reverse, List.length_nil, List.length_cons] at this; omega
  · have := congrArg List.length hrev
    simp only [List.length_reverse, List.length_nil, List.length_cons] at this; omega
  · refine ⟨R'.reverse, p, q, r, ?_⟩
    rw [← List.reverse_reverse l, hrev]; simp

omit [DecidableEq V] in
theorem eq_single_of_head_last {l : List V} {a : V} (hnd : l.Nodup) (hh : l.head? = some a)
    (hl : l.getLast? = some a) : l = [a] := by
  rcases l with _ | ⟨b, l'⟩
  · simp at hh
  · simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rcases l' with _ | ⟨d, l''⟩
    · rfl
    · rw [List.getLast?_cons_cons] at hl
      exact absurd (List.mem_of_mem_getLast? hl) (List.nodup_cons.mp hnd).1

omit [DecidableEq V] in
/-- A non-consecutive pair of a repetition-free list splits it with a non-empty middle. -/
theorem chord_decomp {P : List V} {y z : V} (hnd : P.Nodup) (hy : y ∈ P) (hz : z ∈ P)
    (hyz : y ≠ z) (hc : ¬ ConsecIn P y z) :
    ∃ P₀ M P₁ y' z', P = P₀ ++ y' :: M ++ z' :: P₁ ∧ M ≠ [] ∧
      ((y' = y ∧ z' = z) ∨ (y' = z ∧ z' = y)) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
  rcases List.mem_append.mp hz with hzA | hzB
  · obtain ⟨P₀, M, rfl⟩ := List.append_of_mem hzA
    refine ⟨P₀, M, B, z, y, by simp, ?_, Or.inr ⟨rfl, rfl⟩⟩
    rintro rfl
    apply hc
    exact ConsecIn.symm (by
      rw [show P₀ ++ [z] ++ y :: B = P₀ ++ (z :: y :: B) by simp]
      exact ConsecIn.append_left (Or.inl ⟨rfl, rfl⟩))
  · rcases List.mem_cons.mp hzB with e | hzB
    · exact absurd e.symm hyz
    obtain ⟨M, P₁, rfl⟩ := List.append_of_mem hzB
    refine ⟨A, M, P₁, y, z, by simp, ?_, Or.inl ⟨rfl, rfl⟩⟩
    rintro rfl
    apply hc
    exact ConsecIn.append_left (Or.inl ⟨rfl, rfl⟩)

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Theorem 3, induction step.** -/
theorem thm3_step (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} (hNT : T.NT H S (x :: P)) (hh : Thm3Hyp H S x P a c L g)
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x P a c L := by
  classical
  have h2 := hh.two_le
  rcases P with _ | ⟨a', _ | ⟨q₁, _ | ⟨q₂, _ | ⟨q₃, _ | ⟨q₄, Q⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · -- `k = 3`
    have ha := hh.head; have hc := hh.last
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at ha hc
    subst ha; subst hc
    exact Or.inl (T.thm3_three H hNT L g hh)
  · -- `k = 4`
    have ha := hh.head; have hc := hh.last
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at ha hc
    subst ha; subst hc
    exact T.thm3_four H hNT L g hh
  · -- `k = 5`
    have ha := hh.head; have hc := hh.last
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at ha hc
    subst ha; subst hc
    exact T.thm3_five H hNT L g hh
  -- `k ≥ 6`: reshape the path as `a :: v₃ :: (R ++ [w₄, w₃, c])`
  obtain ⟨R, w₄, w₃, c', hR⟩ := exists_append_three (q₂ :: q₃ :: q₄ :: Q) (by simp)
  rw [hR] at hNT hh ⊢
  have ha := hh.head
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst ha
  have hc := hh.last
  rw [show a' :: q₁ :: (R ++ [w₄, w₃, c']) = (a' :: q₁ :: (R ++ [w₄, w₃])) ++ [c'] by simp,
    List.getLast?_concat] at hc
  simp only [Option.some.injEq] at hc
  subst hc
  have hPnd := (List.nodup_cons.mp (T.nodup hNT)).2
  -- Claim 2: separating triangles
  by_cases hN : T.NoSepTri H S (x :: a' :: q₁ :: (R ++ [w₄, w₃, c']))
  swap
  · unfold NoSepTri at hN
    push Not at hN
    obtain ⟨S₁, p, q, r, h₁, hR₁, u, hu, hun⟩ := hN
    exact T.claim2_ex H hNT hh h₁ hR₁.1 hR₁.2 ⟨u, hu, by simp; tauto⟩ ih
  -- Claim 1: chords avoiding `x`
  by_cases hPc : ∀ y z, y ∈ a' :: q₁ :: (R ++ [w₄, w₃, c']) →
      z ∈ a' :: q₁ :: (R ++ [w₄, w₃, c']) → H.Adj y z →
      ConsecIn (a' :: q₁ :: (R ++ [w₄, w₃, c'])) y z
  swap
  · push Not at hPc
    obtain ⟨y, z, hy, hz, hyz, hnc⟩ := hPc
    have hne : y ≠ z := fun e => H.loopless.irrefl _ (e ▸ hyz)
    obtain ⟨P₀, M, P₁, y', z', hPeq, hM, hyz'⟩ := chord_decomp hPnd hy hz hne hnc
    have hadj : H.Adj y' z' := by
      rcases hyz' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyz
      · exact hyz.symm
    rw [hPeq] at hNT hh ⊢
    exact T.claim1_nox H hNT hh hM hadj ih
  -- Claim 1: chords at `x`
  by_cases hxc : ∀ y ∈ a' :: q₁ :: (R ++ [w₄, w₃, c']), H.Adj x y → y = a' ∨ y = c'
  swap
  · push Not at hxc
    obtain ⟨y, hy, hxy, hya, hyc⟩ := hxc
    obtain ⟨P₀, P₁, hPeq⟩ := List.append_of_mem hy
    have hP₀ : P₀ ≠ [] := by
      rintro rfl
      have := hh.head; rw [hPeq] at this; simp at this; exact hya this
    have hP₁ : P₁ ≠ [] := by
      rintro rfl
      have := hh.last; rw [hPeq] at this; simp at this; exact hyc this
    have hnd' : (P₀ ++ y :: P₁).Nodup := hPeq ▸ hPnd
    have hhead : P₀.head? = some a' := by
      have := hh.head; rw [hPeq, List.head?_append_of_ne_nil _ hP₀] at this; exact this
    have hlast : P₁.getLast? = some c' := by
      have := hh.last
      rw [hPeq, show P₀ ++ y :: P₁ = (P₀ ++ [y]) ++ P₁ by simp,
        List.getLast?_append_of_ne_nil _ hP₁] at this
      exact this
    have hya' : P₀ = [a'] ∨ ¬ H.Adj a' y := by
      by_cases had : H.Adj a' y
      · left
        have hcons := hPc y a' hy (by simp) had.symm
        rw [hPeq] at hcons
        rcases ConsecIn.nbr hnd' hcons with h | h
        · exact eq_single_of_head_last (List.nodup_append.mp hnd').1 hhead h
        · exfalso
          exact (List.nodup_append.mp hnd').2.2 a' (List.mem_of_mem_head? hhead) a'
            (List.mem_cons_of_mem _ (List.mem_of_mem_head? h)) rfl
      · exact Or.inr had
    have hyc' : P₁ = [c'] ∨ ¬ H.Adj y c' := by
      by_cases hac : H.Adj y c'
      · left
        have hcons := hPc y c' hy (by simp) hac
        rw [hPeq] at hcons
        rcases ConsecIn.nbr hnd' hcons with h | h
        · exfalso
          exact (List.nodup_append.mp hnd').2.2 c' (List.mem_of_mem_getLast? h) c'
            (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hlast)) rfl
        · exact eq_single_of_head_last (List.nodup_cons.mp (List.nodup_append.mp hnd').2.1).2
            h hlast
      · exact Or.inr hac
    rw [hPeq] at hNT hh ⊢
    exact T.claim1_x H hNT hh hP₀ hP₁ hxy hya' hyc' ih
  exact T.thm3_final H hNT hh hPc hxc hN ih

/-- **Theorem 3** for all vertex sets of size less than `n`. -/
theorem thm3_below (n : ℕ) : T.Thm3Below n C := by
  induction n with
  | zero => intro H S hS; simp at hS
  | succ n ih =>
    intro H S hS x P a c L g hNT hh
    exact T.thm3_step H hNT hh (fun H' S' hS' => ih H' S' (by omega))

/-- **Theorem 3** (Thomassen 2007). -/
theorem thm3 (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} (hNT : T.NT H S (x :: P)) (hh : Thm3Hyp H S x P a c L g) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x P a c L :=
  T.thm3_below (S.card + 1) H S (by omega) x P a c L g hNT hh

end NTCalc

end ThomassenManyColourings
