/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.GW

/-!
# Algebra of generalized wheels

Length, adjacency of the major vertex to the principal neighbours, gluing two generalized wheels
along a principal edge, reversal, and the front triangle of a generalized wheel.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V]

section

variable {H : SimpleGraph V} {m : ℕ} {x : V}

theorem IsPathL.reverse {P : List V} (h : IsPathL H P) : IsPathL H P.reverse := by
  unfold IsPathL at h ⊢
  rw [List.isChain_reverse]
  exact h.imp (fun _ _ hab => hab.symm)

theorem Block.two_le {P : List V} {U : Finset V} (h : Block H m x P U) : 2 ≤ P.length := by
  cases h with
  | tri => simp
  | wheel hP => exact hP

theorem GW.two_le {P : List V} {U : Finset V} (h : GW H m x P U) : 2 ≤ P.length := by
  induction h with
  | one hB => exact hB.two_le
  | cons hB _ ih =>
    have := hB.two_le
    simp only [List.length_append, List.length_cons, List.length_nil] at this ih ⊢
    omega

theorem Block.adj_head {P : List V} {U : Finset V} (h : Block H m x P U) :
    ∀ y ∈ P.head?, H.Adj x y := by
  cases h with
  | tri hxa _ _ => intro y hy; simp at hy; exact hy ▸ hxa
  | wheel _ _ _ _ _ hh _ => exact hh

theorem Block.adj_last {P : List V} {U : Finset V} (h : Block H m x P U) :
    ∀ y ∈ P.getLast?, H.Adj x y := by
  cases h with
  | tri _ hxb _ => intro y hy; simp at hy; exact hy ▸ hxb
  | wheel _ _ _ _ _ _ hl => exact hl

theorem Block.reverse {P : List V} {U : Finset V} (h : Block H m x P U) :
    Block H m x P.reverse U := by
  cases h with
  | tri hxa hxb hab => exact Block.tri hxb hxa hab.symm
  | wheel hP hm hpath hu hux hh hl =>
    refine Block.wheel (by simpa using hP) (by simpa using hm) hpath.reverse (fun y hy => hu y (by simpa using hy))
      hux ?_ ?_
    · intro y hy; rw [List.head?_reverse] at hy; exact hl y hy
    · intro y hy; rw [List.getLast?_reverse] at hy; exact hh y hy

theorem GW.adj_head {P : List V} {U : Finset V} (h : GW H m x P U) :
    ∀ y ∈ P.head?, H.Adj x y := by
  induction h with
  | one hB => exact hB.adj_head
  | @cons P Q b U U' hB _ _ =>
    intro y hy
    apply hB.adj_head y
    rcases P with _ | ⟨p, P⟩
    · simpa using hy
    · simpa using hy

theorem GW.adj_last {P : List V} {U : Finset V} (h : GW H m x P U) :
    ∀ y ∈ P.getLast?, H.Adj x y := by
  induction h with
  | one hB => exact hB.adj_last
  | @cons P Q b U U' _ _ ih =>
    intro y hy
    apply ih y
    rw [List.getLast?_append] at hy
    simpa [List.getLast?_cons] using hy

/-- Gluing two generalized wheels along the principal edge `x b`. -/
theorem GW.append {P Q : List V} {b : V} {U U' : Finset V} (h₁ : GW H m x (P ++ [b]) U)
    (h₂ : GW H m x (b :: Q) U') : GW H m x (P ++ b :: Q) (U ∪ U') := by
  generalize hPb : P ++ [b] = PB at h₁
  induction h₁ generalizing P with
  | one hB => subst hPb; exact GW.cons hB h₂
  | @cons P' Q' b' U₁ U₂ hB hrest ih =>
    have hQ' : Q' ≠ [] := by
      have := hrest.two_le; intro h; subst h; simp at this
    obtain ⟨Q'', c, hQc⟩ : ∃ Q'' c, Q' = Q'' ++ [c] := by
      rcases Q'.eq_nil_or_concat with h | ⟨Q'', c, h⟩
      · exact absurd h hQ'
      · exact ⟨Q'', c, by simpa using h⟩
    subst hQc
    have hcb : c = b ∧ P = P' ++ b' :: Q'' := by
      have h1 : P' ++ b' :: (Q'' ++ [c]) = (P' ++ b' :: Q'') ++ [c] := by simp
      rw [h1] at hPb
      have := List.append_inj' hPb rfl
      simp only [List.cons.injEq, and_true] at this
      exact ⟨this.2.symm, this.1⟩
    obtain ⟨rfl, rfl⟩ := hcb
    have h3 := ih (P := b' :: Q'') (by simp)
    have h4 := GW.cons hB h3
    simpa [Finset.union_assoc] using h4

/-- Reversal of a generalized wheel. -/
theorem GW.reverse {P : List V} {U : Finset V} (h : GW H m x P U) : GW H m x P.reverse U := by
  induction h with
  | one hB => exact GW.one hB.reverse
  | @cons P Q b U U' hB _ ih =>
    have h1 : GW H m x (Q.reverse ++ [b]) U' := by simpa using ih
    have h2 : GW H m x (b :: P.reverse) U := GW.one (by simpa using hB.reverse)
    have h3 := GW.append h1 h2
    simpa [Finset.union_comm] using h3

/-- Centres of a generalized wheel on the path `b :: Q` are joined to a vertex of `Q`. -/
theorem GW.centre_adj_tail {b : V} {Q : List V} {U : Finset V} (h : GW H m x (b :: Q) U) :
    ∀ u ∈ U, ∃ q ∈ Q, H.Adj u q := by
  generalize hbQ : b :: Q = BQ at h
  induction h generalizing b Q with
  | one hB =>
    cases hB with
    | tri => simp
    | wheel hP _ _ hu =>
      intro u hu'
      simp only [Finset.mem_singleton] at hu'
      subst hu'; subst hbQ
      have : Q ≠ [] := by intro e; subst e; simp at hP
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil Q this
      exact ⟨q, hq, hu q (by simp [hq])⟩
  | @cons P' Q' b' U₁ U₂ hB hrest ih =>
    have hP' : P' ≠ [] := by
      have := hB.two_le; intro e; subst e; simp at this
    generalize hPB : P' ++ [b'] = PB at hB
    obtain ⟨p, P'', rfl⟩ := List.exists_cons_of_ne_nil hP'
    simp only [List.cons_append, List.cons.injEq] at hbQ
    obtain ⟨rfl, rfl⟩ := hbQ
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · cases hB with
      | tri => simp at hu
      | wheel _ _ _ hadj =>
        simp only [Finset.mem_singleton] at hu
        subst hu
        exact ⟨b', by simp, hadj b' (by rw [← hPB]; simp)⟩
    · obtain ⟨q, hq, hq'⟩ := ih (b := b') (Q := Q') rfl u hu
      exact ⟨q, by simp [hq], hq'⟩

/-- The front block of a generalized wheel is a triangle or contains a centre. -/
theorem GW.front_tri {a v : V} {R : List V} {U : Finset V}
    (h : GW H m x (a :: v :: R) U) :
    (H.Adj x a ∧ H.Adj x v ∧ H.Adj a v ∧ (R = [] ∧ U = ∅ ∨ GW H m x (v :: R) U)) ∨
      ∃ u, u ∈ U := by
  generalize hP : a :: v :: R = P at h
  cases h with
  | one hB =>
    cases hB with
    | tri hxa hxb hab =>
      simp only [List.cons.injEq] at hP
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact Or.inl ⟨hxa, hxb, hab, Or.inl ⟨rfl, rfl⟩⟩
    | wheel => exact Or.inr ⟨_, Finset.mem_singleton_self _⟩
  | @cons P' Q b U₁ U₂ hB hrest =>
    generalize hPb : P' ++ [b] = PB at hB
    cases hB with
    | @tri a' b' hxa hxb hab =>
      have h1 : P' ++ [b] = [a'] ++ [b'] := hPb
      obtain ⟨rfl, hb⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, and_true] at hb
      subst hb
      simp only [List.singleton_append, List.cons.injEq] at hP
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact Or.inl ⟨hxa, hxb, hab, Or.inr (by simpa using hrest)⟩
    | wheel => exact Or.inr ⟨_, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩

end

end ThomassenManyColourings
