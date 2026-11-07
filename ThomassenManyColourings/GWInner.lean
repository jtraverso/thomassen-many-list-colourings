/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.ListFacts

/-!
# Inner path vertices of generalized wheels

A vertex of the outer path of a generalized wheel which is not joined to the major vertex lies
inside a wheel block: the centre of that block is joined to it and to its two path neighbours.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*}

/-- `p, y, n` are three consecutive entries of the list. -/
def Consec3 : List V → V → V → V → Prop
  | a :: b :: c :: l, p, y, n => (p = a ∧ y = b ∧ n = c) ∨ Consec3 (b :: c :: l) p y n
  | _, _, _, _ => False

theorem Consec3.mem : ∀ {l : List V} {p y n : V}, Consec3 l p y n → p ∈ l ∧ y ∈ l ∧ n ∈ l
  | [], _, _, _, h => by simp [Consec3] at h
  | [_], _, _, _, h => by simp [Consec3] at h
  | [_, _], _, _, _, h => by simp [Consec3] at h
  | a :: b :: c :: l, p, y, n, h => by
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · simp
    · have := Consec3.mem h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2.1,
        List.mem_cons_of_mem _ this.2.2⟩

theorem Consec3.of_append : ∀ (R : List V) (p y n : V), Consec3 (R ++ [p, y, n]) p y n
  | [], p, y, n => Or.inl ⟨rfl, rfl, rfl⟩
  | r :: R, p, y, n => by
    have ih := Consec3.of_append R p y n
    rcases hR : R ++ [p, y, n] with _ | ⟨s₁, _ | ⟨s₂, rest⟩⟩
    · simp at hR
    · have := congrArg List.length hR; simp at this
    · rw [hR] at ih
      show Consec3 (r :: (R ++ [p, y, n])) p y n
      rw [hR]
      exact Or.inr ih

/-- A consecutive triple of `A ++ b :: Q` whose middle entry is not `b` lies in `A ++ [b]` or in
`b :: Q`. -/
theorem Consec3.split : ∀ (A : List V) {b : V} {Q : List V} {p y n : V},
    Consec3 (A ++ b :: Q) p y n → y ≠ b → Consec3 (A ++ [b]) p y n ∨ Consec3 (b :: Q) p y n
  | [], _, _, _, _, _, h, _ => Or.inr h
  | [a₁], b, Q, p, y, n, h, hyb => by
    rcases Q with _ | ⟨q, Q'⟩
    · simp [Consec3] at h
    · rcases h with ⟨-, h, -⟩ | h
      · exact absurd h hyb
      · exact Or.inr h
  | a₁ :: a₂ :: A, b, Q, p, y, n, h, hyb => by
    rcases hA : A ++ b :: Q with _ | ⟨t, rest⟩
    · simp at hA
    · have h' : Consec3 (a₁ :: a₂ :: t :: rest) p y n := by
        have : Consec3 (a₁ :: a₂ :: (A ++ b :: Q)) p y n := h
        rwa [hA] at this
      rcases h' with ⟨e1, e2, e3⟩ | h''
      · left
        rcases hA' : A ++ [b] with _ | ⟨t', rest'⟩
        · simp at hA'
        · have htt : t' = t := by
            rcases A with _ | ⟨a₃, A'⟩
            · simp at hA hA'; rw [← hA.1, ← hA'.1]
            · simp at hA hA'; rw [← hA.1, ← hA'.1]
          show Consec3 (a₁ :: a₂ :: (A ++ [b])) p y n
          rw [hA']
          exact Or.inl ⟨e1, e2, htt ▸ e3⟩
      · have h3 : Consec3 ((a₂ :: A) ++ b :: Q) p y n := by
          show Consec3 (a₂ :: (A ++ b :: Q)) p y n
          rw [hA]; exact h''
        rcases Consec3.split (a₂ :: A) h3 hyb with h4 | h4
        · left
          show Consec3 (a₁ :: a₂ :: (A ++ [b])) p y n
          rcases hA' : A ++ [b] with _ | ⟨t', rest'⟩
          · simp at hA'
          · have h5 : Consec3 (a₂ :: t' :: rest') p y n := by
              have : Consec3 (a₂ :: (A ++ [b])) p y n := h4
              rwa [hA'] at this
            exact Or.inr h5
        · exact Or.inr h4

section

variable {H : SimpleGraph V} {m : ℕ} {x : V}

theorem Block.centre_of_inner [DecidableEq V] {P : List V} {U : Finset V}
    (hB : Block H m x P U) {p y n : V} (h : Consec3 P p y n) :
    ∃ z ∈ U, H.Adj z p ∧ H.Adj z y ∧ H.Adj z n ∧ H.Adj z x := by
  cases hB with
  | tri => simp [Consec3] at h
  | wheel _ _ _ hu hux =>
    have hm := h.mem
    exact ⟨_, Finset.mem_singleton_self _, hu p hm.1, hu y hm.2.1, hu n hm.2.2, hux⟩

/-- An inner vertex of the outer path not joined to the major vertex has a centre joined to it
and to its two path neighbours. -/
theorem GW.centre_of_inner [DecidableEq V] {P : List V} {U : Finset V} (hW : GW H m x P U) :
    ∀ {p y n : V}, Consec3 P p y n → ¬ H.Adj x y →
      ∃ z ∈ U, H.Adj z p ∧ H.Adj z y ∧ H.Adj z n ∧ H.Adj z x := by
  induction hW with
  | one hB => exact fun h _ => hB.centre_of_inner h
  | @cons P Q b U U' hB hrest ih =>
    intro p y n h hxy
    have hyb : y ≠ b := fun e => hxy (e ▸ hB.adj_last b (by simp))
    rcases Consec3.split P h hyb with h1 | h1
    · obtain ⟨z, hz, h⟩ := hB.centre_of_inner h1
      exact ⟨z, Finset.mem_union_left _ hz, h⟩
    · obtain ⟨z, hz, h⟩ := ih h1 hxy
      exact ⟨z, Finset.mem_union_right _ hz, h⟩

end

end ThomassenManyColourings
