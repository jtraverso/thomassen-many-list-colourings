/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim11

/-!
# The exceptional configuration of Theorem 3 without chords is a wheel

If the outer path is chordless, `v₁` is joined only to `v₂, v_k` on it and there is no separating
triangle, a generalized wheel on the outer path is a single wheel filling `G`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

omit [DecidableEq C] in
theorem exc3_wheel (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} (hNT : T.NT H S (x :: P)) (hP3 : 3 ≤ P.length)
    (hhead : P.head? = some a) (hlast : P.getLast? = some c)
    (hPc : ∀ y z, y ∈ P → z ∈ P → H.Adj y z → ConsecIn P y z)
    (hxc : ∀ y ∈ P, H.Adj x y → y = a ∨ y = c) (hN : T.NoSepTri H S (x :: P))
    (hE : Exc3 H S x P a c L) :
    ∃ u, u ∈ S ∧ u ∉ x :: P ∧ (∀ y ∈ P, H.Adj u y) ∧ H.Adj u x ∧
      (∀ z ∈ S, z = x ∨ z ∈ P ∨ z = u) ∧ (∀ y ∈ P, y ≠ a → y ≠ c → (L y).card = 3) := by
  classical
  obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := hE
  have hPnd : P.Nodup := (List.nodup_cons.mp (T.nodup hNT)).2
  have hPW : PW = P := path_eq_of_chordless P PW hPnd hndW hsubW (hhW.trans hhead.symm)
    (hlW.trans hlast.symm) hGW.isPath hPc
  subst hPW
  obtain ⟨hfill, hGW3⟩ := gw_fill hN hGW hNT (Region.refl H S _) hUW
  cases hGW3 with
  | one hB =>
    cases hB with
    | tri => simp at hP3
    | wheel _ _ _ hu hux _ _ =>
      refine ⟨_, (hUW _ (Finset.mem_singleton_self _)).1,
        (hUW _ (Finset.mem_singleton_self _)).2, hu, hux, fun z hz => ?_, hLW⟩
      rcases hfill z hz with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Finset.mem_singleton.mp h))
  | @cons P₁ Q₂ b U₁ U₂ hB hrest =>
    exfalso
    have hP₁ : P₁ ≠ [] := fun h => by subst h; have := hB.two_le; simp at this
    have hQ₂ : Q₂ ≠ [] := fun h => by subst h; have := hrest.two_le; simp at this
    have hxb : H.Adj x b := hB.adj_last b (by simp)
    obtain ⟨hba, hbc⟩ := junction_inner hPnd hP₁ hQ₂ hhead hlast
    rcases hxc b (by simp) hxb with h | h
    · exact hba h
    · exact hbc h

end NTCalc

end ThomassenManyColourings
