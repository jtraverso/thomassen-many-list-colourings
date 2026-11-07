/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm2

/-!
# Generalized wheels

A generalized wheel with major vertex `x` is described by its outer path `P` (from one principal
neighbour of `x` to the other) and its set `U` of wheel centres. It is a sequence of blocks, each a
triangle `x a b` or a wheel (a centre joined to `x` and to every vertex of its path), consecutive
blocks sharing a principal edge `x b`; this is Thomassen's recursive gluing, read from one end.
Broken wheels are those with `U = ∅`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- Consecutive vertices of the list are adjacent. -/
def IsPathL (H : SimpleGraph V) (P : List V) : Prop := P.IsChain H.Adj

/-- The blocks of a generalized wheel with major vertex `x`: a triangle `x a b`, or a wheel whose
centre is joined to `x` and to every vertex of the outer path `P` (at least `m` vertices; `m = 3`
excludes wheels on a triangle). -/
inductive Block (H : SimpleGraph V) (m : ℕ) (x : V) : List V → Finset V → Prop
  | tri {a b : V} : H.Adj x a → H.Adj x b → H.Adj a b → Block H m x [a, b] ∅
  | wheel {P : List V} {u : V} : 2 ≤ P.length → m ≤ P.length → IsPathL H P →
      (∀ y ∈ P, H.Adj u y) →
      H.Adj u x → (∀ y ∈ P.head?, H.Adj x y) → (∀ y ∈ P.getLast?, H.Adj x y) → Block H m x P {u}

/-- Generalized wheels with major vertex `x`, outer path `P` (between the principal neighbours) and
wheel centres `U`: a sequence of blocks, consecutive ones sharing a principal edge `x b`. -/
inductive GW (H : SimpleGraph V) (m : ℕ) (x : V) : List V → Finset V → Prop
  | one {P : List V} {U : Finset V} : Block H m x P U → GW H m x P U
  | cons {P Q : List V} {b : V} {U U' : Finset V} : Block H m x (P ++ [b]) U → GW H m x (b :: Q) U' →
      GW H m x (P ++ b :: Q) (U ∪ U')

/-- Updating a proper colouring at `v` with a colour avoided by the neighbours of `v`. -/
theorem isProperOn_update {H : SimpleGraph V} {S : Finset V} {v : V} {f : V → C} {col : C}
    (hf : IsProperOn H (S.erase v) f) (hv : ∀ w ∈ S, H.Adj v w → f w ≠ col) :
    IsProperOn H S (Function.update f v col) := by
  intro a ha b hb hab
  by_cases hav : a = v
  · subst hav
    have hba : b ≠ a := fun e => H.loopless.irrefl _ (e ▸ hab)
    rw [Function.update_self, Function.update_of_ne hba]
    exact (hv b hb hab).symm
  · by_cases hbv : b = v
    · subst hbv
      rw [Function.update_self, Function.update_of_ne hav]
      exact hv a ha hab.symm
    · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
      exact hf a (Finset.mem_erase.mpr ⟨hav, ha⟩) b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab

namespace NTCalc

variable (T : NTCalc V)

/-- An interior vertex joined to every outer vertex forbids chords. -/
theorem no_chord_of_hub {H : SimpleGraph V} {S : Finset V} {x y : V} {l₁ l₂ : List V}
    (hNT : T.NT H S (x :: (l₁ ++ y :: l₂))) (hl₁ : l₁ ≠ []) (hl₂ : l₂ ≠ [])
    {u : V} (huS : u ∈ S) (hu : u ∉ x :: (l₁ ++ y :: l₂))
    (hhub : ∀ z ∈ x :: (l₁ ++ y :: l₂), H.Adj u z) : ¬ H.Adj x y := by
  intro hxy
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hNT hl₁ hl₂ hxy
  have hmem : ∀ z, z ∈ S₁ → z ∈ S₂ → z = x ∨ z = y := by
    intro z h1 h2
    have : z ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hnd := T.nodup hNT
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l₁ hl₁
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil l₂ hl₂
  have haS₁ : a ∈ S₁ := T.subset h₁ a (by simp [ha])
  have hbS₂ : b ∈ S₂ := T.subset h₂ b (by simp [hb])
  simp only [List.nodup_cons, List.mem_append, List.mem_cons, not_or, List.nodup_append]
    at hnd
  have hax : a ≠ x := fun e => hnd.1.1 (e ▸ ha)
  have hbx : b ≠ x := fun e => hnd.1.2.2 (e ▸ hb)
  have hay : a ≠ y := fun e => hnd.2.2.2 a ha y (by simp) e
  have hby : b ≠ y := fun e => hnd.2.2.1.1 (e ▸ hb)
  have haS₂ : a ∉ S₂ := fun h => (hmem a haS₁ h).elim hax hay
  have hbS₁ : b ∉ S₁ := fun h => (hmem b h hbS₂).elim hbx hby
  have huxy : u ≠ x ∧ u ≠ y := ⟨fun e => hu (by simp [e]), fun e => hu (by simp [e])⟩
  have huS' : u ∈ S₁ ∪ S₂ := hU ▸ huS
  rcases Finset.mem_union.mp huS' with h1 | h2
  · have hu2 : u ∉ S₂ := fun h => (hmem u h1 h).elim huxy.1 huxy.2
    rcases hX u h1 b hbS₂ (hhub b (by simp [hb])) with h | h
    · exact hu2 h
    · exact hbS₁ h
  · have hu1 : u ∉ S₁ := fun h => (hmem u h h2).elim huxy.1 huxy.2
    rcases hX a haS₁ u h2 (hhub a (by simp [ha])).symm with h | h
    · exact haS₂ h
    · exact hu1 h

end NTCalc

end ThomassenManyColourings
