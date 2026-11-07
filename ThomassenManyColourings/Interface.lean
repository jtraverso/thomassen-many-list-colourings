/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# An abstract calculus of near-triangulations

`NT H S c` stands for "the graph `H` restricted to the vertex set `S` is a plane near-triangulation
whose outer cycle is `c`" (a cycle written as a list; a list of length two is a single edge). The
fields of `NTCalc` are the separation facts about near-triangulations used in Thomassen's proofs;
they are proved for plane maps separately.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V]

/-- The geometric facts about near-triangulations used by the colouring arguments. -/
structure NTCalc (V : Type*) [DecidableEq V] where
  /-- `H` on `S` is a near-triangulation with outer cycle `c`. -/
  NT : SimpleGraph V → Finset V → List V → Prop
  nodup : ∀ {H S c}, NT H S c → c.Nodup
  two_le : ∀ {H S c}, NT H S c → 2 ≤ c.length
  subset : ∀ {H S c}, NT H S c → ∀ v ∈ c, v ∈ S
  /-- Consecutive vertices of the outer cycle are adjacent. -/
  adj_cons : ∀ {H S x y l}, NT H S (x :: y :: l) → H.Adj x y
  /-- A single edge has no other vertex. -/
  two : ∀ {H S x y}, NT H S [x, y] → S = {x, y}
  /-- Rotation of the outer cycle. -/
  rotate : ∀ {H S x l}, NT H S (x :: l) → NT H S (l ++ [x])
  /-- Reversal of the outer cycle. -/
  reverse : ∀ {H S c}, NT H S c → NT H S c.reverse
  /-- Splitting along a chord `x y` of the outer cycle `x l₁ y l₂`. -/
  chord : ∀ {H S x y l₁ l₂}, NT H S (x :: (l₁ ++ y :: l₂)) → l₁ ≠ [] → l₂ ≠ [] → H.Adj x y →
    ∃ S₁ S₂ : Finset V, NT H S₁ (x :: (l₁ ++ [y])) ∧ NT H S₂ (y :: (l₂ ++ [x])) ∧
      S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {x, y} ∧
      ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁
  /-- Deleting an outer vertex `v` incident with no chord: its other neighbours form a path `us`
  of interior vertices, and `S \ {v}` is a near-triangulation with outer cycle `l ++ us`. -/
  delete : ∀ {H S v l}, NT H S (v :: l) → 3 ≤ (v :: l).length →
    (∀ z ∈ l, H.Adj v z → l.head? = some z ∨ l.getLast? = some z) →
    ∃ us : List V, (∀ u ∈ us, u ∈ S ∧ u ∉ v :: l) ∧
      (∀ z ∈ S, H.Adj v z → l.head? = some z ∨ l.getLast? = some z ∨ z ∈ us) ∧
      NT H (S.erase v) (l ++ us) ∧ ∀ u ∈ us, H.Adj v u
  /-- Cutting along a path `x u y` through an interior vertex `u`, where `x y` is not an edge (an
  edge `x y` would lie on one side only, and be a chord of the other piece's outer cycle that is
  not inside it). -/
  cut : ∀ {H S x y u l₁ l₂}, NT H S (x :: (l₁ ++ y :: l₂)) → u ∈ S →
    u ∉ x :: (l₁ ++ y :: l₂) → H.Adj u x → H.Adj u y → ¬ H.Adj x y →
    ∃ S₁ S₂ : Finset V, NT H S₁ (x :: (l₁ ++ [y, u])) ∧ NT H S₂ (y :: (l₂ ++ [x, u])) ∧
      S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {x, y, u} ∧
      ∀ a ∈ S₁, ∀ w ∈ S₂, H.Adj a w → a ∈ S₂ ∨ w ∈ S₁
  /-- Two interior vertices `u, w` joined to both ends of an outer edge `x y`: one of the triangles
  `x y u`, `x y w` contains the other apex (the inner face at `x y` is unique). The vertices on or
  inside that triangle form a near-triangulation whose inner vertices are interior vertices of `S`
  with all their neighbours inside. -/
  apex2 : ∀ {H S x y u w l}, NT H S (x :: y :: l) → u ∈ S → w ∈ S → u ∉ x :: y :: l →
    w ∉ x :: y :: l → u ≠ w → H.Adj u x → H.Adj u y → H.Adj w x → H.Adj w y →
    ∃ (S₁ : Finset V) (p : V), (p = u ∨ p = w) ∧ NT H S₁ [x, y, p] ∧ S₁ ⊆ S ∧ u ∈ S₁ ∧
      w ∈ S₁ ∧ ∀ v ∈ S₁, v ∉ [x, y, p] → v ∉ x :: y :: l ∧ ∀ z ∈ S, H.Adj v z → z ∈ S₁
  /-- Excising the inside of a triangle: if `S₁ ⊆ S` is a near-triangulation with outer cycle the
  triangle `p q r` and its other vertices are interior vertices of `S` with no neighbour outside
  `S₁`, deleting them leaves a near-triangulation with the same outer cycle. -/
  excise3 : ∀ {H S c S₁ p q r}, NT H S c → NT H S₁ [p, q, r] → S₁ ⊆ S →
    (∀ u ∈ S₁, u ∉ [p, q, r] → u ∉ c ∧ ∀ w ∈ S, H.Adj u w → w ∈ S₁) →
    NT H ((S \ S₁) ∪ {p, q, r}) c

namespace NTCalc

variable (T : NTCalc V)

theorem rotate_back {H : SimpleGraph V} {S : Finset V} {x : V} {l : List V}
    (h : T.NT H S (l ++ [x])) : T.NT H S (x :: l) := by
  have h1 := T.reverse h
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at h1
  have h2 := T.reverse (T.rotate h1)
  simpa [List.reverse_append] using h2

end NTCalc

end ThomassenManyColourings
