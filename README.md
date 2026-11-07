# Thomassen (2007): exponentially many 5-list-colourings of planar graphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of C. Thomassen, *Exponentially many 5-list-colorings of planar
graphs*, J. Combin. Theory Ser. B 97 (2007) 571–583
([doi:10.1016/j.jctb.2006.09.002](https://doi.org/10.1016/j.jctb.2006.09.002)).

## Statement (`ThomassenManyColouringsChallenge.lean`, namespace `ThomassenManyColourings`)

```lean
theorem two_rpow_card_div_nine_le_ncard_listColourings {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) {C : Type*} (L : V → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card) :
    (2 : ℝ) ^ ((Fintype.card V : ℝ) / 9) ≤ (listColourings G L).ncard
```

A finite planar graph with `n` vertices, every vertex of which has at least five available
colours, has at least `2^{n/9}` distinct list colourings (the main result of the paper).
`listColourings G L` is the set of maps `f : V → C` with `f v ∈ L v` for every `v` and
`f u ≠ f v` for every edge `u v`. Planarity is combinatorial: `IsPlanar G` means that `G` has a
`PlaneMap`, a rotation system (a cyclic order of the darts at every vertex) whose hypermap with the
dart reversal has Euler defect `0`, i.e. genus zero on every component. These definitions are
copied verbatim from the registered entry thomassen-girth-five (PALOMAR-2026-10-28-000023),
`ThomassenMainChallenge.lean`, and are included in the Challenge so that it depends on Mathlib
only.

## Structure of the proof (`ThomassenManyColourings/`)

The combinatorial argument of the paper is proved for an abstract interface `NTCalc`
(`Interface.lean`): a predicate `NT H S c` ("`H` restricted to `S` is a near-triangulation with
outer cycle `c`") together with the geometric facts the colouring arguments use (rotation and
reversal of the outer cycle, splitting along a chord or along a path `x u y` through an interior
vertex, deleting an outer vertex without chords, the triangle spanned by two apices over an outer
edge, excising the inside of a triangle).

* Layer A (colourings, for any `NTCalc`):
  * `Thm1.lean`, `LemmaE.lean`: Theorem 1 (2-extendability of near-triangulations, Thomassen
    1994, with lists of size at least three on the outer cycle);
  * `Thm2.lean`, `Thm2Five.lean`: Theorem 2 (precoloured outer cycles of length at most five);
  * `GW*.lean`, `Wheel.lean`, `Lemma1.lean`, `Lemma3.lean`, `Thm3*.lean`: generalized wheels and
    Theorem 3 (3-extendability with respect to a precoloured path of length two);
  * `Counting.lean`, `Thm4*.lean`: Theorem 4 (at least `2^{n/9 − r/3}` colourings), Claims 8–13,
    Cases 1 and 2 with their subcases (`Thm4Final.lean`, `NTCalc.thm4`);
  * `Thm4Cor.lean`: the corollary for near-triangulations and their spanning subgraphs,
    `2^{|S|} ≤ N^9` (`NTCalc.many_colourings_sub`).
* Layer B (geometry): `PlaneNT.lean` defines plane near-triangulations `PNT` (a plane map of the
  induced graph whose outer face is the cycle and whose other faces are triangles);
  `PlaneChord*.lean`, `PlaneCut*.lean`, `PlaneDelete.lean`, `PlaneApex.lean`,
  `PlaneExcise.lean` prove the interface fields, and `PlaneInstance.lean` assembles
  `planeNTCalc : NTCalc V`. The separations use the registered Jordan-type separation theorems of
  thomassen-girth-five (`Thomassen.facial_arc_chord_separation`,
  `Thomassen.facial_arc_path_separation`, `Thomassen.cycle_sides_*`).
* Completion and conclusion: `PlaneComplete.lean` shows that every finite planar graph with at
  least three vertices is a spanning subgraph of a plane near-triangulation (a planar supergraph
  with the most edges is connected, the vertices of each face form a clique, and Euler's formula
  forces every face to be a triangle); `PlaneFinal.lean` concludes, with the cases of at most two
  vertices treated directly.

`ThomassenManyColouringsSolution.lean` restates the definitions of the Challenge and proves the
theorem from `PlaneFinal.two_rpow_le_ncard`, through the equality of the two definitions of
planarity (`LeanPool.K5MinorFreeChoosability.IsPlanar`) and of the set of list colourings.

## Dependency

The pinned dependency `thomassen_girth_five` (jtraverso/thomassen-girth-five @ 12765f3, registered
as PALOMAR-2026-10-28-000023) is imported, not copied: plane maps, Euler's formula, the
restriction of plane maps to subgraphs, the separation theorems for cycles in plane maps, the
addition of an edge inside a face, and the gluing of plane maps along one vertex.

## Checking

```
lake build ThomassenManyColouringsChallenge ThomassenManyColouringsSolution
```

`ThomassenManyColouringsChallenge.lean` states the result (with `sorry`) using only Mathlib;
`ThomassenManyColouringsSolution.lean` imports the proof. `comparator.json` lists the compared
theorem and definitions; `MATHLIB_DEFINITIONS.md` excerpts the Mathlib definitions used in the
statement.

## AI disclosure

The Lean development was written by an AI agent (Claude Opus 5.5 in Claude Code) under the
author's direction, and mechanically verified (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`). The formalization is by a different author than the article; its author was not
involved.
