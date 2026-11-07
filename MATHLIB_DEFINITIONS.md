# Mathlib definitions used in ThomassenManyColouringsChallenge.lean

Verbatim excerpts of the Mathlib definitions used by the statements in `ThomassenManyColouringsChallenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib. `Setoid`, `Quotient` and `Nat` are from the Lean core library.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 89:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.Dart

`Mathlib/Combinatorics/SimpleGraph/Dart.lean`, line 24:

```lean
/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart extends V × V where
  adj : G.Adj fst snd
  deriving DecidableEq
```

## SimpleGraph.Dart.symm

`Mathlib/Combinatorics/SimpleGraph/Dart.lean`, line 71:

```lean
/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, d.adj.symm⟩
```

## Equiv

`Mathlib/Logic/Equiv/Defs.lean`, line 66:

```lean
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α β : Sort*) where
  /-- The forward map of an equivalence.
```

## Equiv.Perm

`Mathlib/Logic/Equiv/Defs.lean`, line 95:

```lean
/-- `Perm α` is the type of bijections from `α` to itself. -/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α
```

## Function.Involutive.toPerm

`Mathlib/Logic/Equiv/Basic.lean`, line 770:

```lean
/-- Convert an involutive function `f` to a permutation with `toFun = invFun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.leftInverse, h.rightInverse⟩
```

## Equiv.Perm.SameCycle

`Mathlib/GroupTheory/Perm/Cycle/Basic.lean`, line 52:

```lean
/-- The equivalence relation indicating that two points are in the same cycle of a permutation. -/
def SameCycle (f : Perm α) (x y : α) : Prop :=
  ∃ i : ℤ, (f ^ i) x = y
```

## Equiv.Perm.SameCycle.setoid

`Mathlib/GroupTheory/Perm/Cycle/Basic.lean`, line 80:

```lean
/-- The setoid defined by the `SameCycle` relation. -/
@[instance_reducible]
def SameCycle.setoid (f : Perm α) : Setoid α where
  r := f.SameCycle
  iseqv := SameCycle.equivalence f
```

## Relation.EqvGen

`Mathlib/Logic/Relation.lean`, line 409:

```lean
/-- `EqvGen r`: equivalence closure of `r`. -/
@[mk_iff]
inductive EqvGen : α → α → Prop
  | rel x y : r x y → EqvGen x y
  | refl x : EqvGen x x
  | symm x y : EqvGen x y → EqvGen y x
  | trans x y z : EqvGen x y → EqvGen y z → EqvGen x z
```

## Nat.card

`Mathlib/SetTheory/Cardinal/Finite.lean`, line 39:

```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```

## Fintype.card

`Mathlib/Data/Fintype/Card.lean`, line 39:

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```

## Finset.card

`Mathlib/Data/Finset/Card.lean`, line 44:

```lean
/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Set.encard

`Mathlib/Data/Set/Card.lean`, line 66:

```lean
/-- The cardinality of a set as a term in `ℕ∞` -/
noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s
```

## Set.ncard

`Mathlib/Data/Set/Card.lean`, line 612:

```lean
/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) : ℕ := ENat.toNat s.encard
```

## Real.rpow (notation `x ^ y` for real `y`)

`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, line 31:

```lean
/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
```
