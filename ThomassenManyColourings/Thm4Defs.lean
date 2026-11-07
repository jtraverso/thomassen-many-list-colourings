/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Counting

/-!
# Theorem 4: statement

`G` is a near-triangulation with outer cycle `x :: P`, `P = a … c`. Either `c, x, a` (`t3`) or
`x, a` are precoloured by `g`; the other outer vertices have at least three colours and the
interior vertices at least five. `n` is the number of non-precoloured vertices and `r` the
number of those with exactly three colours. If `G` has a colouring, it has at least
`2^{n/9 - r/3}` of them, written `2^n ≤ N^9 · 8^r`, unless (`t3`) a vertex with exactly four
colours is joined to the three precoloured vertices and has only one colour not used on them.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The precoloured vertices. -/
def pcList (t3 : Bool) (x a c : V) : List V := if t3 then [c, x, a] else [x, a]

/-- The hypotheses of Theorem 4. -/
structure Thm4Hyp (H : SimpleGraph V) (S : Finset V) (x : V) (P : List V) (a c : V)
    (L : V → Finset C) (g : V → C) (t3 : Bool) : Prop where
  head : P.head? = some a
  last : P.getLast? = some c
  two_le : 2 ≤ P.length
  xa : g x ≠ g a
  xc : t3 → g x ≠ g c
  ac : t3 → H.Adj a c → g a ≠ g c
  three : ∀ y ∈ P, y ∉ pcList t3 x a c → 3 ≤ (L y).card
  five : ∀ y ∈ S, y ∉ x :: P → 5 ≤ (L y).card

/-- The number of non-precoloured vertices. -/
def nCount (S : Finset V) (pc : List V) : ℕ := (S.filter (· ∉ pc)).card

/-- The number of non-precoloured vertices with exactly three colours. -/
def rCount (S : Finset V) (pc : List V) (L : V → Finset C) : ℕ :=
  (S.filter (fun v => v ∉ pc ∧ (L v).card = 3)).card

/-- The exception of Theorem 4. -/
def Exc4 (H : SimpleGraph V) (S : Finset V) (x a c : V) (L : V → Finset C) (g : V → C)
    (t3 : Bool) : Prop :=
  t3 = true ∧ ∃ u ∈ S, u ∉ [c, x, a] ∧ (L u).card = 4 ∧ H.Adj u c ∧ H.Adj u x ∧ H.Adj u a ∧
    ((L u) \ {g c, g x, g a}).card = 1

/-- `N ≥ 2^{n/9 - r/3}`. -/
def Bound4 (N n r : ℕ) : Prop := 2 ^ n ≤ N ^ 9 * 8 ^ r

/-- The conclusion of Theorem 4. -/
def Thm4Concl (H : SimpleGraph V) (S : Finset V) (x a c : V) (L : V → Finset C) (g : V → C)
    (t3 : Bool) : Prop :=
  (ExtSet H S (pcList t3 x a c) L g).Nonempty → ¬ Exc4 H S x a c L g t3 →
    Bound4 (ExtSet H S (pcList t3 x a c) L g).ncard (nCount S (pcList t3 x a c))
      (rCount S (pcList t3 x a c) L)

theorem bound4_of_le {N n r : ℕ} (hN : 1 ≤ N) (h : n ≤ 3 * r) : Bound4 N n r := by
  unfold Bound4
  have h1 : 2 ^ n ≤ 8 ^ r := by
    calc 2 ^ n ≤ 2 ^ (3 * r) := Nat.pow_le_pow_right (by norm_num) h
      _ = 8 ^ r := by rw [pow_mul]; norm_num
  have h2 : 1 ≤ N ^ 9 := Nat.one_le_pow _ _ hN
  calc 2 ^ n ≤ 8 ^ r := h1
    _ ≤ N ^ 9 * 8 ^ r := Nat.le_mul_of_pos_left _ h2

theorem bound4_mul {N₁ N₂ n₁ n₂ r₁ r₂ : ℕ} (h₁ : Bound4 N₁ n₁ r₁) (h₂ : Bound4 N₂ n₂ r₂) :
    Bound4 (N₁ * N₂) (n₁ + n₂) (r₁ + r₂) := by
  unfold Bound4 at *
  calc 2 ^ (n₁ + n₂) = 2 ^ n₁ * 2 ^ n₂ := pow_add _ _ _
    _ ≤ (N₁ ^ 9 * 8 ^ r₁) * (N₂ ^ 9 * 8 ^ r₂) := Nat.mul_le_mul h₁ h₂
    _ = (N₁ * N₂) ^ 9 * 8 ^ (r₁ + r₂) := by rw [mul_pow, pow_add]; ring

theorem bound4_mono {N N' n r : ℕ} (h : Bound4 N n r) (hN : N ≤ N') : Bound4 N' n r :=
  le_trans h (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 9))

theorem ncard_extSet_pos {H : SimpleGraph V} {S : Finset V} {c : List V} {L : V → Finset C}
    {f₀ : V → C} (h : (ExtSet H S c L f₀).Nonempty) : 1 ≤ (ExtSet H S c L f₀).ncard :=
  (Set.ncard_pos (extSet_finite H S c L f₀)).mpr h

/-- **Theorem 4 when `n ≤ 3r`**: a single colouring suffices. -/
theorem thm4_of_le {H : SimpleGraph V} {S : Finset V} {x a c : V} {L : V → Finset C}
    {g : V → C} {t3 : Bool}
    (h : nCount S (pcList t3 x a c) ≤ 3 * rCount S (pcList t3 x a c) L) :
    Thm4Concl H S x a c L g t3 :=
  fun hne _ => bound4_of_le (ncard_extSet_pos hne) h

end ThomassenManyColourings
