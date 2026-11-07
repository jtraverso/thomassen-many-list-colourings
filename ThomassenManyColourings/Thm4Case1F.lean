/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1E

/-!
# Theorem 4, Case 1: auxiliary facts for the assembly

* `updL`: precolouring the cut vertices by a list of colours.
* `ncard_ge_card_mul`: disjoint subsets of size at least `M`, one per index of `F`.
* `case1_arith`: the final inequality.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*}

/-- Colour the vertices `ks` by the colours `cs`. -/
def updL (g : V → C) : List V → List C → V → C
  | k :: ks, col :: cs => Function.update (updL g ks cs) k col
  | _, _ => g

theorem updL_of_not_mem (g : V → C) : ∀ (ks : List V) (cs : List C) (v : V), v ∉ ks →
    updL g ks cs v = g v
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, col :: cs, v, hv => by
    simp only [List.mem_cons, not_or] at hv
    simp only [updL]
    rw [Function.update_of_ne hv.1]
    exact updL_of_not_mem g ks cs v hv.2

omit [DecidableEq V] in
theorem forall₂_imp_mem {R R' : V → C → Prop} : ∀ {l₁ : List V} {l₂ : List C},
    List.Forall₂ R l₁ l₂ → (∀ a ∈ l₁, ∀ b, R a b → R' a b) → List.Forall₂ R' l₁ l₂
  | [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h r, hi =>
    List.Forall₂.cons (hi _ List.mem_cons_self _ h)
      (forall₂_imp_mem r (fun a ha b hab => hi a (List.mem_cons_of_mem _ ha) b hab))

theorem updL_forall₂ (g : V → C) : ∀ (ks : List V) (cs : List C), ks.Nodup →
    ks.length = cs.length → List.Forall₂ (fun k col => updL g ks cs k = col) ks cs
  | [], [], _, _ => List.Forall₂.nil
  | k :: ks, col :: cs, hnd, hl => by
    have hk := (List.nodup_cons.mp hnd).1
    refine List.Forall₂.cons (by simp [updL]) ?_
    have := updL_forall₂ g ks cs (List.nodup_cons.mp hnd).2 (by simpa using hl)
    refine forall₂_imp_mem this (fun k₁ hk₁ c₁ h => ?_)
    simp only [updL]
    rw [Function.update_of_ne (fun e => hk (by rw [← e]; exact hk₁))]
    exact h
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

omit [DecidableEq V] in
theorem forall₂_eq_of_forall₂ {f : V → C} : ∀ {ks : List V} {cs cs' : List C},
    List.Forall₂ (fun k col => f k = col) ks cs → List.Forall₂ (fun k col => f k = col) ks cs' →
    cs = cs'
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h₁ r₁, List.Forall₂.cons h₂ r₂ => by
    rw [← h₁, ← h₂, forall₂_eq_of_forall₂ r₁ r₂]

/-- Disjoint subsets of `T`, at least `M` elements each, one for each index in `F`. -/
theorem ncard_ge_card_mul {ι α : Type*} [DecidableEq ι] (F : Finset ι) (E : ι → Set α)
    (T : Set α) (hT : T.Finite) (hsub : ∀ i ∈ F, E i ⊆ T)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (E i) (E j)) (M : ℕ)
    (hM : ∀ i ∈ F, M ≤ (E i).ncard) : F.card * M ≤ T.ncard := by
  have key : ∀ G ⊆ F, G.card * M ≤ (⋃ i ∈ G, E i).ncard ∧ (⋃ i ∈ G, E i) ⊆ T := by
    intro G
    induction G using Finset.induction_on with
    | empty => intro _; simp
    | @insert j G hj ih =>
      intro hG
      obtain ⟨h1, h2⟩ := ih (fun i hi => hG (Finset.mem_insert_of_mem hi))
      have hjF : j ∈ F := hG (Finset.mem_insert_self j G)
      have hU : (⋃ i ∈ insert j G, E i) = E j ∪ ⋃ i ∈ G, E i := by
        ext v; simp
      have hd : Disjoint (E j) (⋃ i ∈ G, E i) := by
        rw [Set.disjoint_iUnion₂_right]
        intro i hi
        exact hdisj j hjF i (hG (Finset.mem_insert_of_mem hi)) (fun e => hj (e ▸ hi))
      have hfin₁ : (E j).Finite := hT.subset (hsub j hjF)
      have hfin₂ : (⋃ i ∈ G, E i).Finite := hT.subset h2
      refine ⟨?_, ?_⟩
      · rw [hU, Set.ncard_union_eq hd hfin₁ hfin₂, Finset.card_insert_of_notMem hj]
        have := hM j hjF
        nlinarith
      · rw [hU]; exact Set.union_subset (hsub j hjF) h2
  obtain ⟨h1, h2⟩ := key F subset_rfl
  exact h1.trans (Set.ncard_le_ncard h2 hT)

/-- The final inequality of Case 1. -/
theorem case1_arith {N F M n' s q : ℕ} (hN : F * M ≤ N) (hM : 2 ^ n' ≤ M ^ 9 * 8 ^ s)
    (hF : 2 ^ (1 + 3 * s) ≤ F ^ 9 * 4 ^ q) : 2 ^ (n' + q + 1) ≤ N ^ 9 * 8 ^ q := by
  have h8 : ∀ k, (8 : ℕ) ^ k = 2 ^ (3 * k) := fun k => by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have h4 : ∀ k, (4 : ℕ) ^ k = 2 ^ (2 * k) := fun k => by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h8] at hM ⊢
  rw [h4] at hF
  have hpos : 0 < 2 ^ (3 * s) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc 2 ^ (n' + q + 1) * 2 ^ (3 * s) = 2 ^ n' * 2 ^ (1 + 3 * s) * 2 ^ q := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ (M ^ 9 * 2 ^ (3 * s)) * (F ^ 9 * 2 ^ (2 * q)) * 2 ^ q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hM hF)
    _ = (F * M) ^ 9 * 2 ^ (3 * q) * 2 ^ (3 * s) := by
        rw [mul_pow, show 3 * q = 2 * q + q by ring, pow_add]; ring
    _ ≤ N ^ 9 * 2 ^ (3 * q) * 2 ^ (3 * s) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 9))

omit [DecidableEq V] in
theorem length_interleave : ∀ (ks : List V) (Bs : List (List V)), ks.length = Bs.length + 1 →
    (interleave ks Bs).length = ks.length + (Bs.map List.length).sum
  | [_], [], _ => rfl
  | k :: k' :: ks, B :: Bs, hl => by
    show (k :: (B ++ interleave (k' :: ks) Bs)).length = _
    rw [List.length_cons, List.length_append,
      length_interleave (k' :: ks) Bs (by simpa using hl)]
    simp; ring
  | [], _, hl => by simp at hl
  | [_], _ :: _, hl => by simp at hl
  | _ :: _ :: _, [], hl => by simp at hl

omit [DecidableEq V] in
theorem ks_sublist_interleave : ∀ (ks : List V) (Bs : List (List V)),
    ks.length = Bs.length + 1 → ks.Sublist (interleave ks Bs)
  | [_], [], _ => List.Sublist.refl _
  | k :: k' :: ks, B :: Bs, hl => by
    show (k :: k' :: ks).Sublist (k :: (B ++ interleave (k' :: ks) Bs))
    exact (ks_sublist_interleave (k' :: ks) Bs (by simpa using hl)).trans
      (List.sublist_append_right B _) |>.cons_cons k
  | [], _, hl => by simp at hl
  | [_], _ :: _, hl => by simp at hl
  | _ :: _ :: _, [], hl => by simp at hl

end ThomassenManyColourings
