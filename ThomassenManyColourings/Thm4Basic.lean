/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Defs

/-!
# Theorem 4: induction hypothesis and the triangle case

The induction runs on `(n, n − r, t3)` lexicographically. A triangle with all three vertices
precoloured becomes, after deleting `v_k`, an instance with two precoloured vertices and the
same `n` and `r = 0`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The lexicographic order on `(n, s, t3)` (`false < true`). -/
def Lex4 (n s : ℕ) (t : Bool) (n₀ s₀ : ℕ) (t₀ : Bool) : Prop :=
  n < n₀ ∨ (n = n₀ ∧ (s < s₀ ∨ (s = s₀ ∧ t = false ∧ t₀ = true)))

namespace NTCalc

variable (T : NTCalc V)

/-- Theorem 4 for all instances below `(n₀, s₀, t₀)`. -/
def Thm4Lt (C : Type*) [DecidableEq C] (n₀ s₀ : ℕ) (t₀ : Bool) : Prop :=
  ∀ (H : SimpleGraph V) (S : Finset V) (x : V) (P : List V) (a c : V) (L : V → Finset C)
    (g : V → C) (t3 : Bool), T.NT H S (x :: P) → Thm4Hyp H S x P a c L g t3 →
    Lex4 (nCount S (pcList t3 x a c))
      (nCount S (pcList t3 x a c) - rCount S (pcList t3 x a c) L) t3 n₀ s₀ t₀ →
    Thm4Concl H S x a c L g t3

set_option maxHeartbeats 4000000 in
/-- **Theorem 4 for a precoloured triangle**: delete `c`. -/
theorem thm4_k3 (H : SimpleGraph V) {S : Finset V} {x a c : V} {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S [x, a, c]) (hh : Thm4Hyp H S x [a, c] a c L g true)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hxa, hxc⟩, hac, -⟩ := hnd
  have hpc : pcList true x a c = [c, x, a] := rfl
  -- interior vertices have five colours, so `r = 0`
  have h5 : ∀ y ∈ S, y ∉ [c, x, a] → 5 ≤ (L y).card := fun y hy hyc =>
    hh.five y hy (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hyc ⊢; tauto)
  have hr : rCount S [c, x, a] L = 0 := by
    unfold rCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy ⟨hyc, h3⟩
    have := h5 y hy hyc; omega
  have hrot : T.NT H S (c :: [x, a]) := T.rotate_back (by simpa using hNT)
  obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp) (by
    intro z hz _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · left; rfl
    · right; rfl)
  by_cases husn : us = []
  · -- no interior vertex
    subst husn
    apply thm4_of_le
    rw [hpc, hr]
    have hS : S.erase c = {x, a} := T.two (by simpa using hNT')
    have : (S.filter (· ∉ [c, x, a])) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hy hyc
      have hyc' : y ≠ c := fun e => hyc (by simp [e])
      have : y ∈ S.erase c := Finset.mem_erase.mpr ⟨hyc', hy⟩
      rw [hS] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc
      tauto
    unfold nCount; rw [this]; simp
  have husne : us ≠ [] := husn
  obtain ⟨c'', hc''⟩ : ∃ c'', (a :: us).getLast? = some c'' :=
    ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
  let L' : V → Finset C := fun u => if u ∈ us then (L u).erase (g c) else L u
  have hus5 : ∀ u ∈ us, 5 ≤ (L u).card := fun u hu =>
    h5 u (hus u hu).1 (fun h => (hus u hu).2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))
  have hEq : ExtSet H S [c, x, a] L g = ExtSet H (S.erase c) [x, a] L' g := by
    refine extSet_erase_pc (by simp) (T.subset hNT c (by simp)) (fun w => ?_) ?_ ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨Or.inr (Or.inl rfl), hxc⟩
        · exact ⟨Or.inr (Or.inr rfl), hac⟩
      · rintro ⟨h | h | h, hne⟩
        · exact absurd h hne
        · exact Or.inl h
        · exact Or.inr h
    · intro u hu huc hcu
      rcases hnb u hu hcu with h | h | h
      · simp at h; simp [h] at huc
      · simp at h; simp [h] at huc
      · simp [L', h]
    · intro u hu huc hcu
      have : u ∉ us := fun h => hcu (hadj u h)
      simp [L', this]
    · intro w hw _ hcw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact absurd hcw (H.loopless.irrefl _)
      · exact fun e => hh.xc rfl e.symm
      · exact fun e => hh.ac rfl hcw.symm e.symm
  have hn : nCount (S.erase c) [x, a] = nCount S [c, x, a] := by
    unfold nCount
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    tauto
  have hr' : rCount (S.erase c) [x, a] L' = 0 := by
    unfold rCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy ⟨hyc, h3⟩
    have hyS := Finset.mem_of_mem_erase hy
    have hyc' : y ≠ c := Finset.ne_of_mem_erase hy
    by_cases hyu : y ∈ us
    · simp only [L', hyu, ite_true] at h3
      have := Finset.pred_card_le_card_erase (s := L y) (a := g c)
      have := hus5 y hyu; omega
    · simp only [L', hyu, ite_false] at h3
      have := h5 y hyS (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc ⊢
        exact ⟨hyc', hyc⟩)
      omega
  have hNT2 : T.NT H (S.erase c) (x :: (a :: us)) := by simpa using hNT'
  have hh2 : Thm4Hyp H (S.erase c) x (a :: us) a c'' L' g false := by
    refine ⟨rfl, hc'', by simp; exact List.length_pos_iff.mpr husne, hh.xa, by simp,
      by simp, ?_, ?_⟩
    · intro y hy hyp
      have hyu : y ∈ us := by
        simp only [pcList, List.mem_cons, List.not_mem_nil, or_false, not_or,
          Bool.false_eq_true, ite_false] at hy hyp
        tauto
      simp only [L', hyu, ite_true]
      have := Finset.pred_card_le_card_erase (s := L y) (a := g c)
      have := hus5 y hyu; omega
    · intro y hy hyc
      have hyu : y ∉ us := fun h => hyc (by simp [h])
      simp only [L', hyu, ite_false]
      exact h5 y (Finset.mem_of_mem_erase hy) (by
        have := Finset.ne_of_mem_erase hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc ⊢
        exact ⟨this, hyc.1, hyc.2.1⟩)
  have hpc2 : pcList false x a c'' = [x, a] := rfl
  have key := ih H (S.erase c) x (a :: us) a c'' L' g false hNT2 hh2 (by
    rw [hpc2, hn, hr', hpc, hr]
    exact Or.inr ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩)
  intro hne _
  have hne2 : (ExtSet H (S.erase c) [x, a] L' g).Nonempty := by rw [← hEq]; exact hne
  have h1 := key hne2 (fun h => by simp [Exc4] at h)
  change Bound4 (ExtSet H (S.erase c) [x, a] L' g).ncard (nCount (S.erase c) [x, a])
    (rCount (S.erase c) [x, a] L') at h1
  change Bound4 (ExtSet H S [c, x, a] L g).ncard (nCount S [c, x, a]) (rCount S [c, x, a] L)
  rw [hEq, hr, ← hn]
  rwa [hr'] at h1

end NTCalc

end ThomassenManyColourings
