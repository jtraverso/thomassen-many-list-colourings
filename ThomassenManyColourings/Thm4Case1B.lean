/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1A

/-!
# Theorem 4, Case 1: the blocks of the broken wheel string

A vertex of `Q` is *inner* if it has at most one interior neighbour. A run `B` of inner vertices
between two vertices `k, k'` of the outer path has a common interior neighbour (the major vertex
of the block), joined to `k` and `k'` (`block_major`). Splitting `Q` at the non-inner vertices
(`exists_interleave`) gives the blocks.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- Interleave cut vertices `k₀ k₁ … k_s` with the runs `B₁ … B_s` between them. -/
def interleave : List V → List (List V) → List V
  | [k], [] => [k]
  | k :: k' :: ks, B :: Bs => k :: (B ++ interleave (k' :: ks) Bs)
  | _, _ => []

omit [DecidableEq V] in
/-- Every list whose first and last entries satisfy `p` splits at the entries satisfying `p`. -/
theorem exists_interleave (p : V → Prop) [DecidablePred p] :
    ∀ (n : ℕ) (l : List V), l.length = n → l ≠ [] → (∀ h ∈ l.head?, p h) →
    (∀ z ∈ l.getLast?, p z) →
    ∃ (ks : List V) (Bs : List (List V)), l = interleave ks Bs ∧ ks.length = Bs.length + 1 ∧
      ks.head? = l.head? ∧ ks.getLast? = l.getLast? ∧ (∀ k ∈ ks, p k) ∧
      (∀ B ∈ Bs, ∀ b ∈ B, ¬ p b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hne hh hl
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hph : p h := hh h rfl
  by_cases ht : t = []
  · subst ht
    exact ⟨[h], [], rfl, rfl, rfl, rfl, by simpa using hph, by simp⟩
  -- the first run and the rest
  set B := t.takeWhile (fun b => ¬ p b) with hB
  set rest := t.dropWhile (fun b => ¬ p b) with hrest
  have hsplit : t = B ++ rest := (List.takeWhile_append_dropWhile).symm
  have hBnp : ∀ b ∈ B, ¬ p b := by
    intro b hb
    have := List.mem_takeWhile_imp hb
    simpa using this
  have hrestne : rest ≠ [] := by
    intro h0
    rw [h0, List.append_nil] at hsplit
    have hlast : (h :: t).getLast? = t.getLast? := by
      rcases t with _ | ⟨b, t'⟩
      · exact absurd rfl ht
      · rw [List.getLast?_cons_cons]
    obtain ⟨z, hz⟩ : ∃ z, t.getLast? = some z := ⟨_, List.getLast?_eq_some_getLast ht⟩
    have hpz := hl z (by rw [hlast, hz]; rfl)
    have hzt : z ∈ t := List.mem_of_mem_getLast? hz
    rw [hsplit] at hzt
    exact hBnp z hzt hpz
  obtain ⟨k, t', hkt⟩ := List.exists_cons_of_ne_nil hrestne
  have hpk : p k := by
    have := List.head?_dropWhile_not (fun b => decide (¬ p b)) t
    rw [← hrest, hkt] at this
    simpa using this
  have hlen : (k :: t').length < n := by
    rw [← hn]
    have := congrArg List.length hsplit
    simp [hkt] at this ⊢
    omega
  obtain ⟨ks, Bs, heq, hlen', hhd, hlst, hks, hBs⟩ := ih _ hlen (k :: t') rfl (by simp)
    (by simpa using hpk) (by
      intro z hz
      apply hl z
      rw [List.getLast?_cons_of_ne_nil ht, hsplit, hkt,
        List.getLast?_append_of_ne_nil _ (by simp)]
      exact hz)
  obtain ⟨k₀, ks', rfl⟩ : ∃ k₀ ks', ks = k₀ :: ks' := by
    rcases ks with _ | ⟨k₀, ks'⟩
    · simp at hlen'
    · exact ⟨k₀, ks', rfl⟩
  have hk₀ : k₀ = k := by simpa using hhd
  subst hk₀
  refine ⟨h :: k₀ :: ks', B :: Bs, ?_, by simp [hlen'], rfl, ?_, ?_, ?_⟩
  · show h :: t = h :: (B ++ interleave (k₀ :: ks') Bs)
    rw [← heq, ← hkt, ← hsplit]
  · rw [List.getLast?_cons_of_ne_nil (by simp), hlst, List.getLast?_cons_of_ne_nil ht, hsplit,
      hkt, List.getLast?_append_of_ne_nil _ (by simp)]
  · intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hph
    · exact hks k' hk'
  · intro B' hB' b hb
    rcases List.mem_cons.mp hB' with rfl | hB'
    · exact hBnp b hb
    · exact hBs B' hB' b hb

namespace NTCalc

variable {T : NTCalc V}

omit [DecidableEq C] in
set_option maxHeartbeats 8000000 in
/-- **The major vertex of a block**: a nonempty run `B` of vertices with at most one interior
neighbour, between `k` and `k'` on the outer path, has a common interior neighbour `w`, joined to
`k`, `k'` and every vertex of `B`, and the only interior neighbour of each vertex of `B`. -/
theorem Case1Hyp.block_major {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) :
    ∀ (B A E : List V) (k k' : V), a :: (Q ++ [c]) = A ++ k :: (B ++ k' :: E) → B ≠ [] →
    (∀ b ∈ B, ∀ y₁ ∈ S, ∀ y₂ ∈ S, y₁ ∉ x :: a :: (Q ++ [c]) → y₂ ∉ x :: a :: (Q ++ [c]) →
      H.Adj b y₁ → H.Adj b y₂ → y₁ = y₂) →
    ∃ w ∈ S, w ∉ x :: a :: (Q ++ [c]) ∧ H.Adj w k ∧ H.Adj w k' ∧
      ∀ b ∈ B, H.Adj w b ∧ ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj b y → y = w := by
  intro B
  induction B with
  | nil => intro _ _ _ _ _ h; exact absurd rfl h
  | cons b B' ih =>
    intro A E k k' hP _ hinner
    set s := (B' ++ [k']).head (by simp) with hs
    have hdec : a :: (Q ++ [c]) = A ++ k :: b :: s :: ((B' ++ [k']).tail ++ E) := by
      rw [hP]
      rcases B' with _ | ⟨b', B''⟩ <;> simp [hs]
    obtain ⟨us, hne, hnd, hus, hall, hhead, hlast⟩ := hc.q_nbhd hdec
    -- `us = [w]`
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil us hne
    have hus1 : ∀ u ∈ us, u = w := fun u hu =>
      hinner b (by simp) u (hus u hu).1 w (hus w hw).1 (hus u hu).2.1 (hus w hw).2.1
        (hus u hu).2.2 (hus w hw).2.2
    have hwhead : ∀ h ∈ us.head?, h = w := fun h hh => hus1 h (List.mem_of_mem_head? hh)
    have hwlast : ∀ l ∈ us.getLast?, l = w := fun l hl => hus1 l (List.mem_of_mem_getLast? hl)
    obtain ⟨h₀, hh₀⟩ : ∃ h₀, us.head? = some h₀ := ⟨_, List.head?_eq_some_head hne⟩
    obtain ⟨l₀, hl₀⟩ : ∃ l₀, us.getLast? = some l₀ := ⟨_, List.getLast?_eq_some_getLast hne⟩
    have hwk : H.Adj w k := hwhead h₀ hh₀ ▸ hhead h₀ hh₀
    have hws : H.Adj w s := hwlast l₀ hl₀ ▸ hlast l₀ hl₀
    have hwS := (hus w hw).1
    have hwn := (hus w hw).2.1
    have hwb := (hus w hw).2.2
    have hbonly : ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj b y → y = w :=
      fun y hy hyn hby => hus1 y (hall y hy hyn hby)
    rcases B' with _ | ⟨b', B''⟩
    · -- `s = k'`
      refine ⟨w, hwS, hwn, hwk, by simpa [hs] using hws, ?_⟩
      intro b₁ hb₁
      simp only [List.mem_singleton] at hb₁
      subst hb₁
      exact ⟨hwb.symm, hbonly⟩
    · -- the rest of the run, starting after `b`
      have hs' : s = b' := by simp [hs]
      obtain ⟨w', hw'S, hw'n, hw'b, hw'k', hrest⟩ := ih (A ++ [k]) E b k'
        (by rw [hP]; simp) (by simp) (fun b₁ hb₁ => hinner b₁ (List.mem_cons_of_mem _ hb₁))
      -- `w` and `w'` are both apexes of the edge `b b'`
      have hw'b' : H.Adj w' b' := (hrest b' (by simp)).1
      have heq : w = w' := hc.apex_unique (A := A ++ [k]) (B := B'' ++ k' :: E) (u := b)
        (v := b') (by rw [hP]; simp) hwS hw'S hwn hw'n hwb.symm (hs' ▸ hws) hw'b hw'b'
      subst heq
      refine ⟨w, hwS, hwn, hwk, hw'k', ?_⟩
      intro b₁ hb₁
      rcases List.mem_cons.mp hb₁ with rfl | hb₁
      · exact ⟨hwb.symm, hbonly⟩
      · exact hrest b₁ hb₁

end NTCalc

end ThomassenManyColourings
