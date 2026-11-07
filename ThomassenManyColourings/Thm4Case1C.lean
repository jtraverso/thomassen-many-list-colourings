/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1B

/-!
# Theorem 4, Case 1: cut-vertex neighbours of an interior vertex

Let `K` be a set of vertices of `Q` (the cut and clean vertices) such that every vertex of `K`
other than `q₁, q_r` has two interior neighbours. Then an interior vertex `y` is joined to at most
two vertices of `K` (`card_K_nbrs_le_two`), and the interior vertices joined to two vertices of
`K` are apexes of edges `k k⁺` with `k ∈ K \ {q_r}` (`two_K_nbrs_apex`), so there are at most
`|K| - 1` of them. Positions on the outer path are handled by indices; Claim 12 becomes
`C12.idx`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
theorem list_eq_take_getElem_drop (l : List V) (i : ℕ) (hi : i < l.length) :
    l = l.take i ++ l[i] :: l.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons hi]

omit [DecidableEq V] in
/-- A list around two positions `i < j`, with the positions strictly between in the middle. -/
theorem list_eq_two (l : List V) {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    ∃ B, l = l.take i ++ l[i] :: (B ++ l[j] :: l.drop (j + 1)) ∧
      ∀ m (hm : m < l.length), i < m → m < j → l[m] ∈ B := by
  refine ⟨(l.drop (i + 1)).take (j - i - 1), ?_, ?_⟩
  · have e1 := list_eq_take_getElem_drop l i (by omega)
    have e2 := list_eq_take_getElem_drop (l.drop (i + 1)) (j - i - 1) (by simp; omega)
    have e3 : (l.drop (i + 1))[j - i - 1]'(by simp; omega) = l[j] := by
      simp only [List.getElem_drop]; congr 1; omega
    have e4 : (l.drop (i + 1)).drop (j - i - 1 + 1) = l.drop (j + 1) := by
      rw [List.drop_drop]; congr 1; omega
    rw [e3, e4] at e2
    conv_lhs => rw [e1, e2]
  · intro m hm him hmj
    have : (l.drop (i + 1)).take (j - i - 1) = ((l.drop (i + 1)).take (j - i - 1)) := rfl
    rw [List.mem_iff_getElem]
    refine ⟨m - i - 1, by simp; omega, ?_⟩
    simp only [List.getElem_take, List.getElem_drop]
    congr 1; omega

omit [DecidableEq V] in
/-- Claim 12 by positions. -/
theorem C12.idx {H : SimpleGraph V} {S : Finset V} {cyc P : List V} (h : C12 H S cyc P)
    {u : V} (huS : u ∈ S) (hu : u ∉ cyc) {i j m : ℕ} (him : i < m) (hmj : m < j)
    (hj : j < P.length) (hi : H.Adj u (P[i]'(by omega))) (hjj : H.Adj u P[j]) :
    H.Adj u (P[m]'(by omega)) := by
  obtain ⟨B, hB, hmem⟩ := list_eq_two P (by omega : i < j) hj
  exact h u huS hu _ B _ _ _ hB hi hjj _ (hmem m (by omega) him hmj)

namespace NTCalc

variable {T : NTCalc V}

omit [DecidableEq C] in
set_option maxHeartbeats 8000000 in
/-- The apex of the outer edge at position `i`, `i + 1` of the outer path, for `1 ≤ i` (a vertex
of `Q` at `i`): an interior vertex joined to both. -/
theorem Case1Hyp.apex_exists {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i + 1 < (a :: (Q ++ [c])).length) :
    ∃ w ∈ S, w ∉ x :: a :: (Q ++ [c]) ∧ H.Adj w ((a :: (Q ++ [c]))[i]'(by omega)) ∧
      H.Adj w (a :: (Q ++ [c]))[i + 1] := by
  set P := a :: (Q ++ [c]) with hPdef
  have hdec : P = P.take (i - 1) ++ P[i - 1] :: P[i] :: P[i + 1] :: P.drop (i + 2) := by
    conv_lhs => rw [list_eq_take_getElem_drop P (i - 1) (by omega)]
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    simp only [show i - 1 + 1 = i by omega, show i + 1 + 1 = i + 2 by omega]
  obtain ⟨us, hne, -, hus, -, -, hlast⟩ := hc.q_nbhd hdec
  obtain ⟨l, hl⟩ : ∃ l, us.getLast? = some l := ⟨_, List.getLast?_eq_some_getLast hne⟩
  have hlm := List.mem_of_mem_getLast? hl
  exact ⟨l, (hus l hlm).1, (hus l hlm).2.1, ((hus l hlm).2.2).symm, hlast l hl⟩

omit [DecidableEq C] in
set_option maxHeartbeats 16000000 in
/-- An interior vertex joined to both outer neighbours of a vertex `m` of `Q` is its only interior
neighbour. -/
theorem Case1Hyp.only_nbr {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m + 1 < (a :: (Q ++ [c])).length) {y : V} (hyS : y ∈ S)
    (hy : y ∉ x :: a :: (Q ++ [c])) (h₁ : H.Adj y ((a :: (Q ++ [c]))[m - 1]'(by omega)))
    (h₂ : H.Adj y (a :: (Q ++ [c]))[m + 1]) :
    ∀ z ∈ S, z ∉ x :: a :: (Q ++ [c]) → H.Adj ((a :: (Q ++ [c]))[m]'(by omega)) z → z = y := by
  set P := a :: (Q ++ [c]) with hPdef
  have hdec : P = P.take (m - 1) ++ P[m - 1] :: P[m] :: P[m + 1] :: P.drop (m + 2) := by
    conv_lhs => rw [list_eq_take_getElem_drop P (m - 1) (by omega)]
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    simp only [show m - 1 + 1 = m by omega, show m + 1 + 1 = m + 2 by omega]
  obtain ⟨us, hne, hnd, hus, hall, hhead, hlast⟩ := hc.q_nbhd hdec
  -- `y` is joined to `P[m]` (Claim 12), so it is the apex of both outer edges at `P[m]`
  have hyPm : H.Adj y P[m] :=
    hc.c12.idx hyS hy (by omega : m - 1 < m) (by omega : m < m + 1) hm h₁ h₂
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, us.head? = some h₀ := ⟨_, List.head?_eq_some_head hne⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, us.getLast? = some l₀ := ⟨_, List.getLast?_eq_some_getLast hne⟩
  have hh₀m := List.mem_of_mem_head? hh₀
  have hl₀m := List.mem_of_mem_getLast? hl₀
  have hdec2 : P = (P.take (m - 1) ++ [P[m - 1]]) ++ P[m] :: P[m + 1] :: P.drop (m + 2) := by
    rw [List.append_assoc, List.singleton_append]; exact hdec
  have hh : h₀ = y := hc.apex_unique hdec (hus h₀ hh₀m).1 hyS (hus h₀ hh₀m).2.1 hy
    (hhead h₀ hh₀) (hus h₀ hh₀m).2.2.symm h₁ hyPm
  have hl : l₀ = y := hc.apex_unique hdec2 (hus l₀ hl₀m).1 hyS (hus l₀ hl₀m).2.1 hy
    (hus l₀ hl₀m).2.2.symm (hlast l₀ hl₀) hyPm h₂
  -- a repetition-free list whose head equals its last element is a singleton
  have hsingle : us = [y] := by
    rcases us with _ | ⟨u₀, us'⟩
    · exact absurd rfl hne
    · simp only [List.head?_cons, Option.some.injEq] at hh₀
      subst hh₀
      rcases us' with _ | ⟨u₁, us''⟩
      · rw [hh]
      · exfalso
        rw [List.getLast?_cons_cons] at hl₀
        have := List.mem_of_mem_getLast? hl₀
        rw [hl, ← hh] at this
        exact (List.nodup_cons.mp hnd).1 this
  intro z hzS hzn hz
  have := hall z hzS hzn hz
  rw [hsingle] at this
  simpa using this

/-- The vertices of `K` in the situation of Case 1, by positions on the outer path `a Q c`: each is
a vertex of `Q`, and it is `q₁`, `q_r` or has two interior neighbours. -/
def Case1KOK (H : SimpleGraph V) (S : Finset V) (x a c : V) (Q : List V) (K : Finset V) : Prop :=
  ∀ k ∈ K, ∃ (i : ℕ) (hi : i < (a :: (Q ++ [c])).length), (a :: (Q ++ [c]))[i] = k ∧ 1 ≤ i ∧
    i + 2 ≤ (a :: (Q ++ [c])).length ∧ (i = 1 ∨ i + 2 = (a :: (Q ++ [c])).length ∨
      ∃ y₁ ∈ S, ∃ y₂ ∈ S, y₁ ∉ x :: a :: (Q ++ [c]) ∧ y₂ ∉ x :: a :: (Q ++ [c]) ∧ y₁ ≠ y₂ ∧
        H.Adj k y₁ ∧ H.Adj k y₂)

omit [DecidableEq C] in
set_option maxHeartbeats 16000000 in
open Classical in
/-- Positions of the `K`-neighbours of an interior vertex `y`, and their number. -/
theorem Case1Hyp.K_nbrs {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {K : Finset V}
    (hK : Case1KOK H S x a c Q K) {y : V} (hyS : y ∈ S) (hy : y ∉ x :: a :: (Q ++ [c])) :
    (K.filter (fun k => H.Adj y k)).card ≤ 2 ∧
    (2 ≤ (K.filter (fun k => H.Adj y k)).card →
      ∃ (i : ℕ) (hi : i + 1 < (a :: (Q ++ [c])).length), (a :: (Q ++ [c]))[i] ∈ K ∧
        i + 2 < (a :: (Q ++ [c])).length ∧ 1 ≤ i ∧
        H.Adj y (a :: (Q ++ [c]))[i] ∧ H.Adj y (a :: (Q ++ [c]))[i + 1]) := by
  classical
  set P := a :: (Q ++ [c]) with hPdef
  have hPnd : P.Nodup := (List.nodup_cons.mp (T.nodup hc.nt)).2
  have hPl : (a :: (Q ++ [c])).length = P.length := rfl
  -- positions of the `K`-neighbours
  set I := (Finset.range P.length).filter (fun i => P.getD i a ∈ K ∧ H.Adj y (P.getD i a))
    with hI
  have hsub : K.filter (fun k => H.Adj y k) ⊆ I.image (fun i => P.getD i a) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨i, hi, hik, -⟩ := hK k hk.1
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      rw [List.getD_eq_getElem _ _ hi, hik]
      exact ⟨hi, hk.1, hk.2⟩
    · rw [List.getD_eq_getElem _ _ hi, hik]
  have hcardI : (K.filter (fun k => H.Adj y k)).card ≤ I.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hIpos : ∀ i ∈ I, ∃ hi : i < P.length, P[i] ∈ K ∧ H.Adj y P[i] ∧ 1 ≤ i ∧
      i + 2 ≤ P.length ∧ (i = 1 ∨ i + 2 = P.length ∨
        ∃ y₁ ∈ S, ∃ y₂ ∈ S, y₁ ∉ x :: a :: (Q ++ [c]) ∧ y₂ ∉ x :: a :: (Q ++ [c]) ∧ y₁ ≠ y₂ ∧
          H.Adj P[i] y₁ ∧ H.Adj P[i] y₂) := by
    intro i hiI
    rw [Finset.mem_filter, Finset.mem_range] at hiI
    obtain ⟨hi, hK1, hA⟩ := hiI
    rw [List.getD_eq_getElem _ _ hi] at hK1 hA
    obtain ⟨j, hj, hjk, h1, h2, h3⟩ := hK _ hK1
    have : j = i := (List.Nodup.getElem_inj_iff hPnd).mp hjk
    subst this
    exact ⟨hi, hK1, hA, h1, h2, by rw [hjk] at h3; exact h3⟩
  refine ⟨?_, ?_⟩
  · -- at most two
    by_contra hlt
    push Not at hlt
    have h3 : 3 ≤ I.card := by omega
    have hne : I.Nonempty := Finset.card_pos.mp (by omega)
    set lo := I.min' hne
    set hi := I.max' hne
    obtain ⟨mid, hmid, hmlo, hmhi⟩ : ∃ mid ∈ I, mid ≠ lo ∧ mid ≠ hi := by
      have : 1 ≤ ((I.erase lo).erase hi).card := by
        have := Finset.pred_card_le_card_erase (s := I) (a := lo)
        have := Finset.pred_card_le_card_erase (s := I.erase lo) (a := hi)
        omega
      obtain ⟨m, hm⟩ := Finset.card_pos.mp this
      simp only [Finset.mem_erase] at hm
      exact ⟨m, hm.2.2, hm.2.1, hm.1⟩
    have hlo : lo < mid := lt_of_le_of_ne (Finset.min'_le I mid hmid) (Ne.symm hmlo)
    have hhi : mid < hi := lt_of_le_of_ne (Finset.le_max' I mid hmid) hmhi
    obtain ⟨hlol, -, hloA, hlo1, -, -⟩ := hIpos lo (Finset.min'_mem I hne)
    obtain ⟨hhil, -, hhiA, -, hhi2, -⟩ := hIpos hi (Finset.max'_mem I hne)
    obtain ⟨hmidl, hmK, -, -, -, hmcase⟩ := hIpos mid hmid
    have hprev : H.Adj y (P[mid - 1]'(by omega)) := by
      rcases Nat.lt_or_ge lo (mid - 1) with h | h
      · exact hc.c12.idx hyS hy h (by omega) hhil hloA hhiA
      · have e : mid - 1 = lo := by omega
        have h' : H.Adj y (P.getD (mid - 1) a) := by
          rw [e, List.getD_eq_getElem _ _ hlol]; exact hloA
        rwa [List.getD_eq_getElem _ _ (by omega)] at h'
    have hnext : H.Adj y (P[mid + 1]'(by omega)) := by
      rcases Nat.lt_or_ge (mid + 1) hi with h | h
      · exact hc.c12.idx hyS hy (by omega) h hhil hloA hhiA
      · have e : mid + 1 = hi := by omega
        have h' : H.Adj y (P.getD (mid + 1) a) := by
          rw [e, List.getD_eq_getElem _ _ hhil]; exact hhiA
        rwa [List.getD_eq_getElem _ _ (by omega)] at h'
    have honly := hc.only_nbr (m := mid) (by omega) (by omega) hyS hy hprev hnext
    rcases hmcase with h | h | ⟨y₁, hy₁S, y₂, hy₂S, hy₁, hy₂, h12, hA1, hA2⟩
    · omega
    · omega
    · exact h12 ((honly y₁ hy₁S hy₁ hA1).trans (honly y₂ hy₂S hy₂ hA2).symm)
  · -- two: the first `K`-neighbour and the next vertex
    intro h2
    have h2' : 2 ≤ I.card := h2.trans hcardI
    have hne : I.Nonempty := Finset.card_pos.mp (by omega)
    set lo := I.min' hne
    set hi := I.max' hne
    have hlohi : lo < hi := Finset.min'_lt_max'_of_card I (by omega)
    obtain ⟨hlol, hloK, hloA, hlo1, -, -⟩ := hIpos lo (Finset.min'_mem I hne)
    obtain ⟨hhil, -, hhiA, -, hhi2, -⟩ := hIpos hi (Finset.max'_mem I hne)
    have hnext : H.Adj y (P[lo + 1]'(by omega)) := by
      rcases Nat.lt_or_ge (lo + 1) hi with h | h
      · exact hc.c12.idx hyS hy (by omega) h hhil hloA hhiA
      · have e : lo + 1 = hi := by omega
        have h' : H.Adj y (P.getD (lo + 1) a) := by
          rw [e, List.getD_eq_getElem _ _ hhil]; exact hhiA
        rwa [List.getD_eq_getElem _ _ (by omega)] at h'
    exact ⟨lo, by omega, hloK, by omega, hlo1, hloA, hnext⟩

end NTCalc

end ThomassenManyColourings
