/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.FanColour

/-!
# Lemma 3: two interior vertices (double fan)

The outer path `a = v₂, …, v_k = c` is chordless, `x = v₁` is joined only to `a, c` on it, and the
interior consists of `u` (joined at most to `x, w, a, …, v_i`) and `w` (joined at most to
`x, u, v_i, …, c`). Then every precolouring of `c x a` extends (Lemma 3 of the paper).

Proof (different from the paper's): colour `u` with `α` and `w` with `β ≠ α`. The left path
`v₃ … v_{i-1}` (lists minus `α`) can be coloured with any prescribed colour avoided at its end next
to `v_i` when `L(v₃) ∖ {c(v₂), α}` has two colours ("flexible"), and with some end colour
otherwise; similarly on the right. If a flexible `α` and a flexible `β` can be chosen distinct,
colour `v_i` first. Otherwise a single colour `δ` is flexible on both sides, and a short case
analysis on `L(v_i)` (which has three colours) finds a working pair.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
/-- An element of a set of at least three colours avoiding two given colours. -/
theorem three_pick {A : Finset C} (hA : 3 ≤ A.card) (p q : C) : ∃ z ∈ A, z ≠ p ∧ z ≠ q := by
  have h1 := Finset.pred_card_le_card_erase (s := A) (a := p)
  have h2 := Finset.pred_card_le_card_erase (s := A.erase p) (a := q)
  obtain ⟨z, hz⟩ : ((A.erase p).erase q).Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨z, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz),
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz), Finset.ne_of_mem_erase hz⟩

/-- Colouring a path whose first vertex is flexible: it avoids `h0` and `α`, all vertices avoid
`α`, and the last vertex avoids `d`. -/
theorem side_flex (L : V → Finset C) (h0 α d : C) {m₁ : V} {R : List V} (hnd : (m₁ :: R).Nodup)
    (hflex : 2 ≤ (((L m₁).erase h0).erase α).card) (h3 : ∀ y ∈ R, 3 ≤ (L y).card) :
    ∃ φ : V → C, (∀ y ∈ m₁ :: R, φ y ∈ L y ∧ φ y ≠ α) ∧ φ m₁ ≠ h0 ∧
      (∀ z ∈ (m₁ :: R).getLast?, φ z ≠ d) ∧ (m₁ :: R).IsChain (fun y z => φ y ≠ φ z) := by
  obtain ⟨f₀, hf₀, hf₀e, hf₀c⟩ := path_colour L α R d (List.nodup_cons.mp hnd).2 (fun y hy => by
    have := Finset.pred_card_le_card_erase (s := L y) (a := α)
    have := h3 y hy; omega)
  have hmR : m₁ ∉ R := (List.nodup_cons.mp hnd).1
  let nx : C := (R.head?.map f₀).getD d
  obtain ⟨col, hcol, hcolnx⟩ : ∃ col ∈ ((L m₁).erase h0).erase α, col ≠ nx := by
    obtain ⟨c1, h1, c2, h2', hne⟩ := Finset.one_lt_card.mp
      (show 1 < (((L m₁).erase h0).erase α).card by omega)
    by_cases hc1 : c1 = nx
    · exact ⟨c2, h2', fun h => hne (hc1.trans h.symm)⟩
    · exact ⟨c1, h1, hc1⟩
  have hcolα : col ≠ α := Finset.ne_of_mem_erase hcol
  have hcol0 : col ≠ h0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcol)
  have hcolL : col ∈ L m₁ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcol)
  refine ⟨Function.update f₀ m₁ col, ?_, by rw [Function.update_self]; exact hcol0, ?_, ?_⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [Function.update_self]; exact ⟨hcolL, hcolα⟩
    · have hym : y ≠ m₁ := fun h => hmR (h ▸ hy)
      rw [Function.update_of_ne hym]; exact hf₀ y hy
  · intro z hz
    rcases R with _ | ⟨r, R'⟩
    · simp at hz; subst hz; rw [Function.update_self]; exact hcolnx
    · have hz' : z ∈ (r :: R').getLast? := by simpa [List.getLast?_cons_cons] using hz
      have hzm : z ≠ m₁ := fun h => hmR (h ▸ List.mem_of_mem_getLast? hz')
      rw [Function.update_of_ne hzm]; exact hf₀e z hz'
  · rcases R with _ | ⟨r, R'⟩
    · simp
    · refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
      · have hrm : r ≠ m₁ := fun h => hmR (h ▸ List.mem_cons_self)
        rw [Function.update_self, Function.update_of_ne hrm]; exact hcolnx
      · refine isChain_congr (fun p hp q hq hpq => ?_) hf₀c
        have hpm : p ≠ m₁ := fun h => hmR (h ▸ hp)
        have hqm : q ≠ m₁ := fun h => hmR (h ▸ hq)
        rw [Function.update_of_ne hpm, Function.update_of_ne hqm]; exact hpq

omit [DecidableEq V] [DecidableEq C] in
theorem isChain_ne_reverse {φ : V → C} {l : List V}
    (h : l.reverse.IsChain (fun y z => φ y ≠ φ z)) : l.IsChain (fun y z => φ y ≠ φ z) := by
  rw [List.isChain_reverse] at h
  exact isChain_congr (fun p _ q _ hpq => Ne.symm hpq) h

omit [DecidableEq V] [DecidableEq C] in
theorem isChain_ne_reverse' {φ : V → C} {l : List V}
    (h : l.IsChain (fun y z => φ y ≠ φ z)) : l.reverse.IsChain (fun y z => φ y ≠ φ z) := by
  rw [List.isChain_reverse]
  exact isChain_congr (fun p _ q _ hpq => Ne.symm hpq) h

omit [DecidableEq C] in
/-- The colouring of the whole configuration from a colouring `F` of the outer path. -/
theorem dfan_extend (H : SimpleGraph V) {S : Finset V} {x u w a c : V} {P : List V}
    (hS : ∀ z ∈ S, z = x ∨ z = u ∨ z = w ∨ z ∈ P)
    (hnd : (x :: u :: w :: P).Nodup) (ha : a ∈ P) (hc : c ∈ P)
    (hPc : ∀ y z, y ∈ P → z ∈ P → H.Adj y z → ConsecIn P y z)
    (hxP : ∀ y ∈ P, H.Adj x y → y = a ∨ y = c)
    (L : V → Finset C) (g : V → C) (hxa : g x ≠ g a) (hxc : g x ≠ g c)
    (α β : C) (hαL : α ∈ L u) (hαx : α ≠ g x) (hβL : β ∈ L w) (hβx : β ≠ g x) (hαβ : α ≠ β)
    (F : V → C) (hFa : F a = g a) (hFc : F c = g c)
    (hFL : ∀ y ∈ P, y ≠ a → y ≠ c → F y ∈ L y)
    (hFu : ∀ y ∈ P, H.Adj u y → F y ≠ α) (hFw : ∀ y ∈ P, H.Adj w y → F y ≠ β)
    (hch : P.IsChain (fun y z => F y ≠ F z)) :
    Extends H S [c, x, a] L g := by
  classical
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  obtain ⟨⟨hxu, hxw, hxP'⟩, ⟨huw, huP'⟩, hwP', -⟩ := hnd
  let f : V → C := fun z => if z = x then g x else if z = u then α else if z = w then β else F z
  have fx : f x = g x := by simp [f]
  have fu : f u = α := by simp [f, Ne.symm hxu]
  have fw : f w = β := by simp [f, Ne.symm hxw, Ne.symm huw]
  have fP : ∀ z ∈ P, f z = F z := by
    intro z hz
    have h1 : z ≠ x := fun h => hxP' (h ▸ hz)
    have h2 : z ≠ u := fun h => huP' (h ▸ hz)
    have h3 : z ≠ w := fun h => hwP' (h ▸ hz)
    simp [f, h1, h2, h3]
  have hxv : ∀ z ∈ P, H.Adj x z → f x ≠ f z := by
    intro z hz hxz
    rw [fx, fP z hz]
    rcases hxP z hz hxz with rfl | rfl
    · rw [hFa]; exact hxa
    · rw [hFc]; exact hxc
  have huv : ∀ z ∈ P, H.Adj u z → f u ≠ f z := by
    intro z hz huz; rw [fu, fP z hz]; exact (hFu z hz huz).symm
  have hwv : ∀ z ∈ P, H.Adj w z → f w ≠ f z := by
    intro z hz hwz; rw [fw, fP z hz]; exact (hFw z hz hwz).symm
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · rw [fP z hc, hFc]
    · exact fx
    · rw [fP z ha, hFa]
  · intro z hz hzc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzc
    rcases hS z hz with rfl | rfl | rfl | hzP
    · exact absurd rfl hzc.2.1
    · rw [fu]; exact hαL
    · rw [fw]; exact hβL
    · rw [fP z hzP]; exact hFL z hzP hzc.2.2 hzc.1
  · intro v hv z hz hvz
    rcases hS v hv with rfl | rfl | rfl | hvP <;> rcases hS z hz with rfl | rfl | rfl | hzP
    · exact absurd hvz (H.loopless.irrefl _)
    · rw [fx, fu]; exact hαx.symm
    · rw [fx, fw]; exact hβx.symm
    · exact hxv z hzP hvz
    · rw [fx, fu]; exact hαx
    · exact absurd hvz (H.loopless.irrefl _)
    · rw [fu, fw]; exact hαβ
    · exact huv z hzP hvz
    · rw [fx, fw]; exact hβx
    · rw [fu, fw]; exact hαβ.symm
    · exact absurd hvz (H.loopless.irrefl _)
    · exact hwv z hzP hvz
    · exact (hxv v hvP hvz.symm).symm
    · exact (huv v hvP hvz.symm).symm
    · exact (hwv v hvP hvz.symm).symm
    · rw [fP v hvP, fP z hzP]
      rcases (hPc v z hvP hzP hvz).chain hch with h | h
      · exact h
      · exact Ne.symm h

omit [DecidableEq C] in
/-- The path colouring assembled from a left colouring, a colour at `v_i` and a right
colouring. -/
theorem dfan_build {a vi c m₁ : V} {RL PR : List V}
    (hnd : (a :: (m₁ :: RL ++ vi :: (PR ++ [c]))).Nodup)
    (L : V → Finset C) (g : V → C) (α β ci : C) (hαa : α ≠ g a) (hβc : β ≠ g c)
    (φL : V → C) (hφL : ∀ y ∈ m₁ :: RL, φL y ∈ L y ∧ φL y ≠ α) (hφLa : φL m₁ ≠ g a)
    (hφLe : ∀ z ∈ (m₁ :: RL).getLast?, φL z ≠ ci)
    (hφLc : (m₁ :: RL).IsChain (fun y z => φL y ≠ φL z))
    (φR : V → C) (hφR : ∀ y ∈ PR, φR y ∈ L y ∧ φR y ≠ β)
    (hφRs : ∀ z ∈ PR.head?, φR z ≠ ci) (hφRe : ∀ z ∈ PR.getLast?, φR z ≠ g c)
    (hφRc : PR.IsChain (fun y z => φR y ≠ φR z))
    (hci : ci ∈ L vi) (hciα : ci ≠ α) (hciβ : ci ≠ β) (hcic : PR = [] → ci ≠ g c) :
    ∃ F : V → C, F a = g a ∧ F c = g c ∧
      (∀ y ∈ a :: (m₁ :: RL ++ vi :: (PR ++ [c])), y ≠ a → y ≠ c → F y ∈ L y) ∧
      (∀ y ∈ a :: (m₁ :: RL ++ [vi]), F y ≠ α) ∧ (∀ y ∈ vi :: (PR ++ [c]), F y ≠ β) ∧
      (a :: (m₁ :: RL ++ vi :: (PR ++ [c]))).IsChain (fun y z => F y ≠ F z) := by
  classical
  have h1 : ((a :: m₁ :: RL) ++ (vi :: (PR ++ [c]))).Nodup := hnd
  obtain ⟨hA, hB, hAB⟩ := List.nodup_append.mp h1
  have haL : a ∉ m₁ :: RL := (List.nodup_cons.mp hA).1
  have hviPR : vi ∉ PR := fun h => (List.nodup_cons.mp hB).1 (List.mem_append_left _ h)
  have hvic : vi ≠ c := fun h => (List.nodup_cons.mp hB).1 (by simp [h])
  have hcPR : c ∉ PR := fun h =>
    (List.nodup_append.mp (List.nodup_cons.mp hB).2).2.2 c h c (by simp) rfl
  have hLR : ∀ p ∈ a :: m₁ :: RL, p ≠ vi ∧ p ∉ PR ∧ p ≠ c := fun p hp =>
    ⟨hAB p hp vi (by simp), fun h => hAB p hp p (by simp [h]) rfl, hAB p hp c (by simp)⟩
  let F : V → C := fun z => if z ∈ m₁ :: RL then φL z else if z ∈ PR then φR z else
    if z = vi then ci else g z
  have FL : ∀ y ∈ m₁ :: RL, F y = φL y := fun y hy => by simp only [F, hy, ite_true]
  have FR : ∀ y ∈ PR, F y = φR y := by
    intro y hy
    have : y ∉ m₁ :: RL := fun h => (hLR y (List.mem_cons_of_mem _ h)).2.1 hy
    simp only [F, hy, this, ite_true, ite_false]
  have Fvi : F vi = ci := by
    have : vi ∉ m₁ :: RL := fun h => (hLR vi (List.mem_cons_of_mem _ h)).1 rfl
    simp only [F, this, hviPR, ite_true, ite_false]
  have Fa : F a = g a := by
    have h3 := hLR a (by simp)
    simp only [F, haL, h3.1, h3.2.1, ite_false]
  have Fc : F c = g c := by
    have : c ∉ m₁ :: RL := fun h => (hLR c (List.mem_cons_of_mem _ h)).2.2 rfl
    simp only [F, this, hcPR, Ne.symm hvic, ite_false]
  refine ⟨F, Fa, Fc, ?_, ?_, ?_, ?_⟩
  · intro y hy hya hyc
    have hcl : y = a ∨ y ∈ m₁ :: RL ∨ y = vi ∨ y ∈ PR ∨ y = c := by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
    rcases hcl with h | h | h | h | h
    · exact absurd h hya
    · rw [FL y h]; exact (hφL y h).1
    · rw [h, Fvi]; exact hci
    · rw [FR y h]; exact (hφR y h).1
    · exact absurd h hyc
  · intro y hy
    have hcl : y = a ∨ y ∈ m₁ :: RL ∨ y = vi := by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
    rcases hcl with h | h | h
    · rw [h, Fa]; exact hαa.symm
    · rw [FL y h]; exact (hφL y h).2
    · rw [h, Fvi]; exact hciα
  · intro y hy
    have hcl : y = vi ∨ y ∈ PR ∨ y = c := by
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
    rcases hcl with h | h | h
    · rw [h, Fvi]; exact hciβ
    · rw [FR y h]; exact (hφR y h).2
    · rw [h, Fc]; exact hβc.symm
  · have hLchain : (a :: m₁ :: RL).IsChain (fun y z => F y ≠ F z) := by
      refine List.isChain_cons_cons.mpr ⟨by rw [Fa, FL m₁ (by simp)]; exact Ne.symm hφLa, ?_⟩
      exact isChain_congr (fun p hp q hq hpq => by rw [FL p hp, FL q hq]; exact hpq) hφLc
    have hRchain : (vi :: (PR ++ [c])).IsChain (fun y z => F y ≠ F z) := by
      rcases PR with _ | ⟨r, PR'⟩
      · simp only [List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true]
        rw [Fvi, Fc]; exact hcic rfl
      · refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
        · rw [Fvi, FR r (by simp)]; exact Ne.symm (hφRs r rfl)
        · have : (r :: PR' ++ [c]).IsChain (fun y z => F y ≠ F z) := by
            rw [List.isChain_append]
            refine ⟨isChain_congr (fun p hp q hq hpq => by rw [FR p hp, FR q hq]; exact hpq)
              hφRc, by simp, ?_⟩
            intro p hp q hq
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
            subst hq
            rw [FR p (List.mem_of_mem_getLast? hp), Fc]; exact hφRe p hp
          simpa using this
    have := List.isChain_append.mpr ⟨hLchain, hRchain, ?_⟩
    · simpa using this
    · intro p hp q hq
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      have hp' : p ∈ (m₁ :: RL).getLast? := by
        rcases RL with _ | ⟨r, RL'⟩
        · simpa using hp
        · simpa [List.getLast?_cons_cons] using hp
      rw [FL p (List.mem_of_mem_getLast? hp'), Fvi]; exact hφLe p hp'

omit [DecidableEq V] in
/-- A colour of `A` leaving two colours in `L₁ ∖ {h0, α}`. -/
theorem exists_flex {A : Finset C} (hA : 3 ≤ A.card) (L₁ : Finset C) (h0 : C)
    (hL : 3 ≤ L₁.card) : ∃ α ∈ A, 2 ≤ ((L₁.erase h0).erase α).card := by
  have hB2 : 2 ≤ (L₁.erase h0).card := by
    have := Finset.pred_card_le_card_erase (s := L₁) (a := h0); omega
  obtain ⟨γ₁, h1, γ₂, h2, γ₃, h3', h12, h13, h23⟩ :=
    Finset.two_lt_card.mp (show 2 < A.card by omega)
  by_cases n1 : γ₁ ∈ L₁.erase h0
  · by_cases n2 : γ₂ ∈ L₁.erase h0
    · by_cases n3 : γ₃ ∈ L₁.erase h0
      · refine ⟨γ₁, h1, ?_⟩
        have hB3 : 3 ≤ (L₁.erase h0).card := by
          have : ({γ₁, γ₂, γ₃} : Finset C) ⊆ L₁.erase h0 := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have hc3 : ({γ₁, γ₂, γ₃} : Finset C).card = 3 :=
            Finset.card_eq_three.mpr ⟨γ₁, γ₂, γ₃, h12, h13, h23, rfl⟩
          exact hc3 ▸ Finset.card_le_card this
        have := Finset.card_erase_of_mem n1; omega
      · exact ⟨γ₃, h3', by rw [Finset.erase_eq_of_notMem n3]; exact hB2⟩
    · exact ⟨γ₂, h2, by rw [Finset.erase_eq_of_notMem n2]; exact hB2⟩
  · exact ⟨γ₁, h1, by rw [Finset.erase_eq_of_notMem n1]; exact hB2⟩

set_option maxHeartbeats 8000000 in
/-- **Lemma 3** (double fan): every precolouring of `c x a` extends. -/
theorem dfan (H : SimpleGraph V) {S : Finset V} {x u w a vi c m₁ : V} {RL PR : List V}
    (hS : ∀ z ∈ S, z = x ∨ z = u ∨ z = w ∨ z ∈ a :: (m₁ :: RL ++ vi :: (PR ++ [c])))
    (hnd : (x :: u :: w :: a :: (m₁ :: RL ++ vi :: (PR ++ [c]))).Nodup)
    (hPc : ∀ y z, y ∈ a :: (m₁ :: RL ++ vi :: (PR ++ [c])) →
      z ∈ a :: (m₁ :: RL ++ vi :: (PR ++ [c])) → H.Adj y z →
      ConsecIn (a :: (m₁ :: RL ++ vi :: (PR ++ [c]))) y z)
    (hxP : ∀ y ∈ a :: (m₁ :: RL ++ vi :: (PR ++ [c])), H.Adj x y → y = a ∨ y = c)
    (hun : ∀ z ∈ PR ++ [c], ¬ H.Adj u z) (hwn : ∀ z ∈ a :: m₁ :: RL, ¬ H.Adj w z)
    (L : V → Finset C) (g : V → C) (hxa : g x ≠ g a) (hxc : g x ≠ g c)
    (h3 : ∀ y ∈ m₁ :: RL ++ vi :: PR, 3 ≤ (L y).card) (h5u : 5 ≤ (L u).card)
    (h5w : 5 ≤ (L w).card) :
    Extends H S [c, x, a] L g := by
  classical
  have hPnd : (a :: (m₁ :: RL ++ vi :: (PR ++ [c]))).Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).2
  have hLnd : (m₁ :: RL).Nodup := by
    have h1 : ((a :: m₁ :: RL) ++ (vi :: (PR ++ [c]))).Nodup := hPnd
    exact (List.nodup_cons.mp (List.nodup_append.mp h1).1).2
  have hRnd : PR.Nodup := by
    have h1 : ((a :: m₁ :: RL) ++ (vi :: (PR ++ [c]))).Nodup := hPnd
    exact (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_append.mp h1).2.1).2).1
  have h3L : ∀ y ∈ RL, 3 ≤ (L y).card := fun y hy => h3 y (by simp [hy])
  have h3R : ∀ y ∈ PR, 3 ≤ (L y).card := fun y hy => h3 y (by simp [hy])
  have h3m : 3 ≤ (L m₁).card := h3 m₁ (by simp)
  have h3v : 3 ≤ (L vi).card := h3 vi (by simp)
  -- assembling a colouring from its pieces
  have finish : ∀ α β ci : C, α ∈ L u → α ≠ g x → α ≠ g a → β ∈ L w → β ≠ g x → β ≠ g c →
      α ≠ β → ci ∈ L vi → ci ≠ α → ci ≠ β → (PR = [] → ci ≠ g c) →
      ∀ φL : V → C, (∀ y ∈ m₁ :: RL, φL y ∈ L y ∧ φL y ≠ α) → φL m₁ ≠ g a →
      (∀ z ∈ (m₁ :: RL).getLast?, φL z ≠ ci) → (m₁ :: RL).IsChain (fun y z => φL y ≠ φL z) →
      ∀ φR : V → C, (∀ y ∈ PR, φR y ∈ L y ∧ φR y ≠ β) → (∀ z ∈ PR.head?, φR z ≠ ci) →
      (∀ z ∈ PR.getLast?, φR z ≠ g c) → PR.IsChain (fun y z => φR y ≠ φR z) →
      Extends H S [c, x, a] L g := by
    intro α β ci hαL hαx hαa hβL hβx hβc hαβ hci hciα hciβ hcic φL l1 l2 l3 l4 φR r1 r2 r3 r4
    obtain ⟨F, hFa, hFc, hFL, hFα, hFβ, hch⟩ :=
      dfan_build hPnd L g α β ci hαa hβc φL l1 l2 l3 l4 φR r1 r2 r3 r4 hci hciα hciβ hcic
    refine dfan_extend H hS hnd (by simp) (by simp) hPc hxP L g hxa hxc α β hαL hαx hβL hβx
      hαβ F hFa hFc hFL ?_ ?_ hch
    · intro y hy huy
      apply hFα y
      have : y ∉ PR ++ [c] := fun h => hun y h huy
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy this ⊢
      tauto
    · intro y hy hwy
      apply hFβ y
      have : y ∉ a :: m₁ :: RL := fun h => hwn y h hwy
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy this ⊢
      tauto
  -- candidate colours of `u` and `w`
  have hAu3 : 3 ≤ (((L u).erase (g x)).erase (g a)).card := by
    have := Finset.pred_card_le_card_erase (s := L u) (a := g x)
    have := Finset.pred_card_le_card_erase (s := (L u).erase (g x)) (a := g a); omega
  have hAw3 : 3 ≤ (((L w).erase (g x)).erase (g c)).card := by
    have := Finset.pred_card_le_card_erase (s := L w) (a := g x)
    have := Finset.pred_card_le_card_erase (s := (L w).erase (g x)) (a := g c); omega
  set Au := ((L u).erase (g x)).erase (g a) with hAudef
  set Aw := ((L w).erase (g x)).erase (g c) with hAwdef
  have hAu : ∀ α ∈ Au, α ∈ L u ∧ α ≠ g x ∧ α ≠ g a := fun α h =>
    ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h),
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
  have hAw : ∀ β ∈ Aw, β ∈ L w ∧ β ≠ g x ∧ β ≠ g c := fun β h =>
    ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h),
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
  -- left colourings
  have leftFlex : ∀ α ci, 2 ≤ (((L m₁).erase (g a)).erase α).card →
      ∃ φ : V → C, (∀ y ∈ m₁ :: RL, φ y ∈ L y ∧ φ y ≠ α) ∧ φ m₁ ≠ g a ∧
        (∀ z ∈ (m₁ :: RL).getLast?, φ z ≠ ci) ∧ (m₁ :: RL).IsChain (fun y z => φ y ≠ φ z) :=
    fun α ci hfl => side_flex L (g a) α ci hLnd hfl h3L
  obtain ⟨t, ht⟩ : ∃ t, (m₁ :: RL).getLast? = some t :=
    ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
  have leftAny : ∀ α, ∃ φ : V → C, (∀ y ∈ m₁ :: RL, φ y ∈ L y ∧ φ y ≠ α) ∧ φ m₁ ≠ g a ∧
      (m₁ :: RL).IsChain (fun y z => φ y ≠ φ z) := by
    intro α
    obtain ⟨φ, h1, h2, h4⟩ := path_colour L α (m₁ :: RL).reverse (g a)
      (List.nodup_reverse.mpr hLnd)
      (fun y hy => by
        have := Finset.pred_card_le_card_erase (s := L y) (a := α)
        have := h3 y (by simp at hy ⊢; tauto); omega)
    refine ⟨φ, fun y hy => h1 y (List.mem_reverse.mpr hy), h2 m₁ (by simp), ?_⟩
    exact isChain_ne_reverse h4
  have endL : ∀ (φ : V → C) (ci : C), φ t ≠ ci → ∀ z ∈ (m₁ :: RL).getLast?, φ z ≠ ci := by
    intro φ ci h z hz
    rw [ht] at hz; simp only [Option.mem_def, Option.some.injEq] at hz; subst hz; exact h
  obtain ⟨α₀, hα₀, hfl₀⟩ := exists_flex hAu3 (L m₁) (g a) h3m
  rcases PR.eq_nil_or_concat with hPR | ⟨PR₀, mR, hPR⟩
  · -- no right path: colour `v_i`, the left path, then `w`
    subst hPR
    obtain ⟨ci, hci, hciα, hcic⟩ := three_pick h3v α₀ (g c)
    obtain ⟨φ, h1, h2, h3', h4⟩ := leftFlex α₀ ci hfl₀
    obtain ⟨β, hβ, hβα, hβci⟩ := three_pick hAw3 α₀ ci
    exact finish α₀ β ci (hAu α₀ hα₀).1 (hAu α₀ hα₀).2.1 (hAu α₀ hα₀).2.2 (hAw β hβ).1
      (hAw β hβ).2.1 (hAw β hβ).2.2 (Ne.symm hβα) hci hciα (Ne.symm hβci) (fun _ => hcic)
      φ h1 h2 h3' h4 (fun _ => β) (by simp) (by simp) (by simp) (by simp)
  · -- a right path `PR₀ ++ [mR]`, `mR` next to `c`
    have hPRne : PR ≠ [] := by simp [hPR]
    obtain ⟨p, PR', hp⟩ := List.exists_cons_of_ne_nil hPRne
    have hRrev : PR.reverse = mR :: PR₀.reverse := by simp [hPR]
    have hRrnd : (mR :: PR₀.reverse).Nodup := hRrev ▸ List.nodup_reverse.mpr hRnd
    have hmR : 3 ≤ (L mR).card := h3R mR (by simp [hPR])
    have rightFlex : ∀ β ci, 2 ≤ (((L mR).erase (g c)).erase β).card →
        ∃ φ : V → C, (∀ y ∈ PR, φ y ∈ L y ∧ φ y ≠ β) ∧ (∀ z ∈ PR.head?, φ z ≠ ci) ∧
          (∀ z ∈ PR.getLast?, φ z ≠ g c) ∧ PR.IsChain (fun y z => φ y ≠ φ z) := by
      intro β ci hfl
      obtain ⟨φ, h1, h2, h3', h4⟩ := side_flex L (g c) β ci hRrnd hfl (fun y hy => h3R y (by
        rw [List.mem_reverse] at hy; simp [hPR, hy]))
      refine ⟨φ, fun y hy => h1 y (by rw [← hRrev]; exact List.mem_reverse.mpr hy), ?_, ?_, ?_⟩
      · intro z hz
        apply h3' z
        rw [← hRrev, List.getLast?_reverse]; exact hz
      · intro z hz
        rw [hPR, List.concat_eq_append, List.getLast?_concat] at hz
        simp only [Option.mem_def, Option.some.injEq] at hz; subst hz; exact h2
      · have : PR.reverse.IsChain (fun y z => φ y ≠ φ z) := by rw [hRrev]; exact h4
        exact isChain_ne_reverse this
    have rightAny : ∀ β, ∃ φ : V → C, (∀ y ∈ PR, φ y ∈ L y ∧ φ y ≠ β) ∧
        (∀ z ∈ PR.getLast?, φ z ≠ g c) ∧ PR.IsChain (fun y z => φ y ≠ φ z) := by
      intro β
      exact path_colour L β PR (g c) hRnd (fun y hy => by
        have := Finset.pred_card_le_card_erase (s := L y) (a := β)
        have := h3R y hy; omega)
    have startR : ∀ (φ : V → C) (ci : C), φ p ≠ ci → ∀ z ∈ PR.head?, φ z ≠ ci := by
      intro φ ci h z hz
      rw [hp] at hz; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hz; exact h
    have hcic : PR = [] → ∀ ci : C, ci ≠ g c := fun h => absurd h hPRne
    obtain ⟨β₀, hβ₀, hflR₀⟩ := exists_flex hAw3 (L mR) (g c) hmR
    by_cases hpair : ∃ α ∈ Au, 2 ≤ (((L m₁).erase (g a)).erase α).card ∧
        ∃ β ∈ Aw, 2 ≤ (((L mR).erase (g c)).erase β).card ∧ α ≠ β
    · obtain ⟨α, hα, hflα, β, hβ, hflβ, hαβ⟩ := hpair
      obtain ⟨ci, hci, hciα, hciβ⟩ := three_pick h3v α β
      obtain ⟨φ, h1, h2, h3', h4⟩ := leftFlex α ci hflα
      obtain ⟨ψ, k1, k2, k3, k4⟩ := rightFlex β ci hflβ
      exact finish α β ci (hAu α hα).1 (hAu α hα).2.1 (hAu α hα).2.2 (hAw β hβ).1
        (hAw β hβ).2.1 (hAw β hβ).2.2 hαβ hci hciα hciβ (fun h => hcic h ci)
        φ h1 h2 h3' h4 ψ k1 k2 k3 k4
    push Not at hpair
    -- a single colour `δ` is flexible on both sides
    have hδ : α₀ = β₀ := hpair α₀ hα₀ hfl₀ β₀ hβ₀ hflR₀
    obtain ⟨α₁, hα₁, hα₁δ, -⟩ := three_pick hAu3 α₀ α₀
    obtain ⟨β₁, hβ₁, hβ₁δ, -⟩ := three_pick hAw3 α₀ α₀
    obtain ⟨β₂, hβ₂, hβ₂δ, hβ₂₁⟩ := three_pick hAw3 α₀ β₁
    obtain ⟨ψ₁, a1, a2, a3⟩ := rightAny β₁
    obtain ⟨ψ₂, b1, b2, b3⟩ := rightAny β₂
    obtain ⟨φ₁, c1, c2, c3⟩ := leftAny α₁
    have hα₀u := hAu α₀ hα₀
    have hα₀w := hAw α₀ (hδ ▸ hβ₀)
    have hflR : 2 ≤ (((L mR).erase (g c)).erase α₀).card := hδ ▸ hflR₀
    -- option `(δ, β₁)`
    by_cases hA : ∃ ci ∈ L vi, ci ≠ α₀ ∧ ci ≠ β₁ ∧ ci ≠ ψ₁ p
    · obtain ⟨ci, hci, h1', h2', h3''⟩ := hA
      obtain ⟨φ, l1, l2, l3, l4⟩ := leftFlex α₀ ci hfl₀
      exact finish α₀ β₁ ci hα₀u.1 hα₀u.2.1 hα₀u.2.2 (hAw β₁ hβ₁).1 (hAw β₁ hβ₁).2.1
        (hAw β₁ hβ₁).2.2 (Ne.symm hβ₁δ) hci h1' h2' (fun h => hcic h ci) φ l1 l2 l3 l4
        ψ₁ a1 (startR ψ₁ ci (Ne.symm h3'')) a2 a3
    -- option `(δ, β₂)`
    by_cases hB : ∃ ci ∈ L vi, ci ≠ α₀ ∧ ci ≠ β₂ ∧ ci ≠ ψ₂ p
    · obtain ⟨ci, hci, h1', h2', h3''⟩ := hB
      obtain ⟨φ, l1, l2, l3, l4⟩ := leftFlex α₀ ci hfl₀
      exact finish α₀ β₂ ci hα₀u.1 hα₀u.2.1 hα₀u.2.2 (hAw β₂ hβ₂).1 (hAw β₂ hβ₂).2.1
        (hAw β₂ hβ₂).2.2 (Ne.symm hβ₂δ) hci h1' h2' (fun h => hcic h ci) φ l1 l2 l3 l4
        ψ₂ b1 (startR ψ₂ ci (Ne.symm h3'')) b2 b3
    -- option `(α₁, δ)`
    by_cases hC : ∃ ci ∈ L vi, ci ≠ α₁ ∧ ci ≠ α₀ ∧ ci ≠ φ₁ t
    · obtain ⟨ci, hci, h1', h2', h3''⟩ := hC
      obtain ⟨ψ, k1, k2, k3, k4⟩ := rightFlex α₀ ci hflR
      exact finish α₁ α₀ ci (hAu α₁ hα₁).1 (hAu α₁ hα₁).2.1 (hAu α₁ hα₁).2.2 hα₀w.1 hα₀w.2.1
        hα₀w.2.2 hα₁δ hci h1' h2' (fun h => hcic h ci) φ₁ c1 c2
        (endL φ₁ ci (Ne.symm h3'')) c3 ψ k1 k2 k3 k4
    -- all three fail: `δ ∈ L(v_i)` and the end colours of the other options differ from `δ`
    push Not at hA hB hC
    have hδL : α₀ ∈ L vi := by
      by_contra hn
      obtain ⟨z, hz, hz1, hz2⟩ := three_pick h3v β₁ (ψ₁ p)
      exact hz2 (hA z hz (fun e => hn (e ▸ hz)) hz1)
    have hr1 : ψ₁ p ≠ α₀ := by
      intro e
      obtain ⟨z, hz, hz1, hz2⟩ := three_pick h3v α₀ β₁
      exact hz1 ((hA z hz hz1 hz2).trans e)
    have hr2 : ψ₂ p ≠ α₀ := by
      intro e
      obtain ⟨z, hz, hz1, hz2⟩ := three_pick h3v α₀ β₂
      exact hz1 ((hB z hz hz1 hz2).trans e)
    have hl1 : φ₁ t ≠ α₀ := by
      intro e
      obtain ⟨z, hz, hz1, hz2⟩ := three_pick h3v α₁ α₀
      exact hz2 ((hC z hz hz1 hz2).trans e)
    by_cases h11 : α₁ = β₁
    · have hαβ : α₁ ≠ β₂ := fun e => hβ₂₁ (e.symm.trans h11)
      exact finish α₁ β₂ α₀ (hAu α₁ hα₁).1 (hAu α₁ hα₁).2.1 (hAu α₁ hα₁).2.2 (hAw β₂ hβ₂).1
        (hAw β₂ hβ₂).2.1 (hAw β₂ hβ₂).2.2 hαβ hδL (Ne.symm hα₁δ) (Ne.symm hβ₂δ)
        (fun h => hcic h α₀) φ₁ c1 c2 (endL φ₁ α₀ hl1) c3 ψ₂ b1 (startR ψ₂ α₀ hr2) b2 b3
    · exact finish α₁ β₁ α₀ (hAu α₁ hα₁).1 (hAu α₁ hα₁).2.1 (hAu α₁ hα₁).2.2 (hAw β₁ hβ₁).1
        (hAw β₁ hβ₁).2.1 (hAw β₁ hβ₁).2.2 h11 hδL (Ne.symm hα₁δ) (Ne.symm hβ₁δ)
        (fun h => hcic h α₀) φ₁ c1 c2 (endL φ₁ α₀ hl1) c3 ψ₁ a1 (startR ψ₁ α₀ hr1) a2 a3

end ThomassenManyColourings
