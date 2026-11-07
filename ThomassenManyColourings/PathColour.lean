/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Colouring the paths of a broken wheel string (Lemmas 4 and 5, list form)

A block of a broken wheel string is a path `p₀ p₁ … p_m` whose vertices are all joined to the
major vertex. Once the ends `p₀, p_m` (cut vertices) are coloured, the inner path `p₁ … p_{m-1}`
must be colourable for *every* colour `γ` of the major vertex. Everything is expressed with the
lists of the inner vertices only:

* `ColFrom γ p Ms q`: the inner path with lists `Ms` (avoiding `γ`) can be coloured between ends
  coloured `p` and `q` (for `Ms = []`: `p ≠ q`, the ends are adjacent).
* `Ach γ F Ms`: the colours achievable at the last inner vertex (`colFrom_iff`).
* `lemma4_path` (Lemma 4): given `p`, among any three colours `q` one works for every `γ`.
* `lemma5_block` (Lemma 5 for one block): ends with two-colour lists can be coloured so that
  every `γ` works.
* `lemma5_string` (Lemma 5): the same for a string of blocks.
* `many_strOK`: counting admissible colourings of the cut vertices (Subcase 1.2).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {C : Type*} [DecidableEq C]

/-- The inner path with lists `Ms`, avoiding `γ`, can be coloured between ends coloured `p, q`. -/
def ColFrom (γ : C) : C → List (Finset C) → C → Prop
  | p, [], q => p ≠ q
  | p, M :: Ms, q => ∃ e ∈ M, e ≠ γ ∧ e ≠ p ∧ ColFrom γ e Ms q

/-- Colours of a vertex with list `M` compatible with some colour of `F` at its predecessor. -/
def nxt (γ : C) (F M : Finset C) : Finset C := (M.erase γ).filter (fun d => ∃ e ∈ F, e ≠ d)

/-- The colours achievable at the end of the path. -/
def Ach (γ : C) : Finset C → List (Finset C) → Finset C
  | F, [] => F
  | F, M :: Ms => Ach γ (nxt γ F M) Ms

theorem exists_colFrom_iff (γ : C) : ∀ (Ms : List (Finset C)) (F : Finset C) (q : C),
    (∃ d ∈ F, ColFrom γ d Ms q) ↔ ∃ e ∈ Ach γ F Ms, e ≠ q
  | [], F, q => by simp [ColFrom, Ach]
  | M :: Ms, F, q => by
    have ih := exists_colFrom_iff γ Ms (nxt γ F M) q
    simp only [Ach]
    rw [← ih]
    simp only [ColFrom, nxt, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨d, hd, e, he, heγ, hed, hc⟩
      exact ⟨e, ⟨⟨heγ, he⟩, d, hd, fun h => hed h.symm⟩, hc⟩
    · rintro ⟨e, ⟨⟨heγ, he⟩, d, hd, hde⟩, hc⟩
      exact ⟨d, hd, e, he, heγ, fun h => hde h.symm, hc⟩

theorem colFrom_iff (γ p q : C) (Ms : List (Finset C)) :
    ColFrom γ p Ms q ↔ ∃ e ∈ Ach γ {p} Ms, e ≠ q := by
  rw [← exists_colFrom_iff]; simp

theorem nxt_singleton (γ p : C) (M : Finset C) : nxt γ {p} M = (M.erase γ).erase p := by
  ext d
  simp only [nxt, Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun h => h3 h.symm, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h3⟩, fun h => h1 h.symm⟩

theorem two_le_nxt {γ : C} {F M : Finset C} (hF : 2 ≤ F.card) (hM : 3 ≤ M.card) :
    2 ≤ (nxt γ F M).card := by
  have : nxt γ F M = M.erase γ := by
    unfold nxt
    apply Finset.filter_true_of_mem
    intro d _
    obtain ⟨e₁, h₁, e₂, h₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    by_cases h : e₁ = d
    · exact ⟨e₂, h₂, fun h' => h12 (h.trans h'.symm)⟩
    · exact ⟨e₁, h₁, h⟩
  rw [this]
  have := Finset.pred_card_le_card_erase (s := M) (a := γ)
  omega

theorem two_le_ach {γ : C} : ∀ (Ms : List (Finset C)) (F : Finset C), (∀ M ∈ Ms, 3 ≤ M.card) →
    2 ≤ F.card → 2 ≤ (Ach γ F Ms).card
  | [], _, _, hF => hF
  | M :: Ms, _, hMs, hF =>
    two_le_ach Ms _ (fun M' h => hMs M' (List.mem_cons_of_mem _ h))
      (two_le_nxt hF (hMs M List.mem_cons_self))

theorem nxt_nonempty {γ : C} {F M : Finset C} (hF : F.Nonempty) (hM : 3 ≤ M.card) :
    (nxt γ F M).Nonempty := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨d, hd⟩ : ((M.erase γ).erase f).Nonempty := Finset.card_pos.mp (by
    have := Finset.pred_card_le_card_erase (s := M) (a := γ)
    have := Finset.pred_card_le_card_erase (s := M.erase γ) (a := f)
    omega)
  rw [Finset.mem_erase] at hd
  exact ⟨d, Finset.mem_filter.mpr ⟨hd.2, f, hf, fun h => hd.1 h.symm⟩⟩

theorem ach_nonempty {γ : C} : ∀ (Ms : List (Finset C)) (F : Finset C), (∀ M ∈ Ms, 3 ≤ M.card) →
    F.Nonempty → (Ach γ F Ms).Nonempty
  | [], _, _, hF => hF
  | M :: Ms, _, hMs, hF =>
    ach_nonempty Ms _ (fun M' h => hMs M' (List.mem_cons_of_mem _ h))
      (nxt_nonempty hF (hMs M List.mem_cons_self))

/-- A failing block forces the achievable set to be `{q}`. -/
theorem ach_eq_of_not_colFrom {γ p q : C} {Ms : List (Finset C)} (hMs : ∀ M ∈ Ms, 3 ≤ M.card)
    (h : ¬ ColFrom γ p Ms q) : Ach γ {p} Ms = {q} := by
  rw [colFrom_iff] at h
  push Not at h
  obtain ⟨d, hd⟩ := ach_nonempty (γ := γ) Ms {p} hMs (Finset.singleton_nonempty p)
  ext e
  constructor
  · intro he; rw [Finset.mem_singleton]; exact h e he
  · intro he
    rw [Finset.mem_singleton] at he
    rw [he, ← h d hd]
    exact hd

/-- Removing two colours leaves at most one only if both were present and there were three. -/
theorem erase_erase_card_le_one {M : Finset C} {u v : C} (hM : 3 ≤ M.card) (huv : u ≠ v)
    (h : ((M.erase u).erase v).card ≤ 1) : u ∈ M ∧ v ∈ M ∧ M.card = 3 := by
  by_cases hu : u ∈ M <;> by_cases hv : v ∈ M
  · refine ⟨hu, hv, ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩),
      Finset.card_erase_of_mem hu] at h
    omega
  · rw [Finset.erase_eq_of_notMem (fun h' => hv (Finset.mem_of_mem_erase h')),
      Finset.card_erase_of_mem hu] at h
    omega
  · rw [Finset.erase_eq_of_notMem hu] at h
    have := Finset.pred_card_le_card_erase (s := M) (a := v)
    omega
  · rw [Finset.erase_eq_of_notMem hu, Finset.erase_eq_of_notMem hv] at h
    omega

/-- The first inner list of a failing block contains `γ` and `p` and has three colours. -/
theorem bad_first {γ p q : C} {M : Finset C} {Ms : List (Finset C)} (hM : 3 ≤ M.card)
    (hMs : ∀ M' ∈ Ms, 3 ≤ M'.card) (h : ¬ ColFrom γ p (M :: Ms) q) (hγp : γ ≠ p) :
    γ ∈ M ∧ p ∈ M ∧ M.card = 3 := by
  have hall : ∀ M' ∈ M :: Ms, 3 ≤ M'.card := by
    intro M' h'
    rcases List.mem_cons.mp h' with rfl | h'
    · exact hM
    · exact hMs M' h'
  have hA := ach_eq_of_not_colFrom hall h
  refine erase_erase_card_le_one hM hγp ?_
  by_contra hge
  push Not at hge
  have h2 := two_le_ach (γ := γ) Ms (nxt γ {p} M) hMs (by rw [nxt_singleton]; omega)
  have e : Ach γ {p} (M :: Ms) = Ach γ (nxt γ {p} M) Ms := rfl
  rw [← e, hA] at h2
  simp at h2

/-- **Lemma 4** (path form): given the colour `p` of one end, among any three colours of the other
end one works for every colour of the major vertex. -/
theorem lemma4_path {Ms : List (Finset C)} (hMs : ∀ M ∈ Ms, 3 ≤ M.card) (p : C) {T : Finset C}
    (hT : 3 ≤ T.card) : ∃ q ∈ T, ∀ γ, γ ≠ p → γ ≠ q → ColFrom γ p Ms q := by
  by_contra hcon
  push Not at hcon
  have : Nonempty C := ⟨p⟩
  cases Ms with
  | nil =>
    obtain ⟨q, hq⟩ : (T.erase p).Nonempty := Finset.card_pos.mp (by
      have := Finset.pred_card_le_card_erase (s := T) (a := p); omega)
    obtain ⟨γ, -, -, hc⟩ := hcon q (Finset.mem_of_mem_erase hq)
    exact hc (Ne.symm (Finset.ne_of_mem_erase hq))
  | cons M Ms' =>
    have hM3 := hMs M List.mem_cons_self
    have hR : ∀ M' ∈ Ms', 3 ≤ M'.card := fun M' h => hMs M' (List.mem_cons_of_mem _ h)
    choose! γf hγp hγq hbad using hcon
    have hmaps : ∀ q ∈ T, γf q ∈ M.erase p := fun q hq =>
      Finset.mem_erase.mpr ⟨hγp q hq, (bad_first hM3 hR (hbad q hq) (hγp q hq)).1⟩
    obtain ⟨q₀, hq₀⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    have hcard : (M.erase p).card ≤ 2 := by
      obtain ⟨-, hp, h3⟩ := bad_first hM3 hR (hbad q₀ hq₀) (hγp q₀ hq₀)
      rw [Finset.card_erase_of_mem hp]
      omega
    obtain ⟨q₁, h₁, q₂, h₂, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by omega : (M.erase p).card < T.card) hmaps
    have e1 := ach_eq_of_not_colFrom hMs (hbad q₁ h₁)
    have e2 := ach_eq_of_not_colFrom hMs (hbad q₂ h₂)
    rw [heq, e2] at e1
    exact hne (Finset.singleton_injective e1).symm

/-- Achievable colours along a constant list `{u, v, w}` with `γ = u`: they alternate. -/
theorem ach_const : ∀ (Ms : List (Finset C)) (u v w : C), u ≠ v → u ≠ w → v ≠ w →
    (∀ M ∈ Ms, M = {u, v, w}) → Ach u {v} Ms = if Even Ms.length then {v} else {w}
  | [], _, _, _, _, _, _, _ => by simp [Ach]
  | M :: Ms, u, v, w, huv, huw, hvw, h => by
    have hM := h M List.mem_cons_self
    have e : nxt u {v} M = {w} := by
      rw [nxt_singleton, hM]
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3 | h3 | h3⟩
        · exact absurd h3 h2
        · exact absurd h3 h1
        · exact h3
      · rintro rfl
        exact ⟨hvw.symm, huw.symm, Or.inr (Or.inr rfl)⟩
    have ih := ach_const Ms u w v huw huv hvw.symm (fun M' h' => by
      rw [h M' (List.mem_cons_of_mem _ h'), Finset.pair_comm])
    show Ach u (nxt u {v} M) Ms = _
    rw [e, ih]
    by_cases hn : Even Ms.length
    · have h' : ¬ Even (M :: Ms).length := by
        rw [List.length_cons, Nat.even_add_one]; exact not_not.mpr hn
      simp only [hn, h', ite_true, ite_false]
    · have h' : Even (M :: Ms).length := by rw [List.length_cons, Nat.even_add_one]; exact hn
      simp only [hn, h', ite_true, ite_false]

/-- If both `γ = e` chains from `α` and from `β` are forced, every list is `{e, α, β}`. -/
theorem chain_const : ∀ (Ms : List (Finset C)) (e α β : C), e ≠ α → e ≠ β → α ≠ β →
    (∀ M ∈ Ms, 3 ≤ M.card) → (Ach e {β} Ms).card ≤ 1 → (Ach e {α} Ms).card ≤ 1 →
    ∀ M ∈ Ms, M = {e, α, β}
  | [], _, _, _, _, _, _, _, _, _ => by simp
  | M :: Ms, e, α, β, heα, heβ, hαβ, h3, h1, h2 => by
    have hM3 := h3 M List.mem_cons_self
    have hR : ∀ M' ∈ Ms, 3 ≤ M'.card := fun M' h => h3 M' (List.mem_cons_of_mem _ h)
    have s1 : ((M.erase e).erase β).card ≤ 1 := by
      by_contra hc
      push Not at hc
      have := two_le_ach (γ := e) Ms (nxt e {β} M) hR (by rw [nxt_singleton]; omega)
      change 2 ≤ (Ach e {β} (M :: Ms)).card at this
      omega
    have s2 : ((M.erase e).erase α).card ≤ 1 := by
      by_contra hc
      push Not at hc
      have := two_le_ach (γ := e) Ms (nxt e {α} M) hR (by rw [nxt_singleton]; omega)
      change 2 ≤ (Ach e {α} (M :: Ms)).card at this
      omega
    obtain ⟨heM, hβM, hcard⟩ := erase_erase_card_le_one hM3 heβ s1
    obtain ⟨-, hαM, -⟩ := erase_erase_card_le_one hM3 heα s2
    have hMe : M = {e, α, β} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl <;> assumption
      · rw [hcard, Finset.card_insert_of_notMem (by simp [heα, heβ]),
          Finset.card_insert_of_notMem (by simp [hαβ]), Finset.card_singleton]
    have n1 : nxt e {β} M = {α} := by
      rw [nxt_singleton, hMe]
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3 | h3 | h3⟩
        · exact absurd h3 h2
        · exact h3
        · exact absurd h3 h1
      · rintro rfl
        exact ⟨hαβ, heα.symm, Or.inr (Or.inl rfl)⟩
    have n2 : nxt e {α} M = {β} := by
      rw [nxt_singleton, hMe]
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3 | h3 | h3⟩
        · exact absurd h3 h2
        · exact absurd h3 h1
        · exact h3
      · rintro rfl
        exact ⟨hαβ.symm, heβ.symm, Or.inr (Or.inr rfl)⟩
    have h1' : (Ach e {α} Ms).card ≤ 1 := by
      have : Ach e {β} (M :: Ms) = Ach e (nxt e {β} M) Ms := rfl
      rw [this, n1] at h1; exact h1
    have h2' : (Ach e {β} Ms).card ≤ 1 := by
      have : Ach e {α} (M :: Ms) = Ach e (nxt e {α} M) Ms := rfl
      rw [this, n2] at h2; exact h2
    intro M' hM'
    rcases List.mem_cons.mp hM' with rfl | hM'
    · exact hMe
    · exact chain_const Ms e α β heα heβ hαβ hR h2' h1' M' hM'

/-- **Lemma 5 for one block**: ends with lists of two colours can be coloured so that the inner
path can be coloured for every colour of the major vertex. -/
theorem lemma5_block {Ms : List (Finset C)} (hMs : ∀ M ∈ Ms, 3 ≤ M.card) {A B : Finset C}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    ∃ p ∈ A, ∃ q ∈ B, ∀ γ, γ ≠ p → γ ≠ q → ColFrom γ p Ms q := by
  cases Ms with
  | nil =>
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    obtain ⟨q, hq⟩ : (B.erase p).Nonempty := Finset.card_pos.mp (by
      have := Finset.pred_card_le_card_erase (s := B) (a := p); omega)
    exact ⟨p, hp, q, Finset.mem_of_mem_erase hq, fun γ _ _ => Ne.symm (Finset.ne_of_mem_erase hq)⟩
  | cons M Ms' =>
    have hM3 := hMs M List.mem_cons_self
    have hR : ∀ M' ∈ Ms', 3 ≤ M'.card := fun M' h => hMs M' (List.mem_cons_of_mem _ h)
    by_contra hcon
    push Not at hcon
    obtain ⟨q₁, h₁, q₂, h₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    -- for `p ∈ A`, the bad colours for `q₁, q₂` are the two colours of `M` other than `p`
    have key : ∀ p ∈ A, ∃ γ₁ γ₂, γ₁ ≠ γ₂ ∧ γ₁ ∈ M.erase p ∧ γ₂ ∈ M.erase p ∧
        Ach γ₁ {p} (M :: Ms') = {q₁} ∧ Ach γ₂ {p} (M :: Ms') = {q₂} ∧ p ∈ M ∧ M.card = 3 := by
      intro p hp
      obtain ⟨γ₁, hp1, -, hb1⟩ := hcon p hp q₁ h₁
      obtain ⟨γ₂, hp2, -, hb2⟩ := hcon p hp q₂ h₂
      obtain ⟨hγ1M, hpM, h3⟩ := bad_first hM3 hR hb1 hp1
      obtain ⟨hγ2M, -, -⟩ := bad_first hM3 hR hb2 hp2
      have e1 := ach_eq_of_not_colFrom hMs hb1
      have e2 := ach_eq_of_not_colFrom hMs hb2
      refine ⟨γ₁, γ₂, ?_, Finset.mem_erase.mpr ⟨hp1, hγ1M⟩, Finset.mem_erase.mpr ⟨hp2, hγ2M⟩,
        e1, e2, hpM, h3⟩
      rintro rfl
      rw [e1] at e2
      exact h12 (Finset.singleton_injective e2)
    obtain ⟨a1, a2, ha12, ha1, ha2, ea1, ea2, hαM, hM3'⟩ := key α hα
    obtain ⟨b1, b2, hb12, hb1, hb2, eb1, eb2, hβM, -⟩ := key β hβ
    -- the third colour `e` of `M`
    obtain ⟨e, he⟩ : ∃ e, (M.erase α).erase β = {e} := Finset.card_eq_one.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hαβ, hβM⟩),
        Finset.card_erase_of_mem hαM]
      omega)
    have heM : e ∈ M := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
      (he ▸ Finset.mem_singleton_self e))
    have heα : e ≠ α := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase
      (he ▸ Finset.mem_singleton_self e))
    have heβ : e ≠ β := Finset.ne_of_mem_erase (he ▸ Finset.mem_singleton_self e)
    have hMe : M = {e, α, β} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl <;> assumption
      · rw [hM3', Finset.card_insert_of_notMem (by simp [heα, heβ]),
          Finset.card_insert_of_notMem (by simp [hαβ]), Finset.card_singleton]
    have hMα : M.erase α = {e, β} := by
      rw [hMe]; ext d; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2 | h2⟩
        · exact Or.inl h2
        · exact absurd h2 h1
        · exact Or.inr h2
      · rintro (rfl | rfl)
        · exact ⟨heα, Or.inl rfl⟩
        · exact ⟨hαβ.symm, Or.inr (Or.inr rfl)⟩
    have hMβ : M.erase β = {e, α} := by
      rw [hMe]; ext d; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2 | h2⟩
        · exact Or.inl h2
        · exact Or.inr h2
        · exact absurd h2 h1
      · rintro (rfl | rfl)
        · exact ⟨heβ, Or.inl rfl⟩
        · exact ⟨hαβ, Or.inr (Or.inl rfl)⟩
    -- first steps
    have nx : ∀ u v w : C, u ≠ v → u ≠ w → v ≠ w → M = {u, v, w} → nxt u {v} M = {w} := by
      intro u v w huv huw hvw hM
      rw [nxt_singleton, hM]
      ext d
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3 | h3 | h3⟩
        · exact absurd h3 h2
        · exact absurd h3 h1
        · exact h3
      · rintro rfl
        exact ⟨hvw.symm, huw.symm, Or.inr (Or.inr rfl)⟩
    have hM1 : M = {e, α, β} := hMe
    have hM2 : M = {e, β, α} := by rw [hMe, Finset.pair_comm]
    have hM3e : M = {β, α, e} := by
      rw [hMe]; ext d; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have hM4 : M = {α, β, e} := by
      rw [hMe]; ext d; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    -- the four relevant achievable sets
    have A_eα : Ach e {α} (M :: Ms') = Ach e {β} Ms' := by
      show Ach e (nxt e {α} M) Ms' = _; rw [nx e α β heα heβ hαβ hM1]
    have A_eβ : Ach e {β} (M :: Ms') = Ach e {α} Ms' := by
      show Ach e (nxt e {β} M) Ms' = _; rw [nx e β α heβ heα hαβ.symm hM2]
    have A_βα : Ach β {α} (M :: Ms') = Ach β {e} Ms' := by
      show Ach β (nxt β {α} M) Ms' = _; rw [nx β α e hαβ.symm heβ.symm heα.symm hM3e]
    have A_αβ : Ach α {β} (M :: Ms') = Ach α {e} Ms' := by
      show Ach α (nxt α {β} M) Ms' = _; rw [nx α β e hαβ heα.symm heβ.symm hM4]
    -- union of the two singletons from `α` and from `β`
    have hUα : Ach β {α} (M :: Ms') ∪ Ach e {α} (M :: Ms') = {q₁, q₂} := by
      rw [hMα] at ha1 ha2
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 ha2
      rcases ha1 with rfl | rfl <;> rcases ha2 with rfl | rfl
      · exact absurd rfl ha12
      · rw [ea2, ea1]; ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [ea1, ea2]; ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      · exact absurd rfl ha12
    have hUβ : Ach α {β} (M :: Ms') ∪ Ach e {β} (M :: Ms') = {q₁, q₂} := by
      rw [hMβ] at hb1 hb2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb1 hb2
      rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
      · exact absurd rfl hb12
      · rw [eb2, eb1]; ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [eb1, eb2]; ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      · exact absurd rfl hb12
    -- both `γ = e` chains are forced
    have c1 : (Ach e {β} Ms').card ≤ 1 := by
      rw [← A_eα]
      rw [hMα] at ha1 ha2
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 ha2
      rcases ha1 with rfl | rfl
      · rw [ea1]; simp
      · rcases ha2 with rfl | rfl
        · rw [ea2]; simp
        · exact absurd rfl ha12
    have c2 : (Ach e {α} Ms').card ≤ 1 := by
      rw [← A_eβ]
      rw [hMβ] at hb1 hb2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb1 hb2
      rcases hb1 with rfl | rfl
      · rw [eb1]; simp
      · rcases hb2 with rfl | rfl
        · rw [eb2]; simp
        · exact absurd rfl hb12
    have hall := chain_const Ms' e α β heα heβ hαβ hR c1 c2
    -- explicit values
    have v1 := ach_const Ms' β e α heβ.symm hαβ.symm heα (fun M' h => by
      rw [hall M' h]; ext d; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have v2 := ach_const Ms' e β α heβ heα hαβ.symm (fun M' h => by
      rw [hall M' h]; ext d; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have v3 := ach_const Ms' α e β heα.symm hαβ heβ (fun M' h => by
      rw [hall M' h]; ext d; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have v4 := ach_const Ms' e α β heα heβ hαβ (fun M' h => by
      rw [hall M' h])
    rw [A_βα, A_eα, v1, v2] at hUα
    rw [A_αβ, A_eβ, v3, v4] at hUβ
    have hcard2 : ({q₁, q₂} : Finset C).card = 2 := Finset.card_pair h12
    by_cases hev : Even Ms'.length
    · simp only [hev, ite_true] at hUα hUβ
      have : β ∈ ({e} ∪ {α} : Finset C) := by
        rw [hUβ, ← hUα]; simp
      simp at this
      rcases this with h | h
      · exact heβ h.symm
      · exact hαβ h.symm
    · simp only [hev, ite_false] at hUα
      rw [Finset.union_self] at hUα
      rw [← hUα] at hcard2
      simp at hcard2

/-- Admissible colourings of the cut vertices of a string (with the inner lists of its blocks). -/
def StrOK : List C → List (List (Finset C)) → Prop
  | [_], [] => True
  | k :: k' :: ks, I :: Is => (∀ γ, γ ≠ k → γ ≠ k' → ColFrom γ k I k') ∧ StrOK (k' :: ks) Is
  | _, _ => False

/-- **Lemma 5**: the cut vertices of a broken wheel string whose clean vertices have two colours
can be coloured so that every colouring of the major vertices extends. -/
theorem lemma5_string : ∀ (Is : List (List (Finset C))) (K₀ : Finset C) (Ks : List (Finset C)),
    Ks.length = Is.length → (∀ I ∈ Is, ∀ M ∈ I, 3 ≤ M.card) → 2 ≤ K₀.card →
    (∀ K ∈ Ks.dropLast, 3 ≤ K.card) → (∀ K ∈ Ks.getLast?, 2 ≤ K.card) →
    ∃ κs : List C, List.Forall₂ (· ∈ ·) κs (K₀ :: Ks) ∧ StrOK κs Is
  | [], K₀, Ks, hl, _, h0, _, _ => by
    have hKs : Ks = [] := List.eq_nil_of_length_eq_zero hl
    subst hKs
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < K₀.card)
    exact ⟨[p], List.Forall₂.cons hp List.Forall₂.nil, trivial⟩
  | I :: Is, K₀, Ks, hl, hI, h0, hmid, hlast => by
    obtain ⟨K₁, Ks', rfl⟩ : ∃ K₁ Ks', Ks = K₁ :: Ks' := by
      rcases Ks with _ | ⟨K₁, Ks'⟩
      · simp at hl
      · exact ⟨K₁, Ks', rfl⟩
    have hl' : Ks'.length = Is.length := by simpa using hl
    have hI₀ : ∀ M ∈ I, 3 ≤ M.card := hI I List.mem_cons_self
    have hIs : ∀ I' ∈ Is, ∀ M ∈ I', 3 ≤ M.card := fun I' h => hI I' (List.mem_cons_of_mem _ h)
    rcases Is with _ | ⟨I', Is'⟩
    · -- one block
      have hKs' : Ks' = [] := List.eq_nil_of_length_eq_zero hl'
      subst hKs'
      have h1 : 2 ≤ K₁.card := hlast K₁ (by simp)
      obtain ⟨p, hp, q, hq, hpq⟩ := lemma5_block hI₀ h0 h1
      exact ⟨[p, q], List.Forall₂.cons hp (List.Forall₂.cons hq List.Forall₂.nil), hpq, trivial⟩
    · -- split at `K₁`
      have hKs'ne : Ks' ≠ [] := by
        intro h; subst h; simp at hl'
      have h1 : 3 ≤ K₁.card := hmid K₁ (by rw [List.dropLast_cons_of_ne_nil hKs'ne]; simp)
      have hmid' : ∀ K ∈ Ks'.dropLast, 3 ≤ K.card := fun K h =>
        hmid K (by rw [List.dropLast_cons_of_ne_nil hKs'ne]; exact List.mem_cons_of_mem _ h)
      have hlast' : ∀ K ∈ Ks'.getLast?, 2 ≤ K.card := fun K h =>
        hlast K (by rw [List.getLast?_cons_of_ne_nil hKs'ne]; exact h)
      obtain ⟨κs₁, hf₁, hs₁⟩ := lemma5_string (I' :: Is') K₁ Ks' hl' hIs (by omega) hmid' hlast'
      obtain ⟨ρ₁, κt₁, rfl⟩ : ∃ ρ κt, κs₁ = ρ :: κt := by
        rcases κs₁ with _ | ⟨ρ, κt⟩
        · cases hf₁
        · exact ⟨ρ, κt, rfl⟩
      have hρ₁ : ρ₁ ∈ K₁ := by cases hf₁; assumption
      obtain ⟨κs₂, hf₂, hs₂⟩ := lemma5_string (I' :: Is') (K₁.erase ρ₁) Ks' hl' hIs
        (by have := Finset.pred_card_le_card_erase (s := K₁) (a := ρ₁); omega) hmid' hlast'
      obtain ⟨ρ₂, κt₂, rfl⟩ : ∃ ρ κt, κs₂ = ρ :: κt := by
        rcases κs₂ with _ | ⟨ρ, κt⟩
        · cases hf₂
        · exact ⟨ρ, κt, rfl⟩
      have hρ₂ : ρ₂ ∈ K₁.erase ρ₁ := by cases hf₂; assumption
      have h12 : ρ₂ ≠ ρ₁ := Finset.ne_of_mem_erase hρ₂
      obtain ⟨p, hp, q, hq, hpq⟩ := lemma5_block hI₀ h0
        (show 2 ≤ ({ρ₁, ρ₂} : Finset C).card by rw [Finset.card_pair h12.symm])
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · refine ⟨p :: q :: κt₁, List.Forall₂.cons hp ?_, hpq, hs₁⟩
        cases hf₁ with
        | cons h hr => exact List.Forall₂.cons h hr
      · refine ⟨p :: q :: κt₂, List.Forall₂.cons hp ?_, hpq, hs₂⟩
        cases hf₂ with
        | cons h hr => exact List.Forall₂.cons (Finset.mem_of_mem_erase h) hr

omit [DecidableEq C] in
theorem colFrom_snoc (γ : C) : ∀ (Ms : List (Finset C)) (p q : C) (M : Finset C),
    ColFrom γ p (Ms ++ [M]) q ↔ ∃ e ∈ M, e ≠ γ ∧ e ≠ q ∧ ColFrom γ p Ms e
  | [], p, q, M => by
    simp only [List.nil_append, ColFrom]
    constructor
    · rintro ⟨e, he, h1, h2, h3⟩; exact ⟨e, he, h1, h3, fun h => h2 h.symm⟩
    · rintro ⟨e, he, h1, h2, h3⟩; exact ⟨e, he, h1, fun h => h3 h.symm, h2⟩
  | N :: Ms, p, q, M => by
    simp only [List.cons_append, ColFrom]
    constructor
    · rintro ⟨d, hd, h1, h2, h3⟩
      obtain ⟨e, he, e1, e2, e3⟩ := (colFrom_snoc γ Ms d q M).1 h3
      exact ⟨e, he, e1, e2, d, hd, h1, h2, e3⟩
    · rintro ⟨e, he, e1, e2, d, hd, h1, h2, e3⟩
      exact ⟨d, hd, h1, h2, (colFrom_snoc γ Ms d q M).2 ⟨e, he, e1, e2, e3⟩⟩

omit [DecidableEq C] in
theorem colFrom_reverse (γ : C) : ∀ (Ms : List (Finset C)) (p q : C),
    ColFrom γ p Ms q ↔ ColFrom γ q Ms.reverse p
  | [], p, q => by simp only [ColFrom, List.reverse_nil]; exact ne_comm
  | M :: Ms, p, q => by
    rw [List.reverse_cons, colFrom_snoc]
    simp only [ColFrom]
    constructor
    · rintro ⟨e, he, h1, h2, h3⟩; exact ⟨e, he, h1, h2, (colFrom_reverse γ Ms e q).1 h3⟩
    · rintro ⟨e, he, h1, h2, h3⟩; exact ⟨e, he, h1, h2, (colFrom_reverse γ Ms e q).2 h3⟩

/-- **Lemma 4**, the other direction: given the colour `q` of the far end, among any three
colours of the near end one works. -/
theorem lemma4_path_rev {Ms : List (Finset C)} (hMs : ∀ M ∈ Ms, 3 ≤ M.card) (q : C)
    {T : Finset C} (hT : 3 ≤ T.card) : ∃ p ∈ T, ∀ γ, γ ≠ p → γ ≠ q → ColFrom γ p Ms q := by
  obtain ⟨p, hp, h⟩ := lemma4_path (Ms := Ms.reverse) (fun M hM => hMs M (List.mem_reverse.mp hM))
    q hT
  exact ⟨p, hp, fun γ h1 h2 => (colFrom_reverse γ Ms p q).2 (h γ h2 h1)⟩

/-- The number of triangle blocks. -/
def nTri : List (List (Finset C)) → ℕ
  | [] => 0
  | [] :: Is => nTri Is + 1
  | (_ :: _) :: Is => nTri Is

/-- **Counting** admissible colourings of the cut vertices, anchored at the last (clean) vertex:
at least `2 · 2^t` of them, `t` the number of triangle blocks. -/
theorem many_strOK : ∀ (Is : List (List (Finset C))) (K₀ : Finset C) (Ks : List (Finset C)),
    Ks.length = Is.length → (∀ I ∈ Is, ∀ M ∈ I, 3 ≤ M.card) →
    (∀ K ∈ (K₀ :: Ks).dropLast, 3 ≤ K.card) → (∀ K ∈ (K₀ :: Ks).getLast?, 2 ≤ K.card) →
    ∃ F : Finset (List C), 2 ^ nTri Is * 2 ≤ F.card ∧
      ∀ κs ∈ F, List.Forall₂ (· ∈ ·) κs (K₀ :: Ks) ∧ StrOK κs Is
  | [], K₀, Ks, hl, _, _, hlast => by
    have hKs : Ks = [] := List.eq_nil_of_length_eq_zero hl
    subst hKs
    refine ⟨K₀.image (fun c => [c]), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => (List.cons.inj h).1)]
      simpa [nTri] using hlast K₀ (by simp)
    · intro κs hκ
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
      exact ⟨List.Forall₂.cons hc List.Forall₂.nil, trivial⟩
  | I :: Is, K₀, Ks, hl, hI, hmid, hlast => by
    classical
    obtain ⟨K₁, Ks', rfl⟩ : ∃ K₁ Ks', Ks = K₁ :: Ks' := by
      rcases Ks with _ | ⟨K₁, Ks'⟩
      · simp at hl
      · exact ⟨K₁, Ks', rfl⟩
    have hl' : Ks'.length = Is.length := by simpa using hl
    have hI₀ : ∀ M ∈ I, 3 ≤ M.card := hI I List.mem_cons_self
    have hIs : ∀ I' ∈ Is, ∀ M ∈ I', 3 ≤ M.card := fun I' h => hI I' (List.mem_cons_of_mem _ h)
    have h0 : 3 ≤ K₀.card := hmid K₀ (by simp)
    have hmid' : ∀ K ∈ (K₁ :: Ks').dropLast, 3 ≤ K.card := fun K h =>
      hmid K (by rw [List.dropLast_cons_of_ne_nil (by simp)]; exact List.mem_cons_of_mem _ h)
    have hlast' : ∀ K ∈ (K₁ :: Ks').getLast?, 2 ≤ K.card := fun K h =>
      hlast K (by rw [List.getLast?_cons_of_ne_nil (by simp)]; exact h)
    obtain ⟨F', hF', hF'm⟩ := many_strOK Is K₁ Ks' hl' hIs hmid' hlast'
    let D : List C → Finset C := fun κs' =>
      K₀.filter (fun d => ∀ ρ ∈ κs'.head?, ∀ γ, γ ≠ d → γ ≠ ρ → ColFrom γ d I ρ)
    have hD : ∀ κs' ∈ F', (if I = [] then 2 else 1) ≤ (D κs').card := by
      intro κs' hκ
      obtain ⟨hf, -⟩ := hF'm κs' hκ
      obtain ⟨ρ, κt, rfl⟩ : ∃ ρ κt, κs' = ρ :: κt := by
        rcases κs' with _ | ⟨ρ, κt⟩
        · cases hf
        · exact ⟨ρ, κt, rfl⟩
      by_cases hIe : I = []
      · subst hIe
        simp only [ite_true]
        have : K₀.erase ρ ⊆ D (ρ :: κt) := by
          intro d hd
          simp only [D, Finset.mem_filter, List.head?_cons, Option.mem_def, Option.some.injEq,
            forall_eq']
          exact ⟨Finset.mem_of_mem_erase hd, fun γ _ _ => Finset.ne_of_mem_erase hd⟩
        have := Finset.card_le_card this
        have := Finset.pred_card_le_card_erase (s := K₀) (a := ρ)
        omega
      · simp only [hIe, ite_false]
        obtain ⟨d, hd, hgood⟩ := lemma4_path_rev hI₀ ρ h0
        refine Finset.card_pos.mpr ⟨d, ?_⟩
        simp only [D, Finset.mem_filter, List.head?_cons, Option.mem_def, Option.some.injEq,
          forall_eq']
        exact ⟨hd, hgood⟩
    refine ⟨F'.biUnion (fun κs' => (D κs').image (fun d => d :: κs')), ?_, ?_⟩
    · rw [Finset.card_biUnion]
      · have hc : ∀ κs' ∈ F', ((D κs').image (fun d => d :: κs')).card = (D κs').card :=
          fun κs' _ => Finset.card_image_of_injective _ (fun a b h => (List.cons.inj h).1)
        rw [Finset.sum_congr rfl hc]
        calc 2 ^ nTri (I :: Is) * 2 ≤ F'.card * (if I = [] then 2 else 1) := by
              by_cases hIe : I = []
              · subst hIe; simp only [nTri, ite_true, pow_succ]; nlinarith
              · obtain ⟨M, I', rfl⟩ := List.exists_cons_of_ne_nil hIe
                simp only [nTri, reduceCtorEq, ite_false, mul_one]; exact hF'
          _ = ∑ _κs' ∈ F', (if I = [] then 2 else 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ κs' ∈ F', (D κs').card := Finset.sum_le_sum hD
      · intro a _ b _ hab
        rw [Function.onFun, Finset.disjoint_left]
        intro l h1 h2
        obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨d', -, h⟩ := Finset.mem_image.mp h2
        exact hab (List.cons.inj h).2.symm
    · intro κs hκ
      obtain ⟨κs', hκ', hκs⟩ := Finset.mem_biUnion.mp hκ
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hκs
      obtain ⟨hf, hs⟩ := hF'm κs' hκ'
      simp only [D, Finset.mem_filter] at hd
      obtain ⟨ρ, κt, rfl⟩ : ∃ ρ κt, κs' = ρ :: κt := by
        rcases κs' with _ | ⟨ρ, κt⟩
        · cases hf
        · exact ⟨ρ, κt, rfl⟩
      exact ⟨List.Forall₂.cons hd.1 hf, hd.2 ρ (by simp), hs⟩

end ThomassenManyColourings
