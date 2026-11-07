/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Wheel
public import ThomassenManyColourings.GWAlg

/-!
# Lemma 1

A generalized wheel that is not a broken wheel and has no wheel on a triangle (no `K4` block) has
at most one precolouring of its principal path that does not extend. (The paper states it without
the `K4` restriction, which is false: see `NOTES_T07.md`; all its uses exclude separating
triangles.)
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The precolouring `g` of the principal path `b x a` is proper. -/
def PathOK (H : SimpleGraph V) (x a b : V) (g : V → C) : Prop :=
  g x ≠ g a ∧ g x ≠ g b ∧ (H.Adj a b → g a ≠ g b)

/-- At most one proper precolouring of the principal path `b x a` fails to extend. -/
def BadUnique (H : SimpleGraph V) (S : Finset V) (x a b : V) (L : V → Finset C) : Prop :=
  ∀ g g' : V → C, PathOK H x a b g → PathOK H x a b g' → ¬ Extends H S [b, x, a] L g →
    ¬ Extends H S [b, x, a] L g' → g x = g' x ∧ g a = g' a ∧ g b = g' b

/-- Two colours, one avoiding `d, c` and the other `d, c'`, chosen distinct. -/
theorem two_choice (L : Finset C) (hL : 3 ≤ L.card) (d c c' : C) (hcc : c ≠ c') :
    ∃ β ∈ L, β ≠ d ∧ β ≠ c ∧ ∃ β' ∈ L, β' ≠ d ∧ β' ≠ c' ∧ β ≠ β' := by
  have h2 : 1 < (L.erase d).card := by
    have := Finset.pred_card_le_card_erase (s := L) (a := d); omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
  have hpL := Finset.mem_of_mem_erase hp
  have hqL := Finset.mem_of_mem_erase hq
  have hpd := Finset.ne_of_mem_erase hp
  have hqd := Finset.ne_of_mem_erase hq
  by_cases h : p ≠ c ∧ q ≠ c'
  · exact ⟨p, hpL, hpd, h.1, q, hqL, hqd, h.2, hpq⟩
  · have h' : p = c ∨ q = c' := by tauto
    refine ⟨q, hqL, hqd, ?_, p, hpL, hpd, ?_, hpq.symm⟩
    · rcases h' with rfl | rfl
      · exact fun e => hpq e.symm
      · exact fun e => hcc e.symm
    · rcases h' with rfl | rfl
      · exact hcc
      · exact hpq

/-- A colour avoiding two given colours in a list of size three. -/
theorem exists_avoid2 (L : Finset C) (hL : 3 ≤ L.card) (d c : C) :
    ∃ β ∈ L, β ≠ d ∧ β ≠ c := by
  have h1 := Finset.pred_card_le_card_erase (s := L) (a := d)
  have h2 := Finset.pred_card_le_card_erase (s := L.erase d) (a := c)
  obtain ⟨β, hβ⟩ := Finset.card_pos.mp (by omega : 0 < ((L.erase d).erase c).card)
  exact ⟨β, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hβ),
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hβ), Finset.ne_of_mem_erase hβ⟩

namespace NTCalc

variable (T : NTCalc V)

/-- A chord `y z` is impossible when an edge, or an interior vertex, joins the two sides. -/
theorem no_chord_of_crossing {H : SimpleGraph V} {S : Finset V} {y z : V} {l₁ l₂ : List V}
    (hNT : T.NT H S (y :: (l₁ ++ z :: l₂))) (hl₁ : l₁ ≠ []) (hl₂ : l₂ ≠ [])
    {p q : V} (hp : p ∈ l₁) (hq : q ∈ l₂)
    (hcross : H.Adj p q ∨ ∃ w ∈ S, w ∉ y :: (l₁ ++ z :: l₂) ∧ H.Adj w p ∧ H.Adj w q) :
    ¬ H.Adj y z := by
  intro hyz
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hNT hl₁ hl₂ hyz
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = y ∨ w = z := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_append, List.mem_cons, not_or, List.nodup_append]
    at hnd
  have hpy : p ≠ y := fun e => hnd.1.1 (e ▸ hp)
  have hqy : q ≠ y := fun e => hnd.1.2.2 (e ▸ hq)
  have hpz : p ≠ z := fun e => hnd.2.2.2 p hp z (by simp) e
  have hqz : q ≠ z := fun e => hnd.2.2.1.1 (e ▸ hq)
  have hpS₁ : p ∈ S₁ := T.subset h₁ p (by simp [hp])
  have hqS₂ : q ∈ S₂ := T.subset h₂ q (by simp [hq])
  have hpS₂ : p ∉ S₂ := fun h => (hmem p hpS₁ h).elim hpy hpz
  have hqS₁ : q ∉ S₁ := fun h => (hmem q h hqS₂).elim hqy hqz
  rcases hcross with hpq | ⟨w, hwS, hwc, hwp, hwq⟩
  · rcases hX p hpS₁ q hqS₂ hpq with h | h
    · exact hpS₂ h
    · exact hqS₁ h
  · have hwy : w ≠ y := fun e => hwc (by simp [e])
    have hwz : w ≠ z := fun e => hwc (by simp [e])
    have : w ∈ S₁ ∪ S₂ := hU ▸ hwS
    rcases Finset.mem_union.mp this with h1 | h2
    · have hw2 : w ∉ S₂ := fun h => (hmem w h1 h).elim hwy hwz
      rcases hX w h1 q hqS₂ hwq with h | h
      · exact hw2 h
      · exact hqS₁ h
    · have hw1 : w ∉ S₁ := fun h => (hmem w h h2).elim hwy hwz
      rcases hX p hpS₁ w h2 hwp.symm with h | h
      · exact hpS₂ h
      · exact hw1 h

end NTCalc

/-- The second vertex of a generalized wheel is joined to `x` or to a centre joined to `x`. -/
theorem GW.front_second {H : SimpleGraph V} {m : ℕ} {x a v : V} {R : List V} {U : Finset V}
    (h : GW H m x (a :: v :: R) U) : H.Adj x v ∨ ∃ u ∈ U, H.Adj u x ∧ H.Adj u v := by
  generalize hP : a :: v :: R = P at h
  cases h with
  | one hB =>
    cases hB with
    | tri hxa hxb hab =>
      simp only [List.cons.injEq] at hP; obtain ⟨rfl, rfl, -⟩ := hP; exact Or.inl hxb
    | wheel _ _ _ hu hux =>
      exact Or.inr ⟨_, Finset.mem_singleton_self _, hux, hu v (by rw [← hP]; simp)⟩
  | @cons P' Q b U₁ U₂ hB hrest =>
    have hP2 := hB.two_le
    generalize hPb : P' ++ [b] = PB at hB
    have hv : v ∈ PB ∧ ∀ y ∈ PB.getLast?, y = v → True := by
      refine ⟨?_, fun _ _ _ => trivial⟩
      rcases P' with _ | ⟨p, _ | ⟨p', P''⟩⟩
      · simp at hP2
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hP
        obtain ⟨-, rfl, -⟩ := hP; rw [← hPb]; simp
      · simp only [List.cons_append, List.cons.injEq] at hP
        obtain ⟨-, rfl, -⟩ := hP; rw [← hPb]; simp
    cases hB with
    | @tri a' b' hxa hxb hab =>
      have h1 : P' ++ [b] = [a'] ++ [b'] := hPb
      obtain ⟨rfl, hb⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, and_true] at hb
      subst hb
      simp only [List.singleton_append, List.cons.injEq] at hP
      obtain ⟨-, rfl, -⟩ := hP
      exact Or.inl hxb
    | wheel _ _ _ hu hux =>
      exact Or.inr ⟨_, Finset.mem_union_left _ (Finset.mem_singleton_self _), hux, hu v hv.1⟩

namespace NTCalc

variable (T : NTCalc V)

/-- **Lemma 1, front triangle.** Peeling the triangle `x a v` off a generalized wheel. -/
theorem l1_front (H : SimpleGraph V) {S : Finset V} {x a v b : V} {R : List V}
    {U : Finset V} (hNT : T.NT H S (x :: a :: v :: R)) (hb : R.getLast? = some b)
    (hR2 : 2 ≤ R.length) (hxv : H.Adj x v)
    (hrest : GW H 3 x (v :: R) U)
    (hSd : ∀ y ∈ S, y = x ∨ y ∈ a :: v :: R ∨ y ∈ U)
    (hU : ∀ u ∈ U, u ∈ S ∧ u ∉ x :: a :: v :: R)
    (L : V → Finset C) (hv3 : 3 ≤ (L v).card)
    (ih : ∀ S₂ : Finset V, T.NT H S₂ (x :: v :: R) → (∀ y ∈ S₂, y = x ∨ y ∈ v :: R ∨ y ∈ U) →
      (∀ u ∈ U, u ∈ S₂ ∧ u ∉ x :: v :: R) → BadUnique H S₂ x v b L) :
    BadUnique H S x a b L := by
  classical
  have hRne : R ≠ [] := by intro h; subst h; simp at hR2
  have hnd := T.nodup hNT
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd'
  obtain ⟨⟨hxa_ne, hxv_ne, hxR⟩, ⟨hav_ne, haR⟩, hvR, hRnd⟩ := hnd'
  have hbR : b ∈ R := List.mem_of_mem_getLast? hb
  obtain ⟨S₁, S₂, h₁, h₂, hUn, hI, hX⟩ :=
    T.chord (x := x) (l₁ := [a]) (y := v) (l₂ := R) (by simpa using hNT) (by simp) hRne hxv
  have h₁' : T.NT H S₁ [x, a, v] := by simpa using h₁
  have h₂' : T.NT H S₂ (x :: v :: R) := T.rotate_back (by simpa using h₂)
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = x ∨ w = v := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hUn ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hUn ▸ Finset.subset_union_right
  have haS₁ : a ∈ S₁ := T.subset h₁' a (by simp)
  have haS₂ : a ∉ S₂ := fun h => (hmem a haS₁ h).elim (fun e => hxa_ne e.symm) hav_ne
  have hRS₂ : ∀ q ∈ R, q ∈ S₂ := fun q hq => T.subset h₂' q (by simp [hq])
  have hRS₁ : ∀ q ∈ R, q ∉ S₁ := fun q hq h =>
    (hmem q h (hRS₂ q hq)).elim (fun e => hxR (e ▸ hq)) (fun e => hvR (e ▸ hq))
  have hUS₂ : ∀ u ∈ U, u ∈ S₂ ∧ u ∉ S₁ := by
    intro u hu
    obtain ⟨huS, hun⟩ := hU u hu
    have hux : u ≠ x := fun e => hun (by simp [e])
    have huv : u ≠ v := fun e => hun (by simp [e])
    obtain ⟨q, hq, huq⟩ := hrest.centre_adj_tail u hu
    have : u ∈ S₁ ∪ S₂ := hUn ▸ huS
    have hu2 : u ∈ S₂ := by
      rcases Finset.mem_union.mp this with h1 | h2
      · rcases hX u h1 q (hRS₂ q hq) huq with h | h
        · exact h
        · exact absurd h (hRS₁ q hq)
      · exact h2
    exact ⟨hu2, fun h1 => (hmem u h1 hu2).elim hux huv⟩
  have hS₁sub : ∀ y ∈ S₁, y = x ∨ y = a ∨ y = v := by
    intro y hy
    rcases hSd y (hS₁ hy) with h | h | h
    · exact Or.inl h
    · simp only [List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd hy (hRS₁ y h)
    · exact absurd hy (hUS₂ y h).2
  have hSerase : S.erase a = S₂ := by
    ext y
    constructor
    · intro hy
      have hya := Finset.ne_of_mem_erase hy
      have : y ∈ S₁ ∪ S₂ := hUn ▸ Finset.mem_of_mem_erase hy
      rcases Finset.mem_union.mp this with h1 | h2
      · rcases hS₁sub y h1 with rfl | rfl | rfl
        · exact T.subset h₂' y (by simp)
        · exact absurd rfl hya
        · exact T.subset h₂' y (by simp)
      · exact h2
    · intro hy
      exact Finset.mem_erase.mpr ⟨fun e => haS₂ (e ▸ hy), hS₂ hy⟩
  have hanb : ∀ w ∈ S, H.Adj a w → w = x ∨ w = v := by
    intro w hw haw
    have hw1 : w ∈ S₁ := by
      have : w ∈ S₁ ∪ S₂ := hUn ▸ hw
      rcases Finset.mem_union.mp this with h1 | h2
      · exact h1
      · rcases hX a haS₁ w h2 haw with h | h
        · exact absurd h haS₂
        · exact h
    rcases hS₁sub w hw1 with h | h | h
    · exact Or.inl h
    · subst h; exact absurd haw (H.loopless.irrefl _)
    · exact Or.inr h
  -- `v` and `b` are not adjacent
  have hvb : ¬ H.Adj v b := by
    obtain ⟨R', hR'⟩ : ∃ R', R = R' ++ [b] := by
      rcases R.eq_nil_or_concat with h | ⟨R', c, h⟩
      · exact absurd h hRne
      · rw [h, List.concat_eq_append] at hb; simp at hb; subst hb
        exact ⟨R', by simpa using h⟩
    subst hR'
    have hR'ne : R' ≠ [] := by intro h; subst h; simp at hR2
    obtain ⟨r, R'', rfl⟩ := List.exists_cons_of_ne_nil hR'ne
    have hrot : T.NT H S (v :: ((r :: R'') ++ b :: [x, a])) := by
      have := T.rotate_append (A := [x, a]) (B := v :: (r :: R'' ++ [b])) (by simpa using hNT)
      simpa using this
    apply T.no_chord_of_crossing hrot (by simp) (by simp) (p := r) (q := x) (by simp) (by simp)
    rcases GW.front_second hrest with h | ⟨u, hu, hux, hur⟩
    · exact Or.inl h.symm
    · refine Or.inr ⟨u, (hU u hu).1, ?_, hur, hux⟩
      intro hmem'
      apply (hU u hu).2
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem' ⊢
      tauto
  -- the main argument
  intro g g' hok hok' hbad hbad'
  by_contra hne
  have hb_ne_v : b ≠ v := fun e => hvR (e ▸ hbR)
  have hb_ne_a : b ≠ a := fun e => haR (e ▸ hbR)
  obtain ⟨β, hβ, hβx, hβa, β', hβ', hβx', hβa', hββ⟩ :
      ∃ β ∈ L v, β ≠ g x ∧ β ≠ g a ∧ ∃ β' ∈ L v, β' ≠ g' x ∧ β' ≠ g' a ∧
        (g x = g' x → g b = g' b → β ≠ β') := by
    by_cases hc : g x = g' x ∧ g b = g' b
    · have hga : g a ≠ g' a := fun e => hne ⟨hc.1, e, hc.2⟩
      obtain ⟨β, hβ, hβx, hβa, β', hβ', hβx', hβa', hββ⟩ := two_choice (L v) hv3 (g x) _ _ hga
      exact ⟨β, hβ, hβx, hβa, β', hβ', hc.1 ▸ hβx', hβa', fun _ _ => hββ⟩
    · obtain ⟨β, hβ, hβx, hβa⟩ := exists_avoid2 (L v) hv3 (g x) (g a)
      obtain ⟨β', hβ', hβx', hβa'⟩ := exists_avoid2 (L v) hv3 (g' x) (g' a)
      exact ⟨β, hβ, hβx, hβa, β', hβ', hβx', hβa', fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  -- transfer to the rest
  have transfer : ∀ (g : V → C) (β : C), β ∈ L v → β ≠ g x → β ≠ g a → PathOK H x a b g →
      ¬ Extends H S [b, x, a] L g →
      PathOK H x v b (Function.update g v β) ∧
        ¬ Extends H S₂ [b, x, v] L (Function.update g v β) := by
    intro g β hβ hβx hβa hok hbad
    have hxv' : x ≠ v := hxv_ne
    refine ⟨⟨?_, ?_, fun h => absurd h hvb⟩, ?_⟩
    · rw [Function.update_self, Function.update_of_ne hxv']; exact hβx.symm
    · rw [Function.update_of_ne hxv', Function.update_of_ne hb_ne_v]; exact hok.2.1
    · rintro ⟨f₂, hf₂c, hf₂L, hf₂p⟩
      apply hbad
      have hf₂x : f₂ x = g x := by
        rw [hf₂c x (by simp), Function.update_of_ne hxv']
      have hf₂v : f₂ v = β := by rw [hf₂c v (by simp), Function.update_self]
      have hf₂b : f₂ b = g b := by
        rw [hf₂c b (by simp), Function.update_of_ne hb_ne_v]
      refine ⟨Function.update f₂ a (g a), ?_, ?_, ?_⟩
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · rw [Function.update_of_ne hb_ne_a]; exact hf₂b
        · rw [Function.update_of_ne hxa_ne]; exact hf₂x
        · simp
      · intro y hy hyc
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc
        rw [Function.update_of_ne hyc.2.2]
        have hy₂ : y ∈ S₂ := hSerase ▸ Finset.mem_erase.mpr ⟨hyc.2.2, hy⟩
        by_cases hyv : y = v
        · subst hyv; rw [hf₂v]; exact hβ
        · exact hf₂L y hy₂ (by simp [hyc.1, hyc.2.1, hyv])
      · apply isProperOn_update (hSerase ▸ hf₂p)
        intro w hw haw
        rcases hanb w hw haw with rfl | rfl
        · rw [hf₂x]; exact hok.1
        · rw [hf₂v]; exact hβa
  obtain ⟨hokh, hbadh⟩ := transfer g β hβ hβx hβa hok hbad
  obtain ⟨hokh', hbadh'⟩ := transfer g' β' hβ' hβx' hβa' hok' hbad'
  have hSd₂ : ∀ y ∈ S₂, y = x ∨ y ∈ v :: R ∨ y ∈ U := by
    intro y hy
    rcases hSd y (hS₂ hy) with h | h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact absurd hy haS₂
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hU₂ : ∀ u ∈ U, u ∈ S₂ ∧ u ∉ x :: v :: R := fun u hu =>
    ⟨(hUS₂ u hu).1, fun h => (hU u hu).2 (by simp only [List.mem_cons] at h ⊢; tauto)⟩
  obtain ⟨h1, h2, h3⟩ := ih S₂ h₂' hSd₂ hU₂ _ _ hokh hokh' hbadh hbadh'
  have hxv' : x ≠ v := hxv_ne
  rw [Function.update_of_ne hxv', Function.update_of_ne hxv'] at h1
  rw [Function.update_self, Function.update_self] at h2
  rw [Function.update_of_ne hb_ne_v, Function.update_of_ne hb_ne_v] at h3
  exact hββ h1 h3 h2

end NTCalc

/-- A non-broken generalized wheel without `K4` blocks has at least three path vertices. -/
theorem GW.three_le {H : SimpleGraph V} {x : V} {P : List V} {U : Finset V} (h : GW H 3 x P U)
    (hU : U.Nonempty) : 3 ≤ P.length := by
  cases h with
  | one hB =>
    cases hB with
    | tri => simp at hU
    | wheel _ hm => exact hm
  | cons hB hrest =>
    have h1 := hB.two_le
    have h2 := hrest.two_le
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2 ⊢
    omega

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 1000000 in
/-- **Lemma 1, splitting along `x b`.** Both sides are non-broken: any extension of one side
yields a non-extendable precolouring of the other. -/
theorem l1_split (H : SimpleGraph V) {S : Finset V} {x a b c : V} {P₁ Q : List V}
    {U₁ U₂ : Finset V} (hNT : T.NT H S (x :: (P₁ ++ b :: Q)))
    (ha : P₁.head? = some a) (hc : Q.getLast? = some c) (hxb : H.Adj x b)
    (hab : ¬ H.Adj a b) (hbc : ¬ H.Adj b c)
    (hSd : ∀ y ∈ S, y = x ∨ y ∈ P₁ ++ b :: Q ∨ y ∈ U₁ ∨ y ∈ U₂)
    (hU₁ : ∀ u ∈ U₁, u ∈ S ∧ u ∉ x :: (P₁ ++ b :: Q) ∧ ∃ p ∈ P₁, H.Adj u p)
    (hU₂ : ∀ u ∈ U₂, u ∈ S ∧ u ∉ x :: (P₁ ++ b :: Q) ∧ ∃ q ∈ Q, H.Adj u q)
    (L : V → Finset C) (h5 : ∀ u ∈ U₁ ∪ U₂, 5 ≤ (L u).card)
    (h3 : ∀ y ∈ P₁ ++ b :: Q, y ≠ a → y ≠ c → 3 ≤ (L y).card)
    (ih₁ : ∀ S₁ : Finset V, T.NT H S₁ (x :: (P₁ ++ [b])) →
      (∀ y ∈ S₁, y = x ∨ y ∈ P₁ ++ [b] ∨ y ∈ U₁) → (∀ u ∈ U₁, u ∈ S₁ ∧ u ∉ x :: (P₁ ++ [b])) →
      BadUnique H S₁ x a b L)
    (ih₂ : ∀ S₂ : Finset V, T.NT H S₂ (x :: b :: Q) →
      (∀ y ∈ S₂, y = x ∨ y ∈ b :: Q ∨ y ∈ U₂) → (∀ u ∈ U₂, u ∈ S₂ ∧ u ∉ x :: b :: Q) →
      BadUnique H S₂ x b c L) :
    BadUnique H S x a c L := by
  classical
  have hP₁ne : P₁ ≠ [] := by intro h; simp [h] at ha
  have hQne : Q ≠ [] := by intro h; simp [h] at hc
  obtain ⟨a', P₁', rfl⟩ := List.exists_cons_of_ne_nil hP₁ne
  have ha' : a' = a := by simpa using ha
  subst a'
  obtain ⟨Q', hQ⟩ : ∃ Q', Q = Q' ++ [c] := by
    rcases Q.eq_nil_or_concat with h | ⟨Q', c', h⟩
    · exact absurd h hQne
    · rw [h, List.concat_eq_append, List.getLast?_append] at hc
      simp at hc; subst hc; exact ⟨Q', by simpa using h⟩
  subst hQ
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.cons_append, List.mem_cons, List.mem_append,
    List.nodup_append, not_or] at hnd
  obtain ⟨S₁, S₂, h₁, h₂, hUn, hI, hX⟩ := T.chord (x := x) (l₁ := a :: P₁') (y := b)
    (l₂ := Q' ++ [c]) (by simpa using hNT) (by simp) (by simp) hxb
  have h₂' : T.NT H S₂ (x :: b :: (Q' ++ [c])) := T.rotate_back (by simpa using h₂)
  have hmem : ∀ w, w ∈ S₁ → w ∈ S₂ → w = x ∨ w = b := by
    intro w h1 h2
    have : w ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : S₁ ⊆ S := hUn ▸ Finset.subset_union_left
  have hS₂ : S₂ ⊆ S := hUn ▸ Finset.subset_union_right
  have hside : ∀ y ∈ S, y ∉ S₁ → y ∈ S₂ := fun y hy h1 =>
    (Finset.mem_union.mp (hUn ▸ hy)).resolve_left h1
  have hxS₁ : x ∈ S₁ := T.subset h₁ x (by simp)
  have hbS₁ : b ∈ S₁ := T.subset h₁ b (by simp)
  have hxS₂ : x ∈ S₂ := T.subset h₂' x (by simp)
  have hbS₂ : b ∈ S₂ := T.subset h₂' b (by simp)
  -- the two sides of the cycle
  have hP₁side : ∀ p ∈ a :: P₁', p ∈ S₁ ∧ p ∉ S₂ := by
    intro p hp
    have hp1 : p ∈ S₁ := T.subset h₁ p (by simp only [List.mem_cons] at hp ⊢; simp; tauto)
    refine ⟨hp1, fun h2 => ?_⟩
    rcases hmem p hp1 h2 with rfl | rfl
    · simp only [List.mem_cons] at hp; tauto
    · simp only [List.mem_cons] at hp; tauto
  have hQside : ∀ q ∈ Q' ++ [c], q ∈ S₂ ∧ q ∉ S₁ := by
    intro q hq
    have hq2 : q ∈ S₂ := T.subset h₂' q (by simp only [List.mem_append, List.mem_cons] at hq ⊢; tauto)
    refine ⟨hq2, fun h1 => ?_⟩
    rcases hmem q h1 hq2 with rfl | rfl
    · simp only [List.mem_append, List.mem_cons] at hq; tauto
    · simp only [List.mem_append, List.mem_cons] at hq; tauto
  have hU₁side : ∀ u ∈ U₁, u ∈ S₁ ∧ u ∉ S₂ := by
    intro u hu
    obtain ⟨huS, hun, p, hp, hup⟩ := hU₁ u hu
    obtain ⟨hp1, hp2⟩ := hP₁side p hp
    have hu1 : u ∈ S₁ := by
      by_contra h
      rcases hX p hp1 u (hside u huS h) hup.symm with h' | h'
      · exact hp2 h'
      · exact h h'
    refine ⟨hu1, fun h2 => ?_⟩
    rcases hmem u hu1 h2 with rfl | rfl <;> exact hun (by simp)
  have hU₂side : ∀ u ∈ U₂, u ∈ S₂ ∧ u ∉ S₁ := by
    intro u hu
    obtain ⟨huS, hun, q, hq, huq⟩ := hU₂ u hu
    obtain ⟨hq2, hq1⟩ := hQside q hq
    have hu2 : u ∈ S₂ := by
      by_contra h
      have hu1 : u ∈ S₁ := (Finset.mem_union.mp (hUn ▸ huS)).resolve_right h
      rcases hX u hu1 q hq2 huq with h' | h'
      · exact h h'
      · exact hq1 h'
    refine ⟨hu2, fun h1 => ?_⟩
    rcases hmem u h1 hu2 with rfl | rfl <;> exact hun (by simp)
  have hSd₁ : ∀ y ∈ S₁, y = x ∨ y ∈ a :: P₁' ++ [b] ∨ y ∈ U₁ := by
    intro y hy
    rcases hSd y (hS₁ hy) with h | h | h | h
    · exact Or.inl h
    · right; left
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp [h]))
      · exact absurd hy (hQside y (by simpa using h)).2
    · exact Or.inr (Or.inr h)
    · exact absurd hy (hU₂side y h).2
  have hSd₂ : ∀ y ∈ S₂, y = x ∨ y ∈ b :: (Q' ++ [c]) ∨ y ∈ U₂ := by
    intro y hy
    rcases hSd y (hS₂ hy) with h | h | h | h
    · exact Or.inl h
    · right; left
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h | h
      · exact absurd hy (hP₁side y (by simp [h])).2
      · exact absurd hy (hP₁side y (by simp [h])).2
      · exact Or.inl h
      · exact Or.inr h
    · exact absurd hy (hU₁side y h).2
    · exact Or.inr (Or.inr h)
  have hU₁' : ∀ u ∈ U₁, u ∈ S₁ ∧ u ∉ x :: (a :: P₁' ++ [b]) := fun u hu =>
    ⟨(hU₁side u hu).1, fun h => (hU₁ u hu).2.1 (by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)⟩
  have hU₂' : ∀ u ∈ U₂, u ∈ S₂ ∧ u ∉ x :: b :: (Q' ++ [c]) := fun u hu =>
    ⟨(hU₂side u hu).1, fun h => (hU₂ u hu).2.1 (by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h ⊢; tauto)⟩
  have BU₁ := ih₁ S₁ h₁ hSd₁ hU₁'
  have BU₂ := ih₂ S₂ h₂' hSd₂ hU₂'
  -- extensions of each side by Theorem 1
  have haS₁ := (hP₁side a (by simp)).1
  have haS₂ := (hP₁side a (by simp)).2
  have hcS₂ := (hQside c (by simp)).1
  have hcS₁ := (hQside c (by simp)).2
  have hxa' : x ≠ a := fun e => haS₂ (e ▸ hxS₂)
  have hxc : x ≠ c := fun e => hcS₁ (e ▸ hxS₁)
  have hba : b ≠ a := fun e => haS₂ (e ▸ hbS₂)
  have hbc' : b ≠ c := fun e => hcS₁ (e ▸ hbS₁)
  have hnd₁ := T.nodup h₁
  simp only [List.nodup_cons, List.cons_append, List.mem_cons, List.mem_append, not_or] at hnd₁
  have h₂'' : T.NT H S₂ (c :: x :: b :: Q') := T.rotate_back (by simpa using h₂')
  have hnd₂ := T.nodup h₂''
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd₂
  have ext₁ : ∀ g : V → C, g x ≠ g a → ∃ f₁ : V → C, f₁ x = g x ∧ f₁ a = g a ∧
      (∀ y ∈ S₁, y ≠ x → y ≠ a → f₁ y ∈ L y) ∧ IsProperOn H S₁ f₁ := by
    intro g hg
    have h1' : T.NT H S₁ (x :: a :: (P₁' ++ [b])) := by simpa using h₁
    refine T.thm1 H _ S₁ rfl x a (P₁' ++ [b]) h1' L g hg ?_ ?_
    · intro y hy
      have hyS₁ : y ∈ S₁ := T.subset h1' y (by simp [hy])
      apply h3 y
      · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at hy ⊢
        tauto
      · intro e; subst e
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with h | h
        · exact hnd₁.2.1.1 h
        · exact hba h.symm
      · intro e; subst e; exact hcS₁ hyS₁
    · intro y hy hyc
      rcases hSd₁ y hy with h | h | h
      · exact absurd (by simp [h]) hyc
      · exact absurd (List.mem_cons_of_mem x (by simpa using h)) hyc
      · exact h5 y (Finset.mem_union_left _ h)
  have ext₂ : ∀ g : V → C, g c ≠ g x → ∃ f₂ : V → C, f₂ c = g c ∧ f₂ x = g x ∧
      (∀ y ∈ S₂, y ≠ c → y ≠ x → f₂ y ∈ L y) ∧ IsProperOn H S₂ f₂ := by
    intro g hg
    refine T.thm1 H _ S₂ rfl c x (b :: Q') h₂'' L g hg ?_ ?_
    · intro y hy
      have hyS₂ : y ∈ S₂ := T.subset h₂'' y (by simp [hy])
      apply h3 y
      · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at hy ⊢
        tauto
      · intro e; subst e; exact haS₂ hyS₂
      · intro e; subst e
        rcases List.mem_cons.mp hy with h | h
        · exact hbc' h.symm
        · exact hnd₂.1.2.2 h
    · intro y hy hyc
      rcases hSd₂ y hy with h | h | h
      · exact absurd (by simp [h]) hyc
      · exfalso; apply hyc
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at h ⊢
        tauto
      · exact h5 y (Finset.mem_union_right _ h)
  have glue : ∀ (g f₁ f₂ : V → C), f₁ x = g x → f₁ a = g a →
      (∀ y ∈ S₁, y ≠ x → y ≠ a → f₁ y ∈ L y) → IsProperOn H S₁ f₁ →
      f₂ c = g c → f₂ x = g x → (∀ y ∈ S₂, y ≠ c → y ≠ x → f₂ y ∈ L y) →
      IsProperOn H S₂ f₂ → f₁ b = f₂ b → Extends H S [c, x, a] L g := by
    intro g f₁ f₂ h1x h1a h1L h1p h2c h2x h2L h2p hb
    refine ⟨fun y => if y ∈ S₁ then f₁ y else f₂ y, ?_, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · simp [hcS₁, h2c]
      · simp [hxS₁, h1x]
      · simp [haS₁, h1a]
    · intro y hy hyc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc
      by_cases h1 : y ∈ S₁
      · simp only [h1, if_true]; exact h1L y h1 hyc.2.1 hyc.2.2
      · simp only [h1, if_false]; exact h2L y (hside y hy h1) hyc.1 hyc.2.1
    · refine isProperOn_glue hUn hX h1p h2p ?_
      intro y h1 h2
      rcases hmem y h1 h2 with rfl | rfl
      · rw [h2x, h1x]
      · exact hb.symm
  intro g g' hok hok' hbad hbad'
  have key : ∀ g : V → C, PathOK H x a c g → ¬ Extends H S [c, x, a] L g →
      ∃ α β : C, PathOK H x b c (Function.update g b α) ∧
        ¬ Extends H S₂ [c, x, b] L (Function.update g b α) ∧
        PathOK H x a b (Function.update g b β) ∧
        ¬ Extends H S₁ [b, x, a] L (Function.update g b β) := by
    intro g hok hbad
    obtain ⟨f₁, h1x, h1a, h1L, h1p⟩ := ext₁ g hok.1
    obtain ⟨f₂, h2c, h2x, h2L, h2p⟩ := ext₂ g (fun e => hok.2.1 e.symm)
    have hxb' : x ≠ b := fun e => H.loopless.irrefl x (e ▸ hxb)
    refine ⟨f₁ b, f₂ b, ⟨?_, ?_, fun h => absurd h hbc⟩, ?_, ⟨?_, ?_, fun h => absurd h hab⟩, ?_⟩
    · rw [Function.update_self, Function.update_of_ne hxb', ← h1x]
      exact h1p x hxS₁ b hbS₁ hxb
    · rw [Function.update_of_ne hxb', Function.update_of_ne hbc'.symm]; exact hok.2.1
    · rintro ⟨f₂', hc', hL', hp'⟩
      apply hbad
      refine glue g f₁ f₂' h1x h1a h1L h1p ?_ ?_ ?_ hp' ?_
      · rw [hc' c (by simp), Function.update_of_ne hbc'.symm]
      · rw [hc' x (by simp), Function.update_of_ne hxb']
      · intro y hy hyc hyx
        by_cases hyb : y = b
        · subst hyb; rw [hc' y (by simp), Function.update_self]
          exact h1L y hbS₁ hxb'.symm hba
        · exact hL' y hy (by simp [hyc, hyx, hyb])
      · rw [hc' b (by simp), Function.update_self]
    · rw [Function.update_of_ne hxb', Function.update_of_ne hba.symm]; exact hok.1
    · rw [Function.update_self, Function.update_of_ne hxb', ← h2x]
      exact h2p x hxS₂ b hbS₂ hxb
    · rintro ⟨f₁', hc', hL', hp'⟩
      apply hbad
      refine glue g f₁' f₂ ?_ ?_ ?_ hp' h2c h2x h2L h2p ?_
      · rw [hc' x (by simp), Function.update_of_ne hxb']
      · rw [hc' a (by simp), Function.update_of_ne hba.symm]
      · intro y hy hyx hya
        by_cases hyb : y = b
        · subst hyb; rw [hc' y (by simp), Function.update_self]
          exact h2L y hbS₂ hbc' hxb'.symm
        · exact hL' y hy (by simp [hyx, hya, hyb])
      · rw [hc' b (by simp), Function.update_self]
  obtain ⟨α, β, hok₂, hbad₂, hok₁, hbad₁⟩ := key g hok hbad
  obtain ⟨α', β', hok₂', hbad₂', hok₁', hbad₁'⟩ := key g' hok' hbad'
  have hxb' : x ≠ b := fun e => H.loopless.irrefl x (e ▸ hxb)
  obtain ⟨e1, -, e3⟩ := BU₂ _ _ hok₂ hok₂' hbad₂ hbad₂'
  obtain ⟨-, e5, -⟩ := BU₁ _ _ hok₁ hok₁' hbad₁ hbad₁'
  rw [Function.update_of_ne hxb', Function.update_of_ne hxb'] at e1
  rw [Function.update_of_ne hbc'.symm, Function.update_of_ne hbc'.symm] at e3
  rw [Function.update_of_ne hba.symm, Function.update_of_ne hba.symm] at e5
  exact ⟨e1, e5, e3⟩

end NTCalc

theorem badUnique_symm {H : SimpleGraph V} {S : Finset V} {x a c : V} {L : V → Finset C}
    (h : BadUnique H S x c a L) : BadUnique H S x a c L := by
  intro g g' hok hok' hbad hbad'
  have hperm : ∀ y, y ∈ [a, x, c] ↔ y ∈ [c, x, a] := by intro y; simp; tauto
  have hsw : ∀ g : V → C, PathOK H x a c g → PathOK H x c a g := fun g hg =>
    ⟨hg.2.1, hg.1, fun hca => (hg.2.2 hca.symm).symm⟩
  obtain ⟨h1, h2, h3⟩ := h g g' (hsw g hok) (hsw g' hok')
    (fun he => hbad (NTCalc.extends_of_mem_iff hperm he))
    (fun he => hbad' (NTCalc.extends_of_mem_iff hperm he))
  exact ⟨h1, h3, h2⟩

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 2000000 in
/-- **Lemma 1** (without `K4` blocks). -/
theorem lemma1 (H : SimpleGraph V) (x : V) :
    ∀ (n : ℕ) (P : List V) (U : Finset V), P.length = n → GW H 3 x P U → U.Nonempty →
    ∀ (S : Finset V) (a c : V), P.head? = some a → P.getLast? = some c → T.NT H S (x :: P) →
    (∀ y ∈ S, y = x ∨ y ∈ P ∨ y ∈ U) → (∀ u ∈ U, u ∈ S ∧ u ∉ x :: P) →
    ∀ L : V → Finset C, (∀ u ∈ U, 5 ≤ (L u).card) →
    (∀ y ∈ P, y ≠ a → y ≠ c → 3 ≤ (L y).card) → BadUnique H S x a c L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P U hn hGW hUne S a c ha hc hNT hSd hU L h5 h3
  have hnd := T.nodup hNT
  cases hGW with
  | one hB =>
    cases hB with
    | tri => simp at hUne
    | @wheel P u hP2 hP3 hpath hu hux hh hl =>
      obtain ⟨v₃, M, rfl⟩ : ∃ v₃ M, P = a :: v₃ :: (M ++ [c]) := by
        rcases P with _ | ⟨p0, _ | ⟨p1, P2⟩⟩
        · simp at hP3
        · simp at hP3
        · have hP2ne : P2 ≠ [] := by intro h; subst h; simp at hP3
          rcases P2.eq_nil_or_concat with h | ⟨M, c', h⟩
          · exact absurd h hP2ne
          · subst h
            simp only [List.head?_cons, Option.some.injEq] at ha
            subst ha
            rw [List.concat_eq_append, List.getLast?_cons_cons, List.getLast?_cons,
              List.getLast?_append] at hc
            simp at hc
            subst hc
            exact ⟨p1, M, by simp⟩
      have huS := (hU u (Finset.mem_singleton_self u)).1
      have hun := (hU u (Finset.mem_singleton_self u)).2
      have hhub : ∀ z ∈ x :: a :: v₃ :: (M ++ [c]), H.Adj u z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hux
        · exact hu z hz
      have hS : ∀ y ∈ S, y ∈ x :: a :: v₃ :: (M ++ [c]) ∨ y = u := by
        intro y hy
        rcases hSd y hy with h | h | h
        · left; simp [h]
        · left; exact List.mem_cons_of_mem _ h
        · right; simpa using h
      have hndP : (a :: v₃ :: (M ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
      have haP : a ∉ v₃ :: (M ++ [c]) := (List.nodup_cons.mp hndP).1
      have hcvM : c ∉ v₃ :: M := by
        have h1 : ((v₃ :: M) ++ [c]).Nodup := by simpa using (List.nodup_cons.mp hndP).2
        intro hc'
        exact (List.nodup_append.mp h1).2.2 c hc' c (by simp) rfl
      have h3w : ∀ y ∈ v₃ :: M, 3 ≤ (L y).card := by
        intro y hy
        apply h3 y (by simp only [List.mem_cons, List.mem_append] at hy ⊢; tauto)
        · intro e; subst e; apply haP
          simp only [List.mem_cons, List.mem_append] at hy ⊢; tauto
        · intro e; subst e; exact hcvM hy
      intro g g' hok hok' hbad hbad'
      exact T.wheel_unique H hNT hS huS hun hhub L (h5 u (Finset.mem_singleton_self u)) h3w
        hok.1 hok.2.1 hok'.1 hok'.2.1 hbad hbad'
  | @cons P₁ Q b U₁ U₂ hB hrest =>
    have hB2 := hB.two_le
    have hP₁ne : P₁ ≠ [] := by intro h; subst h; simp at hB2
    have hQne : Q ≠ [] := by have := hrest.two_le; intro h; subst h; simp at this
    have hxb : H.Adj x b := hB.adj_last b (by simp)
    obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' ++ [c] := by
      rcases Q.eq_nil_or_concat with h | ⟨Q', c', h⟩
      · exact absurd h hQne
      · subst h
        rw [List.concat_eq_append, List.getLast?_append, List.getLast?_cons,
          List.getLast?_append] at hc
        simp at hc; subst hc; exact ⟨Q', by simp⟩
    obtain ⟨P₁', rfl⟩ : ∃ P₁', P₁ = a :: P₁' := by
      obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP₁ne
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at ha
      subst ha; exact ⟨P', rfl⟩
    have hndc := T.nodup hNT
    have h3rest : ∀ y ∈ b :: (Q' ++ [c]), y ≠ b → y ≠ c → 3 ≤ (L y).card := by
      intro y hy hyb hyc
      apply h3 y (by simp only [List.cons_append, List.mem_cons, List.mem_append] at hy ⊢; tauto)
        _ hyc
      intro e; subst e
      simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons] at hndc
      rcases List.mem_cons.mp hy with h | h
      · exact hyb h
      · exact hndc.2.1 (Or.inr (Or.inr (by simpa using h)))
    generalize hPb : (a :: P₁') ++ [b] = PB at hB
    cases hB with
    | @tri a' b' hxa hxb' hab' =>
      have h1 : (a :: P₁') ++ [b] = [a'] ++ [b'] := hPb
      obtain ⟨h1a, h1b⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, and_true] at h1a h1b
      obtain ⟨rfl, rfl⟩ := h1a
      subst h1b
      have hU₂ne : U₂.Nonempty := by simpa using hUne
      have hR3 := hrest.three_le hU₂ne
      simp only [List.length_cons, List.length_append, List.length_nil] at hR3
      have hNT' : T.NT H S (x :: a :: b :: (Q' ++ [c])) := by simpa using hNT
      refine T.l1_front H hNT' (by simp) (by simp; omega) hxb hrest ?_ ?_ L ?_ ?_
      · intro y hy
        rcases hSd y hy with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by simpa using h))
        · exact Or.inr (Or.inr (by simpa using h))
      · intro u hu
        obtain ⟨huS, hun⟩ := hU u (by simp [hu])
        exact ⟨huS, by simpa using hun⟩
      · apply h3 b (by simp)
        · intro e; subst e
          simp at hndc
        · intro e; subst e
          simp at hndc
      · intro S₂ h₂ hd hu
        exact ih _ (by rw [← hn]; simp only [List.cons_append, List.length_cons,
          List.length_append, List.length_nil]; omega) (b :: (Q' ++ [c]))
          U₂ rfl hrest hU₂ne S₂ b c rfl
          (by rw [List.getLast?_cons, List.getLast?_append]; simp) h₂ hd hu L
          (fun u hu => h5 u (by simp [hu])) h3rest
    | @wheel PB' u hPB2 hPB3 hpath hu hux hh hl =>
      subst hPb
      have hP₁'ne : P₁' ≠ [] := by
        intro h; subst h; simp at hPB3
      have hGW₁ : GW H 3 x ((a :: P₁') ++ [b]) {u} :=
        GW.one (Block.wheel hPB2 hPB3 hpath hu hux hh hl)
      have huS := (hU u (by simp)).1
      have hun := (hU u (by simp)).2
      have hSd' : ∀ y ∈ S, y = x ∨ y ∈ (a :: P₁') ++ b :: (Q' ++ [c]) ∨ y ∈ ({u} : Finset V) ∨
          y ∈ U₂ := by
        intro y hy
        rcases hSd y hy with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rcases Finset.mem_union.mp h with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      by_cases hU₂ne : U₂.Nonempty
      · -- both sides non-broken
        have hR3 := hrest.three_le hU₂ne
        have hQ'ne : Q' ≠ [] := by
          intro h; subst h; simp at hR3
        have hab : ¬ H.Adj a b := by
          obtain ⟨p, P'', rfl⟩ := List.exists_cons_of_ne_nil hP₁'ne
          have hrot : T.NT H S (a :: ((p :: P'') ++ b :: (Q' ++ [c] ++ [x]))) := by
            simpa using T.rotate hNT
          refine T.no_chord_of_crossing hrot (by simp) (by simp) (p := p) (q := x) (by simp)
            (by simp) (Or.inr ⟨u, huS, ?_, hu p (by simp), hux⟩)
          intro h; apply hun
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at h ⊢
          tauto
        have hbc : ¬ H.Adj b c := by
          obtain ⟨q, Q'', rfl⟩ := List.exists_cons_of_ne_nil hQ'ne
          have hrot : T.NT H S (b :: ((q :: Q'') ++ c :: (x :: a :: P₁'))) := by
            have := T.rotate_append (A := x :: a :: P₁') (B := b :: (q :: Q'' ++ [c]))
              (by simpa using hNT)
            simpa using this
          refine T.no_chord_of_crossing hrot (by simp) (by simp) (p := q) (q := x) (by simp)
            (by simp) ?_
          rcases GW.front_second (by simpa using hrest) with h | ⟨u', hu', hu'x, hu'q⟩
          · exact Or.inl h.symm
          · refine Or.inr ⟨u', (hU u' (by simp [hu'])).1, ?_, hu'q, hu'x⟩
            intro h; apply (hU u' (by simp [hu'])).2
            simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton]
              at h ⊢
            tauto
        refine T.l1_split H hNT (by simp)
          (by rw [List.getLast?_append]; simp) hxb hab hbc hSd' ?_ ?_ L ?_ ?_ ?_ ?_
        · intro u' hu'
          simp only [Finset.mem_singleton] at hu'; subst hu'
          exact ⟨huS, hun, a, by simp, hu a (by simp)⟩
        · intro u' hu'
          obtain ⟨huS', hun'⟩ := hU u' (by simp [hu'])
          obtain ⟨q, hq, huq⟩ := hrest.centre_adj_tail u' hu'
          exact ⟨huS', hun', q, hq, huq⟩
        · intro u' hu'; exact h5 u' hu'
        · intro y hy hya hyc; exact h3 y hy hya hyc
        · intro S₁ h₁ hd₁ hu₁
          refine ih _ (by rw [← hn]; simp only [List.cons_append, List.length_cons,
            List.length_append, List.length_nil]; omega) _ {u} rfl hGW₁ (by simp) S₁ a b
            (by simp) (by rw [List.getLast?_append]; simp) h₁ hd₁ hu₁ L
            (fun u' hu' => h5 u' (by simp only [Finset.mem_singleton] at hu'; simp [hu'])) ?_
          intro y hy hya hyb
          apply h3 y (by simp only [List.cons_append, List.mem_cons, List.mem_append,
            List.mem_singleton] at hy ⊢; tauto) hya
          intro e
          have hndP : ((a :: P₁') ++ b :: (Q' ++ [c])).Nodup :=
            (List.nodup_cons.mp (T.nodup hNT)).2
          have hyP : y ∈ a :: P₁' :=
            (List.mem_append.mp hy).resolve_right (by simpa using hyb)
          exact (List.nodup_append.mp hndP).2.2 y hyP y (by rw [e]; simp) rfl
        · intro S₂ h₂ hd₂ hu₂
          exact ih _ (by rw [← hn]; simp only [List.cons_append, List.length_cons,
            List.length_append, List.length_nil]; omega) (b :: (Q' ++ [c]))
            U₂ rfl hrest hU₂ne S₂ b c rfl
            (by rw [List.getLast?_cons, List.getLast?_append]; simp) h₂ hd₂ hu₂ L
            (fun u hu => h5 u (by simp [hu])) h3rest
      · -- the rest is broken: argue from the other end
        have hU₂e : U₂ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU₂ne
        subst hU₂e
        have hrr : GW H 3 x (c :: (Q'.reverse ++ [b])) ∅ := by simpa using hrest.reverse
        obtain ⟨v, R₀, hvR⟩ : ∃ v R₀, Q'.reverse ++ [b] = v :: R₀ :=
          List.exists_cons_of_ne_nil (by simp)
        rw [hvR] at hrr
        rcases hrr.front_tri with ⟨-, hxv, -, hR⟩ | ⟨w, hw⟩
        swap
        · simp at hw
        have hGWr : GW H 3 x (v :: (R₀ ++ (P₁'.reverse ++ [a]))) {u} := by
          rcases hR with ⟨hR0, -⟩ | hR
          · subst hR0
            have h1 : Q'.reverse = [] ∧ b = v := by
              have := congrArg List.length hvR
              simp only [List.length_append, List.length_reverse, List.length_cons,
                List.length_nil] at this
              have hQ0 : Q' = [] := List.eq_nil_of_length_eq_zero (by omega)
              subst hQ0; simp at hvR; exact ⟨rfl, hvR⟩
            obtain ⟨-, rfl⟩ := h1
            simpa using hGW₁.reverse
          · have hR₀ne : R₀ ≠ [] := by
              have := hR.two_le; intro h; subst h; simp at this
            obtain ⟨R₀', hR₀'⟩ : ∃ R₀', R₀ = R₀' ++ [b] := by
              rcases R₀.eq_nil_or_concat with h | ⟨R₀', z, h⟩
              · exact absurd h hR₀ne
              · rw [h, List.concat_eq_append] at hvR
                have h' := congrArg List.reverse hvR
                simp only [List.reverse_append, List.reverse_reverse, List.reverse_cons,
                  List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append,
                  List.append_assoc] at h'
                have hzb : b = z := (List.cons.inj h').1
                subst hzb
                exact ⟨R₀', by simpa using h⟩
            subst hR₀'
            have h2 : GW H 3 x (b :: (P₁'.reverse ++ [a])) {u} := by simpa using hGW₁.reverse
            have h3' := GW.append (P := v :: R₀') (by simpa using hR) h2
            simpa using h3'
        have hPr : c :: v :: (R₀ ++ (P₁'.reverse ++ [a])) =
            ((a :: P₁') ++ b :: (Q' ++ [c])).reverse := by
          have : ((a :: P₁') ++ b :: (Q' ++ [c])).reverse =
              c :: ((Q'.reverse ++ [b]) ++ (P₁'.reverse ++ [a])) := by simp
          rw [this, hvR]; simp
        have hmemr : ∀ y, y ∈ c :: v :: (R₀ ++ (P₁'.reverse ++ [a])) ↔
            y ∈ (a :: P₁') ++ b :: (Q' ++ [c]) := by
          intro y; rw [hPr, List.mem_reverse]
        have hNTr : T.NT H S (x :: c :: v :: (R₀ ++ (P₁'.reverse ++ [a]))) := by
          have h1 := T.reverse hNT
          rw [List.reverse_cons, ← hPr] at h1
          exact T.rotate_back h1
        have hndr := T.nodup hNTr
        have hndr' := (List.nodup_cons.mp hndr).2
        have hcv : c ∉ v :: (R₀ ++ (P₁'.reverse ++ [a])) := (List.nodup_cons.mp hndr').1
        have hav : a ∉ c :: v :: (R₀ ++ P₁'.reverse) := by
          have h1 : (c :: v :: (R₀ ++ P₁'.reverse) ++ [a]).Nodup := by simpa using hndr'
          intro ha'
          exact (List.nodup_append.mp h1).2.2 a ha' a (by simp) rfl
        refine badUnique_symm (T.l1_front H hNTr (by simp) ?_ hxv hGWr ?_ ?_ L ?_ ?_)
        · obtain ⟨p, P'', rfl⟩ := List.exists_cons_of_ne_nil hP₁'ne
          simp only [List.length_append, List.length_reverse, List.length_cons,
            List.length_nil]; omega
        · intro y hy
          rcases hSd' y hy with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ((hmemr y).2 h))
          · exact Or.inr (Or.inr h)
          · simp at h
        · intro u' hu'
          simp only [Finset.mem_singleton] at hu'; subst hu'
          refine ⟨huS, fun h => hun ?_⟩
          rcases List.mem_cons.mp h with h | h
          · exact List.mem_cons.mpr (Or.inl h)
          · exact List.mem_cons_of_mem _ ((hmemr _).1 h)
        · apply h3 v ((hmemr v).1 (by simp))
          · intro e; subst e; exact hav (by simp)
          · intro e; subst e; exact hcv (by simp)
        · intro S₂ h₂ hd₂ hu₂
          refine ih _ ?_ _ {u} rfl hGWr (by simp) S₂ v a rfl
            (by rw [List.getLast?_cons, List.getLast?_append, List.getLast?_append]; simp)
            h₂ hd₂ hu₂ L
            (fun u' hu' => h5 u' (by simp only [Finset.mem_singleton] at hu'; simp [hu'])) ?_
          · rw [← hn]
            have := congrArg List.length hPr
            simp only [List.length_cons, List.length_append, List.length_reverse] at this ⊢
            omega
          · intro y hy hyv hya
            apply h3 y ((hmemr y).1 (List.mem_cons_of_mem _ hy)) hya
            intro e; subst e; exact hcv hy

end NTCalc

end ThomassenManyColourings
