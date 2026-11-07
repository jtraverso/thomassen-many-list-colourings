/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Wheel

/-!
# Theorem 4, Claim 10: outer vertices have exactly three colours

If a non-precoloured outer vertex `v_i` has at least four colours, choose four of them, `L₄`, and
replace `L(v_i)` by each of the four 3-subsets of `L₄`: `r` grows by one, so by induction each
of the four instances has at least `2^{n/9 - (r+1)/3}` colourings (they have one: Theorem 1, or
Theorem 3 whose exception is a wheel, treated directly). Every colouring of `G` is counted at
most three times, and `(4/3)^9 ≥ 8`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

theorem bound4_of_four_thirds {M N n r : ℕ} (hM : 2 ^ n ≤ M ^ 9 * 8 ^ (r + 1))
    (h : 4 * M ≤ 3 * N) : Bound4 N n r := by
  have h1 : (4 * M) ^ 9 ≤ (3 * N) ^ 9 := Nat.pow_le_pow_left h 9
  rw [mul_pow, mul_pow] at h1
  have h8 : 8 * M ^ 9 ≤ N ^ 9 := by
    have h2 : 3 ^ 9 * (8 * M ^ 9) ≤ 3 ^ 9 * N ^ 9 := by
      calc 3 ^ 9 * (8 * M ^ 9) = 157464 * M ^ 9 := by ring
        _ ≤ 262144 * M ^ 9 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 4 ^ 9 * M ^ 9 := by norm_num
        _ ≤ 3 ^ 9 * N ^ 9 := h1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  unfold Bound4
  calc 2 ^ n ≤ M ^ 9 * 8 ^ (r + 1) := hM
    _ = 8 * M ^ 9 * 8 ^ r := by ring
    _ ≤ N ^ 9 * 8 ^ r := Nat.mul_le_mul_right _ h8

omit [DecidableEq V] in
/-- Double counting: colourings of the four restricted instances are colourings of `G`, each
counted at most three times. -/
theorem four_mul_le_three_mul {E : Finset (V → C)} {vi : V} (L₄ : Finset C) (hL₄ : L₄.card = 4)
    (A : C → Finset (V → C)) (hA : ∀ β ∈ L₄, A β ⊆ E)
    (hmem : ∀ β ∈ L₄, ∀ f ∈ A β, f vi ∈ L₄ ∧ f vi ≠ β) (M : ℕ)
    (hM : ∀ β ∈ L₄, M ≤ (A β).card) : 4 * M ≤ 3 * E.card := by
  classical
  have h1 : 4 * M ≤ ∑ β ∈ L₄, (A β).card := by
    rw [← hL₄, ← smul_eq_mul]; exact Finset.card_nsmul_le_sum _ _ _ hM
  have h2 : ∑ β ∈ L₄, (A β).card = ∑ f ∈ E, (L₄.filter (fun β => f ∈ A β)).card := by
    have : ∀ β ∈ L₄, (A β).card = ∑ f ∈ E, if f ∈ A β then 1 else 0 := by
      intro β hβ
      rw [← Finset.card_filter]
      congr 1
      ext f
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hA β hβ h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Finset.card_filter]
  have h3 : ∀ f ∈ E, (L₄.filter (fun β => f ∈ A β)).card ≤ 3 := by
    intro f _
    by_cases hf : f vi ∈ L₄
    · have hsub : L₄.filter (fun β => f ∈ A β) ⊆ L₄.erase (f vi) := by
        intro β hβ
        simp only [Finset.mem_filter] at hβ
        exact Finset.mem_erase.mpr ⟨(hmem β hβ.1 f hβ.2).2.symm, hβ.1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hf, hL₄] at this; omega
    · have : L₄.filter (fun β => f ∈ A β) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro β hβ hfA
        exact hf (hmem β hβ f hfA).1
      rw [this]; simp
  calc 4 * M ≤ ∑ f ∈ E, (L₄.filter (fun β => f ∈ A β)).card := h2 ▸ h1
    _ ≤ ∑ _f ∈ E, 3 := Finset.sum_le_sum h3
    _ = 3 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The least `M` with `2^n ≤ M^9 · 8^r`. -/
noncomputable def minM8 (n r : ℕ) : ℕ := Nat.find (⟨2 ^ n, by
  calc 2 ^ n ≤ (2 ^ n) ^ 9 := Nat.le_self_pow (by norm_num) _
    _ ≤ (2 ^ n) ^ 9 * 8 ^ r := Nat.le_mul_of_pos_right _ (by positivity)⟩ :
    ∃ M, 2 ^ n ≤ M ^ 9 * 8 ^ r)

theorem minM8_spec (n r : ℕ) : 2 ^ n ≤ minM8 n r ^ 9 * 8 ^ r :=
  Nat.find_spec (p := fun M => 2 ^ n ≤ M ^ 9 * 8 ^ r) _

theorem minM8_le {n r N : ℕ} (h : Bound4 N n r) : minM8 n r ≤ N := Nat.find_min' _ h


namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 16000000 in
/-- **Claim 10**, as a reduction: a non-precoloured outer vertex with at least four colours. -/
theorem thm4_claim10 (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c vi : V}
    {L : V → Finset C} {g : V → C} {t3 : Bool}
    (hNT : T.NT H S (x :: P)) (hh : Thm4Hyp H S x P a c L g t3)
    (hPc : ∀ y z, y ∈ P → z ∈ P → H.Adj y z → ConsecIn P y z)
    (hxc : ∀ y ∈ P, H.Adj x y → y = a ∨ y = c) (hN : T.NoSepTri H S (x :: P))
    (hvi : vi ∈ P) (hvin : vi ∉ pcList t3 x a c) (h4 : 4 ≤ (L vi).card)
    (ih : T.Thm4Lt C (nCount S (pcList t3 x a c))
      (nCount S (pcList t3 x a c) - rCount S (pcList t3 x a c) L) t3) :
    Thm4Concl H S x a c L g t3 := by
  classical
  set pc := pcList t3 x a c with hpcdef
  intro hne hexc
  change (ExtSet H S pc L g).Nonempty at hne
  show Bound4 (ExtSet H S pc L g).ncard (nCount S pc) (rCount S pc L)
  have hviS : vi ∈ S := T.subset hNT vi (List.mem_cons_of_mem _ hvi)
  obtain ⟨L₄, hL₄s, hL₄c⟩ := Finset.exists_subset_card_eq (s := L vi) (n := 4) h4
  let Lβ : C → V → Finset C := fun β => Function.update L vi (L₄.erase β)
  have Lβvi : ∀ β, Lβ β vi = L₄.erase β := fun β => Function.update_self ..
  have Lβne : ∀ β v, v ≠ vi → Lβ β v = L v := fun β v hv => Function.update_of_ne hv ..
  have hcard3 : ∀ β ∈ L₄, (Lβ β vi).card = 3 := by
    intro β hβ; rw [Lβvi, Finset.card_erase_of_mem hβ, hL₄c]
  have hhβ : ∀ β ∈ L₄, Thm4Hyp H S x P a c (Lβ β) g t3 := by
    intro β hβ
    refine ⟨hh.head, hh.last, hh.two_le, hh.xa, hh.xc, hh.ac, fun y hy hyn => ?_,
      fun y hy hyc => ?_⟩
    · by_cases hyv : y = vi
      · rw [hyv, hcard3 β hβ]
      · rw [Lβne β y hyv]; exact hh.three y hy hyn
    · have hyv : y ≠ vi := fun e => hyc (e ▸ List.mem_cons_of_mem _ hvi)
      rw [Lβne β y hyv]; exact hh.five y hy hyc
  have hr4 : (L vi).card ≠ 3 := by omega
  have hrβ : ∀ β ∈ L₄, rCount S pc (Lβ β) = rCount S pc L + 1 := by
    intro β hβ
    unfold rCount
    rw [← Finset.card_insert_of_notMem (a := vi) (s := S.filter (fun v => v ∉ pc ∧ (L v).card = 3))
      (by simp [hr4])]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert]
    by_cases hv : v = vi
    · subst hv; simp [hviS, hvin, hcard3 β hβ]
    · rw [Lβne β v hv]; simp [hv]
  have hrn : rCount S pc L + 1 ≤ nCount S pc := by
    obtain ⟨β, hβ⟩ : L₄.Nonempty := Finset.card_pos.mp (by omega)
    rw [← hrβ β hβ]
    exact Finset.card_le_card (fun v hv => by
      simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, hv.2.1⟩)
  have hsubβ : ∀ β ∈ L₄, ExtSet H S pc (Lβ β) g ⊆ ExtSet H S pc L g := by
    rintro β hβ f ⟨h1, h2, h3⟩
    refine ⟨h1, fun v hv hvn => ?_, h3⟩
    have := h2 v hv hvn
    by_cases hvv : v = vi
    · subst hvv; rw [Lβvi] at this; exact hL₄s (Finset.mem_of_mem_erase this)
    · rwa [Lβne β v hvv] at this
  have hmemβ : ∀ β ∈ L₄, ∀ f ∈ ExtSet H S pc (Lβ β) g, f vi ∈ L₄ ∧ f vi ≠ β := by
    intro β hβ f hf
    have := hf.2.1 vi hviS hvin
    rw [Lβvi] at this
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hexcβ : ∀ β ∈ L₄, ¬ Exc4 H S x a c (Lβ β) g t3 := by
    rintro β hβ ⟨ht, u, hu, hun, h4u, rest⟩
    by_cases huv : u = vi
    · rw [huv, hcard3 β hβ] at h4u; omega
    · rw [Lβne β u huv] at h4u rest
      exact hexc ⟨ht, u, hu, hun, h4u, rest⟩
  by_cases hall : ∀ β ∈ L₄, (ExtSet H S pc (Lβ β) g).Nonempty
  · -- double counting
    set n := nCount S pc
    set r := rCount S pc L
    have hM : ∀ β ∈ L₄, minM8 n (r + 1) ≤ (ExtSet H S pc (Lβ β) g).ncard := by
      intro β hβ
      apply minM8_le
      have := ih H S x P a c (Lβ β) g t3 hNT (hhβ β hβ) (by
        right; refine ⟨rfl, Or.inl ?_⟩
        rw [← hpcdef, hrβ β hβ]; omega) (hall β hβ) (hexcβ β hβ)
      rwa [← hpcdef, hrβ β hβ] at this
    have h43 := four_mul_le_three_mul (E := (extSet_finite H S pc L g).toFinset) (vi := vi) L₄
      hL₄c (fun β => (extSet_finite H S pc (Lβ β) g).toFinset)
      (fun β hβ f hf => by
        simp only [Set.Finite.mem_toFinset] at hf ⊢; exact hsubβ β hβ hf)
      (fun β hβ f hf => by
        simp only [Set.Finite.mem_toFinset] at hf; exact hmemβ β hβ f hf)
      (minM8 n (r + 1))
      (fun β hβ => by
        rw [← Set.ncard_eq_toFinset_card _ (extSet_finite H S pc (Lβ β) g)]; exact hM β hβ)
    rw [← Set.ncard_eq_toFinset_card _ (extSet_finite H S pc L g)] at h43
    exact bound4_of_four_thirds (minM8_spec n (r + 1)) h43
  -- some restricted instance has no colouring
  push Not at hall
  obtain ⟨β, hβ, hβe⟩ := hall
  have hβne : ¬ (ExtSet H S pc (Lβ β) g).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty]; exact hβe
  obtain ⟨rest, hrest⟩ : ∃ rest, P = a :: rest := by
    rcases P with _ | ⟨b, rest⟩
    · simp at hvi
    · have := hh.head; simp only [List.head?_cons, Option.some.injEq] at this
      exact ⟨rest, by rw [this]⟩
  cases t3 with
  | false =>
    -- Theorem 1 colours the restricted instance
    exfalso; apply hβne
    have hNT' : T.NT H S (x :: a :: rest) := hrest ▸ hNT
    obtain ⟨f, hfx, hfa, hfL, hfp⟩ := T.thm1 H _ S rfl x a rest hNT' (Lβ β) g hh.xa
      (fun v hv => (hhβ β hβ).three v (by rw [hrest]; exact List.mem_cons_of_mem _ hv) (by
        have hnd := (List.nodup_cons.mp (T.nodup hNT')).2
        simp only [pcList, Bool.false_eq_true, ite_false, List.mem_cons,
          List.not_mem_nil, or_false, not_or]
        refine ⟨fun e => ?_, fun e => ?_⟩
        · exact (List.nodup_cons.mp (T.nodup hNT')).1 (e ▸ List.mem_cons_of_mem _ hv)
        · exact (List.nodup_cons.mp hnd).1 (e ▸ hv)))
      (fun v hv hvc => (hhβ β hβ).five v hv (by rw [hrest]; exact hvc))
    exact extSet_nonempty_iff.mpr ⟨f, fun v hv => by
      simp only [hpcdef, pcList, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | rfl
      · exact hfx
      · exact hfa, fun v hv hvc => hfL v hv (fun e => hvc (by simp [hpcdef, pcList, e]))
        (fun e => hvc (by simp [hpcdef, pcList, e])), hfp⟩
  | true =>
    have hpc3 : pc = [c, x, a] := rfl
    have hh3 : Thm3Hyp H S x P a c (Lβ β) g :=
      ⟨hh.head, hh.last, hh.two_le, ⟨hh.xa, hh.xc rfl, hh.ac rfl⟩,
        fun y hy hya hyc => (hhβ β hβ).three y hy (by
          rw [← hpcdef, hpc3]
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hyc, fun e => (List.nodup_cons.mp (T.nodup hNT)).1 (e ▸ hy), hya⟩),
        (hhβ β hβ).five⟩
    rcases T.thm3 H hNT hh3 with hE | hE
    · exfalso; apply hβne
      exact extSet_nonempty_iff.mpr (extends_of_mem_iff (fun v => by
        rw [hpc3]) hE)
    -- the exceptional wheel: count directly
    have hP3 : 3 ≤ P.length := by
      rw [hrest] at hvi ⊢
      rcases rest with _ | ⟨b, _ | ⟨d, rest'⟩⟩
      · exfalso; apply hvin; rw [hpc3]; simp at hvi; simp [hvi]
      · exfalso; apply hvin; rw [hpc3]
        have hl := hh.last; rw [hrest] at hl; simp at hl
        simp at hvi; rcases hvi with h | h <;> simp [h, hl]
      · simp
    obtain ⟨u, huS, hun, -, -, hfill, h3card⟩ := T.exc3_wheel H hNT hP3 hh.head hh.last hPc hxc
      hN hE
    have hnr : nCount S pc ≤ rCount S pc L + 2 := by
      unfold nCount rCount
      calc (S.filter (· ∉ pc)).card
          ≤ (insert u (insert vi (S.filter (fun v => v ∉ pc ∧ (L v).card = 3)))).card := by
            apply Finset.card_le_card
            intro z hz
            simp only [Finset.mem_filter] at hz
            simp only [Finset.mem_insert, Finset.mem_filter]
            rcases hfill z hz.1 with h | h | h
            · exfalso; apply hz.2; rw [hpc3, h]; simp
            · by_cases hzv : z = vi
              · exact Or.inr (Or.inl hzv)
              · right; right
                refine ⟨hz.1, hz.2, ?_⟩
                have := h3card z h (fun e => hz.2 (by rw [hpc3, e]; simp))
                  (fun e => hz.2 (by rw [hpc3, e]; simp))
                rwa [Lβne β z hzv] at this
            · exact Or.inl h
        _ ≤ _ := by
            refine (Finset.card_insert_le _ _).trans ?_
            exact Nat.succ_le_succ (Finset.card_insert_le _ _)
    by_cases hr0 : 1 ≤ rCount S pc L
    · exact bound4_of_le (ncard_extSet_pos hne) (by omega)
    -- `r = 0`: the vertices are `x, a, c, v_i` and the hub `u`; two colourings
    have hr0' : rCount S pc L = 0 := by omega
    have hcls : ∀ z ∈ S, z = x ∨ z = u ∨ z = vi ∨ z = a ∨ z = c := by
      intro z hz
      rcases hfill z hz with h | h | h
      · exact Or.inl h
      · by_cases hza : z = a
        · exact Or.inr (Or.inr (Or.inr (Or.inl hza)))
        by_cases hzc : z = c
        · exact Or.inr (Or.inr (Or.inr (Or.inr hzc)))
        by_cases hzv : z = vi
        · exact Or.inr (Or.inr (Or.inl hzv))
        exfalso
        have h3 := h3card z h hza hzc
        rw [Lβne β z hzv] at h3
        have hzx : z ≠ x := fun e => (List.nodup_cons.mp (T.nodup hNT)).1 (e ▸ h)
        have : z ∈ S.filter (fun v => v ∉ pc ∧ (L v).card = 3) := by
          simp only [Finset.mem_filter, hpc3, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hz, ⟨hzc, hzx, hza⟩, h3⟩
        have := Finset.card_pos.mpr ⟨z, this⟩
        unfold rCount at hr0'; omega
      · exact Or.inr (Or.inl h)
    have huvi : u ≠ vi := fun e => hun (e ▸ List.mem_cons_of_mem _ hvi)
    have hux : u ≠ x := fun e => hun (by simp [e])
    have hua : u ≠ a := fun e => hun (by simp [e, List.mem_of_mem_head? hh.head])
    have huc : u ≠ c := fun e => hun (by simp [e, List.mem_of_mem_getLast? hh.last])
    have hvix : vi ≠ x := fun e => (List.nodup_cons.mp (T.nodup hNT)).1 (e ▸ hvi)
    have hvia : vi ≠ a := fun e => hvin (by rw [hpc3, e]; simp)
    have hvic : vi ≠ c := fun e => hvin (by rw [hpc3, e]; simp)
    have hnxv : ¬ H.Adj x vi := fun h => by
      rcases hxc vi hvi h with e | e
      · exact hvia e
      · exact hvic e
    have h5u : 5 ≤ (L u).card := hh.five u huS hun
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hγ₁₂⟩ : ∃ γ₁ ∈ ((L u).erase (g x)).erase (g a) |>.erase (g c),
        ∃ γ₂ ∈ ((L u).erase (g x)).erase (g a) |>.erase (g c), γ₁ ≠ γ₂ := by
      apply Finset.one_lt_card.mp
      have := Finset.pred_card_le_card_erase (s := L u) (a := g x)
      have := Finset.pred_card_le_card_erase (s := (L u).erase (g x)) (a := g a)
      have := Finset.pred_card_le_card_erase (s := ((L u).erase (g x)).erase (g a)) (a := g c)
      omega
    have mk : ∀ γ ∈ ((L u).erase (g x)).erase (g a) |>.erase (g c),
        ∃ f ∈ ExtSet H S pc L g, f u = γ := by
      intro γ hγ
      simp only [Finset.mem_erase] at hγ
      obtain ⟨hγc, hγa, hγx, hγL⟩ := hγ
      obtain ⟨δ, hδ⟩ : (((L vi).erase (g a)).erase (g c)).erase γ |>.Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.pred_card_le_card_erase (s := L vi) (a := g a)
        have := Finset.pred_card_le_card_erase (s := (L vi).erase (g a)) (a := g c)
        have := Finset.pred_card_le_card_erase (s := ((L vi).erase (g a)).erase (g c)) (a := γ)
        omega
      simp only [Finset.mem_erase] at hδ
      obtain ⟨hδγ, hδc, hδa, hδL⟩ := hδ
      let f : V → C := fun z => if z = u then γ else if z = vi then δ else g z
      have fu : f u = γ := by simp [f]
      have fvi : f vi = δ := by simp [f, Ne.symm huvi]
      have fo : ∀ z, z ≠ u → z ≠ vi → f z = g z := fun z h1 h2 => by simp [f, h1, h2]
      refine ⟨f, ⟨fun z hz => ?_, fun z hz hzn => ?_, fun p hp q hq hpq => ?_⟩, fu⟩
      · have hzu : z ≠ u := by
          rintro rfl; rcases hz with hz | hz
          · exact hz huS
          · rw [hpc3] at hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with h | h | h
            · exact huc h
            · exact hux h
            · exact hua h
        have hzv : z ≠ vi := by
          rintro rfl; rcases hz with hz | hz
          · exact hz hviS
          · exact hvin hz
        exact fo z hzu hzv
      · rcases hcls z hz with h | h | h | h | h
        · exfalso; apply hzn; rw [hpc3, h]; simp
        · rw [h, fu]; exact hγL
        · rw [h, fvi]; exact hδL
        · exfalso; apply hzn; rw [hpc3, h]; simp
        · exfalso; apply hzn; rw [hpc3, h]; simp
      · have hval : ∀ z ∈ S, f z = γ ∨ f z = δ ∨ f z = g x ∨ f z = g a ∨ f z = g c := by
          intro z hz
          rcases hcls z hz with h | h | h | h | h
          · right; right; left; rw [h, fo x (Ne.symm hux) (Ne.symm hvix)]
          · left; rw [h, fu]
          · right; left; rw [h, fvi]
          · right; right; right; left; rw [h, fo a (Ne.symm hua) (Ne.symm hvia)]
          · right; right; right; right; rw [h, fo c (Ne.symm huc) (Ne.symm hvic)]
        rcases hcls p hp with hp' | hp' | hp' | hp' | hp' <;>
          rcases hcls q hq with hq' | hq' | hq' | hq' | hq' <;>
          rw [hp', hq'] at hpq ⊢ <;>
          simp only [fu, fvi, fo x (Ne.symm hux) (Ne.symm hvix), fo a (Ne.symm hua) (Ne.symm hvia),
            fo c (Ne.symm huc) (Ne.symm hvic)] <;>
          first
          | exact absurd hpq (H.loopless.irrefl _)
          | exact absurd hpq hnxv | exact absurd hpq.symm hnxv
          | exact hγx | exact hγx.symm | exact hγa | exact hγa.symm | exact hγc | exact hγc.symm
          | exact hδγ | exact hδγ.symm | exact hδa | exact hδa.symm | exact hδc | exact hδc.symm
          | exact hh.xa | exact hh.xa.symm | exact hh.xc rfl | exact (hh.xc rfl).symm
          | exact hh.ac rfl hpq | exact (hh.ac rfl hpq.symm).symm
    obtain ⟨f₁, hf₁, hf₁u⟩ := mk γ₁ hγ₁
    obtain ⟨f₂, hf₂, hf₂u⟩ := mk γ₂ hγ₂
    have hf12 : f₁ ≠ f₂ := fun e => hγ₁₂ (hf₁u ▸ hf₂u ▸ congrFun e u)
    have h2 : 2 ≤ (ExtSet H S pc L g).ncard := by
      have := Set.ncard_le_ncard (s := {f₁, f₂}) (t := ExtSet H S pc L g)
        (by intro f hf; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
            rcases hf with rfl | rfl <;> assumption) (extSet_finite H S pc L g)
      rwa [Set.ncard_pair hf12] at this
    unfold Bound4
    rw [hr0']
    have hn2 : nCount S pc ≤ 2 := by omega
    calc 2 ^ nCount S pc ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (ExtSet H S pc L g).ncard ^ 9 := Nat.pow_le_pow_left h2 9
      _ = _ := by simp

end NTCalc

end ThomassenManyColourings
