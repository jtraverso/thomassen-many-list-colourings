/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim8

/-!
# Theorem 4, Claim 11: `v_k` is precoloured

With only `v₁, v₂` precoloured (and every other outer vertex with exactly three colours, Claim
10), colour `v_k` as in some colouring of `G`: `n` and `r` drop by one, and no exceptional vertex
can appear since there is no vertex with four colours.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 4000000 in
/-- **Claim 11**, as a reduction. -/
theorem thm4_claim11 (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: P)) (hh : Thm4Hyp H S x P a c L g false)
    (h10 : ∀ y ∈ P, y ∉ [x, a] → (L y).card = 3)
    (ih : T.Thm4Lt C (nCount S (pcList false x a c))
      (nCount S (pcList false x a c) - rCount S (pcList false x a c) L) false) :
    Thm4Concl H S x a c L g false := by
  classical
  have hpc : pcList false x a c = [x, a] := rfl
  have hpc3 : pcList true x a c = [c, x, a] := rfl
  intro hne _
  rw [hpc] at hne ⊢
  obtain ⟨f, hf1, hf2, hf3⟩ := hne
  have hnd := T.nodup hNT
  have hcP : c ∈ P := List.mem_of_mem_getLast? hh.last
  have haP : a ∈ P := List.mem_of_mem_head? hh.head
  have hxc : x ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hcP)
  have hac : a ≠ c := by
    intro e
    obtain ⟨b, P', rfl⟩ : ∃ b P', P = b :: P' := List.exists_cons_of_ne_nil (by
      intro h; have := hh.two_le; simp [h] at this)
    have hb := hh.head; simp only [List.head?_cons, Option.some.injEq] at hb; subst hb
    have hP' : P' ≠ [] := by intro h; have := hh.two_le; simp [h] at this
    have hl := hh.last
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hP'] at hl
    simp only [Option.getD_some, Option.some.injEq] at hl
    exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      (e ▸ hl ▸ List.getLast_mem hP')
  have hcS : c ∈ S := T.subset hNT c (List.mem_cons_of_mem _ hcP)
  have hxS : x ∈ S := T.subset hNT x List.mem_cons_self
  have haS : a ∈ S := T.subset hNT a (List.mem_cons_of_mem _ haP)
  have hcn : c ∉ [x, a] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm hxc, Ne.symm hac⟩
  have hc3 : (L c).card = 3 := h10 c hcP hcn
  -- adjacency of `c` to `x`
  have hcx : H.Adj c x := by
    have := NT_chain (T.rotate hNT)
    rw [List.isChain_append] at this
    exact this.2.2 c (by
      rcases P.eq_nil_or_concat with h | ⟨P', z, h⟩
      · simp [h] at hcP
      · have hl := hh.last
        rw [h, List.concat_eq_append, List.getLast?_concat] at hl ⊢
        exact hl) x rfl
  set col := f c with hcol
  let g' := Function.update g c col
  have g'c : g' c = col := Function.update_self ..
  have g'ne : ∀ v, v ≠ c → g' v = g v := fun v hv => Function.update_of_ne hv ..
  have hfx : f x = g x := hf1 x (Or.inr (by simp))
  have hfa : f a = g a := hf1 a (Or.inr (by simp))
  have hh3 : Thm4Hyp H S x P a c L g' true := by
    refine ⟨hh.head, hh.last, hh.two_le, by rw [g'ne x hxc, g'ne a hac]; exact hh.xa, ?_, ?_,
      ?_, hh.five⟩
    · intro _; rw [g'ne x hxc, g'c, ← hfx]; exact hf3 x hxS c hcS hcx.symm
    · intro _ hac'; rw [g'ne a hac, g'c, ← hfa]; exact hf3 a haS c hcS hac'
    · intro y hy hyn
      exact hh.three y hy (by
        intro h; apply hyn
        simp only [pcList, ite_true, ite_false, List.mem_cons, List.not_mem_nil, or_false,
          Bool.false_eq_true] at h ⊢
        tauto)
  -- counts
  have hsub : ExtSet H S [c, x, a] L g' ⊆ ExtSet H S [x, a] L g := by
    rintro f' ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, fun v hv hvn => ?_, h3⟩
    · have hvc : v ≠ c := by
        rintro rfl
        rcases hv with hv | hv
        · exact hv hcS
        · exact hcn hv
      rw [← g'ne v hvc]
      exact h1 v (by
        rcases hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (List.mem_cons_of_mem _ hv))
    · by_cases hvc : v = c
      · rw [hvc, h1 c (Or.inr (by simp)), g'c]; exact hf2 c hcS hcn
      · exact h2 v hv (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn ⊢
          exact ⟨hvc, hvn⟩)
  have hfmem : f ∈ ExtSet H S [c, x, a] L g' := by
    refine ⟨fun v hv => ?_, fun v hv hvn => hf2 v hv (fun h => hvn (List.mem_cons_of_mem _ h)),
      hf3⟩
    by_cases hvc : v = c
    · rw [hvc, g'c]
    · rw [g'ne v hvc]
      exact hf1 v (by
        rcases hv with hv | hv
        · exact Or.inl hv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with h | h | h
          · exact absurd h hvc
          · exact Or.inr (by simp [h])
          · exact Or.inr (by simp [h]))
  have hfilt : S.filter (· ∉ [c, x, a]) = (S.filter (· ∉ [x, a])).erase c := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    tauto
  have hn : nCount S [x, a] = nCount S [c, x, a] + 1 := by
    unfold nCount
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hcS, hcn⟩)]
    have : 0 < (S.filter (· ∉ [x, a])).card :=
      Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hcS, hcn⟩⟩
    omega
  have hfiltr : S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3) =
      (S.filter (fun v => v ∉ [x, a] ∧ (L v).card = 3)).erase c := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    tauto
  have hr : rCount S [x, a] L = rCount S [c, x, a] L + 1 := by
    unfold rCount
    rw [hfiltr, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hcS, hcn, hc3⟩)]
    have : 0 < (S.filter (fun v => v ∉ [x, a] ∧ (L v).card = 3)).card :=
      Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hcS, hcn, hc3⟩⟩
    omega
  have hB := ih H S x P a c L g' true hNT hh3 (by left; rw [hpc3, hpc, hn]; omega)
    (by rw [hpc3]; exact ⟨f, hfmem⟩)
    (by
      rintro ⟨-, u, hu, hun, h4, hux, -, -, -⟩
      by_cases huP : u ∈ P
      · have := h10 u huP (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun ⊢
          exact hun.2)
        omega
      · have := hh.five u hu (by
          simp only [List.mem_cons, not_or]
          exact ⟨fun e => by simp [e] at hun, huP⟩)
        omega)
  rw [hpc3] at hB
  have hle := Set.ncard_le_ncard hsub (extSet_finite H S [x, a] L g)
  unfold Bound4 at hB ⊢
  rw [hn, hr, pow_succ, pow_succ]
  calc 2 ^ nCount S [c, x, a] * 2 ≤ (ExtSet H S [c, x, a] L g').ncard ^ 9 *
        8 ^ rCount S [c, x, a] L * 2 := Nat.mul_le_mul_right _ hB
    _ ≤ (ExtSet H S [x, a] L g).ncard ^ 9 * 8 ^ rCount S [c, x, a] L * 8 := by
        apply Nat.mul_le_mul _ (by norm_num)
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle 9)
    _ = _ := by ring

end NTCalc

end ThomassenManyColourings
