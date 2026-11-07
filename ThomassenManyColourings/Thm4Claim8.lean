/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Basic

/-!
# Theorem 4, Claim 8: separating triangles

Excise the inside of a separating triangle: the outside has fewer non-precoloured vertices and
the same `r`; every colouring of it has at least `2^{n₂/9}` extensions inside (induction with the
triangle precoloured), so the counts multiply.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] [DecidableEq C] in
theorem extends_mono {H : SimpleGraph V} {S S' : Finset V} {c : List V} {L : V → Finset C}
    {f₀ : V → C} (hS : S' ⊆ S) (h : Extends H S c L f₀) : Extends H S' c L f₀ := by
  obtain ⟨f, h1, h2, h3⟩ := h
  exact ⟨f, h1, fun v hv hvc => h2 v (hS hv) hvc,
    fun p hp q hq hpq => h3 p (hS hp) q (hS hq) hpq⟩

/-- The least `M` with `2^n ≤ M^9`. -/
noncomputable def minM (n : ℕ) : ℕ := Nat.find (⟨2 ^ n, by
  calc 2 ^ n ≤ (2 ^ n) ^ 9 := Nat.le_self_pow (by norm_num) _⟩ : ∃ M, 2 ^ n ≤ M ^ 9)

theorem minM_spec (n : ℕ) : 2 ^ n ≤ minM n ^ 9 := Nat.find_spec (p := fun M => 2 ^ n ≤ M ^ 9) _

theorem minM_le {n N : ℕ} (h : 2 ^ n ≤ N ^ 9) : minM n ≤ N := Nat.find_min' _ h

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Claim 8**, as a reduction: a triangle region with a vertex strictly inside (and a
non-precoloured outer vertex outside it). -/
theorem thm4_claim8 (H : SimpleGraph V) {S S₁ : Finset V} {x : V} {P : List V} {a c p q r : V}
    {L : V → Finset C} {g : V → C} {t3 : Bool}
    (hNT : T.NT H S (x :: P)) (hh : Thm4Hyp H S x P a c L g t3)
    (hfree : ∃ y ∈ P, y ∉ pcList t3 x a c)
    (h₁ : T.NT H S₁ [p, q, r]) (hR : Region H S (x :: P) S₁ [p, q, r])
    (hsep : ∃ z ∈ S₁, z ∉ [p, q, r])
    (ih : T.Thm4Lt C (nCount S (pcList t3 x a c))
      (nCount S (pcList t3 x a c) - rCount S (pcList t3 x a c) L) t3) :
    Thm4Concl H S x a c L g t3 := by
  classical
  set pc := pcList t3 x a c with hpcdef
  have hpcP : ∀ z ∈ pc, z ∈ x :: P := by
    intro z hz
    simp only [hpcdef, pcList] at hz
    split_ifs at hz
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hh.last)
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_of_mem_head? hh.head)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_of_mem_head? hh.head)
  have hpS : p ∈ S₁ := T.subset h₁ p (by simp)
  have hqS : q ∈ S₁ := T.subset h₁ q (by simp)
  have hrS : r ∈ S₁ := T.subset h₁ r (by simp)
  set G1 := (S \ S₁) ∪ {p, q, r} with hG1
  have hG1NT : T.NT H G1 (x :: P) := T.excise3 hNT h₁ hR.1 hR.2
  have hG1S : G1 ⊆ S := by
    intro z hz
    simp only [hG1, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton] at hz
    rcases hz with ⟨h, -⟩ | rfl | rfl | rfl
    · exact h
    · exact hR.1 hpS
    · exact hR.1 hqS
    · exact hR.1 hrS
  have hstrict : ∀ z ∈ S₁, z ∉ [p, q, r] → z ∉ G1 := by
    intro z hz hzn h
    simp only [hG1, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzn
    rcases h with ⟨-, h⟩ | h | h | h
    · exact h hz
    · exact hzn.1 h
    · exact hzn.2.1 h
    · exact hzn.2.2 h
  have hcycG1 : ∀ z ∈ x :: P, z ∈ G1 := fun z hz => T.subset hG1NT z hz
  -- the pieces
  have hU : G1 ∪ S₁ = S := by
    ext z
    simp only [hG1, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ((⟨h, -⟩ | rfl | rfl | rfl) | h)
      · exact h
      · exact hR.1 hpS
      · exact hR.1 hqS
      · exact hR.1 hrS
      · exact hR.1 h
    · intro h; by_cases h1 : z ∈ S₁
      · exact Or.inr h1
      · exact Or.inl (Or.inl ⟨h, h1⟩)
  have hX : ∀ u ∈ G1, ∀ w ∈ S₁, H.Adj u w → u ∈ S₁ ∨ w ∈ G1 := by
    intro u hu w hw huw
    by_cases hwt : w ∈ [p, q, r]
    · right
      simp only [hG1, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwt
      tauto
    · left; exact (hR.2 w hw hwt).2 u (hG1S hu) huw.symm
  have hI : ∀ z ∈ G1, z ∈ S₁ → z ∈ [p, q, r] := by
    intro z h1 h2
    by_contra hn; exact hstrict z h2 hn h1
  -- counts
  have hn : nCount S pc = nCount G1 pc + nCount S₁ [p, q, r] := by
    unfold nCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hz, hzpc⟩
        by_cases h1 : z ∈ S₁
        · by_cases hzt : z ∈ [p, q, r]
          · left
            refine ⟨?_, hzpc⟩
            simp only [hG1, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hzt
            tauto
          · exact Or.inr ⟨h1, hzt⟩
        · exact Or.inl ⟨by simp [hG1, hz, h1], hzpc⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨hG1S h1, h2⟩
        · exact ⟨hR.1 h1, fun h => (hR.2 z h1 h2).1 (hpcP z h)⟩
    · rw [Finset.disjoint_left]
      intro z h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hstrict z h2.1 h2.2 h1.1
  have hr : rCount S pc L = rCount G1 pc L := by
    unfold rCount
    congr 1
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hzpc, h3⟩
      refine ⟨?_, hzpc, h3⟩
      by_contra hn
      have h1 : z ∈ S₁ := (Finset.mem_union.mp (hU ▸ hz)).resolve_left hn
      have hzt : z ∉ [p, q, r] := fun h => hn (by
        simp only [hG1, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        tauto)
      have := hh.five z hz (hR.2 z h1 hzt).1; omega
    · rintro ⟨hz, hzpc, h3⟩; exact ⟨hG1S hz, hzpc, h3⟩
  have hn1pos : 0 < nCount G1 pc := by
    obtain ⟨y, hy, hyn⟩ := hfree
    unfold nCount
    exact Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hcycG1 y (List.mem_cons_of_mem _ hy),
      hyn⟩⟩
  have hn2pos : 0 < nCount S₁ [p, q, r] := by
    obtain ⟨z, hz, hzn⟩ := hsep
    unfold nCount
    exact Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hzn⟩⟩
  intro hne hexc
  -- the outside
  have hh1 : Thm4Hyp H G1 x P a c L g t3 :=
    ⟨hh.head, hh.last, hh.two_le, hh.xa, hh.xc, hh.ac, hh.three,
      fun y hy hyc => hh.five y (hG1S hy) hyc⟩
  have hB1 := ih H G1 x P a c L g t3 hG1NT hh1 (by
    left; first | omega | (rw [← hpcdef]; omega))
    (extSet_nonempty_iff.mpr (extends_mono hG1S (extSet_nonempty_iff.mp hne)))
    (fun ⟨ht, u, hu, h⟩ => hexc ⟨ht, u, hG1S hu, h⟩)
  rw [← hpcdef, ← hr] at hB1
  -- the inside, with the triangle precoloured by a colouring of the outside
  set n₂ := nCount S₁ [p, q, r] with hn₂
  have hM : ∀ f₁ ∈ ExtSet H G1 pc L g, minM n₂ ≤ (ExtSet H S₁ [p, q, r] L f₁).ncard := by
    intro f₁ hf₁
    apply minM_le
    have hpG : p ∈ G1 := by simp [hG1]
    have hqG : q ∈ G1 := by simp [hG1]
    have hrG : r ∈ G1 := by simp [hG1]
    have hch := NT_chain h₁
    have hpq : H.Adj p q := (List.isChain_cons_cons.mp hch).1
    have hqr : H.Adj q r := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hch).2).1
    have hrp : H.Adj r p := T.adj_cons (by simpa using T.rotate (T.rotate h₁))
    have hNT2 : T.NT H S₁ (q :: [r, p]) := by simpa using T.rotate h₁
    have hh2 : Thm4Hyp H S₁ q [r, p] r p L f₁ true := by
      refine ⟨rfl, rfl, by simp, hf₁.2.2 q hqG r hrG hqr, fun _ => (hf₁.2.2 p hpG q hqG hpq).symm,
        fun _ _ => hf₁.2.2 r hrG p hpG hrp, ?_, ?_⟩
      · intro y hy hyn
        exfalso; apply hyn
        show y ∈ [p, q, r]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto
      · intro y hy hyc
        exact hh.five y (hR.1 hy) (hR.2 y hy (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyc ⊢; tauto)).1
    have hpc2 : pcList true q r p = [p, q, r] := rfl
    have hr2 : rCount S₁ [p, q, r] L = 0 := by
      unfold rCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy ⟨hyt, h3⟩
      have := hh.five y (hR.1 hy) (hR.2 y hy hyt).1; omega
    have hne2 : (ExtSet H S₁ [p, q, r] L f₁).Nonempty := by
      apply extSet_nonempty_iff.mpr
      refine T.thm2_three H h₁ L f₁ ?_ (fun y hy hyt => hh.five y (hR.1 hy) (hR.2 y hy hyt).1)
      intro u hu w hw huw
      have hu' : u ∈ G1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl <;> assumption
      have hw' : w ∈ G1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      exact hf₁.2.2 u hu' w hw' huw
    have hB2 := ih H S₁ q [r, p] r p L f₁ true hNT2 hh2 (by
      left; first | omega | (rw [hpc2]; omega))
      (by rw [hpc2]; exact hne2)
      (by
        rintro ⟨-, u, hu, hun, h4, -⟩
        have := hh.five u (hR.1 hu) (hR.2 u hu (by
          simp only [List.mem_cons, List.not_mem_nil, or_false,
            not_or] at hun ⊢
          tauto)).1
        omega)
    rw [hpc2, hr2] at hB2
    unfold Bound4 at hB2; simpa using hB2
  have hglue := ncard_extSet_glue (H := H) (S := S) (S₁ := G1) (S₂ := S₁) (c := pc) (c₁ := pc)
    (c₂ := [p, q, r]) (L := L) (f₀ := g) (minM n₂) hU hX hI
    (fun z hz => ⟨fun _ => hz, fun h1 => by
      by_contra hn; exact (hR.2 z h1 hn).1 (hpcP z hz)⟩)
    (fun z hz hn => absurd (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> simp [hG1]) hn)
    (fun z hz _ hzc => absurd hz hzc) hM
  have hB2' : Bound4 (minM n₂) n₂ 0 := by unfold Bound4; simpa using minM_spec n₂
  rw [hn]
  exact bound4_mono (by simpa using bound4_mul hB1 hB2') hglue

end NTCalc

end ThomassenManyColourings
