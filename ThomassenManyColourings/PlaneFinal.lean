/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneComplete
public import ThomassenManyColourings.Thm4Cor

/-!
# Exponentially many list colourings of planar graphs

**Thomassen (2007).** A finite planar graph `G` with `n` vertices, every vertex of which has a
list of at least five colours, has at least `2^{n/9}` list colourings (`two_rpow_le_ncard`).
For `n ≥ 3`, `G` is a spanning subgraph of a plane near-triangulation (`exists_PNT_supergraph`),
and the corollary of Theorem 4 (`NTCalc.many_colourings_sub`) applies to the interface realised
by plane near-triangulations (`planeNTCalc`). For `n = 2` the near-triangulation is a single
edge, and for `n ≤ 1` the colourings are counted directly.
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]

/-- Two vertices joined by an edge form a plane near-triangulation with outer cycle `x y`. -/
theorem PNT_top_two {x y : V} (hxy : x ≠ y) (hV : ∀ z, z = x ∨ z = y) :
    PNT (⊤ : SimpleGraph V) Finset.univ [x, y] := by
  classical
  have hP : IsPlanar (indG (⊤ : SimpleGraph V) Finset.univ) := by
    rw [indG_univ]
    refine isPlanar_of_card_le_four (S := {x, y}) (fun a b _ => ?_)
      (Finset.card_le_two.trans (by norm_num))
    rcases hV a with rfl | rfl <;> simp
  obtain ⟨M⟩ := hP
  have hout : ∀ d : (indG (⊤ : SimpleGraph V) Finset.univ).Dart, IsOuter [x, y] d := by
    intro d
    have hne : d.fst ≠ d.snd := d.adj.1.ne
    show CycSucc [x, y] d.fst d.snd
    rcases hV d.fst with h1 | h1 <;> rcases hV d.snd with h2 | h2 <;> rw [h1, h2] at hne ⊢
    · exact absurd rfl hne
    · exact cycSucc_cons_cons x y []
    · exact Or.inr ⟨[], rfl⟩
    · exact absurd rfl hne
  refine ⟨by simp [hxy], by simp, fun v _ => Finset.mem_univ v, fun u v huv => ?_,
    fun u _ v _ => ?_, M, fun d _ => hout _, fun d hd => absurd (hout d) hd⟩
  · rcases (show (u = x ∧ v = y) ∨ (u = y ∧ v = x) by
      rcases huv with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
      · rcases A with _ | ⟨a, _ | ⟨a', A⟩⟩
        · simp only [List.nil_append, List.cons.injEq] at hAB
          exact Or.inl ⟨hAB.1.symm, hAB.2.1.symm⟩
        · simp at hAB
        · have := congrArg List.length hAB; simp at this
      · simp only [List.cons.injEq] at hMm
        have h' : [y] = Mm ++ [u] := hMm.2
        obtain ⟨-, h2⟩ := List.append_inj' (show [] ++ [y] = Mm ++ [u] by simpa using h')
          (by simp)
        simp only [List.cons.injEq, and_true] at h2
        exact Or.inr ⟨h2.symm, hMm.1.symm⟩) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm
  · by_cases huv : u = v
    · rw [huv]
    · exact SimpleGraph.Adj.reachable ⟨huv, by simp, by simp⟩

set_option maxHeartbeats 4000000 in
-- the case analysis on the number of vertices exceeds the default heartbeat budget
/-- **Thomassen (2007)**, counting form: `2^n ≤ N^9`. -/
theorem two_pow_le_ncard_pow (G : SimpleGraph V) (hG : IsPlanar G) (L : V → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card) (f₀ : V → C) :
    2 ^ Fintype.card V ≤ (ColSet G Finset.univ L f₀).ncard ^ 9 := by
  classical
  have hfin := extSet_finite G Finset.univ [] L f₀
  have hmem : ∀ f : V → C, (∀ v, f v ∈ L v) → (∀ u w, G.Adj u w → f u ≠ f w) →
      f ∈ ColSet G Finset.univ L f₀ := by
    intro f hf hp
    refine ⟨fun v hv => ?_, fun v _ _ => hf v, fun u _ w _ huw => hp u w huw⟩
    rcases hv with hv | hv
    · exact absurd (Finset.mem_univ v) hv
    · simp at hv
  rcases Nat.lt_or_ge (Fintype.card V) 3 with h3 | h3
  · interval_cases hn : Fintype.card V
    · -- no vertex
      have hne : f₀ ∈ ColSet G Finset.univ L f₀ := by
        refine hmem f₀ (fun v => ?_) (fun u w _ => ?_)
        · exact (Fintype.card_eq_zero_iff.mp hn).elim v
        · exact (Fintype.card_eq_zero_iff.mp hn).elim u
      have h0 : 0 < (ColSet G Finset.univ L f₀).ncard := (Set.ncard_pos hfin).mpr ⟨f₀, hne⟩
      rw [pow_zero]
      exact Nat.one_le_pow _ _ h0
    · -- one vertex
      obtain ⟨v₀, hv₀⟩ := Fintype.card_eq_one_iff.mp hn
      obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := Finset.one_lt_card.mp
        (show 1 < (L v₀).card by have := hL v₀; omega)
      have hcol : ∀ c ∈ L v₀, (fun _ : V => c) ∈ ColSet G Finset.univ L f₀ := by
        intro c hc'
        refine hmem _ (fun v => by rw [hv₀ v]; exact hc') (fun u w huw => ?_)
        exact absurd ((hv₀ u).trans (hv₀ w).symm) huw.ne
      have h2 : 1 < (ColSet G Finset.univ L f₀).ncard :=
        (Set.one_lt_ncard_iff hfin).mpr ⟨_, _, hcol c₁ hc₁, hcol c₂ hc₂,
          fun e => hc (congrFun e v₀)⟩
      calc 2 ^ 1 ≤ (ColSet G Finset.univ L f₀).ncard := by omega
        _ ≤ _ := Nat.le_self_pow (by norm_num) _
    · -- two vertices: a single edge
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card V by omega)
      have hV : ∀ z, z = x ∨ z = y := by
        intro z
        by_contra hz
        push Not at hz
        have hsub : ({x, y, z} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
        rw [Finset.card_eq_three.mpr ⟨x, y, z, hxy, hz.1.symm, hz.2.symm, rfl⟩, hn] at hsub
        omega
      have := (planeNTCalc V).many_colourings_sub (le_top : G ≤ ⊤) (PNT_top_two hxy hV) L
        (fun v _ => hL v) f₀
      rwa [Finset.card_univ, hn] at this
  · obtain ⟨H, hGH, x, a, b, hP⟩ := exists_PNT_supergraph G hG h3
    have := (planeNTCalc V).many_colourings_sub hGH (l := [b]) hP L (fun v _ => hL v) f₀
    rwa [Finset.card_univ] at this

/-- **Thomassen (2007).** A finite planar graph with `n` vertices, every vertex of which has a
list of at least five colours, has at least `2^{n/9}` list colourings. -/
theorem two_rpow_le_ncard (G : SimpleGraph V) (hG : IsPlanar G) (L : V → Finset C)
    (hL : ∀ v, 5 ≤ (L v).card) (f₀ : V → C) :
    (2 : ℝ) ^ ((Fintype.card V : ℝ) / 9) ≤ (ColSet G Finset.univ L f₀).ncard := by
  have h := two_pow_le_ncard_pow G hG L hL f₀
  have hpow : ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 9)) ^ (9 : ℕ) = (2 : ℝ) ^ Fintype.card V := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (Fintype.card V : ℝ) / 9 * ((9 : ℕ) : ℝ) = (Fintype.card V : ℕ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  have h' : ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 9)) ^ (9 : ℕ) ≤
      ((ColSet G Finset.univ L f₀).ncard : ℝ) ^ (9 : ℕ) := by
    rw [hpow]
    exact_mod_cast h
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h'

end ThomassenManyColourings
