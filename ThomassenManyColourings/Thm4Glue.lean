/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim10

/-!
# Theorem 4: gluing along a separating edge with a free side

`S = S₁ ∪ S₂` where `S₂` meets `S₁` only in an edge `x₂ a₂` of both outer cycles and contains no
other precoloured vertex. Every colouring of `S₁` extends to `S₂` (Theorem 1), and by induction
in at least `2^{n₂/9 - r₂/3}` ways; the bounds multiply.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Gluing a free side.** -/
theorem thm4_glue_free (H : SimpleGraph V) {S S₁ S₂ : Finset V} {x x₂ : V} {P₁ P₂ : List V}
    {a c c₁ a₂ c₂ : V} {L : V → Finset C} {g : V → C} {t3 : Bool}
    (hNT₁ : T.NT H S₁ (x :: P₁)) (hh₁ : Thm4Hyp H S₁ x P₁ a c₁ L g t3) (hc₁ : t3 = true → c₁ = c)
    (hNT₂ : T.NT H S₂ (x₂ :: P₂)) (hhead₂ : P₂.head? = some a₂)
    (hlast₂ : P₂.getLast? = some c₂) (htwo₂ : 2 ≤ P₂.length)
    (h3₂ : ∀ y ∈ P₂, y ≠ a₂ → 3 ≤ (L y).card) (h5₂ : ∀ y ∈ S₂, y ∉ x₂ :: P₂ → 5 ≤ (L y).card)
    (hU : S₁ ∪ S₂ = S) (hX : ∀ p ∈ S₁, ∀ q ∈ S₂, H.Adj p q → p ∈ S₂ ∨ q ∈ S₁)
    (hI : ∀ z ∈ S₁, z ∈ S₂ → z = x₂ ∨ z = a₂) (hx₂ : x₂ ∈ S₁) (ha₂ : a₂ ∈ S₁)
    (hxa₂ : H.Adj x₂ a₂)
    (hpc : ∀ z ∈ pcList t3 x a c, z ∈ S₂ → z = x₂ ∨ z = a₂)
    (hpos₂ : 0 < nCount S₂ [x₂, a₂]) (hpos₁ : 0 < nCount S₁ (pcList t3 x a c) ∨ t3 = true)
    (ih : T.Thm4Lt C (nCount S (pcList t3 x a c))
      (nCount S (pcList t3 x a c) - rCount S (pcList t3 x a c) L) t3) :
    Thm4Concl H S x a c L g t3 := by
  classical
  set pc := pcList t3 x a c with hpcdef
  have hpc2 : pcList false x₂ a₂ c₂ = [x₂, a₂] := rfl
  intro hne hexc
  change (ExtSet H S pc L g).Nonempty at hne
  show Bound4 (ExtSet H S pc L g).ncard (nCount S pc) (rCount S pc L)
  have hS₁ : S₁ ⊆ S := fun z hz => hU ▸ Finset.mem_union_left _ hz
  have hS₂ : S₂ ⊆ S := fun z hz => hU ▸ Finset.mem_union_right _ hz
  -- counts split
  have hsplit : ∀ q : V → Prop, [DecidablePred q] →
      (S.filter (fun v => v ∉ pc ∧ q v)).card =
        (S₁.filter (fun v => v ∉ pc ∧ q v)).card +
          (S₂.filter (fun v => v ∉ [x₂, a₂] ∧ q v)).card := by
    intro q _
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_union, List.mem_cons, List.not_mem_nil, or_false,
        not_or]
      constructor
      · rintro ⟨hv, hvpc, hq⟩
        by_cases h1 : v ∈ S₁
        · exact Or.inl ⟨h1, hvpc, hq⟩
        · have h2 : v ∈ S₂ := (Finset.mem_union.mp (hU ▸ hv)).resolve_left h1
          refine Or.inr ⟨h2, ⟨fun e => h1 (e ▸ hx₂), fun e => h1 (e ▸ ha₂)⟩, hq⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, ⟨h2, h2'⟩, h3⟩)
        · exact ⟨hS₁ h1, h2, h3⟩
        · refine ⟨hS₂ h1, fun h => ?_, h3⟩
          rcases hpc v h h1 with e | e
          · exact h2 e
          · exact h2' e
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
      rcases hI v h1.1 h2.1 with e | e
      · exact h2.2.1.1 e
      · exact h2.2.1.2 e
  have hn : nCount S pc = nCount S₁ pc + nCount S₂ [x₂, a₂] := by
    have := hsplit (fun _ => True)
    simp only [and_true] at this
    exact this
  have hr : rCount S pc L = rCount S₁ pc L + rCount S₂ [x₂, a₂] L := by
    unfold rCount
    exact hsplit (fun v => (L v).card = 3)
  -- the first piece
  have hne₁ : (ExtSet H S₁ pc L g).Nonempty :=
    extSet_nonempty_iff.mpr (extends_mono hS₁ (extSet_nonempty_iff.mp hne))
  have hr₁n : rCount S₁ pc L ≤ nCount S₁ pc := Finset.card_le_card (fun v hv => by
    simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, hv.2.1⟩)
  have hr₂n : rCount S₂ [x₂, a₂] L ≤ nCount S₂ [x₂, a₂] := Finset.card_le_card (fun v hv => by
    simp only [Finset.mem_filter] at hv ⊢; exact ⟨hv.1, hv.2.1⟩)
  have hlex₁ : Lex4 (nCount S₁ pc) (nCount S₁ pc - rCount S₁ pc L) t3 (nCount S pc)
      (nCount S pc - rCount S pc L) t3 := Or.inl (by omega)
  have hlex : Lex4 (nCount S₂ [x₂, a₂]) (nCount S₂ [x₂, a₂] - rCount S₂ [x₂, a₂] L) false
      (nCount S pc) (nCount S pc - rCount S pc L) t3 := by
    rcases hpos₁ with h | h
    · exact Or.inl (by omega)
    · by_cases h0 : nCount S₁ pc = 0
      · right; refine ⟨by omega, Or.inr ⟨by omega, rfl, h⟩⟩
      · exact Or.inl (by omega)
  have hpcc : pcList t3 x a c₁ = pc := by
    cases t3
    · rfl
    · rw [hc₁ rfl]
  have hB1 := ih H S₁ x P₁ a c₁ L g t3 hNT₁ hh₁ (by rw [hpcc]; exact hlex₁)
    (by rw [hpcc]; exact hne₁)
    (fun ⟨ht, u, hu, h⟩ => hexc ⟨ht, u, hS₁ hu, by rw [← hc₁ ht]; exact h⟩)
  rw [hpcc] at hB1
  -- extensions to the free side
  set n₂ := nCount S₂ [x₂, a₂]
  set r₂ := rCount S₂ [x₂, a₂] L
  have hM : ∀ f₁ ∈ ExtSet H S₁ pc L g, minM8 n₂ r₂ ≤ (ExtSet H S₂ [x₂, a₂] L f₁).ncard := by
    intro f₁ hf₁
    apply minM8_le
    have hh₂ : Thm4Hyp H S₂ x₂ P₂ a₂ c₂ L f₁ false := by
      refine ⟨hhead₂, hlast₂, htwo₂, hf₁.2.2 x₂ hx₂ a₂ ha₂ hxa₂, by simp, by simp, ?_, h5₂⟩
      intro y hy hyn
      exact h3₂ y hy (fun e => hyn (by rw [hpc2, e]; simp))
    obtain ⟨a', rest, hrest⟩ : ∃ a' rest, P₂ = a' :: rest := List.exists_cons_of_ne_nil (by
      intro h; rw [h] at htwo₂; simp at htwo₂)
    have ha' : a' = a₂ := by rw [hrest] at hhead₂; simpa using hhead₂
    subst ha'
    have hNT₂' : T.NT H S₂ (x₂ :: a' :: rest) := hrest ▸ hNT₂
    obtain ⟨f, hfx, hfa, hfL, hfp⟩ := T.thm1 H _ S₂ rfl x₂ a' rest hNT₂' L f₁
      (hf₁.2.2 x₂ hx₂ a' ha₂ hxa₂)
      (fun v hv => h3₂ v (by rw [hrest]; exact List.mem_cons_of_mem _ hv) (by
        intro e; subst e
        exact (List.nodup_cons.mp (List.nodup_cons.mp (T.nodup hNT₂')).2).1 hv))
      (fun v hv hvc => h5₂ v hv (by rw [hrest]; exact hvc))
    have hne₂ : (ExtSet H S₂ [x₂, a'] L f₁).Nonempty := extSet_nonempty_iff.mpr ⟨f, by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hfx
      · exact hfa, fun v hv hvc => hfL v hv (fun e => hvc (by simp [e]))
        (fun e => hvc (by simp [e])), hfp⟩
    have := ih H S₂ x₂ P₂ a' c₂ L f₁ false hNT₂ hh₂ (by rw [hpc2]; exact hlex)
      (by rw [hpc2]; exact hne₂)
      (fun h => by simp [Exc4] at h)
    rwa [hpc2] at this
  have hglue := ncard_extSet_glue (H := H) (S := S) (S₁ := S₁) (S₂ := S₂) (c := pc) (c₁ := pc)
    (c₂ := [x₂, a₂]) (L := L) (f₀ := g) (minM8 n₂ r₂) hU hX
    (fun z h1 h2 => by rcases hI z h1 h2 with e | e <;> simp [e])
    (fun z hz => ⟨fun _ => hz, fun h2 => by rcases hpc z hz h2 with e | e <;> simp [e]⟩)
    (fun z hz hn => absurd (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hx₂
      · exact ha₂) hn)
    (fun z hz _ hzc => absurd hz hzc) hM
  rw [hn, hr]
  exact bound4_mono (bound4_mul hB1 (minM8_spec n₂ r₂)) hglue

end NTCalc

end ThomassenManyColourings
