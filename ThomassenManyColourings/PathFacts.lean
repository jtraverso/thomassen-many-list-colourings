/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Claim1

/-!
# Paths along a chordless outer path

A path through vertices of a chordless path `P`, with the same ends and no repetition, is `P`
itself. Generalized wheels have a path as outer path, and broken wheels are fans.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V]

/-- `y, z` are consecutive in the list. -/
def ConsecIn : List V → V → V → Prop
  | a :: b :: l, y, z => (y = a ∧ z = b) ∨ (y = b ∧ z = a) ∨ ConsecIn (b :: l) y z
  | _, _, _ => False

theorem ConsecIn.mem : ∀ {l : List V} {y z : V}, ConsecIn l y z → y ∈ l ∧ z ∈ l
  | [], _, _, h => by simp [ConsecIn] at h
  | [_], _, _, h => by simp [ConsecIn] at h
  | a :: b :: l, y, z, h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · simp
    · simp
    · have := ConsecIn.mem h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

/-- The ends of a repetition-free list with a vertex between them are not consecutive. -/
theorem ConsecIn.not_ends {y z : V} {M : List V} (hM : M ≠ []) (hnd : (y :: (M ++ [z])).Nodup) :
    ¬ ConsecIn (y :: (M ++ [z])) y z := by
  obtain ⟨m, M', rfl⟩ := List.exists_cons_of_ne_nil hM
  have hy := (List.nodup_cons.mp hnd).1
  have hm := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  intro h
  rcases h with ⟨-, rfl⟩ | ⟨rfl, -⟩ | h
  · exact hm (by simp)
  · exact hy (by simp)
  · exact hy (by simpa using (ConsecIn.mem h).1)

/-- A repetition-free path with the ends of a chordless path `P` and vertices in `P` is `P`. -/
theorem path_eq_of_chordless {R : V → V → Prop} :
    ∀ (P Q : List V), P.Nodup → Q.Nodup → (∀ y ∈ Q, y ∈ P) → Q.head? = P.head? →
    Q.getLast? = P.getLast? → Q.IsChain R → (∀ y z, y ∈ P → z ∈ P → R y z → ConsecIn P y z) →
    Q = P
  | [], Q, _, _, _, hh, _, _, _ => by simpa using hh
  | [p], Q, _, hQ, hsub, hh, _, _, _ => by
    rcases Q with _ | ⟨q, Q'⟩
    · simp at hh
    · simp at hh; subst hh
      rcases Q' with _ | ⟨q', Q''⟩
      · rfl
      · have := hsub q' (by simp); simp at this; subst this; simp at hQ
  | p :: p₂ :: P'', Q, hP, hQ, hsub, hh, hl, hc, hR => by
    rcases Q with _ | ⟨q, Q'⟩
    · simp at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hpP : q ∉ p₂ :: P'' := (List.nodup_cons.mp hP).1
    rcases Q' with _ | ⟨q₂, Q''⟩
    · exfalso
      simp only [List.getLast?_singleton, List.getLast?_cons_cons] at hl
      exact hpP (List.mem_of_mem_getLast? hl.symm)
    have hR1 : R q q₂ := (List.isChain_cons_cons.mp hc).1
    have hq₂ : q₂ = p₂ := by
      rcases hR q q₂ (by simp) (hsub q₂ (by simp)) hR1 with ⟨-, h⟩ | ⟨h, -⟩ | h
      · exact h
      · exact absurd (h ▸ List.mem_cons_self) hpP
      · exact absurd h.mem.1 hpP
    subst q₂
    congr 1
    refine path_eq_of_chordless (p₂ :: P'') (p₂ :: Q'') (List.nodup_cons.mp hP).2
      (List.nodup_cons.mp hQ).2 ?_ rfl ?_ (List.isChain_cons_cons.mp hc).2 ?_
    · intro y hy
      rcases List.mem_cons.mp (hsub y (List.mem_cons_of_mem _ hy)) with h | h
      · subst h; exact absurd hy (List.nodup_cons.mp hQ).1
      · exact h
    · simpa [List.getLast?_cons_cons] using hl
    · intro y z hy hz hyz
      rcases hR y z (List.mem_cons_of_mem _ hy) (List.mem_cons_of_mem _ hz) hyz with
        ⟨rfl, -⟩ | ⟨-, rfl⟩ | h
      · exact absurd hy hpP
      · exact absurd hz hpP
      · exact h

section

variable {H : SimpleGraph V} {m : ℕ} {x : V}

theorem Block.isPath {P : List V} {U : Finset V} (h : Block H m x P U) : P.IsChain H.Adj := by
  cases h with
  | tri _ _ hab => simp [hab]
  | wheel _ _ hp => exact hp

/-- The outer path of a generalized wheel is a path of `H`. -/
theorem GW.isPath {P : List V} {U : Finset V} (h : GW H m x P U) : P.IsChain H.Adj := by
  induction h with
  | one hB => exact hB.isPath
  | cons hB _ ih => exact List.isChain_split.mpr ⟨hB.isPath, ih⟩

theorem Block.broken_adj {P : List V} {U : Finset V} (h : Block H m x P U) (hU : U = ∅) :
    ∀ y ∈ P, H.Adj x y := by
  cases h with
  | tri hxa hxb _ =>
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hxa
    · exact hxb
  | wheel => simp at hU

/-- A broken wheel is a fan: the major vertex is joined to every vertex of the path. -/
theorem GW.broken_adj {P : List V} {U : Finset V} (h : GW H m x P U) (hU : U = ∅) :
    ∀ y ∈ P, H.Adj x y := by
  induction h with
  | one hB => exact hB.broken_adj hU
  | @cons P Q b U₁ U₂ hB hrest ih =>
    have h1 : U₁ = ∅ := by
      have := Finset.union_eq_empty.mp hU; exact this.1
    have h2 : U₂ = ∅ := by
      have := Finset.union_eq_empty.mp hU; exact this.2
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hB.broken_adj h1 y (List.mem_append_left _ h)
    · exact ih h2 y h

end

end ThomassenManyColourings
