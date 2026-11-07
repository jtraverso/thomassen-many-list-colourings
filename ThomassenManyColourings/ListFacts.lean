/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PathFacts

/-!
# Consecutive pairs in sublists

Consecutiveness in a repetition-free list restricts to contiguous sublists containing both
vertices and extends to larger lists; a predicate holding somewhere on a list has a last
occurrence.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*}

theorem ConsecIn.append_left : ∀ {A Q : List V} {y z : V}, ConsecIn Q y z → ConsecIn (A ++ Q) y z
  | [], _, _, _, h => h
  | p :: A, Q, y, z, h => by
    have ih := ConsecIn.append_left (A := A) h
    rcases hAQ : A ++ Q with _ | ⟨q, rest⟩
    · rw [hAQ] at ih; simp [ConsecIn] at ih
    · rw [hAQ] at ih
      show ConsecIn (p :: (A ++ Q)) y z
      rw [hAQ]
      exact Or.inr (Or.inr ih)

theorem ConsecIn.append_right : ∀ {Q B : List V} {y z : V}, ConsecIn Q y z → ConsecIn (Q ++ B) y z
  | [], _, _, _, h => by simp [ConsecIn] at h
  | [_], _, _, _, h => by simp [ConsecIn] at h
  | q :: q' :: Q, B, y, z, h => by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ConsecIn.append_right (Q := q' :: Q) h))

theorem ConsecIn.of_append_left : ∀ {A Q : List V} {y z : V}, (A ++ Q).Nodup → y ∈ Q → z ∈ Q →
    ConsecIn (A ++ Q) y z → ConsecIn Q y z
  | [], _, _, _, _, _, _, h => h
  | p :: A, Q, y, z, hnd, hy, hz, h => by
    have hpn : p ∉ A ++ Q := (List.nodup_cons.mp hnd).1
    have hpy : y ≠ p := fun e => hpn (List.mem_append_right _ (e ▸ hy))
    have hpz : z ≠ p := fun e => hpn (List.mem_append_right _ (e ▸ hz))
    rcases hAQ : A ++ Q with _ | ⟨q, rest⟩
    · exact absurd (List.mem_append_right A hy) (by rw [hAQ]; simp)
    · have h' : ConsecIn (p :: q :: rest) y z := by
        have : ConsecIn (p :: (A ++ Q)) y z := h
        rwa [hAQ] at this
      rcases h' with ⟨e1, -⟩ | ⟨-, e2⟩ | h''
      · exact absurd e1 hpy
      · exact absurd e2 hpz
      · exact ConsecIn.of_append_left (List.nodup_cons.mp hnd).2 hy hz (by rw [hAQ]; exact h'')

theorem ConsecIn.of_append_right [DecidableEq V] : ∀ {Q B : List V} {y z : V}, (Q ++ B).Nodup → y ∈ Q → z ∈ Q →
    ConsecIn (Q ++ B) y z → ConsecIn Q y z
  | [], _, _, _, _, hy, _, _ => by simp at hy
  | [q], B, y, z, hnd, hy, hz, h => by
    simp only [List.mem_singleton] at hy hz
    subst hy; subst hz
    exfalso
    rcases B with _ | ⟨b, B'⟩
    · simp [ConsecIn] at h
    · rcases h with ⟨-, e⟩ | ⟨e, -⟩ | h
      · subst e; simp at hnd
      · subst e; simp at hnd
      · exact (List.nodup_cons.mp hnd).1 (ConsecIn.mem h).1
  | q :: q' :: Q, B, y, z, hnd, hy, hz, h => by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hqn : q ∉ q' :: (Q ++ B) := (List.nodup_cons.mp hnd).1
      have hy' : y ∈ q' :: Q := by
        rcases List.mem_cons.mp hy with e | e
        · exact absurd (e ▸ (ConsecIn.mem h).1) hqn
        · exact e
      have hz' : z ∈ q' :: Q := by
        rcases List.mem_cons.mp hz with e | e
        · exact absurd (e ▸ (ConsecIn.mem h).2) hqn
        · exact e
      exact Or.inr (Or.inr (ConsecIn.of_append_right (Q := q' :: Q) (List.nodup_cons.mp hnd).2
        hy' hz' h))

/-- Consecutiveness restricts to a contiguous sublist. -/
theorem ConsecIn.infix [DecidableEq V] {A Q B : List V} {y z : V} (hnd : (A ++ Q ++ B).Nodup) (hy : y ∈ Q)
    (hz : z ∈ Q) (h : ConsecIn (A ++ Q ++ B) y z) : ConsecIn Q y z := by
  rw [List.append_assoc] at hnd h
  exact ConsecIn.of_append_right (List.nodup_append.mp hnd).2.1 hy hz
    (ConsecIn.of_append_left hnd (List.mem_append_left _ hy) (List.mem_append_left _ hz) h)

/-- Two vertices of a repetition-free list with a vertex between them are not consecutive. -/
theorem ConsecIn.not_gap [DecidableEq V] {A M B : List V} {y z : V} (hM : M ≠ [])
    (hnd : (A ++ y :: (M ++ z :: B)).Nodup) : ¬ ConsecIn (A ++ y :: (M ++ z :: B)) y z := by
  have e : A ++ y :: (M ++ z :: B) = A ++ (y :: (M ++ [z])) ++ B := by simp
  rw [e] at hnd ⊢
  intro h
  have hQnd : (y :: (M ++ [z])).Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  exact ConsecIn.not_ends hM hQnd (ConsecIn.infix hnd (by simp) (by simp) h)

/-- The last occurrence of a predicate on a list. -/
theorem exists_last_mem (p : V → Prop) : ∀ (l : List V), (∃ z ∈ l, p z) →
    ∃ A z B, l = A ++ z :: B ∧ p z ∧ ∀ y ∈ B, ¬ p y
  | [], h => by simp at h
  | y :: l, h => by
    by_cases h' : ∃ z ∈ l, p z
    · obtain ⟨A, z, B, rfl, hz, hB⟩ := exists_last_mem p l h'
      exact ⟨y :: A, z, B, rfl, hz, hB⟩
    · push Not at h'
      obtain ⟨z, hz, hpz⟩ := h
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact ⟨[], z, l, rfl, hpz, h'⟩
      · exact absurd hpz (h' z hz')

/-- A junction strictly inside a repetition-free list is neither its first nor its last
element. -/
theorem junction_inner [DecidableEq V] {P₁ Q₂ : List V} {b h l : V} (hnd : (P₁ ++ b :: Q₂).Nodup)
    (hP : P₁ ≠ []) (hQ : Q₂ ≠ []) (hh : (P₁ ++ b :: Q₂).head? = some h)
    (hl : (P₁ ++ b :: Q₂).getLast? = some l) : b ≠ h ∧ b ≠ l := by
  constructor
  · rintro rfl
    obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
    subst hh
    exact (List.nodup_append.mp hnd).2.2 p (by simp) p (by simp) rfl
  · rintro rfl
    rw [List.getLast?_append_of_ne_nil _ (by simp)] at hl
    obtain ⟨q, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
    rw [List.getLast?_cons_cons] at hl
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (List.mem_of_mem_getLast? hl)

theorem ConsecIn.reverse : ∀ {l : List V} {y z : V}, ConsecIn l y z → ConsecIn l.reverse y z
  | [], _, _, h => by simp [ConsecIn] at h
  | [_], _, _, h => by simp [ConsecIn] at h
  | a :: b :: l, y, z, h => by
    have e : (a :: b :: l).reverse = (b :: l).reverse ++ [a] := by simp
    have e2 : (b :: l).reverse ++ [a] = l.reverse ++ [b, a] := by simp
    rw [e]
    rcases h with h | h | h
    · rw [e2]; exact ConsecIn.append_left (Or.inr (Or.inl h))
    · rw [e2]; exact ConsecIn.append_left (Or.inl h)
    · exact ConsecIn.append_right (ConsecIn.reverse h)

theorem ConsecIn.symm : ∀ {l : List V} {y z : V}, ConsecIn l y z → ConsecIn l z y
  | [], _, _, h => by simp [ConsecIn] at h
  | [_], _, _, h => by simp [ConsecIn] at h
  | _ :: _ :: _, _, _, h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inr (ConsecIn.symm h))

end ThomassenManyColourings
