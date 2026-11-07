/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Strip
public import ThomassenManyColourings.PathColour

/-!
# Theorem 4, Case 1: the neighbourhood of a vertex of `v₃ … v_{k-1}`

`Case1Hyp` bundles the situation after Claims 8–13: three precoloured vertices `c x a`, outer path
`a Q c` chordless with `|Q| ≥ 2`, no chord at `x`, three colours on `Q`, no separating triangle,
Claim 12 and no interior vertex joined to `c, x, a`.

* `q_nbhd`: deleting a vertex `q` of `Q` from `G` exposes its interior neighbours as a nonempty
  path `us` from (a neighbour of) its predecessor to (a neighbour of) its successor.
* `apex_unique`: an edge of the outer path has at most one interior common neighbour.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

/-- The situation of Case 1. -/
structure Case1Hyp (H : SimpleGraph V) (S : Finset V) (x a c : V) (Q : List V)
    (L : V → Finset C) (g : V → C) : Prop where
  nt : T.NT H S (x :: a :: (Q ++ [c]))
  hyp : Thm4Hyp H S x (a :: (Q ++ [c])) a c L g true
  two : 2 ≤ Q.length
  chordless : ∀ y z, y ∈ a :: (Q ++ [c]) → z ∈ a :: (Q ++ [c]) → H.Adj y z →
    ConsecIn (a :: (Q ++ [c])) y z
  xfree : ∀ q ∈ Q, ¬ H.Adj x q
  three : ∀ q ∈ Q, (L q).card = 3
  nosep : T.NoSepTri H S (x :: a :: (Q ++ [c]))
  c12 : C12 H S (x :: a :: (Q ++ [c])) (a :: (Q ++ [c]))
  nohub : ∀ u ∈ S, u ∉ x :: a :: (Q ++ [c]) → ¬ (H.Adj u c ∧ H.Adj u x ∧ H.Adj u a)

variable {T}

omit [DecidableEq C] in
/-- An outer edge `u v` of the path `a Q c` has at most one interior apex. -/
theorem Case1Hyp.apex_unique {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A B : List V} {u v : V}
    (hP : a :: (Q ++ [c]) = A ++ u :: v :: B) {w₁ w₂ : V} (h₁S : w₁ ∈ S) (h₂S : w₂ ∈ S)
    (h₁ : w₁ ∉ x :: a :: (Q ++ [c])) (h₂ : w₂ ∉ x :: a :: (Q ++ [c])) (h₁u : H.Adj w₁ u)
    (h₁v : H.Adj w₁ v) (h₂u : H.Adj w₂ u) (h₂v : H.Adj w₂ v) : w₁ = w₂ := by
  have hrot : T.NT H S (u :: v :: (B ++ x :: A)) := by
    have h0 : T.NT H S (x :: A ++ u :: v :: B) := by
      have := hc.nt; rw [hP] at this; simpa using this
    have := T.rotate_append (A := x :: A) (B := u :: v :: B) h0
    simpa using this
  have hcyc : ∀ y, y ∈ u :: v :: (B ++ x :: A) ↔ y ∈ x :: a :: (Q ++ [c]) := by
    intro y
    rw [show x :: a :: (Q ++ [c]) = x :: (A ++ u :: v :: B) by rw [← hP]]
    simp; tauto
  have hReg : Region H S (x :: a :: (Q ++ [c])) S (u :: v :: (B ++ x :: A)) :=
    ⟨subset_rfl, fun y _ hyc => ⟨fun h => hyc ((hcyc y).2 h), fun w hw _ => hw⟩⟩
  exact two_apex hc.nosep hrot hReg h₁S h₂S (fun h => h₁ ((hcyc _).1 h))
    (fun h => h₂ ((hcyc _).1 h)) h₁u h₁v h₂u h₂v

omit [DecidableEq C] in
set_option maxHeartbeats 8000000 in
/-- **The interior neighbours of a vertex `q` of `Q`** form a nonempty path `us` (in order) whose
first vertex is joined to the predecessor `p` of `q` and whose last vertex is joined to its
successor `s`. -/
theorem Case1Hyp.q_nbhd {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {D R : List V} {p q s : V}
    (hQ : a :: (Q ++ [c]) = D ++ p :: q :: s :: R) :
    ∃ us : List V, us ≠ [] ∧ us.Nodup ∧
      (∀ u ∈ us, u ∈ S ∧ u ∉ x :: a :: (Q ++ [c]) ∧ H.Adj q u) ∧
      (∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj q y → y ∈ us) ∧
      (∀ h ∈ us.head?, H.Adj h p) ∧ (∀ l ∈ us.getLast?, H.Adj l s) := by
  classical
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hPnd' : (D ++ p :: q :: s :: R).Nodup := hQ ▸ hPnd
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  -- `q` is a vertex of `Q`
  have hPnd'' : ((D ++ [p]) ++ q :: (s :: R)).Nodup := by simpa using hPnd'
  have haD : a ∈ D ++ [p] := by
    rcases D with _ | ⟨d, D'⟩
    · simp at hQ; simp [hQ.1]
    · simp at hQ; simp [hQ.1]
  have hcR : c ∈ s :: R := by
    have := congrArg List.getLast? hQ
    rw [show a :: (Q ++ [c]) = (a :: Q) ++ [c] by simp, List.getLast?_concat,
      show D ++ p :: q :: s :: R = (D ++ [p, q]) ++ (s :: R) by simp,
      List.getLast?_append_of_ne_nil _ (by simp)] at this
    exact List.mem_of_mem_getLast? this.symm
  have hqA : q ∉ D ++ [p] := fun h => (List.nodup_append.mp hPnd'').2.2 q h q (by simp) rfl
  have hqB : q ∉ s :: R := (List.nodup_cons.mp (List.nodup_append.mp hPnd'').2.1).1
  have hqQ : q ∈ Q := by
    have hq : q ∈ a :: (Q ++ [c]) := by rw [hQ]; simp
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h
    · exact absurd (by rw [h]; exact haD) hqA
    · exact h
    · exact absurd (by rw [h]; exact hcR) hqB
  -- rotate so that `q` comes first
  have hrot : T.NT H S (q :: (s :: R ++ x :: (D ++ [p]))) := by
    have := T.rotate_append (A := x :: (D ++ [p])) (B := q :: s :: R)
      (by rw [show x :: (D ++ [p]) ++ q :: s :: R = x :: (D ++ p :: q :: s :: R) by simp, ← hQ];
          exact hc.nt)
    simpa using this
  have hnbP : ∀ z ∈ D ++ p :: q :: s :: R, H.Adj q z → z = p ∨ z = s := by
    intro z hz hqz
    have := hc.chordless q z (by rw [hQ]; simp) (by rw [hQ]; exact hz) hqz
    rw [hQ, show D ++ p :: q :: s :: R = (D ++ [p]) ++ q :: (s :: R) by simp] at this
    rcases ConsecIn.nbr hPnd'' this with h | h
    · left; rw [List.getLast?_concat] at h; exact (Option.some.inj h).symm
    · right; exact (Option.some.inj h).symm
  obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp; omega) (by
    intro z hz hqz
    have hz' : z ∈ D ++ p :: q :: s :: R ∨ z = x := by
      simp only [List.mem_cons, List.mem_append] at hz ⊢; tauto
    rcases hz' with hz' | rfl
    · rcases hnbP z hz' hqz with h | h
      · right; rw [h, show s :: R ++ x :: (D ++ [p]) = (s :: R ++ x :: D) ++ [p] by simp,
          List.getLast?_concat]
      · left; rw [h]; rfl
    · exact absurd hqz.symm (hc.xfree q hqQ))
  have hcycm : ∀ y, y ∈ q :: (s :: R ++ x :: (D ++ [p])) ↔ y ∈ x :: a :: (Q ++ [c]) := by
    intro y
    rw [show x :: a :: (Q ++ [c]) = x :: (D ++ p :: q :: s :: R) by rw [← hQ]]
    simp; tauto
  -- the cycle after deleting `q`
  have hNT2 : T.NT H (S.erase q) ((s :: R ++ x :: D) ++ p :: us) := by simpa using hNT'
  refine ⟨us, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- otherwise `p s` would be a chord
    rintro rfl
    have h3 : T.NT H (S.erase q) ([] ++ p :: s :: (R ++ x :: D)) := by
      have := T.rotate_append (A := s :: R ++ x :: D) (B := [p]) (by simpa using hNT2)
      simpa using this
    have hps := T.adj_mid h3
    have := hc.chordless p s (by rw [hQ]; simp) (by rw [hQ]; simp) hps
    rw [hQ] at this
    exact ConsecIn.not_gap (A := D) (M := [q]) (B := R) (by simp) (by simpa using hPnd')
      (by simpa using this)
  · have := T.nodup hNT2
    exact (List.nodup_append.mp this).2.1.of_cons
  · intro u hu
    obtain ⟨huS, hun⟩ := hus u hu
    exact ⟨huS, fun h => hun ((hcycm u).2 h), (hadj u hu)⟩
  · intro y hyS hyn hqy
    rcases hnb y hyS hqy with h | h | h
    · exact absurd ((hcycm y).1 (by simp at h ⊢; tauto)) hyn
    · exfalso; apply hyn; apply (hcycm y).1
      have := List.mem_of_mem_getLast? h
      simp at this ⊢; tauto
    · exact h
  · intro h hh
    obtain ⟨us', rfl⟩ : ∃ us', us = h :: us' := by
      rcases us with _ | ⟨h', us'⟩
      · simp at hh
      · simp at hh; exact ⟨us', by rw [hh]⟩
    exact (T.adj_mid (A := s :: R ++ x :: D) (B := us') (by simpa using hNT2)).symm
  · intro l hl
    have hl' := eq_dropLast_append_of_getLast? (Option.mem_def.mp hl)
    have h3 : T.NT H (S.erase q) (us.dropLast ++ l :: s :: (R ++ x :: (D ++ [p]))) := by
      have := T.rotate_append (A := s :: R ++ x :: (D ++ [p])) (B := us)
        (by simpa using hNT2)
      rw [hl'] at this; simpa using this
    exact T.adj_mid h3

end NTCalc

end ThomassenManyColourings
