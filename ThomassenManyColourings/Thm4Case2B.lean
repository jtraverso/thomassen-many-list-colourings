/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2A

/-!
# Theorem 4, Case 2: extending through a fan, and Subcase 2.2a

`Case1Hyp.fan_extend`: a colouring of the region `G'` (outside the fan of `u`) extends to the inner
fan path `M = v_{m+1} … v_{k-1}` when `ColFrom (f u) (f v_m) (M.map L) (f c)` holds.

`Case1Hyp.case2_del` (Subcase 2.2a): if `|M| ≥ 2`, remove two colours `α, β` of
`L(v_{k-1}) \ {g c}` from `L(u)` and delete `M`; induction on `G'` (`n - |M|`, at most
`r - |M| + 1`) gives the bound.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable {T : NTCalc V}

omit [DecidableEq C] in
set_option maxHeartbeats 16000000 in
/-- **Extending through the fan.** -/
theorem Case1Hyp.fan_extend {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A M : List V}
    {vm u : V} (hP : a :: (Q ++ [c]) = A ++ vm :: (M ++ [c])) (hu : u ∉ x :: a :: (Q ++ [c]))
    (hnbM : ∀ v ∈ M, ∀ z ∈ S, H.Adj v z → z ∈ M ∨ z = u ∨ z = c ∨ z = vm)
    (φ : V → C) (hcol : ColFrom (φ u) (φ vm) (M.map L) (φ c)) :
    ∃ f : V → C, (∀ v, v ∉ M → f v = φ v) ∧ (∀ v ∈ M, f v ∈ L v) ∧
      ∀ v ∈ M, ∀ z ∈ S, H.Adj v z → f v ≠ f z := by
  classical
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hdec : a :: (Q ++ [c]) = A ++ (vm :: (M ++ [c])) ++ [] := by rw [hP]; simp
  have hPnd' := hdec ▸ hPnd
  have hMnd : M.Nodup := by
    have := (List.nodup_append.mp (List.nodup_append.mp hPnd').1).2.1
    exact (List.nodup_append.mp (List.nodup_cons.mp this).2).1
  have hvmM : vm ∉ M := by
    have := (List.nodup_append.mp (List.nodup_append.mp hPnd').1).2.1
    exact fun h => (List.nodup_cons.mp this).1 (List.mem_append_left _ h)
  have hcM : c ∉ M := by
    have := (List.nodup_append.mp (List.nodup_append.mp hPnd').1).2.1
    have := (List.nodup_append.mp (List.nodup_cons.mp this).2).2.2
    exact fun h => this c h c (by simp) rfl
  have huM : u ∉ M := fun h => hu (by rw [hP]; simp [h])
  obtain ⟨h, hh1, hh2⟩ := colFrom_realize L (φ u) M (φ vm) (φ c) hMnd hcol
  refine ⟨fun v => if v ∈ M then h v else φ v, fun v hv => by simp [hv], fun v hv => by
    simpa [hv] using (hh1 v hv).1, ?_⟩
  intro v hv z hzS hvz
  simp only [hv, ite_true]
  rcases hnbM v hv z hzS hvz with hz | rfl | rfl | rfl
  · -- `z` in the path: consecutive
    have hcons := hc.chordless v z (by rw [hP]; simp [hv]) (by rw [hP]; simp [hz]) hvz
    have hcons' := ConsecIn.infix (A := A) (Q := vm :: (M ++ [c])) (B := []) hPnd'
      (by simp [hv]) (by simp [hz]) (hdec ▸ hcons)
    have := chainNe_consec (f := fun v => if v ∈ M then h v else φ v) M vm c (φ vm) (φ c)
      (by simp [hvmM]) (by simp [hcM]) (fun b hb => by simp [hb]) hh2 v z hcons'
    simpa [hv, hz] using this
  · simp only [huM, ite_false]; exact (hh1 v hv).2
  · have hcons := hc.chordless v z (by rw [hP]; simp [hv]) (by simp) hvz
    have hcons' := ConsecIn.infix (A := A) (Q := vm :: (M ++ [z])) (B := []) hPnd'
      (by simp [hv]) (by simp) (hdec ▸ hcons)
    have := chainNe_consec (f := fun v => if v ∈ M then h v else φ v) M vm z (φ vm) (φ z)
      (by simp [hvmM]) (by simp [hcM]) (fun b hb => by simp [hb]) hh2 v z hcons'
    simpa [hv, hcM] using this
  · have hcons := hc.chordless v z (by rw [hP]; simp [hv]) (by rw [hP]; simp) hvz
    have hcons' := ConsecIn.infix (A := A) (Q := z :: (M ++ [c])) (B := []) hPnd'
      (by simp [hv]) (by simp) (hdec ▸ hcons)
    have := chainNe_consec (f := fun v => if v ∈ M then h v else φ v) M z c (φ z) (φ c)
      (by simp [hvmM]) (by simp [hcM]) (fun b hb => by simp [hb]) hh2 v z hcons'
    simpa [hv, hvmM] using this

end NTCalc

end ThomassenManyColourings
