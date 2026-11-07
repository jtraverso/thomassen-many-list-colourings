/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim9w

/-!
# Theorem 4, Claim 9: chords at `v₁` with three precoloured vertices (dispatch)

A chord at `v₁`: to `v_{k-1}` (`thm4_claim9_w`), to `v₃` (the same after reversing the cycle), or
to another vertex (`thm4_claim9_x3`, the four-colour exception being excluded on both sides).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 16000000 in
/-- **Claim 9, chords at `v₁`, three precoloured vertices.** -/
theorem thm4_claim9_x (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: P)) (hh : Thm4Hyp H S x P a c L g true)
    (hPc : ∀ u v, u ∈ P → v ∈ P → H.Adj u v → ConsecIn P u v)
    (hN : T.NoSepTri H S (x :: P))
    (hchord : ∃ y ∈ P, H.Adj x y ∧ y ≠ a ∧ y ≠ c)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hnd := T.nodup hNT
  have hxP := (List.nodup_cons.mp hnd).1
  have hPnd := (List.nodup_cons.mp hnd).2
  obtain ⟨y, hyP, hxy, hya, hyc⟩ := hchord
  have hP3 : 3 ≤ P.length := by
    rcases P with _ | ⟨p, _ | ⟨q, _ | ⟨r, P'⟩⟩⟩
    · simp at hyP
    · have := hh.head; simp at this; subst this; simp at hyP; exact absurd hyP hya
    · have h1 := hh.head; have h2 := hh.last
      simp at h1 h2; subst h1; subst h2
      simp at hyP; rcases hyP with h | h
      · exact absurd h hya
      · exact absurd h hyc
    · simp
  -- the penultimate vertex `w` and the second vertex `v₃`
  obtain ⟨Q, w, c', hQ⟩ : ∃ Q w c', P = Q ++ [w, c'] := by
    obtain ⟨R, p, q, r, h⟩ := exists_append_three P hP3
    exact ⟨R ++ [p], q, r, by rw [h]; simp⟩
  have hc' : c' = c := by
    have := hh.last; rw [hQ] at this
    rw [show Q ++ [w, c'] = (Q ++ [w]) ++ [c'] by simp, List.getLast?_concat] at this
    simpa using this
  subst c'
  obtain ⟨v₃, R, hR⟩ : ∃ v₃ R, P = a :: v₃ :: R := by
    rcases P with _ | ⟨p, _ | ⟨q, R⟩⟩
    · simp at hP3
    · simp at hP3
    · have := hh.head; simp at this; subst this; exact ⟨q, R, rfl⟩
  have hQne : Q ≠ [] := by
    rintro rfl; simp at hQ; rw [hQ] at hP3; simp at hP3
  by_cases hxw : H.Adj x w
  · rw [hQ] at hNT hh hPc hN
    exact T.thm4_claim9_w H hNT hh hQne hxw hPc hN ih
  by_cases hxv : H.Adj x v₃
  · -- reverse the orientation
    apply thm4concl_swap
    obtain ⟨hNTr, hhr⟩ := T.thm4hyp_reverse hNT hh
    have hRr : P.reverse = R.reverse ++ [v₃, a] := by rw [hR]; simp
    have hRrne : R.reverse ≠ [] := by
      intro h
      rw [List.reverse_eq_nil_iff] at h
      rw [hR, h] at hP3; simp at hP3
    have hPcr : ∀ u v, u ∈ P.reverse → v ∈ P.reverse → H.Adj u v → ConsecIn P.reverse u v :=
      fun u v hu hv huv => (hPc u v (List.mem_reverse.mp hu) (List.mem_reverse.mp hv) huv).reverse
    have hcyc : ∀ v, v ∈ x :: P ↔ v ∈ x :: P.reverse := by intro v; simp
    have hNr := T.noSepTri_congr hcyc hN
    rw [hRr] at hNTr hhr hPcr hNr
    exact T.thm4_claim9_w H hNTr hhr hRrne hxv hPcr hNr (by
      rw [nCount_congr (pc3_swap x a c), rCount_congr (pc3_swap x a c)]; exact ih)
  -- a chord to a vertex other than `v₃, v_{k-1}`
  obtain ⟨P₀, P₁, hP01⟩ := List.append_of_mem hyP
  have hyv : y ≠ v₃ := fun e => hxv (e ▸ hxy)
  have hyw : y ≠ w := fun e => hxw (e ▸ hxy)
  have hP₀ : 2 ≤ P₀.length := by
    rcases P₀ with _ | ⟨p, _ | ⟨q, P₀'⟩⟩
    · rw [hR] at hP01; simp at hP01; exact absurd hP01.1.symm hya
    · rw [hR] at hP01; simp at hP01; exact absurd hP01.2.1.symm hyv
    · simp
  have hP₁ : 2 ≤ P₁.length := by
    rcases P₁.eq_nil_or_concat with h | ⟨P₁', z, h⟩
    · subst h
      rw [hQ] at hP01
      have := congrArg List.getLast? hP01
      rw [show Q ++ [w, c] = (Q ++ [w]) ++ [c] by simp, List.getLast?_concat,
        List.getLast?_concat] at this
      simp at this; exact absurd this.symm hyc
    · rcases P₁'.eq_nil_or_concat with h' | ⟨P₁'', z', h'⟩
      · subst h'; subst h
        rw [hQ] at hP01
        have := congrArg (fun l => l.reverse) hP01
        simp at this
        exact absurd this.2.1.symm hyw
      · subst h'; subst h; simp
  -- no four-colour exception on either side
  have h5 := hh.five
  have hno4₂ : ∀ u ∈ S, u ∉ [c, x, y] → (L u).card = 4 → H.Adj u c → H.Adj u x → H.Adj u y →
      False := by
    intro u hu hun h4 huc hux huy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
    by_cases huP : u ∈ P
    · have hcons := hPc u c huP (List.mem_of_mem_getLast? hh.last) huc
      rw [hQ, show Q ++ [w, c] = (Q ++ [w]) ++ c :: [] by simp] at hcons
      have hnd' : ((Q ++ [w]) ++ c :: []).Nodup := by rw [← show Q ++ [w, c] = (Q ++ [w]) ++ c :: [] by simp, ← hQ]; exact hPnd
      rcases ConsecIn.nbr hnd' hcons.symm with h | h
      · rw [List.getLast?_concat] at h; simp at h; exact hxw (h ▸ hux.symm)
      · simp at h
    · have := h5 u hu (by simp only [List.mem_cons, not_or]; exact ⟨hun.2.1, huP⟩); omega
  have hno4₁ : ∀ u ∈ S, u ∉ [a, x, y] → (L u).card = 4 → H.Adj u a → H.Adj u x → H.Adj u y →
      False := by
    intro u hu hun h4 hua hux huy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
    by_cases huP : u ∈ P
    · have hcons := hPc a u (List.mem_of_mem_head? hh.head) huP hua.symm
      rw [hR, show a :: v₃ :: R = [] ++ a :: (v₃ :: R) by simp] at hcons
      have hnd' : ([] ++ a :: (v₃ :: R)).Nodup := by simpa [← hR] using hPnd
      rcases ConsecIn.nbr hnd' hcons with h | h
      · simp at h
      · simp at h; exact hxv (h ▸ hux.symm)
    · have := h5 u hu (by simp only [List.mem_cons, not_or]; exact ⟨hun.2.1, huP⟩); omega
  rw [hP01] at hNT hh hPc hN
  exact T.thm4_claim9_x3 H hNT hh hP₀ hP₁ hxy hPc hN hno4₁ hno4₂ ih

end NTCalc

end ThomassenManyColourings
