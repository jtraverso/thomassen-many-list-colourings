/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim12

/-!
# Theorem 4, Claim 13: `k > 4`

If the outer cycle is `v₁ v₂ v₃ v₄` (`v₁ = x`, `v₂ = a`, `v₄ = c`), colour `v₃` as in some colouring
of `G`, delete it and apply induction: `n` and `r` drop by one (`v₃` has three colours), and the
new outer vertices (the interior neighbours of `v₃`) keep at least four colours. The four-colour
exception cannot occur since no interior vertex is joined to `v₄, v₁, v₂` (`thm4_hub`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

theorem bound4_step {N N' n n' r r' : ℕ} (h : Bound4 N' n' r') (hN : N' ≤ N) (hn : n = n' + 1)
    (hr : r' + 1 ≤ r) : Bound4 N n r := by
  unfold Bound4 at *
  subst hn
  calc 2 ^ (n' + 1) = 2 ^ n' * 2 := pow_succ _ _
    _ ≤ N' ^ 9 * 8 ^ r' * 2 := Nat.mul_le_mul_right _ h
    _ ≤ N ^ 9 * 8 ^ r' * 8 :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 9)) (by norm_num)
    _ = N ^ 9 * 8 ^ (r' + 1) := by rw [pow_succ]; ring
    _ ≤ N ^ 9 * 8 ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr)

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Claim 13**: Theorem 4 when the outer cycle has length four. -/
theorem thm4_claim13 (H : SimpleGraph V) {S : Finset V} {x a w c : V} {L : V → Finset C}
    {g : V → C}
    (hNT : T.NT H S [x, a, w, c]) (hh : Thm4Hyp H S x [a, w, c] a c L g true)
    (hxw : ¬ H.Adj x w) (hac : ¬ H.Adj a c) (hw3 : (L w).card = 3)
    (hhub : ∀ u ∈ S, u ∉ [x, a, w, c] → ¬ (H.Adj u c ∧ H.Adj u x ∧ H.Adj u a))
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hpc : pcList true x a c = [c, x, a] := rfl
  intro hne hexc
  rw [hpc] at hne ⊢
  have hnd := T.nodup hNT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hxa, hxw', hxc⟩, ⟨haw, hac'⟩, hwc, -⟩ := hnd
  have hwS : w ∈ S := T.subset hNT w (by simp)
  have hcS : c ∈ S := T.subset hNT c (by simp)
  have haS : a ∈ S := T.subset hNT a (by simp)
  have hwn : w ∉ [c, x, a] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hwc, fun e => hxw' e.symm, fun e => haw e.symm⟩
  obtain ⟨f, hf1, hf2, hf3⟩ := hne
  set β := f w with hβ
  have hβL : β ∈ L w := hf2 w hwS hwn
  set gβ := Function.update g w β with hgβ
  have gw : gβ w = β := Function.update_self ..
  have gne : ∀ v, v ≠ w → gβ v = g v := fun v hv => Function.update_of_ne hv ..
  have hfc : f c = g c := hf1 c (Or.inr (by simp))
  have hfa : f a = g a := hf1 a (Or.inr (by simp))
  have hwcadj : H.Adj w c := T.adj_cons (by simpa using T.rotate (T.rotate hNT))
  have hawadj : H.Adj a w := T.adj_cons (by simpa using T.rotate hNT)
  -- delete `w`
  have hrot : T.NT H S (w :: [c, x, a]) := by simpa using T.rotate (T.rotate hNT)
  obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp) (by
    intro z hz hwz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · left; rfl
    · exact absurd hwz.symm hxw
    · right; rfl)
  have h5 : ∀ y ∈ S, y ∉ [x, a, w, c] → 5 ≤ (L y).card := hh.five
  have hus5 : ∀ u ∈ us, 5 ≤ (L u).card := fun u hu =>
    h5 u (hus u hu).1 (fun h => (hus u hu).2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))
  have husne : us ≠ [] := by
    rintro rfl
    have h3 : T.NT H (S.erase w) [c, x, a] := by simpa using hNT'
    exact hac (T.adj_cons (by simpa using T.rotate (T.rotate h3)))
  let L' : V → Finset C := fun u => if H.Adj w u then (L u).erase β else L u
  have hL₁ : ∀ u, H.Adj w u → L' u = (L u).erase β := fun u h => by simp [L', h]
  have hL₂ : ∀ u, ¬ H.Adj w u → L' u = L u := fun u h => by simp [L', h]
  have hEq : ExtSet H S [w, c, x, a] L gβ = ExtSet H (S.erase w) [c, x, a] L' gβ := by
    refine extSet_erase_pc (by simp) hwS (fun z => ?_) ?_ ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨Or.inr (Or.inl rfl), Ne.symm hwc⟩
        · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hxw'⟩
        · exact ⟨Or.inr (Or.inr (Or.inr rfl)), haw⟩
      · rintro ⟨h | h | h | h, hne⟩
        · exact absurd h hne
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · intro u _ _ hwu; rw [hL₁ u hwu, gw]
    · intro u _ _ hwu; exact hL₂ u hwu
    · intro z hz hzS hwz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact absurd hwz (H.loopless.irrefl _)
      · rw [gw, gne z (Ne.symm hwc), ← hfc]; exact hf3 w hwS z hcS hwz
      · exact absurd hwz.symm hxw
      · rw [gw, gne z haw, ← hfa]; exact hf3 w hwS z haS hwz
  have hsub : ExtSet H S [w, c, x, a] L gβ ⊆ ExtSet H S [c, x, a] L g := by
    rintro f' ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, fun v hv hvn => ?_, h3⟩
    · have hvw : v ≠ w := by
        rintro rfl
        rcases hv with hv | hv
        · exact hv hwS
        · exact hwn hv
      rw [h1 v (by
        rcases hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (List.mem_cons_of_mem _ hv)), gne v hvw]
    · by_cases hvw : v = w
      · rw [hvw, h1 w (Or.inr (by simp)), gw]; exact hβL
      · exact h2 v hv (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn ⊢
          exact ⟨hvw, hvn⟩)
  have hfmem : f ∈ ExtSet H S [w, c, x, a] L gβ := by
    refine ⟨fun v hv => ?_, fun v hv hvn => hf2 v hv (fun h => hvn (List.mem_cons_of_mem _ h)),
      hf3⟩
    by_cases hvw : v = w
    · rw [hvw, gw]
    · rw [gne v hvw]
      refine hf1 v ?_
      rcases hv with hv | hv
      · exact Or.inl hv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
        rcases hv with h | h | h | h
        · exact absurd h hvw
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
  -- the new instance
  have hNT2 : T.NT H (S.erase w) (x :: (a :: (us ++ [c]))) := by
    simpa using T.rotate (show T.NT H (S.erase w) (c :: (x :: a :: us)) by simpa using hNT')
  have hh2 : Thm4Hyp H (S.erase w) x (a :: (us ++ [c])) a c L' gβ true := by
    refine ⟨rfl, getLast?_cons_append_singleton a c us, by simp, ?_, fun _ => ?_,
      fun _ h => ?_, ?_, ?_⟩
    · rw [gne x hxw', gne a haw]; exact hh.xa
    · rw [gne x hxw', gne c (Ne.symm hwc)]; exact hh.xc rfl
    · rw [gne a haw, gne c (Ne.symm hwc)]; exact hh.ac rfl h
    · intro y hy hyn
      change y ∉ [c, x, a] at hyn
      have hyu : y ∈ us := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at hy hyn
        tauto
      rw [hL₁ y (hadj y hyu)]
      have := Finset.pred_card_le_card_erase (s := L y) (a := β)
      have := hus5 y hyu; omega
    · intro y hy hyc
      have hyS := Finset.mem_of_mem_erase hy
      have hyw : y ≠ w := Finset.ne_of_mem_erase hy
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at hyc
      have hwy : ¬ H.Adj w y := by
        intro h
        rcases hnb y hyS h with e | e | e
        · simp at e; exact hyc.2.2.2 e.symm
        · simp at e; exact hyc.2.1 e.symm
        · exact hyc.2.2.1 e
      rw [hL₂ y hwy]
      exact h5 y hyS (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hyc.1, hyc.2.1, hyw, hyc.2.2.2⟩)
  have hn : nCount S [c, x, a] = nCount (S.erase w) [c, x, a] + 1 := by
    unfold nCount
    rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hwS, hwn⟩)]
    have : 1 ≤ (S.filter (· ∉ [c, x, a])).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwS, hwn⟩⟩
    omega
  have hr : rCount (S.erase w) [c, x, a] L' + 1 ≤ rCount S [c, x, a] L := by
    unfold rCount
    have hwF : w ∈ S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3) :=
      Finset.mem_filter.mpr ⟨hwS, hwn, hw3⟩
    have hsubF : (S.erase w).filter (fun v => v ∉ [c, x, a] ∧ (L' v).card = 3) ⊆
        (S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)).erase w := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_erase] at hv ⊢
      obtain ⟨⟨hvw, hvS⟩, hvn, h3⟩ := hv
      refine ⟨hvw, hvS, hvn, ?_⟩
      by_cases hwv : H.Adj w v
      · exfalso
        rcases hnb v hvS hwv with e | e | e
        · simp at e; exact hvn (by simp [e])
        · simp at e; exact hvn (by simp [e])
        · rw [hL₁ v hwv] at h3
          have := Finset.pred_card_le_card_erase (s := L v) (a := β)
          have := hus5 v e; omega
      · rwa [hL₂ v hwv] at h3
    have := Finset.card_le_card hsubF
    rw [Finset.card_erase_of_mem hwF] at this
    have : 1 ≤ (S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)).card :=
      Finset.card_pos.mpr ⟨w, hwF⟩
    omega
  have hne2 : (ExtSet H (S.erase w) [c, x, a] L' gβ).Nonempty := ⟨f, hEq ▸ hfmem⟩
  have hnoX : ¬ Exc4 H (S.erase w) x a c L' gβ true := by
    rintro ⟨-, u, hu, hun, -, huc, hux, hua, -⟩
    refine hhub u (Finset.mem_of_mem_erase hu) ?_ ⟨huc, hux, hua⟩
    have huw : u ≠ w := Finset.ne_of_mem_erase hu
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun ⊢
    exact ⟨hun.2.1, hun.2.2, huw, hun.1⟩
  have hB : Bound4 (ExtSet H (S.erase w) [c, x, a] L' gβ).ncard (nCount (S.erase w) [c, x, a])
      (rCount (S.erase w) [c, x, a] L') :=
    ih H (S.erase w) x _ a c L' gβ true hNT2 hh2
      (Or.inl (by show nCount (S.erase w) [c, x, a] < nCount S [c, x, a]; omega)) hne2 hnoX
  refine bound4_step hB ?_ hn hr
  rw [← hEq]
  exact Set.ncard_le_ncard hsub (extSet_finite H S [c, x, a] L g)

end NTCalc

end ThomassenManyColourings
