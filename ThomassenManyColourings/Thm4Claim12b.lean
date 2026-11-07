/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2F

/-!
# Theorem 4: Claim 12 with a bonus

In the situation of Claim 12, if `u` is joined to `v_i, v_j` but not to some vertex between them,
and has no other neighbour on the outer path, then `G` has at least `2^{(n+1)/9 - r/3}` colourings
(`thm4_claim12_bonus`): if the inside is a generalized wheel, Lemma 1 lets every colouring of the
outside extend, and the inside contributes `n₂ + 1 ≤ 3 r₂`; otherwise five instances of the
outside with four colours at `u` give a factor `5/4 > 2^{1/9}`. This is the step of Subcase 2.2 of
the paper with `u_{q-1}` not joined to `v_{k-2}`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- `5 M ≤ 4 N` turns `2^{n/9 - r/3} ≤ M` into `2^{(n+1)/9 - r/3} ≤ N` (`5/4 > 2^{1/9}`). -/
theorem bound4_succ_of_five_fourths {M N n r : ℕ} (hM : 2 ^ n ≤ M ^ 9 * 8 ^ r)
    (h : 5 * M ≤ 4 * N) : Bound4 N (n + 1) r := by
  have h1 : (5 * M) ^ 9 ≤ (4 * N) ^ 9 := Nat.pow_le_pow_left h 9
  rw [mul_pow, mul_pow] at h1
  have h2 : 2 * M ^ 9 ≤ N ^ 9 := by
    have h3 : 4 ^ 9 * (2 * M ^ 9) ≤ 4 ^ 9 * N ^ 9 := by
      calc 4 ^ 9 * (2 * M ^ 9) = 524288 * M ^ 9 := by ring
        _ ≤ 1953125 * M ^ 9 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 5 ^ 9 * M ^ 9 := by norm_num
        _ ≤ 4 ^ 9 * N ^ 9 := h1
    exact Nat.le_of_mul_le_mul_left h3 (by norm_num)
  unfold Bound4
  calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    _ ≤ 2 * (M ^ 9 * 8 ^ r) := Nat.mul_le_mul_left _ hM
    _ = 2 * M ^ 9 * 8 ^ r := by ring
    _ ≤ N ^ 9 * 8 ^ r := Nat.mul_le_mul_right _ h2

omit [DecidableEq V] in
/-- Double counting: colourings of the five restricted instances are colourings of `G`, each
counted at most four times. -/
theorem five_mul_le_four_mul {E : Finset (V → C)} {u : V} (L₅ : Finset C) (hL₅ : L₅.card = 5)
    (A : C → Finset (V → C)) (hA : ∀ β ∈ L₅, A β ⊆ E)
    (hmem : ∀ β ∈ L₅, ∀ f ∈ A β, f u ∈ L₅ ∧ f u ≠ β) (M : ℕ)
    (hM : ∀ β ∈ L₅, M ≤ (A β).card) : 5 * M ≤ 4 * E.card := by
  classical
  have h1 : 5 * M ≤ ∑ β ∈ L₅, (A β).card := by
    rw [← hL₅, ← smul_eq_mul]; exact Finset.card_nsmul_le_sum _ _ _ hM
  have h2 : ∑ β ∈ L₅, (A β).card = ∑ f ∈ E, (L₅.filter (fun β => f ∈ A β)).card := by
    have : ∀ β ∈ L₅, (A β).card = ∑ f ∈ E, if f ∈ A β then 1 else 0 := by
      intro β hβ
      rw [← Finset.card_filter]
      congr 1
      ext f
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hA β hβ h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Finset.card_filter]
  have h3 : ∀ f ∈ E, (L₅.filter (fun β => f ∈ A β)).card ≤ 4 := by
    intro f _
    by_cases hf : f u ∈ L₅
    · have hsub : L₅.filter (fun β => f ∈ A β) ⊆ L₅.erase (f u) := by
        intro β hβ
        simp only [Finset.mem_filter] at hβ
        exact Finset.mem_erase.mpr ⟨(hmem β hβ.1 f hβ.2).2.symm, hβ.1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hf, hL₅] at this; omega
    · have : L₅.filter (fun β => f ∈ A β) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro β hβ hfA
        exact hf (hmem β hβ f hfA).1
      rw [this]; simp
  calc 5 * M ≤ ∑ f ∈ E, (L₅.filter (fun β => f ∈ A β)).card := h2 ▸ h1
    _ ≤ ∑ _f ∈ E, 4 := Finset.sum_le_sum h3
    _ = 4 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

omit [DecidableEq V] in
/-- Two vertices on either side of a nonempty block of a repetition-free list are not
consecutive. -/
theorem ConsecIn.not_across {X M Y : List V} {y z : V} (hnd : (X ++ M ++ Y).Nodup)
    (hM : M ≠ []) (hy : y ∈ X) (hz : z ∈ Y) : ¬ ConsecIn (X ++ M ++ Y) y z := by
  intro h
  classical
  obtain ⟨X₁, X₂, rfl⟩ := List.append_of_mem hy
  have e : X₁ ++ y :: X₂ ++ M ++ Y = X₁ ++ y :: (X₂ ++ M ++ Y) := by simp
  rw [e] at h hnd
  have hdis := List.nodup_append.mp (show ((X₁ ++ y :: X₂) ++ (M ++ Y)).Nodup by simpa using hnd)
  rcases ConsecIn.nbr hnd h with h' | h'
  · exact hdis.2.2 z (by simp [List.mem_of_mem_getLast? h']) z (by simp [hz]) rfl
  · rcases X₂ with _ | ⟨x₂, X₂'⟩
    · obtain ⟨m, M', rfl⟩ := List.exists_cons_of_ne_nil hM
      simp only [List.nil_append, List.cons_append, List.head?_cons, Option.some.injEq] at h'
      have hMY := (List.nodup_append.mp hdis.2.1)
      exact hMY.2.2 m (by simp) m (by rw [h']; simp [hz]) rfl
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h'
      exact hdis.2.2 z (by simp [← h']) z (by simp [hz]) rfl

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 64000000 in
/-- **Claim 12 with a bonus**: a vertex `u` joined to `v_i, v_j` and not to some vertex between
them gives `2^{(n+1)/9 - r/3}` colourings. -/
theorem thm4_claim12_bonus (H : SimpleGraph V) {S : Finset V} {x u vi vj : V} {P₀ M P₁ : List V}
    {a c : V} {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (P₀ ++ vi :: (M ++ vj :: P₁))))
    (hh : Thm4Hyp H S x (P₀ ++ vi :: (M ++ vj :: P₁)) a c L g true) (hM : M ≠ [])
    (huS : u ∈ S) (hu : u ∉ x :: (P₀ ++ vi :: (M ++ vj :: P₁)))
    (hui : H.Adj u vi) (huj : H.Adj u vj)
    (hPc : ∀ y z, y ∈ P₀ ++ vi :: (M ++ vj :: P₁) → z ∈ P₀ ++ vi :: (M ++ vj :: P₁) →
      H.Adj y z → ConsecIn (P₀ ++ vi :: (M ++ vj :: P₁)) y z)
    (hQc : ∀ y z, y ∈ vi :: (M ++ [vj]) → z ∈ vi :: (M ++ [vj]) → H.Adj y z →
      ConsecIn (vi :: (M ++ [vj])) y z)
    (h3M : ∀ y ∈ M, (L y).card = 3)
    (hN : T.NoSepTri H S (x :: (P₀ ++ vi :: (M ++ vj :: P₁))))
    (hhub : ¬ (H.Adj u c ∧ H.Adj u x ∧ H.Adj u a))
    (hnot : ∃ m ∈ M, ¬ H.Adj u m) (hexc : ¬ Exc4 H S x a c L g true)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Bound4 (ExtSet H S [c, x, a] L g).ncard (nCount S [c, x, a] + 1)
      (rCount S [c, x, a] L) := by
  classical
  -- cutting along `vi u vj`
  have hrot : T.NT H S (vi :: (M ++ vj :: (P₁ ++ x :: P₀))) := by
    have := T.rotate_append (A := x :: P₀) (B := vi :: (M ++ vj :: P₁)) (by simpa using hNT)
    simpa using this
  have hQnd0 : (vi :: (M ++ [vj])).Nodup := (T.nodup hrot).sublist (by simp)
  have hvivj : ¬ H.Adj vi vj := fun h =>
    ConsecIn.not_ends hM hQnd0 (hQc vi vj (by simp) (by simp) h)
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := vi) (y := vj) (u := u) (l₁ := M)
    (l₂ := P₁ ++ x :: P₀) hrot huS
    (by simp only [List.mem_cons, List.mem_append, not_or] at hu ⊢; tauto) hui huj hvivj
  have hInt : T.NT H S₁ (u :: (vi :: (M ++ [vj]))) := T.rotate_back (by simpa using h₁)
  have hExt : T.NT H S₂ (x :: (P₀ ++ vi :: u :: vj :: P₁)) := by
    have := T.rotate_append (A := vj :: P₁) (B := x :: (P₀ ++ [vi, u])) (by simpa using h₂)
    simpa using this
  have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = vi ∨ v = vj ∨ v = u := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : ∀ v ∈ S₁, v ∈ S := fun v hv => hU ▸ Finset.mem_union_left _ hv
  have hS₂ : ∀ v ∈ S₂, v ∈ S := fun v hv => hU ▸ Finset.mem_union_right _ hv
  -- repetition-freeness of the outer cycle
  have hnd := T.nodup hNT
  have hnd0 := List.nodup_cons.mp hnd
  have hA := List.nodup_append.mp hnd0.2
  have hB := List.nodup_cons.mp hA.2.1
  have hC := List.nodup_append.mp hB.2
  have hviM : vi ∉ M := fun h => hB.1 (List.mem_append_left _ h)
  have hvjM : vj ∉ M := fun h => hC.2.2 vj h vj (by simp) rfl
  have huM : u ∉ M := fun h => hu (by simp [h])
  have hxu : x ≠ u := fun h => hu (by simp [h])
  have haP : a ∈ P₀ ++ [vi] := by
    have := hh.head
    rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ [vi]) ++ (M ++ vj :: P₁) by simp,
      List.head?_append_of_ne_nil _ (by simp)] at this
    exact List.mem_of_mem_head? this
  have hcP : c ∈ vj :: P₁ := by
    have := hh.last
    rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ vi :: M) ++ (vj :: P₁) by simp,
      List.getLast?_append_of_ne_nil _ (by simp)] at this
    exact List.mem_of_mem_getLast? this
  have hua : u ≠ a := fun h => hu (by
    rcases List.mem_append.mp haP with h' | h'
    · simp [h ▸ h']
    · simp at h'; simp [h, h'])
  have huc : u ≠ c := fun h => hu (by
    rcases List.mem_cons.mp hcP with h' | h'
    · simp [h, h']
    · simp [h ▸ h'])
  have hMside : ∀ m ∈ M, m ∈ S₁ ∧ m ∉ S₂ := by
    intro m hm
    have h1 : m ∈ S₁ := T.subset hInt m (by simp [hm])
    refine ⟨h1, fun h2 => ?_⟩
    rcases hmem m h1 h2 with rfl | rfl | rfl
    · exact hviM hm
    · exact hvjM hm
    · exact huM hm
  have hxS₂ : x ∈ S₂ := T.subset hExt x (by simp)
  have huS₂ : u ∈ S₂ := T.subset hExt u (by simp)
  have hviS₂ : vi ∈ S₂ := T.subset hExt vi (by simp)
  have hvjS₂ : vj ∈ S₂ := T.subset hExt vj (by simp)
  obtain ⟨m₀, hm₀⟩ := List.exists_mem_of_ne_nil M hM
  -- vertices of the inside off its outer cycle are interior vertices of `G`
  have hInt_out : ∀ w ∈ S₁, w ∉ u :: (vi :: (M ++ [vj])) →
      w ∉ x :: (P₀ ++ vi :: (M ++ vj :: P₁)) := by
    intro w hw hwc hwP
    by_cases hwM : w ∈ M
    · exact hwc (by simp [hwM])
    · have h2 : w ∈ S₂ := T.subset hExt w (by
        simp only [List.mem_cons, List.mem_append] at hwP ⊢; tauto)
      rcases hmem w hw h2 with rfl | rfl | rfl <;> simp at hwc
  have hExt_out : ∀ w ∈ S₂, w ∉ x :: (P₀ ++ vi :: u :: vj :: P₁) →
      w ∉ x :: (P₀ ++ vi :: (M ++ vj :: P₁)) := by
    intro w hw hwc hwP
    by_cases hwM : w ∈ M
    · exact (hMside w hwM).2 hw
    · apply hwc
      simp only [List.mem_cons, List.mem_append] at hwP ⊢; tauto
  have hQl : (vi :: (M ++ [vj])).getLast? = some vj := by
    rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  have hypInt : ∀ h : V → C, PathOK H u vi vj h →
      Thm3Hyp H S₁ u (vi :: (M ++ [vj])) vi vj L h := by
    intro h hok
    refine ⟨rfl, hQl, by simp, hok, ?_, ?_⟩
    · intro y hy hyi hyj
      have hyM : y ∈ M := by simp only [List.mem_cons, List.mem_append] at hy; tauto
      exact (h3M y hyM).ge
    · intro y hy hyc
      exact hh.five y (hS₁ y hy) (hInt_out y hy hyc)
  -- the inside is a region of `G`
  have hRegInt : Region H S (x :: (P₀ ++ vi :: (M ++ vj :: P₁))) S₁ (u :: (vi :: (M ++ [vj]))) := by
    refine (Region.refl H S _).piece (c₂ := x :: (P₀ ++ vi :: u :: vj :: P₁)) hU ?_ hX ?_
      (fun v hv => T.subset hExt v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
  -- facts on the outside
  have hxP1 : x ∉ P₀ ++ vi :: u :: vj :: P₁ := (List.nodup_cons.mp (T.nodup hExt)).1
  have hhead1 : (P₀ ++ vi :: u :: vj :: P₁).head? = some a := by
    have := hh.head
    rcases P₀ with _ | ⟨p, P₀'⟩ <;> simpa using this
  have hlast1 : (P₀ ++ vi :: u :: vj :: P₁).getLast? = some c := by
    have e1 : ∀ R : List V, (R ++ vj :: P₁).getLast? = (vj :: P₁).getLast? := fun R =>
      List.getLast?_append_of_ne_nil _ (by simp)
    have := hh.last
    rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ vi :: M) ++ vj :: P₁ by simp, e1] at this
    rw [show P₀ ++ vi :: u :: vj :: P₁ = (P₀ ++ [vi, u]) ++ vj :: P₁ by simp, e1]
    exact this
  have haS₂ : a ∈ S₂ := T.subset hExt a (List.mem_cons_of_mem _ (List.mem_of_mem_head? hhead1))
  have hcS₂ : c ∈ S₂ := T.subset hExt c (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hlast1))
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  -- a list at `u` of size other than three makes the outside not exceptional
  have hnoE : ∀ L₀ : V → Finset C, (L₀ u).card ≠ 3 →
      ¬ Exc3 H S₂ x (P₀ ++ vi :: u :: vj :: P₁) a c L₀ := by
    intro L₀ hL₀
    rintro ⟨P'', U, hGW, hnd'', hh'', hl'', hsub, -, hL⟩
    have hnu : ∀ y ∈ P'', y ≠ u := by
      intro y hy hyu
      have h3 := hL y hy (hyu ▸ hua) (hyu ▸ huc)
      rw [hyu] at h3
      exact hL₀ h3
    have hsubP : ∀ y ∈ P'', y ∈ P₀ ++ vi :: (M ++ vj :: P₁) := by
      intro y hy
      have h1 := hsub y hy
      have h2 := hnu y hy
      simp only [List.mem_cons, List.mem_append] at h1 ⊢; tauto
    have hPeq := path_eq_of_chordless _ _ hnd0.2 hnd'' hsubP (by rw [hh'', hh.head])
      (by rw [hl'', hh.last]) hGW.isPath hPc
    have hm : m₀ ∈ P'' := by rw [hPeq]; simp [hm₀]
    exact (hMside m₀ hm₀).2 (T.subset hExt m₀ (List.mem_cons_of_mem _ (hsub m₀ hm)))
  -- the outside as an instance, for any list changed only at `u` (keeping at least four colours)
  have hhyp1 : ∀ L₀ : V → Finset C, 4 ≤ (L₀ u).card → (∀ w, w ≠ u → L₀ w = L w) →
      Thm4Hyp H S₂ x (P₀ ++ vi :: u :: vj :: P₁) a c L₀ g true := by
    intro L₀ h4 hne
    refine ⟨hhead1, hlast1, by simp only [List.length_append, List.length_cons]; omega, hh.xa,
      hh.xc, hh.ac, ?_, ?_⟩
    · intro y hy hyn
      by_cases hyu : y = u
      · rw [hyu]; omega
      · rw [hne y hyu]
        exact hh.three y (by simp only [List.mem_cons, List.mem_append] at hy ⊢; tauto) hyn
    · intro y hy hyc
      have hyu : y ≠ u := fun h => hyc (by simp [h])
      rw [hne y hyu]
      exact hh.five y (hS₂ y hy) (hExt_out y hy hyc)
  have hne1 : ∀ L₀ : V → Finset C, 4 ≤ (L₀ u).card → (∀ w, w ≠ u → L₀ w = L w) →
      (ExtSet H S₂ [c, x, a] L₀ g).Nonempty := by
    intro L₀ h4 hne
    have hh' := hhyp1 L₀ h4 hne
    rcases T.thm3 H hExt ⟨hh'.head, hh'.last, hh'.two_le, ⟨hh.xa, hh.xc rfl, hh.ac rfl⟩,
        fun y hy hya hyc => hh'.three y hy (by
          show y ∉ [c, x, a]
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hyc, fun e => hxP1 (e ▸ hy), hya⟩), hh'.five⟩ with h | h
    · exact extSet_nonempty_iff.mpr h
    · exact absurd h (hnoE L₀ (by omega))
  have hnoX1 : ∀ L₀ : V → Finset C, (∀ w, w ≠ u → L₀ w = L w) → ¬ Exc4 H S₂ x a c L₀ g true := by
    intro L₀ hne
    rintro ⟨-, w, hw, hwn, h4, hwc, hwx, hwa, h1⟩
    by_cases hwu : w = u
    · rw [hwu] at hwc hwx hwa; exact hhub ⟨hwc, hwx, hwa⟩
    · rw [hne w hwu] at h4 h1
      exact hexc ⟨rfl, w, hS₂ w hw, hwn, h4, hwc, hwx, hwa, h1⟩
  -- counts
  have hU' : S₂ ∪ S₁ = S := by rw [Finset.union_comm]; exact hU
  have hI' : ∀ z ∈ S₂, z ∈ S₁ → z ∈ [vj, u, vi] := by
    intro z h2 h1
    rcases hmem z h1 h2 with e | e | e <;> simp [e]
  have hpc₂ : ∀ z ∈ [vj, u, vi], z ∈ S₂ := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with e | e | e <;> rw [e]
    · exact hvjS₂
    · exact huS₂
    · exact hviS₂
  have hpcI : ∀ z ∈ [c, x, a], z ∈ S₁ → z ∈ [vj, u, vi] := by
    intro z hz h1
    have h2 : z ∈ S₂ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with e | e | e <;> rw [e]
      · exact hcS₂
      · exact hxS₂
      · exact haS₂
    exact hI' z h2 h1
  have hnsplit : nCount S [c, x, a] = nCount S₂ [c, x, a] + nCount S₁ [vj, u, vi] :=
    nCount_split hU' hI' hpc₂ hpcI
  have hpos₂ : 1 ≤ nCount S₁ [vj, u, vi] := by
    unfold nCount
    refine Finset.card_pos.mpr ⟨m₀, Finset.mem_filter.mpr ⟨(hMside m₀ hm₀).1, ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hvjM (e ▸ hm₀), fun e => huM (e ▸ hm₀), fun e => hviM (e ▸ hm₀)⟩
  have hpos₁ : 1 ≤ nCount S₂ [c, x, a] := by
    unfold nCount
    refine Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨huS₂, ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨huc, fun e => hxu e.symm, hua⟩
  have hrL : ∀ L₀ : V → Finset C, 4 ≤ (L₀ u).card → (∀ w, w ≠ u → L₀ w = L w) →
      rCount S [c, x, a] L₀ = rCount S [c, x, a] L := by
    intro L₀ h4 hne
    unfold rCount
    congr 1
    apply Finset.filter_congr
    intro v _
    by_cases hvu : v = u
    · rw [hvu]
      constructor
      · rintro ⟨-, h⟩; omega
      · rintro ⟨-, h⟩; omega
    · rw [hne v hvu]
  have hokf : ∀ f₁ : V → C, IsProperOn H S₂ f₁ → PathOK H u vi vj f₁ := fun f₁ hf1p =>
    ⟨hf1p u huS₂ vi hviS₂ hui, hf1p u huS₂ vj hvjS₂ huj, fun h => hf1p vi hviS₂ vj hvjS₂ h⟩
  have hsubL : ∀ L₀ : V → Finset C, (∀ w, L₀ w ⊆ L w) →
      ExtSet H S [c, x, a] L₀ g ⊆ ExtSet H S [c, x, a] L g :=
    fun L₀ hsub f hf => ⟨hf.1, fun w hw hwc => hsub w (hf.2.1 w hw hwc), hf.2.2⟩
  have hglue1 : ∀ L₀ : V → Finset C, ∀ K : ℕ,
      (∀ f₁ ∈ ExtSet H S₂ [c, x, a] L₀ g, K ≤ (ExtSet H S₁ [vj, u, vi] L₀ f₁).ncard) →
      (ExtSet H S₂ [c, x, a] L₀ g).ncard * K ≤ (ExtSet H S [c, x, a] L₀ g).ncard :=
    fun L₀ K hK => ncard_extSet_glue (H := H) (S := S) (S₁ := S₂) (S₂ := S₁) (c := [c, x, a])
      (c₁ := [c, x, a]) (c₂ := [vj, u, vi]) (L := L₀) (f₀ := g) K hU'
      (fun p hp q hq hpq => (hX q hq p hp hpq.symm).symm) hI'
      (fun z hz => ⟨fun _ => hz, fun h1 => hpcI z hz h1⟩)
      (fun z hz h => absurd (hpc₂ z hz) h) (fun z hz _ h => absurd hz h) hK
  by_cases hE3 : Exc3 H S₁ u (vi :: (M ++ [vj])) vi vj L
  · -- the inside is a generalized wheel (not broken): Lemma 1
    obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := hE3
    have hQnd : (vi :: (M ++ [vj])).Nodup := (List.nodup_cons.mp (T.nodup hInt)).2
    have hPW : PW = vi :: (M ++ [vj]) :=
      path_eq_of_chordless _ _ hQnd hndW hsubW (by rw [hhW]; rfl) (by rw [hlW, hQl])
        hGW.isPath hQc
    subst hPW
    have hU0 : U ≠ ∅ := by
      intro hU0
      obtain ⟨m, hm, hnm⟩ := hnot
      exact hnm (hGW.broken_adj hU0 m (by simp [hm]))
    have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU0
    obtain ⟨hfill, hGW3⟩ := gw_fill hN hGW hInt hRegInt hUW
    have hBU := T.lemma1 H u _ _ U rfl hGW3 hUne S₁ vi vj rfl hQl hInt hfill hUW L
      (fun w hw => hh.five w (hS₁ w (hUW w hw).1) (hInt_out w (hUW w hw).1 (hUW w hw).2))
      (fun y hy hyi hyj => (h3M y (by
        simp only [List.mem_cons, List.mem_append] at hy; tauto)).ge)
    obtain ⟨col, hbad⟩ : ∃ col : C, ∀ h : V → C, PathOK H u vi vj h →
        ¬ Extends H S₁ [vj, u, vi] L h → h u = col := by
      by_cases hex : ∃ h₀ : V → C, PathOK H u vi vj h₀ ∧ ¬ Extends H S₁ [vj, u, vi] L h₀
      · obtain ⟨h₀, hok₀, hne₀⟩ := hex
        exact ⟨h₀ u, fun h hok hne => (hBU h h₀ hok hok₀ hne hne₀).1⟩
      · push Not at hex
        exact ⟨g u, fun h hok hne => absurd (hex h hok) hne⟩
    -- delete the bad colour and apply induction to the outside
    let L' : V → Finset C := fun w => if w = u then (L u).erase col else L w
    have hL'u : L' u = (L u).erase col := by simp [L']
    have hL'ne : ∀ w, w ≠ u → L' w = L w := fun w hw => by simp [L', hw]
    have h4u : 4 ≤ (L' u).card := by
      rw [hL'u]; have := Finset.pred_card_le_card_erase (s := L u) (a := col); omega
    have hL'sub : ∀ w, L' w ⊆ L w := by
      intro w; by_cases hw : w = u
      · rw [hw, hL'u]; exact Finset.erase_subset _ _
      · rw [hL'ne w hw]
    have hB1 : Bound4 (ExtSet H S₂ [c, x, a] L' g).ncard (nCount S₂ [c, x, a])
        (rCount S₂ [c, x, a] L') :=
      ih H S₂ x _ a c L' g true hExt (hhyp1 L' h4u hL'ne)
        (Or.inl (by show nCount S₂ [c, x, a] < nCount S [c, x, a]; omega))
        (hne1 L' h4u hL'ne) (hnoX1 L' hL'ne)
    -- every colouring of the outside extends to the inside
    have hone : ∀ f₁ ∈ ExtSet H S₂ [c, x, a] L' g, 1 ≤ (ExtSet H S₁ [vj, u, vi] L' f₁).ncard := by
      intro f₁ hf₁
      obtain ⟨-, hf1L, hf1p⟩ := hf₁
      have hfu : f₁ u ∈ (L u).erase col := by
        rw [← hL'u]
        exact hf1L u huS₂ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨huc, fun e => hxu e.symm, hua⟩)
      have hext : Extends H S₁ [vj, u, vi] L f₁ := by
        by_contra hne'
        exact Finset.ne_of_mem_erase hfu (hbad f₁ (hokf f₁ hf1p) hne')
      apply ncard_extSet_pos
      obtain ⟨f, hf⟩ := extSet_nonempty_iff.mpr hext
      refine ⟨f, hf.1, fun w hw hwc => ?_, hf.2.2⟩
      have hwu : w ≠ u := fun e => hwc (by simp [e])
      rw [hL'ne w hwu]; exact hf.2.1 w hw hwc
    have hN := (hglue1 L' 1 hone).trans
      (Set.ncard_le_ncard (hsubL L' hL'sub) (extSet_finite H S [c, x, a] L g))
    rw [mul_one] at hN
    -- counts of the inside
    have hMnd : M.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hQnd).2).1
    have hcU := hGW3.card_add_two_le
    simp only [List.length_cons, List.length_append, List.length_nil] at hcU
    have hn₂ : nCount S₁ [vj, u, vi] ≤ M.length + U.card := by
      unfold nCount
      calc (S₁.filter (· ∉ [vj, u, vi])).card ≤ (M.toFinset ∪ U).card := by
            apply Finset.card_le_card
            intro v hv
            simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
              not_or] at hv
            simp only [Finset.mem_union, List.mem_toFinset]
            rcases hfill v hv.1 with e | e | e
            · exact absurd e hv.2.2.1
            · left
              simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at e
              tauto
            · exact Or.inr e
        _ ≤ M.toFinset.card + U.card := Finset.card_union_le _ _
        _ = _ := by rw [List.toFinset_card_of_nodup hMnd]
    have hr₂ : M.length ≤ rCount S₁ [vj, u, vi] L' := by
      unfold rCount
      rw [← List.toFinset_card_of_nodup hMnd]
      apply Finset.card_le_card
      intro v hv
      rw [List.mem_toFinset] at hv
      simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨T.subset hInt v (by simp [hv]), ⟨fun e => hvjM (e ▸ hv), fun e => huM (e ▸ hv),
        fun e => hviM (e ▸ hv)⟩, ?_⟩
      rw [hL'ne v (fun e => huM (e ▸ hv))]; exact h3M v hv
    have hrsplit : rCount S [c, x, a] L' = rCount S₂ [c, x, a] L' + rCount S₁ [vj, u, vi] L' :=
      rCount_split L' hU' hI' hpc₂ hpcI
    have hr' := hrL L' h4u hL'ne
    have hMpos : 1 ≤ M.length := List.length_pos_iff.mpr hM
    exact bound4_gain hB1 hN (by omega)
  · -- otherwise: every colouring of the outside extends, and the `5/4` trick at `u`
    obtain ⟨F5, hF5sub, hF5card⟩ := Finset.exists_subset_card_eq (s := L u) (n := 5) h5u
    let Lδ : C → V → Finset C := fun δ w => if w = u then F5.erase δ else L w
    have hLδu : ∀ δ ∈ F5, (Lδ δ u).card = 4 := by
      intro δ hδ; simp only [Lδ, ite_true]; rw [Finset.card_erase_of_mem hδ, hF5card]
    have hLδne : ∀ δ, ∀ w, w ≠ u → Lδ δ w = L w := fun δ w hw => by simp [Lδ, hw]
    have hLδsub : ∀ δ w, Lδ δ w ⊆ L w := by
      intro δ w; by_cases hw : w = u
      · rw [hw]; simp only [Lδ, ite_true]; exact (Finset.erase_subset _ _).trans hF5sub
      · rw [hLδne δ w hw]
    -- the outside, with five colours at `u`
    have hrδ : ∀ δ ∈ F5, rCount S₂ [c, x, a] (Lδ δ) = rCount S₂ [c, x, a] L := by
      intro δ hδ
      unfold rCount
      congr 1
      apply Finset.filter_congr
      intro v _
      by_cases hvu : v = u
      · rw [hvu, hLδu δ hδ]
        constructor
        · rintro ⟨-, h⟩; omega
        · rintro ⟨-, h⟩; omega
      · rw [hLδne δ v hvu]
    set B := minM8 (nCount S₂ [c, x, a]) (rCount S₂ [c, x, a] L) with hBdef
    have hBδ : ∀ δ ∈ F5, B ≤ (ExtSet H S₂ [c, x, a] (Lδ δ) g).ncard := by
      intro δ hδ
      have h4 : 4 ≤ (Lδ δ u).card := (hLδu δ hδ).ge
      have := ih H S₂ x _ a c (Lδ δ) g true hExt (hhyp1 (Lδ δ) h4 (hLδne δ))
        (Or.inl (by show nCount S₂ [c, x, a] < nCount S [c, x, a]; omega))
        (hne1 (Lδ δ) h4 (hLδne δ)) (hnoX1 (Lδ δ) (hLδne δ))
      change Bound4 _ (nCount S₂ [c, x, a]) (rCount S₂ [c, x, a] (Lδ δ)) at this
      rw [hrδ δ hδ] at this
      exact minM8_le this
    have h54 : 5 * B ≤ 4 * (ExtSet H S₂ [c, x, a] L g).ncard := by
      have hfin := extSet_finite H S₂ [c, x, a] L g
      rw [Set.ncard_eq_toFinset_card _ hfin]
      refine five_mul_le_four_mul (u := u) F5 hF5card
        (fun δ => (extSet_finite H S₂ [c, x, a] (Lδ δ) g).toFinset) ?_ ?_ B ?_
      · intro δ _ f hf
        simp only [Set.Finite.mem_toFinset] at hf ⊢
        exact ⟨hf.1, fun w hw hwc => hLδsub δ w (hf.2.1 w hw hwc), hf.2.2⟩
      · intro δ _ f hf
        simp only [Set.Finite.mem_toFinset] at hf
        have := hf.2.1 u huS₂ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨huc, fun e => hxu e.symm, hua⟩)
        simp only [Lδ, ite_true, Finset.mem_erase] at this
        exact ⟨this.2, this.1⟩
      · intro δ hδ
        rw [← Set.ncard_eq_toFinset_card _ (extSet_finite H S₂ [c, x, a] (Lδ δ) g)]
        exact hBδ δ hδ
    have hB1 : Bound4 (ExtSet H S₂ [c, x, a] L g).ncard (nCount S₂ [c, x, a] + 1)
        (rCount S₂ [c, x, a] L) :=
      bound4_succ_of_five_fourths (minM8_spec _ _) h54
    -- induction on the inside, for every colouring of the outside
    have hM8 : ∀ f₁ ∈ ExtSet H S₂ [c, x, a] L g,
        minM8 (nCount S₁ [vj, u, vi]) (rCount S₁ [vj, u, vi] L) ≤
          (ExtSet H S₁ [vj, u, vi] L f₁).ncard := by
      intro f₁ hf₁
      obtain ⟨-, -, hf1p⟩ := hf₁
      have hext : Extends H S₁ [vj, u, vi] L f₁ := by
        rcases T.thm3 H hInt (hypInt f₁ (hokf f₁ hf1p)) with h | h
        · exact h
        · exact absurd h hE3
      have hh₂ : Thm4Hyp H S₁ u (vi :: (M ++ [vj])) vi vj L f₁ true := by
        have hok := hokf f₁ hf1p
        refine ⟨rfl, hQl, by simp, hok.1, fun _ => hok.2.1, fun _ h => hok.2.2 h, ?_, ?_⟩
        · intro y hy hyn
          change y ∉ [vj, u, vi] at hyn
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn
          have hyM : y ∈ M := by
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy; tauto
          exact (h3M y hyM).ge
        · intro y hy hyc
          exact hh.five y (hS₁ y hy) (hInt_out y hy hyc)
      have hnoX2 : ¬ Exc4 H S₁ u vi vj L f₁ true := by
        rintro ⟨-, w, hw, hwn, h4, -, -, -, -⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwn
        by_cases hwM : w ∈ M
        · rw [h3M w hwM] at h4; omega
        · have := hh.five w (hS₁ w hw) (hInt_out w hw (by
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
            exact ⟨hwn.2.1, hwn.2.2, hwM, hwn.1⟩))
          omega
      exact minM8_le (ih H S₁ u _ vi vj L f₁ true hInt hh₂
        (Or.inl (by show nCount S₁ [vj, u, vi] < nCount S [c, x, a]; omega))
        (extSet_nonempty_iff.mpr hext) hnoX2)
    have hglue := hglue1 L _ hM8
    have hB2 : Bound4 (minM8 (nCount S₁ [vj, u, vi]) (rCount S₁ [vj, u, vi] L))
        (nCount S₁ [vj, u, vi]) (rCount S₁ [vj, u, vi] L) := minM8_spec _ _
    have hrsplit : rCount S [c, x, a] L = rCount S₂ [c, x, a] L + rCount S₁ [vj, u, vi] L :=
      rCount_split L hU' hI' hpc₂ hpcI
    rw [hnsplit, hrsplit, show nCount S₂ [c, x, a] + nCount S₁ [vj, u, vi] + 1 =
      (nCount S₂ [c, x, a] + 1) + nCount S₁ [vj, u, vi] by ring]
    exact bound4_mono (bound4_mul hB1 hB2) hglue

end NTCalc

end ThomassenManyColourings
