/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Hub

/-!
# Theorem 4, Claim 12: a vertex joined to `v_i, v_j` is joined to everything between

Cut along `v_i u v_j`. The inside has at most one bad colour `α` at `u` unless it is a broken wheel
(Lemma 1 after `gw_fill`; Theorem 3 if it is not a generalized wheel). Delete `α` from `L(u)`;
the outside has a colouring by Theorem 3 (its exception would be a path from `v₂` to `v_k` avoiding
`u`, impossible since the outer path is chordless) and the induction hypothesis applies to both
sides. The four-colour exception for the outside (`u` joined to `v_k, v₁, v₂`) is excluded by
`thm4_hub`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V]

/-- Splitting a filtered count along a separation `S = S₁ ∪ S₂` where the precoloured vertices of
the second side are the common vertices. -/
theorem filter_card_split {S S₁ S₂ : Finset V} {pc pc₂ : List V} (q : V → Prop) [DecidablePred q]
    (hU : S₁ ∪ S₂ = S) (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ pc₂) (hpc₂ : ∀ z ∈ pc₂, z ∈ S₁)
    (hpc : ∀ z ∈ pc, z ∈ S₂ → z ∈ pc₂) :
    (S.filter (fun v => v ∉ pc ∧ q v)).card =
      (S₁.filter (fun v => v ∉ pc ∧ q v)).card + (S₂.filter (fun v => v ∉ pc₂ ∧ q v)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hv, hvpc, hq⟩
      by_cases h1 : v ∈ S₁
      · exact Or.inl ⟨h1, hvpc, hq⟩
      · have h2 : v ∈ S₂ := (Finset.mem_union.mp (hU ▸ hv)).resolve_left h1
        exact Or.inr ⟨h2, fun h => h1 (hpc₂ v h), hq⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨hU ▸ Finset.mem_union_left _ h1, h2, h3⟩
      · exact ⟨hU ▸ Finset.mem_union_right _ h1, fun h => h2 (hpc v h h1), h3⟩
  · rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.1 (hI v h1.1 h2.1)

theorem nCount_split {S S₁ S₂ : Finset V} {pc pc₂ : List V}
    (hU : S₁ ∪ S₂ = S) (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ pc₂) (hpc₂ : ∀ z ∈ pc₂, z ∈ S₁)
    (hpc : ∀ z ∈ pc, z ∈ S₂ → z ∈ pc₂) :
    nCount S pc = nCount S₁ pc + nCount S₂ pc₂ := by
  unfold nCount
  simpa only [and_true] using filter_card_split (pc := pc) (pc₂ := pc₂) (fun _ : V => True)
    hU hI hpc₂ hpc

theorem rCount_split {C : Type*} {S S₁ S₂ : Finset V} {pc pc₂ : List V} (L : V → Finset C)
    (hU : S₁ ∪ S₂ = S) (hI : ∀ z ∈ S₁, z ∈ S₂ → z ∈ pc₂) (hpc₂ : ∀ z ∈ pc₂, z ∈ S₁)
    (hpc : ∀ z ∈ pc, z ∈ S₂ → z ∈ pc₂) :
    rCount S pc L = rCount S₁ pc L + rCount S₂ pc₂ L := by
  unfold rCount
  exact filter_card_split (fun v => (L v).card = 3) hU hI hpc₂ hpc

variable {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 16000000 in
/-- **Claim 12**, as a reduction: either the conclusion of Theorem 4 holds, or `u` is joined to
every vertex strictly between `v_i` and `v_j`. -/
theorem thm4_claim12 (H : SimpleGraph V) {S : Finset V} {x u vi vj : V} {P₀ M P₁ : List V}
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
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true ∨ ∀ m ∈ M, H.Adj u m := by
  classical
  -- cutting along `vi u vj`
  have hrot : T.NT H S (vi :: (M ++ vj :: (P₁ ++ x :: P₀))) := by
    have := T.rotate_append (A := x :: P₀) (B := vi :: (M ++ vj :: P₁)) (by simpa using hNT)
    simpa using this
  have hQnd0 : (vi :: (M ++ [vj])).Nodup := (T.nodup hrot).sublist
    (by simpa using List.Sublist.cons₂ vi (List.Sublist.append_left
      (List.singleton_sublist.mpr (List.mem_cons_self (a := vj) (l := P₁ ++ x :: P₀))) M))
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
  -- at most one bad colour at `u`, unless `u` is joined to all of `M`
  have hcol : (∀ m ∈ M, H.Adj u m) ∨ ∃ col : C, ∀ h : V → C, PathOK H u vi vj h →
      ¬ Extends H S₁ [vj, u, vi] L h → h u = col := by
    by_cases hE3 : Exc3 H S₁ u (vi :: (M ++ [vj])) vi vj L
    · obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := hE3
      have hQnd : (vi :: (M ++ [vj])).Nodup := (List.nodup_cons.mp (T.nodup hInt)).2
      have hPW : PW = vi :: (M ++ [vj]) :=
        path_eq_of_chordless _ _ hQnd hndW hsubW (by rw [hhW]; rfl) (by rw [hlW, hQl])
          hGW.isPath hQc
      subst hPW
      by_cases hU0 : U = ∅
      · left; intro m hm; exact hGW.broken_adj hU0 m (by simp [hm])
      · right
        have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU0
        obtain ⟨hfill, hGW3⟩ := gw_fill hN hGW hInt hRegInt hUW
        have hBU := T.lemma1 H u _ _ U rfl hGW3 hUne S₁ vi vj rfl hQl hInt hfill hUW L
          (fun w hw => hh.five w (hS₁ w (hUW w hw).1) (hInt_out w (hUW w hw).1 (hUW w hw).2))
          (fun y hy hyi hyj => (h3M y (by
            simp only [List.mem_cons, List.mem_append] at hy; tauto)).ge)
        by_cases hex : ∃ h₀ : V → C, PathOK H u vi vj h₀ ∧ ¬ Extends H S₁ [vj, u, vi] L h₀
        · obtain ⟨h₀, hok₀, hne₀⟩ := hex
          exact ⟨h₀ u, fun h hok hne => (hBU h h₀ hok hok₀ hne hne₀).1⟩
        · push Not at hex
          exact ⟨g u, fun h hok hne => absurd (hex h hok) hne⟩
    · right
      refine ⟨g u, fun h hok hne => ?_⟩
      exfalso
      rcases T.thm3 H hInt (hypInt h hok) with hE | hE
      · exact hne hE
      · exact hE3 hE
  rcases hcol with hall | ⟨col, hbad⟩
  · exact Or.inr hall
  left
  intro hne hexc
  show Bound4 (ExtSet H S [c, x, a] L g).ncard (nCount S [c, x, a]) (rCount S [c, x, a] L)
  -- delete the bad colour from `L u`
  let L' : V → Finset C := fun w => if w = u then (L u).erase col else L w
  have hL'u : L' u = (L u).erase col := by simp [L']
  have hL'ne : ∀ w, w ≠ u → L' w = L w := fun w hw => by simp [L', hw]
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  have h4u : 4 ≤ (L' u).card := by
    rw [hL'u]; have := Finset.pred_card_le_card_erase (s := L u) (a := col); omega
  have hL'sub : ∀ w, L' w ⊆ L w := by
    intro w
    by_cases hw : w = u
    · rw [hw, hL'u]; exact Finset.erase_subset _ _
    · rw [hL'ne w hw]
  -- the outside
  have hxP1 : x ∉ P₀ ++ vi :: u :: vj :: P₁ := (List.nodup_cons.mp (T.nodup hExt)).1
  have hh' : Thm4Hyp H S₂ x (P₀ ++ vi :: u :: vj :: P₁) a c L' g true := by
    refine ⟨?_, ?_, by simp only [List.length_append, List.length_cons]; omega, hh.xa, hh.xc,
      hh.ac, ?_, ?_⟩
    · have := hh.head
      rcases P₀ with _ | ⟨p, P₀'⟩ <;> simpa using this
    · have e1 : ∀ R : List V, (R ++ vj :: P₁).getLast? = (vj :: P₁).getLast? := fun R =>
        List.getLast?_append_of_ne_nil _ (by simp)
      have := hh.last
      rw [show P₀ ++ vi :: (M ++ vj :: P₁) = (P₀ ++ vi :: M) ++ vj :: P₁ by simp, e1] at this
      rw [show P₀ ++ vi :: u :: vj :: P₁ = (P₀ ++ [vi, u]) ++ vj :: P₁ by simp, e1]
      exact this
    · intro y hy hyn
      by_cases hyu : y = u
      · rw [hyu]; omega
      · rw [hL'ne y hyu]
        exact hh.three y (by simp only [List.mem_cons, List.mem_append] at hy ⊢; tauto) hyn
    · intro y hy hyc
      have hyu : y ≠ u := fun h => hyc (by simp [h])
      rw [hL'ne y hyu]
      exact hh.five y (hS₂ y hy) (hExt_out y hy hyc)
  have haS₂ : a ∈ S₂ := T.subset hExt a (List.mem_cons_of_mem _ (List.mem_of_mem_head? hh'.head))
  have hcS₂ : c ∈ S₂ := T.subset hExt c
    (List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hh'.last))
  have hh3' : Thm3Hyp H S₂ x (P₀ ++ vi :: u :: vj :: P₁) a c L' g :=
    ⟨hh'.head, hh'.last, hh'.two_le, ⟨hh.xa, hh.xc rfl, hh.ac rfl⟩,
      fun y hy hya hyc => hh'.three y hy (by
        show y ∉ [c, x, a]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hyc, fun e => hxP1 (e ▸ hy), hya⟩), hh'.five⟩
  have hnoE1 : ¬ Exc3 H S₂ x (P₀ ++ vi :: u :: vj :: P₁) a c L' := by
    rintro ⟨P'', U, hGW, hnd'', hh'', hl'', hsub, -, hL⟩
    have hnu : ∀ y ∈ P'', y ≠ u := by
      intro y hy hyu
      have h3 := hL y hy (hyu ▸ hua) (hyu ▸ huc)
      rw [hyu] at h3
      omega
    have hsubP : ∀ y ∈ P'', y ∈ P₀ ++ vi :: (M ++ vj :: P₁) := by
      intro y hy
      have h1 := hsub y hy
      have h2 := hnu y hy
      simp only [List.mem_cons, List.mem_append] at h1 ⊢; tauto
    have hPeq := path_eq_of_chordless _ _ hnd0.2 hnd'' hsubP (by rw [hh'', hh.head])
      (by rw [hl'', hh.last]) hGW.isPath hPc
    have hm : m₀ ∈ P'' := by rw [hPeq]; simp [hm₀]
    exact (hMside m₀ hm₀).2 (T.subset hExt m₀ (List.mem_cons_of_mem _ (hsub m₀ hm)))
  have hne1 : (ExtSet H S₂ [c, x, a] L' g).Nonempty := by
    rcases T.thm3 H hExt hh3' with h | h
    · exact extSet_nonempty_iff.mpr h
    · exact absurd h hnoE1
  have hnoX1 : ¬ Exc4 H S₂ x a c L' g true := by
    rintro ⟨-, w, hw, hwn, h4, hwc, hwx, hwa, h1⟩
    by_cases hwu : w = u
    · rw [hwu] at hwc hwx hwa; exact hhub ⟨hwc, hwx, hwa⟩
    · rw [hL'ne w hwu] at h4 h1
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
  have hrsplit : rCount S [c, x, a] L' = rCount S₂ [c, x, a] L' + rCount S₁ [vj, u, vi] L' :=
    rCount_split L' hU' hI' hpc₂ hpcI
  have hr' : rCount S [c, x, a] L' = rCount S [c, x, a] L := by
    unfold rCount
    congr 1
    apply Finset.filter_congr
    intro v _
    by_cases hvu : v = u
    · rw [hvu]
      constructor
      · rintro ⟨-, h⟩; omega
      · rintro ⟨-, h⟩; omega
    · rw [hL'ne v hvu]
  have hpos₁ : 1 ≤ nCount S₂ [c, x, a] := by
    unfold nCount
    refine Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨huS₂, ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨huc, fun e => hxu e.symm, hua⟩
  have hpos₂ : 1 ≤ nCount S₁ [vj, u, vi] := by
    unfold nCount
    refine Finset.card_pos.mpr ⟨m₀, Finset.mem_filter.mpr ⟨(hMside m₀ hm₀).1, ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hvjM (e ▸ hm₀), fun e => huM (e ▸ hm₀), fun e => hviM (e ▸ hm₀)⟩
  -- induction on the outside
  have hB1 : Bound4 (ExtSet H S₂ [c, x, a] L' g).ncard (nCount S₂ [c, x, a])
      (rCount S₂ [c, x, a] L') :=
    ih H S₂ x _ a c L' g true hExt hh'
      (Or.inl (by show nCount S₂ [c, x, a] < nCount S [c, x, a]; omega)) hne1 hnoX1
  -- induction on the inside, for every colouring of the outside
  have hM8 : ∀ f₁ ∈ ExtSet H S₂ [c, x, a] L' g,
      minM8 (nCount S₁ [vj, u, vi]) (rCount S₁ [vj, u, vi] L') ≤
        (ExtSet H S₁ [vj, u, vi] L' f₁).ncard := by
    intro f₁ hf₁
    obtain ⟨-, hf1L, hf1p⟩ := hf₁
    have hfu : f₁ u ∈ (L u).erase col := by
      rw [← hL'u]
      exact hf1L u huS₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨huc, fun e => hxu e.symm, hua⟩)
    have hokf : PathOK H u vi vj f₁ :=
      ⟨hf1p u huS₂ vi hviS₂ hui, hf1p u huS₂ vj hvjS₂ huj, fun h => hf1p vi hviS₂ vj hvjS₂ h⟩
    have hext : Extends H S₁ [vj, u, vi] L f₁ := by
      by_contra hne'
      exact Finset.ne_of_mem_erase hfu (hbad f₁ hokf hne')
    have hne₂ : (ExtSet H S₁ [vj, u, vi] L' f₁).Nonempty := by
      obtain ⟨f, hf⟩ := extSet_nonempty_iff.mpr hext
      refine ⟨f, hf.1, fun w hw hwc => ?_, hf.2.2⟩
      have hwu : w ≠ u := fun e => hwc (by simp [e])
      rw [hL'ne w hwu]; exact hf.2.1 w hw hwc
    have hh₂ : Thm4Hyp H S₁ u (vi :: (M ++ [vj])) vi vj L' f₁ true := by
      refine ⟨rfl, hQl, by simp, hokf.1, fun _ => hokf.2.1, fun _ h => hokf.2.2 h, ?_, ?_⟩
      · intro y hy hyn
        change y ∉ [vj, u, vi] at hyn
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn
        have hyM : y ∈ M := by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy; tauto
        rw [hL'ne y hyn.2.1]; exact (h3M y hyM).ge
      · intro y hy hyc
        have hyu : y ≠ u := fun e => hyc (by simp [e])
        rw [hL'ne y hyu]
        exact hh.five y (hS₁ y hy) (hInt_out y hy hyc)
    have hnoX2 : ¬ Exc4 H S₁ u vi vj L' f₁ true := by
      rintro ⟨-, w, hw, hwn, h4, -, -, -, -⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwn
      rw [hL'ne w hwn.2.1] at h4
      by_cases hwM : w ∈ M
      · rw [h3M w hwM] at h4; omega
      · have := hh.five w (hS₁ w hw) (hInt_out w hw (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
          exact ⟨hwn.2.1, hwn.2.2, hwM, hwn.1⟩))
        omega
    exact minM8_le (ih H S₁ u _ vi vj L' f₁ true hInt hh₂
      (Or.inl (by show nCount S₁ [vj, u, vi] < nCount S [c, x, a]; omega)) hne₂ hnoX2)
  -- gluing
  have hglue := ncard_extSet_glue (H := H) (S := S) (S₁ := S₂) (S₂ := S₁) (c := [c, x, a])
    (c₁ := [c, x, a]) (c₂ := [vj, u, vi]) (L := L') (f₀ := g) _ hU'
    (fun p hp q hq hpq => (hX q hq p hp hpq.symm).symm) hI'
    (fun z hz => ⟨fun _ => hz, fun h1 => hpcI z hz h1⟩)
    (fun z hz h => absurd (hpc₂ z hz) h) (fun z hz _ h => absurd hz h) hM8
  have hsubL : ExtSet H S [c, x, a] L' g ⊆ ExtSet H S [c, x, a] L g :=
    fun f hf => ⟨hf.1, fun w hw hwc => hL'sub w (hf.2.1 w hw hwc), hf.2.2⟩
  have hle := Set.ncard_le_ncard hsubL (extSet_finite H S [c, x, a] L g)
  have hB2 : Bound4 (minM8 (nCount S₁ [vj, u, vi]) (rCount S₁ [vj, u, vi] L'))
      (nCount S₁ [vj, u, vi]) (rCount S₁ [vj, u, vi] L') := minM8_spec _ _
  rw [hnsplit, ← hr', hrsplit]
  exact bound4_mono (bound4_mul hB1 hB2) (hglue.trans hle)

end NTCalc

end ThomassenManyColourings
