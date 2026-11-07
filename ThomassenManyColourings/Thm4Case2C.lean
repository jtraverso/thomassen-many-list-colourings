/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2B

/-!
# Theorem 4, Case 2: deleting the inner path of a fan (Subcase 2.2a)

`u` interior, joined to `v_m`, to every vertex of `M = v_{m+1} … v_{k-1}` (`|M| ≥ 2`) and to `c`,
and to no vertex before `v_m`. Remove two colours `α, β` of `L(v_{k-1}) \ {g c}` from `L(u)`,
delete `M`, and apply induction to the rest: `n` drops by `|M|` and `r` by at least `|M| - 1`.
If the rest is the exception of Theorem 3 (a generalized wheel), `n ≤ 3r` directly.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- Comparing exponents: `2^{n/9 - r/3} ≤ 2^{n'/9 - r'/3}`. -/
theorem bound4_gain {N N' n n' r r' : ℕ} (hB : Bound4 N' n' r') (hN : N' ≤ N)
    (h : n + 3 * r' ≤ n' + 3 * r) : Bound4 N n r := by
  unfold Bound4 at *
  have h8 : ∀ k, (8 : ℕ) ^ k = 2 ^ (3 * k) := fun k => by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  rw [h8] at hB ⊢
  have hpos : 0 < 2 ^ (3 * r') := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc 2 ^ n * 2 ^ (3 * r') = 2 ^ (n + 3 * r') := (pow_add _ _ _).symm
    _ ≤ 2 ^ (n' + 3 * r) := Nat.pow_le_pow_right (by norm_num) h
    _ = 2 ^ n' * 2 ^ (3 * r) := pow_add _ _ _
    _ ≤ (N' ^ 9 * 2 ^ (3 * r')) * 2 ^ (3 * r) := Nat.mul_le_mul_right _ hB
    _ = N' ^ 9 * 2 ^ (3 * r) * 2 ^ (3 * r') := by ring
    _ ≤ N ^ 9 * 2 ^ (3 * r) * 2 ^ (3 * r') :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 9))

namespace NTCalc

variable {T : NTCalc V}

set_option maxHeartbeats 64000000 in
/-- **Subcase 2.2a**: deleting the inner path of a fan with at least two vertices. -/
theorem Case1Hyp.case2_del {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A M : List V} {vm u : V}
    (hP : a :: (Q ++ [c]) = A ++ vm :: (M ++ [c])) (hM2 : 2 ≤ M.length) (huS : u ∈ S)
    (hu : u ∉ x :: a :: (Q ++ [c])) (hum : H.Adj u vm) (huM : ∀ q ∈ M, H.Adj u q)
    (huc : H.Adj u c) (hmin : ∀ q ∈ A, ¬ H.Adj u q)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  intro hne hexc
  show Bound4 (ExtSet H S [c, x, a] L g).ncard (nCount S [c, x, a]) (rCount S [c, x, a] L)
  have hh := hc.hyp
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  have hPnd' : (A ++ vm :: (M ++ [c])).Nodup := hP ▸ hPnd
  have hMne : M ≠ [] := by intro h; rw [h] at hM2; simp at hM2
  -- membership facts
  have hcQ : c ∉ Q := fun h => (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.2 c h c
    (by simp) rfl
  have haQ : a ∉ Q := fun h => (List.nodup_cons.mp hPnd).1 (List.mem_append_left _ h)
  have hxQ : x ∉ Q := fun h => hxP (by simp [h])
  have hPmem : ∀ v, v ∈ a :: (Q ++ [c]) ↔ v ∈ A ∨ v = vm ∨ v ∈ M ∨ v = c := by
    intro v; rw [hP]; simp
  have hinQ : ∀ v ∈ a :: (Q ++ [c]), v ≠ a → v ≠ c → v ∈ Q := by
    intro v hv hva hvc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    tauto
  have hMP : ∀ v ∈ M, v ∈ a :: (Q ++ [c]) := fun v hv => (hPmem v).2 (Or.inr (Or.inr (Or.inl hv)))
  have hMa : ∀ v ∈ M, v ≠ a := by
    intro v hv e
    have h2 := List.nodup_append.mp hPnd'
    have haA : a ∈ A ∨ a = vm := by
      rcases A with _ | ⟨a', A'⟩
      · simp at hP; right; exact hP.1
      · simp at hP; left; simp [hP.1]
    rcases haA with h | h
    · exact h2.2.2 a h a (by simp [← e, hv]) rfl
    · exact (List.nodup_cons.mp h2.2.1).1 (by rw [← h, ← e]; simp [hv])
  have hMc : ∀ v ∈ M, v ≠ c := by
    intro v hv e
    have h3 := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_append.mp hPnd').2.1).2
    exact h3.2.2 v hv c (by simp) e
  have hMQ : ∀ v ∈ M, v ∈ Q := fun v hv => hinQ v (hMP v hv) (hMa v hv) (hMc v hv)
  have huQ : u ∉ Q := fun h => hu (by simp [h])
  -- two colours of the last vertex of `M`
  set w := M.getLast hMne with hw
  have hwM : w ∈ M := List.getLast_mem hMne
  have hw3 : (L w).card = 3 := hc.three w (hMQ w hwM)
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.mp (show 1 < ((L w).erase (g c)).card by
    have := Finset.pred_card_le_card_erase (s := L w) (a := g c); omega)
  rw [Finset.mem_erase] at hα hβ
  set L' : V → Finset C := fun v => if v = u then ((L u).erase α).erase β else L v with hL'
  have hL'u : L' u = ((L u).erase α).erase β := by simp [hL']
  have hL'ne : ∀ v, v ≠ u → L' v = L v := fun v hv => by simp [hL', hv]
  have hL'sub : ∀ v, L' v ⊆ L v := by
    intro v; by_cases hv : v = u
    · rw [hv, hL'u]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    · rw [hL'ne v hv]
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  have h3u : 3 ≤ (L' u).card := by
    rw [hL'u]
    have := Finset.pred_card_le_card_erase (s := L u) (a := α)
    have := Finset.pred_card_le_card_erase (s := (L u).erase α) (a := β)
    omega
  -- cut off the fan
  obtain ⟨S₂, hNT₂, hS₂m, hR₂, hnbM⟩ := hc.fan_cut hP hMne huS hu hum huM huc
  set P' := A ++ [vm, u, c] with hP'
  have hhead' : P'.head? = some a := by
    rcases A with _ | ⟨a', A'⟩
    · simp at hP; simp [hP'] ; exact hP.1.symm
    · simp at hP; simp [hP', hP.1]
  have hlast' : P'.getLast? = some c := by simp [hP']
  have hP'mem : ∀ v, v ∈ x :: P' ↔ v = x ∨ v ∈ A ∨ v = vm ∨ v = u ∨ v = c := by
    intro v; simp [hP']
  have hS₂S : ∀ v ∈ S₂, v ∈ S := fun v hv => ((hS₂m v).1 hv).1
  -- the hypotheses of Theorem 4 for the rest
  have hh' : Thm4Hyp H S₂ x P' a c L' g true := by
    refine ⟨hhead', hlast', by simp [hP'], hh.xa, hh.xc, hh.ac, ?_, ?_⟩
    · intro y hy hyn
      change y ∉ [c, x, a] at hyn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn
      by_cases hyu : y = u
      · rw [hyu]; exact h3u
      · rw [hL'ne y hyu]
        have hyP : y ∈ a :: (Q ++ [c]) := by
          rw [hPmem]; simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hy
          tauto
        rw [hc.three y (hinQ y hyP hyn.2.2 hyn.1)]
    · intro y hy hyn
      have hyu : y ≠ u := fun e => hyn (by simp [hP', e])
      rw [hL'ne y hyu]
      exact hh.five y (hS₂S y hy) (hR₂.2 y hy hyn).1
  -- no exceptional vertex
  have hexc' : ¬ Exc4 H S₂ x a c L' g true := by
    rintro ⟨-, t, ht, htn, -, htc, htx, hta, -⟩
    by_cases htQ : t ∈ Q
    · exact hc.xfree t htQ htx.symm
    · refine hc.nohub t (hS₂S t ht) ?_ ⟨htc, htx, hta⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htn
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
      exact ⟨htn.2.1, htn.2.2, htQ, htn.1⟩
  -- counts
  have hn : nCount S [c, x, a] = nCount S₂ [c, x, a] + M.length := by
    have hMnd : M.Nodup := (List.nodup_append.mp (List.nodup_cons.mp
      (List.nodup_append.mp hPnd').2.1).2).1
    unfold nCount
    rw [← List.toFinset_card_of_nodup hMnd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_union, List.mem_toFinset, hS₂m]
      constructor
      · rintro ⟨hv, hvn⟩
        by_cases hvM : v ∈ M
        · exact Or.inr hvM
        · exact Or.inl ⟨⟨hv, hvM⟩, hvn⟩
      · rintro (⟨⟨hv, -⟩, hvn⟩ | hvM)
        · exact ⟨hv, hvn⟩
        · refine ⟨T.subset hc.nt v (List.mem_cons_of_mem _ (hMP v hvM)), ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hMc v hvM, fun e => hxQ (e ▸ hMQ v hvM), hMa v hvM⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter, hS₂m] at h1
      exact h1.1.2 (List.mem_toFinset.mp h2)
  have hr : rCount S₂ [c, x, a] L' + M.length ≤ rCount S [c, x, a] L + 1 := by
    have hMnd : M.Nodup := (List.nodup_append.mp (List.nodup_cons.mp
      (List.nodup_append.mp hPnd').2.1).2).1
    unfold rCount
    have hsub : S₂.filter (fun v => v ∉ [c, x, a] ∧ (L' v).card = 3) ⊆
        insert u ((S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)) \ M.toFinset) := by
      intro v hv
      simp only [Finset.mem_filter] at hv
      by_cases hvu : v = u
      · exact Finset.mem_insert.mpr (Or.inl hvu)
      · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
        · rw [hL'ne v hvu] at hv
          exact Finset.mem_filter.mpr ⟨hS₂S v hv.1, hv.2⟩
        · rw [List.mem_toFinset]; exact ((hS₂m v).1 hv.1).2
    have hMsub : M.toFinset ⊆ S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3) := by
      intro v hv
      rw [List.mem_toFinset] at hv
      simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨T.subset hc.nt v (List.mem_cons_of_mem _ (hMP v hv)),
        ⟨hMc v hv, fun e => hxQ (e ▸ hMQ v hv), hMa v hv⟩, hc.three v (hMQ v hv)⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le u ((S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)) \
      M.toFinset)
    have h3 := Finset.card_sdiff_add_card_eq_card hMsub
    rw [List.toFinset_card_of_nodup hMnd] at h3
    omega
  -- the rest has a colouring, or it is a generalized wheel and `n ≤ 3r`
  have hP'nd : P'.Nodup := (List.nodup_cons.mp (T.nodup hNT₂)).2
  have hxP' : x ∉ P' := (List.nodup_cons.mp (T.nodup hNT₂)).1
  have hrQ : Q.length ≤ rCount S [c, x, a] L := by
    unfold rCount
    rw [← List.toFinset_card_of_nodup (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).1]
    apply Finset.card_le_card
    intro v hv
    rw [List.mem_toFinset] at hv
    simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨T.subset hc.nt v (by simp [hv]), ⟨fun e => hcQ (e ▸ hv), fun e => hxQ (e ▸ hv),
      fun e => haQ (e ▸ hv)⟩, hc.three v hv⟩
  have hlenA : A.length + M.length = Q.length := by
    have := congrArg List.length hP; simp at this; omega
  rcases T.thm3 H hNT₂ ⟨hh'.head, hh'.last, hh'.two_le, ⟨hh'.xa, hh'.xc rfl, hh'.ac rfl⟩,
      fun y hy hya hyc => hh'.three y hy (by
        show y ∉ [c, x, a]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hyc, fun e => hxP' (e ▸ hy), hya⟩), hh'.five⟩ with hext | hE3
  swap
  · -- the exception: a generalized wheel on the whole outer path
    obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, -⟩ := hE3
    -- the outer path of the rest is chordless
    have hconsec : ∀ (B D : List V) (y z : V), ConsecIn (B ++ y :: z :: D) y z := by
      intro B D y z
      exact ConsecIn.append_left (Or.inl ⟨rfl, rfl⟩)
    have hPc' : ∀ y z, y ∈ P' → z ∈ P' → H.Adj y z → ConsecIn P' y z := by
      have key : ∀ y z, y ∈ P' → z ∈ P' → y ≠ u → z ≠ u → H.Adj y z → ConsecIn P' y z := by
        intro y z hy hz hyu hzu hyz
        have hyP : y ∈ a :: (Q ++ [c]) := by
          rw [hPmem]; simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hy; tauto
        have hzP : z ∈ a :: (Q ++ [c]) := by
          rw [hPmem]; simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hz; tauto
        have hcons := hc.chordless y z hyP hzP hyz
        rw [hP] at hcons
        have hmid : ∀ v ∈ P', v ≠ u → v ≠ c → v ∈ A ++ [vm] := by
          intro v hv hvu hvc
          simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          simp only [List.mem_append, List.mem_singleton]; tauto
        have hcnb : ∀ v ∈ A ++ [vm], ¬ ConsecIn (A ++ vm :: (M ++ [c])) v c := by
          intro v hv h
          have hdc : A ++ vm :: (M ++ [c]) = (A ++ vm :: M) ++ c :: [] := by simp
          rw [hdc] at h
          have h' := ConsecIn.nbr (hdc ▸ hPnd') h.symm
          rcases h' with h' | h'
          · rw [show A ++ vm :: M = (A ++ [vm]) ++ M by simp,
              List.getLast?_append_of_ne_nil _ hMne] at h'
            have hvM := List.mem_of_mem_getLast? h'
            have := (List.nodup_append.mp (show ((A ++ [vm]) ++ M ++ [c]).Nodup by
              simpa using hPnd')).1
            exact (List.nodup_append.mp this).2.2 v hv v hvM rfl
          · simp at h'
        by_cases hyc : y = c
        · by_cases hzc : z = c
          · rw [hyc, hzc] at hyz; exact absurd hyz (H.loopless.irrefl _)
          · have h' := hcons.symm; rw [hyc] at h'
            exact absurd h' (hcnb z (hmid z hz hzu hzc))
        · by_cases hzc : z = c
          · have h' := hcons; rw [hzc] at h'
            exact absurd h' (hcnb y (hmid y hy hyu hyc))
          · have hy' := hmid y hy hyu hyc
            have hz' := hmid z hz hzu hzc
            have h1 := ConsecIn.infix (A := []) (Q := A ++ [vm]) (B := M ++ [c])
              (by simpa using hPnd') hy' hz' (by simpa using hcons)
            rw [hP', show A ++ [vm, u, c] = (A ++ [vm]) ++ [u, c] by simp]
            exact ConsecIn.append_right h1
      intro y z hy hz hyz
      by_cases hyu : y = u
      · subst hyu
        have hz' : z ∈ A ∨ z = vm ∨ z = c := by
          simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with hz | hz | hz | hz
          · exact Or.inl hz
          · exact Or.inr (Or.inl hz)
          · rw [hz] at hyz; exact absurd hyz (H.loopless.irrefl _)
          · exact Or.inr (Or.inr hz)
        rcases hz' with hz' | rfl | rfl
        · exact absurd hyz (hmin z hz')
        · rw [hP']; exact (hconsec A [c] z y).symm
        · rw [hP', show A ++ [vm, y, z] = (A ++ [vm]) ++ y :: z :: [] by simp]
          exact hconsec _ [] y z
      · by_cases hzu : z = u
        · subst hzu
          have hy' : y ∈ A ∨ y = vm ∨ y = c := by
            simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with hy | hy | hy | hy
            · exact Or.inl hy
            · exact Or.inr (Or.inl hy)
            · exact absurd hy hyu
            · exact Or.inr (Or.inr hy)
          rcases hy' with hy' | rfl | rfl
          · exact absurd hyz.symm (hmin y hy')
          · rw [hP']; exact hconsec A [c] y z
          · rw [hP', show A ++ [vm, z, y] = (A ++ [vm]) ++ z :: y :: [] by simp]
            exact (hconsec _ [] z y).symm
        · exact key y z hy hz hyu hzu hyz
    have hPW : PW = P' := path_eq_of_chordless _ _ hP'nd hndW hsubW (by rw [hhW, hhead'])
      (by rw [hlW, hlast']) hGW.isPath hPc'
    subst hPW
    obtain ⟨hfill, hG3⟩ := gw_fill hc.nosep hGW hNT₂ hR₂ hUW
    have hcU := hG3.card_add_two_le
    have hPl : P'.length = A.length + 3 := by simp [hP']
    -- the non-precoloured vertices of `G`
    have hnle : nCount S [c, x, a] ≤ Q.length + 1 + U.card := by
      unfold nCount
      calc (S.filter (· ∉ [c, x, a])).card ≤ (Q.toFinset ∪ insert u U).card := by
            apply Finset.card_le_card
            intro v hv
            simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
              not_or] at hv
            simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert]
            by_cases hvM : v ∈ M
            · exact Or.inl (hMQ v hvM)
            · have hv2 : v ∈ S₂ := (hS₂m v).2 ⟨hv.1, hvM⟩
              rcases hfill v hv2 with h | h | h
              · exact absurd h hv.2.2.1
              · simp only [hP', List.mem_append, List.mem_cons, List.not_mem_nil,
                  or_false] at h
                rcases h with h | h | h | h
                · left; have hvP : v ∈ a :: (Q ++ [c]) := (hPmem v).2 (Or.inl h)
                  exact hinQ v hvP hv.2.2.2 hv.2.1
                · left; have hvP : v ∈ a :: (Q ++ [c]) := (hPmem v).2 (Or.inr (Or.inl h))
                  exact hinQ v hvP hv.2.2.2 hv.2.1
                · right; left; exact h
                · exact absurd h hv.2.1
              · right; right; exact h
        _ ≤ Q.toFinset.card + (insert u U).card := Finset.card_union_le _ _
        _ ≤ Q.length + (U.card + 1) :=
            Nat.add_le_add (List.toFinset_card_le Q) (Finset.card_insert_le _ _)
        _ = Q.length + 1 + U.card := by ring
    exact bound4_of_le (ncard_extSet_pos hne) (by omega)
  -- induction on the rest
  have hne' : (ExtSet H S₂ [c, x, a] L' g).Nonempty := extSet_nonempty_iff.mpr hext
  have hB := ih H S₂ x P' a c L' g true hNT₂ hh'
    (Or.inl (by show nCount S₂ [c, x, a] < nCount S [c, x, a]; omega)) hne' hexc'
  change Bound4 (ExtSet H S₂ [c, x, a] L' g).ncard (nCount S₂ [c, x, a])
    (rCount S₂ [c, x, a] L') at hB
  -- every colouring of the rest extends through the fan
  have hMdec : M = M.dropLast ++ [w] := (List.dropLast_append_getLast hMne).symm
  have hextend : ∀ φ ∈ ExtSet H S₂ [c, x, a] L' g, ∃ f ∈ ExtSet H S [c, x, a] L g,
      ∀ v ∈ S₂, f v = φ v := by
    intro φ hφ
    obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
    have huS₂ : u ∈ S₂ := (hS₂m u).2 ⟨huS, fun h => huQ (hMQ u h)⟩
    have hφu : φ u ∈ L' u := hφ2 u huS₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hu (by simp [e]), fun e => hu (by simp [e]), fun e => hu (by simp [e])⟩)
    rw [hL'u] at hφu
    simp only [Finset.mem_erase] at hφu
    have hφc : φ c = g c := hφ1 c (Or.inr (by simp))
    have hcol : ColFrom (φ u) (φ vm) (M.map L) (φ c) := by
      rw [hMdec, List.map_append, List.map_singleton, hφc]
      refine colFrom_two_last (fun Lm hLm => ?_) hα.2 hβ.2 hαβ hα.1 hβ.1
        (fun e => hφu.2.1 e.symm) (fun e => hφu.1 e.symm)
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hLm
      rw [hc.three m (hMQ m (List.mem_of_mem_dropLast hm))]
    obtain ⟨f, hf1, hf2, hf3⟩ := hc.fan_extend hP hu hnbM φ hcol
    refine ⟨f, ⟨fun v hv => ?_, fun v hv hvn => ?_, fun p hp q hq hpq => ?_⟩,
      fun v hv => hf1 v ((hS₂m v).1 hv).2⟩
    · have hvM : v ∉ M := by
        intro h
        rcases hv with hv | hv
        · exact hv (T.subset hc.nt v (List.mem_cons_of_mem _ (hMP v h)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with e | e | e
          · exact hMc v h e
          · exact hxQ (e ▸ hMQ v h)
          · exact hMa v h e
      rw [hf1 v hvM]
      exact hφ1 v (by
        rcases hv with hv | hv
        · exact Or.inl (fun h => hv (hS₂S v h))
        · exact Or.inr hv)
    · by_cases hvM : v ∈ M
      · exact hf2 v hvM
      · rw [hf1 v hvM]
        exact hL'sub v (hφ2 v ((hS₂m v).2 ⟨hv, hvM⟩) hvn)
    · by_cases hpM : p ∈ M
      · exact hf3 p hpM q hq hpq
      by_cases hqM : q ∈ M
      · exact (hf3 q hqM p hp hpq.symm).symm
      rw [hf1 p hpM, hf1 q hqM]
      exact hφ3 p ((hS₂m p).2 ⟨hp, hpM⟩) q ((hS₂m q).2 ⟨hq, hqM⟩) hpq
  -- counting
  choose! ext hext1 hext2 using hextend
  have hN : (ExtSet H S₂ [c, x, a] L' g).ncard ≤ (ExtSet H S [c, x, a] L g).ncard := by
    refine Set.ncard_le_ncard_of_injOn ext (fun φ hφ => hext1 φ hφ) ?_
      (extSet_finite H S [c, x, a] L g)
    intro φ hφ φ' hφ' he
    funext v
    by_cases hv : v ∈ S₂
    · rw [← hext2 φ hφ v hv, ← hext2 φ' hφ' v hv, he]
    · rw [hφ.1 v (Or.inl hv), hφ'.1 v (Or.inl hv)]
  exact bound4_gain hB hN (by omega)

end NTCalc

end ThomassenManyColourings
