/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneChord

/-!
# Existence of the chord separation (layer B, part 5)

The cycle `x l₁ y` closed by a chord `x y` of the outer cycle of a plane near-triangulation is
cut by the registered chord separation theorem of thomassen-girth-five
(`Thomassen.facial_arc_chord_separation`, PALOMAR-2026-10-28-000023), applied to the graph induced
on `S` with the transported map (`Thomassen.subtypePlaneMap`). The two sides are transported back
to `V` (`chord_separation`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Consecutive entries by index, cyclically. -/
theorem cycSucc_getD (L : List V) (h2 : 2 ≤ L.length) (e : V) (j : ℕ) (hj : j < L.length) :
    CycSucc L (L.getD j e) (L.getD ((j + 1) % L.length) e) := by
  by_cases hj1 : j + 1 < L.length
  · rw [Nat.mod_eq_of_lt hj1, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj1]
    left
    refine ⟨L.take j, L.drop (j + 2), ?_⟩
    conv_lhs => rw [← List.take_append_drop j L]
    rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hj1]
  · have hjl : j + 1 = L.length := by omega
    rw [hjl, Nat.mod_self]
    right
    rcases L with _ | ⟨a, L'⟩
    · simp at hj
    · have hL' : L' ≠ [] := by rintro rfl; simp at h2
      have hj' : j = L'.length := by simpa using hjl
      subst hj'
      have hlast : (a :: L').getD L'.length e = L'.getLast hL' := by
        rw [List.getD_eq_getElem _ _ hj]
        have := List.getLast_eq_getElem (l := a :: L') (by simp)
        simp only [List.length_cons, Nat.add_sub_cancel] at this
        rw [← this, List.getLast_cons hL']
      refine ⟨L'.dropLast, ?_⟩
      rw [hlast, List.getD_cons_zero, List.dropLast_append_getLast]

omit [DecidableEq V] in
/-- An arc pair not ending at the first vertex is a pair of the whole cycle. -/
theorem cycSucc_arc_big {x y : V} {l₁ l₂ : List V} {a b : V}
    (h : CycSucc (x :: (l₁ ++ [y])) a b) (hb : b ≠ x) : CycSucc (x :: (l₁ ++ y :: l₂)) a b := by
  rcases h with ⟨A, B, hAB⟩ | ⟨M, hM⟩
  · left
    refine ⟨A, B ++ l₂, ?_⟩
    rw [show x :: (l₁ ++ y :: l₂) = (x :: (l₁ ++ [y])) ++ l₂ by simp, hAB]
    simp
  · simp only [List.cons.injEq] at hM
    exact absurd hM.1.symm hb

omit [DecidableEq V] in
/-- Consecutive arc vertices are adjacent; so is the closing pair through the chord. -/
theorem arc_adj {H : SimpleGraph V} {x y : V} {l₁ l₂ : List V}
    (hnd : (x :: (l₁ ++ [y])).Nodup)
    (hadj : ∀ u v, CycSucc (x :: (l₁ ++ y :: l₂)) u v → H.Adj u v) (hxy : H.Adj x y)
    {u v : V} (huv : CycSucc (x :: (l₁ ++ [y])) u v) : H.Adj u v := by
  rcases huv with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
  · refine hadj u v (cycSucc_arc_big (Or.inl ⟨A, B, hAB⟩) ?_)
    intro hvx
    have hmem : v ∈ (x :: (l₁ ++ [y])).tail := by
      rw [hAB]
      rcases A with _ | ⟨a, A'⟩ <;> simp
    rw [hvx] at hmem
    exact (List.nodup_cons.mp hnd).1 hmem
  · simp only [List.cons.injEq] at hMm
    obtain ⟨rfl, hM'⟩ := hMm
    obtain ⟨-, hu⟩ := List.append_inj' hM' rfl
    simp only [List.cons.injEq, and_true] at hu
    rw [← hu]
    exact hxy.symm

section Sep

variable [Fintype V] {H : SimpleGraph V} {S : Finset V}

/-- The outer darts form one face. -/
theorem outer_sameCycle {c : List V} (hP : PNT H S c) {M : PlaneMap (indG H S)}
    (hM : IsNTMap c M) {d e : (indG H S).Dart} (hd : IsOuter c d) (he : IsOuter c e) :
    SameCycle M.facePerm d e := by
  let Q : V → Prop := fun a => ∀ e' : (indG H S).Dart, IsOuter c e' → e'.fst = a →
    SameCycle M.facePerm d e'
  have hQ0 : Q d.fst := by
    intro e' he' hfst
    have h1 : CycSucc c d.fst e'.snd := by
      have h : CycSucc c e'.fst e'.snd := he'
      rwa [hfst] at h
    have : e' = d := dart_ext' hfst (CycSucc.unique hP.nodup h1 hd)
    rw [this]
  have hs : ∀ u v, CycSucc c u v → Q u → Q v := by
    intro u v huv hu e' he' hfst
    let e₀ : (indG H S).Dart := ⟨(u, v), indG_adj_of (hP.adj huv) (hP.subset u huv.mem.1)
      (hP.subset v huv.mem.2)⟩
    have h0 := hu e₀ huv rfl
    have hf := hM.1 e₀ huv
    have hfst' : (M.facePerm e₀).fst = v := face_fst' M e₀
    have hfe : M.facePerm e₀ = e' := by
      apply dart_ext' (hfst'.trans hfst.symm)
      have h1 : CycSucc c v (M.facePerm e₀).snd := by
        have h : CycSucc c (M.facePerm e₀).fst (M.facePerm e₀).snd := hf
        rwa [hfst'] at h
      have h2 : CycSucc c v e'.snd := by
        have h : CycSucc c e'.fst e'.snd := he'
        rwa [hfst] at h
      exact CycSucc.unique hP.nodup h1 h2
    rw [← hfe]
    exact h0.trans ⟨1, by simp⟩
  exact forall_of_cycSucc_closed hd.mem.1 hQ0 hs e.fst he.mem.1 e he rfl

omit [DecidableEq V] [Fintype V] in
/-- A walk inside `S` gives a walk of the induced graph. -/
theorem induce_reachable_of_walk : ∀ {u v : V} (_p : (indG H S).Walk u v) (hu : u ∈ S)
    (hv : v ∈ S), (H.induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩
  | _, _, .nil, _, _ => SimpleGraph.Reachable.refl _
  | _, _, .cons h p, hu, hv =>
    (SimpleGraph.Adj.reachable (G := H.induce (S : Set V))
      (u := ⟨_, hu⟩) (v := ⟨_, Finset.mem_coe.mp h.2.2⟩) h.1).trans
      (induce_reachable_of_walk p (Finset.mem_coe.mp h.2.2) hv)

set_option maxHeartbeats 16000000 in
/-- **The chord separation.** -/
theorem chord_separation {x y : V} {l₁ l₂ : List V} (hP : PNT H S (x :: (l₁ ++ y :: l₂)))
    {M : PlaneMap (indG H S)} (hM : IsNTMap (x :: (l₁ ++ y :: l₂)) M) (hl₁ : l₁ ≠ [])
    (hl₂ : l₂ ≠ []) (hxy : H.Adj x y) :
    ∃ S₁ S₂ : Finset V, S₁ ⊆ S ∧ S₂ ⊆ S ∧ S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {x, y} ∧
      (∀ u ∈ S, ∀ w ∈ S, H.Adj u w → (u ∈ S₁ ∧ w ∈ S₁) ∨ (u ∈ S₂ ∧ w ∈ S₂)) ∧
      (∀ v ∈ x :: (l₁ ++ [y]), v ∈ S₁) ∧ (∀ v ∈ l₂, v ∈ S₂) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₁, (indG H S₁).Reachable u v) ∧
      (∀ u ∈ S₂, ∀ v ∈ S₂, (indG H S₂).Reachable u v) := by
  classical
  have hnd := hP.nodup
  have hbig : x :: (l₁ ++ y :: l₂) = (x :: (l₁ ++ [y])) ++ l₂ := by simp
  have hndL : (x :: (l₁ ++ [y])).Nodup := by
    have := hnd; rw [hbig] at this; exact (List.nodup_append.mp this).1
  set L := x :: (l₁ ++ [y]) with hL
  set k := L.length with hk
  have hk3 : 3 ≤ k := by
    obtain ⟨z, l₁', rfl⟩ := List.exists_cons_of_ne_nil hl₁; simp [hk, hL]
  have : NeZero k := ⟨by omega⟩
  have hLS : ∀ v ∈ L, v ∈ S := fun v hv => hP.subset v (by rw [hbig]; exact List.mem_append_left _ hv)
  let _ : Fintype (S : Set V) := Fintype.ofFinite _
  set G' := H.induce (S : Set V) with hG'
  set M' := Thomassen.subtypePlaneMap (S : Set V) M with hM'
  -- the cycle `x l₁ y` as a map from `ZMod k`
  let cv : ZMod k → V := fun i => L.getD i.val x
  have hcvL : ∀ i, cv i ∈ L := fun i => by
    simp only [cv, List.getD_eq_getElem _ _ (ZMod.val_lt i)]; exact List.getElem_mem _
  let cm : ZMod k → (S : Set V) := fun i => ⟨cv i, Finset.mem_coe.mpr (hLS _ (hcvL i))⟩
  have hval1 : ∀ i : ZMod k, (i + 1).val = (i.val + 1) % k := by
    intro i
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < k)]
  have hsucc : ∀ i : ZMod k, CycSucc L (cv i) (cv (i + 1)) := by
    intro i
    have h := cycSucc_getD L (by omega) x i.val (ZMod.val_lt i)
    simp only [cv, hval1]
    exact h
  have hcv0 : cv 0 = x := by simp [cv, hL]
  have hcvinj : ∀ i j, cv i = cv j → i = j := by
    intro i j h
    simp only [cv, List.getD_eq_getElem _ _ (ZMod.val_lt i),
      List.getD_eq_getElem _ _ (ZMod.val_lt j)] at h
    exact ZMod.val_injective _ ((List.Nodup.getElem_inj_iff hndL).mp h)
  have hadjL : ∀ u v, CycSucc L u v → H.Adj u v := fun u v huv =>
    arc_adj hndL (fun a b h => hP.adj h) hxy huv
  have hc : Grotzsch.IsCycleMap G' cm :=
    ⟨fun i j h => hcvinj i j (congrArg Subtype.val h), fun i => hadjL _ _ (hsucc i)⟩
  -- the face permutation of the transported map
  have hfp : ∀ e : G'.Dart, M'.facePerm e = Thomassen.induceDartEquiv H (S : Set V)
      (M.facePerm ((Thomassen.induceDartEquiv H (S : Set V)).symm e)) := by
    intro e; rw [hM', Thomassen.subtypePlaneMap_facePerm, Equiv.permCongr_apply]
  have hbig_succ : ∀ i : ZMod k, cv (i + 1) ≠ x →
      CycSucc (x :: (l₁ ++ y :: l₂)) (cv i) (cv (i + 1)) :=
    fun i hi => cycSucc_arc_big (hsucc i) hi
  -- the arc `x l₁ y` follows the outer face
  have hArc : Thomassen.IsFacialCycleArc M' hc := by
    intro i hi0 hi1
    have hcvi0 : cv i ≠ x := fun h => hi0 (Subtype.ext (h.trans hcv0.symm))
    have hcvi1 : cv (i + 1) ≠ x := by
      intro h
      have : i + 1 = 0 := hcvinj _ _ (h.trans hcv0.symm)
      exact hi1 (by rw [show i = -1 by linear_combination this])
    let d₀ : (indG H S).Dart := ⟨(cv (i - 1), cv i), indG_adj_of
      (hadjL _ _ (by simpa using hsucc (i - 1))) (hLS _ (hcvL _)) (hLS _ (hcvL _))⟩
    have hd₀ : IsOuter (x :: (l₁ ++ y :: l₂)) d₀ := by
      have := hbig_succ (i - 1) (by simpa using hcvi0)
      simp only [sub_add_cancel] at this
      exact this
    have hf := hM.1 d₀ hd₀
    have hffst : (M.facePerm d₀).fst = cv i := face_fst' M d₀
    have hfsnd : (M.facePerm d₀).snd = cv (i + 1) := by
      have h1 : CycSucc (x :: (l₁ ++ y :: l₂)) (cv i) (M.facePerm d₀).snd := by
        have h : CycSucc (x :: (l₁ ++ y :: l₂)) (M.facePerm d₀).fst (M.facePerm d₀).snd := hf
        rwa [hffst] at h
      exact CycSucc.unique hnd h1 (hbig_succ i hcvi1)
    apply dart_ext'
    · rw [face_fst']
      simp [Thomassen.cycleForward, cm]
    · rw [hfp]
      apply Subtype.ext
      simp only [Thomassen.induceDartEquiv_snd]
      have hsym : (Thomassen.induceDartEquiv H (S : Set V)).symm
          (Grotzsch.toDart Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc (i - 1))) = d₀ := by
        apply dart_ext' <;> simp [Thomassen.induceDartEquiv, Thomassen.cycleForward, cm, d₀]
      rw [hsym, hfsnd]
      simp [Thomassen.cycleForward, cm]
  -- connectivity of the induced graph
  have hconn : G'.Preconnected := by
    intro a b
    obtain ⟨p⟩ := hP.2.2.2.2.1 a.1 (Finset.mem_coe.mp a.2) b.1 (Finset.mem_coe.mp b.2)
    exact induce_reachable_of_walk p (Finset.mem_coe.mp a.2) (Finset.mem_coe.mp b.2)
  -- the root dart of the arc and the vertices of `l₂` on the outer face
  have hcv1 : cv 1 ≠ x := by
    intro h
    have : (1 : ZMod k) = 0 := hcvinj _ _ (h.trans hcv0.symm)
    have h1 : (1 : ZMod k).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    rw [this, ZMod.val_zero] at h1
    exact absurd h1 (by norm_num)
  let o₀ : (indG H S).Dart := ⟨(x, cv 1), indG_adj_of
    (by have := hadjL _ _ (hsucc 0); rwa [hcv0, zero_add] at this) (hLS _ (by simp [hL]))
    (hLS _ (hcvL _))⟩
  have ho₀ : IsOuter (x :: (l₁ ++ y :: l₂)) o₀ := by
    have := hbig_succ 0 (by simpa using hcv1)
    rwa [hcv0, zero_add] at this
  have hroot : Grotzsch.toDart Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc 0) =
      Thomassen.induceDartEquiv H (S : Set V) o₀ := by
    apply dart_ext' <;> apply Subtype.ext <;> simp [Thomassen.cycleForward, cm, o₀, hcv0] <;> rfl
  have hl₂S : ∀ v ∈ l₂, v ∈ S := fun v hv => hP.subset v (by simp [hv])
  have hon : ∀ v (hv : v ∈ l₂), Thomassen.OnOuterFace M'
      (Grotzsch.toDart Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc 0))
      ⟨v, Finset.mem_coe.mpr (hl₂S v hv)⟩ := by
    intro v hv
    have hvc : v ∈ x :: (l₁ ++ y :: l₂) := by simp [hv]
    obtain ⟨w, hvw⟩ := exists_cycSucc hP.two_le hvc
    let e₀ : (indG H S).Dart := ⟨(v, w), indG_adj_of (hP.adj hvw) (hP.subset v hvw.mem.1)
      (hP.subset w hvw.mem.2)⟩
    refine ⟨Thomassen.induceDartEquiv H (S : Set V) e₀, ?_, rfl⟩
    rw [hroot, hM', Thomassen.subtypePlaneMap_sameCycle_iff]
    exact outer_sameCycle hP hM ho₀ hvw
  have hdisj : ∀ v ∈ l₂, v ∉ L := by
    intro v hv hvL
    have := hnd; rw [hbig] at this
    exact (List.nodup_append.mp this).2.2 v hvL v hv rfl
  have houtside : ∃ v, Thomassen.OnOuterFace M'
      (Grotzsch.toDart Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc 0)) v ∧
      v ∉ Set.range cm := by
    obtain ⟨w, l₂', rfl⟩ := List.exists_cons_of_ne_nil hl₂
    refine ⟨⟨w, Finset.mem_coe.mpr (hl₂S w (by simp))⟩, hon w (by simp), ?_⟩
    rintro ⟨i, hi⟩
    have hw : cv i = w := congrArg Subtype.val hi
    exact hdisj w (by simp) (by rw [← hw]; exact hcvL i)
  obtain ⟨S', T', -, -, hcover, hinter, hedges, hSconn, hTconn, hSC, hkeep, -, -⟩ :=
    Thomassen.facial_arc_chord_separation M' hc hk3 hArc hconn houtside
  -- the last vertex of the arc
  have hval_neg : (-1 : ZMod k).val = k - 1 := by
    have h := hval1 (-1)
    rw [neg_add_cancel, ZMod.val_zero] at h
    have hlt := ZMod.val_lt (-1 : ZMod k)
    rcases Nat.lt_or_ge ((-1 : ZMod k).val + 1) k with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; omega
    · omega
  have hcvm1 : cv (-1) = y := by
    simp only [cv, hval_neg, hk, hL]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [List.getElem_append_right]
  have hxS : x ∈ S := hLS x (by simp [hL])
  have hyS : y ∈ S := hLS y (by simp [hL])
  -- the two sides in `V`
  let inS' : V → Prop := fun v => ∃ h : v ∈ S, (⟨v, Finset.mem_coe.mpr h⟩ : (S : Set V)) ∈ S'
  let inT' : V → Prop := fun v => ∃ h : v ∈ S, (⟨v, Finset.mem_coe.mpr h⟩ : (S : Set V)) ∈ T'
  have hmem1 : ∀ v, v ∈ S.filter inS' ↔ v ∈ S ∧ inS' v := fun v => Finset.mem_filter
  have hmem2 : ∀ v, v ∈ S.filter inT' ↔ v ∈ S ∧ inT' v := fun v => Finset.mem_filter
  refine ⟨S.filter inS', S.filter inT', Finset.filter_subset _ _, Finset.filter_subset _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext v
    rw [Finset.mem_union, hmem1, hmem2]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hv
      have : (⟨v, Finset.mem_coe.mpr hv⟩ : (S : Set V)) ∈ S' ∪ T' := by rw [hcover]; trivial
      rcases this with h | h
      · exact Or.inl ⟨hv, hv, h⟩
      · exact Or.inr ⟨hv, hv, h⟩
  · ext v
    rw [Finset.mem_inter, hmem1, hmem2, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hv, h1⟩, -, h2⟩
      obtain ⟨_, hS'⟩ := h1
      obtain ⟨_, hT'⟩ := h2
      have hST : (⟨v, Finset.mem_coe.mpr hv⟩ : (S : Set V)) ∈ S' ∩ T' := ⟨hS', hT'⟩
      rw [hinter] at hST
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hST
      rcases hST with h | h
      · left; have := congrArg Subtype.val h; simpa [cm, hcv0] using this
      · right; have := congrArg Subtype.val h; simpa [cm, hcvm1] using this
    · rintro (rfl | rfl)
      · have hm : cm 0 ∈ S' ∩ T' := by rw [hinter]; exact Or.inl rfl
        have e : cm 0 = ⟨v, Finset.mem_coe.mpr hxS⟩ := Subtype.ext hcv0
        rw [e] at hm
        exact ⟨⟨hxS, hxS, hm.1⟩, hxS, hxS, hm.2⟩
      · have hm : cm (-1) ∈ S' ∩ T' := by rw [hinter]; exact Or.inr rfl
        have e : cm (-1) = ⟨v, Finset.mem_coe.mpr hyS⟩ := Subtype.ext hcvm1
        rw [e] at hm
        exact ⟨⟨hyS, hyS, hm.1⟩, hyS, hyS, hm.2⟩
  · intro u hu w hw huw
    have := hedges (x := ⟨u, Finset.mem_coe.mpr hu⟩) (y := ⟨w, Finset.mem_coe.mpr hw⟩) huw
    rcases this with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨(hmem1 u).2 ⟨hu, hu, a⟩, (hmem1 w).2 ⟨hw, hw, b⟩⟩
    · exact Or.inr ⟨(hmem2 u).2 ⟨hu, hu, a⟩, (hmem2 w).2 ⟨hw, hw, b⟩⟩
  · intro v hv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    have hcvj : cv (j : ZMod k) = v := by
      show L.getD ((j : ZMod k).val) x = v
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj, List.getD_eq_getElem _ _ hj]
      exact hjv
    have hm := hSC (cm (j : ZMod k)) ⟨_, rfl⟩
    have e : cm (j : ZMod k) = ⟨v, Finset.mem_coe.mpr (hLS v hv)⟩ := Subtype.ext hcvj
    rw [e] at hm
    exact (hmem1 v).2 ⟨hLS v hv, hLS v hv, hm⟩
  · intro v hv
    refine (hmem2 v).2 ⟨hl₂S v hv, hl₂S v hv, hkeep _ (hon v hv) ?_⟩
    rintro ⟨⟨i, hi⟩, -⟩
    have hw : cv i = v := congrArg Subtype.val hi
    exact hdisj v hv (by rw [← hw]; exact hcvL i)
  · intro u hu v hv
    obtain ⟨huS, h1⟩ := (hmem1 u).1 hu
    obtain ⟨hvS, h2⟩ := (hmem1 v).1 hv
    obtain ⟨_, hu'⟩ := h1
    obtain ⟨_, hv'⟩ := h2
    let f : G'.induce S' →g indG H (S.filter inS') :=
      ⟨fun p => p.1.1, fun {p q} hpq => ⟨hpq,
        Finset.mem_coe.mpr ((hmem1 _).2 ⟨Finset.mem_coe.mp p.1.2, Finset.mem_coe.mp p.1.2, p.2⟩),
        Finset.mem_coe.mpr ((hmem1 _).2 ⟨Finset.mem_coe.mp q.1.2, Finset.mem_coe.mp q.1.2, q.2⟩)⟩⟩
    exact (hSconn.preconnected ⟨_, hu'⟩ ⟨_, hv'⟩).map f
  · intro u hu v hv
    obtain ⟨huS, h1⟩ := (hmem2 u).1 hu
    obtain ⟨hvS, h2⟩ := (hmem2 v).1 hv
    obtain ⟨_, hu'⟩ := h1
    obtain ⟨_, hv'⟩ := h2
    let f : G'.induce T' →g indG H (S.filter inT') :=
      ⟨fun p => p.1.1, fun {p q} hpq => ⟨hpq,
        Finset.mem_coe.mpr ((hmem2 _).2 ⟨Finset.mem_coe.mp p.1.2, Finset.mem_coe.mp p.1.2, p.2⟩),
        Finset.mem_coe.mpr ((hmem2 _).2 ⟨Finset.mem_coe.mp q.1.2, Finset.mem_coe.mp q.1.2, q.2⟩)⟩⟩
    exact (hTconn.preconnected ⟨_, hu'⟩ ⟨_, hv'⟩).map f

omit [Fintype V] in
theorem isNTMap_rot_append {A B : List V} {M : PlaneMap (indG H S)} (hM : IsNTMap (A ++ B) M) :
    IsNTMap (B ++ A) M := by
  have hiff : ∀ d : (indG H S).Dart, IsOuter (A ++ B) d ↔ IsOuter (B ++ A) d :=
    fun d => cycSucc_rot_append A
  exact ⟨fun d hd => (hiff _).1 (hM.1 d ((hiff d).2 hd)),
    fun d hd => hM.2 d (fun h => hd ((hiff d).1 h))⟩

omit [Fintype V] in
theorem PNT.rot_append {A B : List V} (h : PNT H S (A ++ B)) : PNT H S (B ++ A) := by
  obtain ⟨hnd, h2, hsub, hadj, hreach, M, hM⟩ := h
  refine ⟨(List.perm_append_comm.nodup_iff).mp hnd, by simpa [Nat.add_comm] using h2,
    fun v hv => hsub v (by simp at hv ⊢; tauto),
    fun u v huv => hadj u v ((cycSucc_rot_append A).mpr huv), hreach, M,
    isNTMap_rot_append hM⟩

/-- **The interface field `chord`** for plane near-triangulations. -/
theorem PNT.chord {x y : V} {l₁ l₂ : List V} (h : PNT H S (x :: (l₁ ++ y :: l₂)))
    (hl₁ : l₁ ≠ []) (hl₂ : l₂ ≠ []) (hxy : H.Adj x y) :
    ∃ S₁ S₂ : Finset V, PNT H S₁ (x :: (l₁ ++ [y])) ∧ PNT H S₂ (y :: (l₂ ++ [x])) ∧
      S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {x, y} ∧
      ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁ := by
  obtain ⟨M, hM⟩ := h.2.2.2.2.2
  obtain ⟨S₁, S₂, hS₁, hS₂, hcov, hint, hedges, hL, hl₂in, hr₁, hr₂⟩ :=
    chord_separation h hM hl₁ hl₂ hxy
  have hnd := h.nodup
  have hxl₂ : x ∉ l₂ := fun hx => (List.nodup_cons.mp hnd).1 (by simp [hx])
  have hyl₂ : y ∉ l₂ := by
    have : (y :: l₂).Nodup := (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.1
    exact (List.nodup_cons.mp this).1
  have hxl₁ : x ∉ l₁ := fun hx => (List.nodup_cons.mp hnd).1 (by simp [hx])
  have hyl₁ : y ∉ l₁ := fun hy =>
    (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.2 y hy y (by simp) rfl
  have hcross : ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁ := by
    intro u hu w hw huw
    rcases hedges u (hS₁ hu) w (hS₂ hw) huw with ⟨-, hw1⟩ | ⟨hu2, -⟩
    · exact Or.inr hw1
    · exact Or.inl hu2
  have hinter : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = y := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this
    simpa using this
  have hxy₁ : x ∈ S₁ ∧ y ∈ S₁ := ⟨hL x (by simp), hL y (by simp)⟩
  have hxy₂ : x ∈ S₂ ∧ y ∈ S₂ := by
    have hx : x ∈ S₁ ∩ S₂ := by rw [hint]; simp
    have hy : y ∈ S₁ ∩ S₂ := by rw [hint]; simp
    exact ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩
  refine ⟨S₁, S₂, ?_, ?_, hcov, hint, hcross⟩
  · refine chord_side h hM hl₁ hl₂ hxy hS₁ hcov hint hcross hL (fun v hv hv1 => ?_) hr₁
    rcases hinter v hv1 (hl₂in v hv) with rfl | rfl
    · exact hxl₂ hv
    · exact hyl₂ hv
  · have e : x :: (l₁ ++ y :: l₂) = (x :: l₁) ++ (y :: l₂) := by simp
    have h' : PNT H S (y :: (l₂ ++ x :: l₁)) := by
      have := (e ▸ h : PNT H S ((x :: l₁) ++ (y :: l₂))).rot_append
      simpa using this
    have hM' : IsNTMap (y :: (l₂ ++ x :: l₁)) M := by
      have := isNTMap_rot_append (e ▸ hM : IsNTMap ((x :: l₁) ++ (y :: l₂)) M)
      simpa using this
    refine chord_side h' hM' hl₂ hl₁ hxy.symm hS₂ (by rw [Finset.union_comm]; exact hcov)
      (by rw [Finset.inter_comm, hint, Finset.pair_comm])
      (fun u hu w hw huw => (hcross w hw u hu huw.symm).symm) (fun v hv => ?_)
      (fun v hv hv2 => ?_) hr₂
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv | rfl
      · exact hxy₂.2
      · exact hl₂in v hv
      · exact hxy₂.1
    · rcases hinter v (hL v (by simp [hv])) hv2 with rfl | rfl
      · exact hxl₁ hv
      · exact hyl₁ hv

end Sep

end ThomassenManyColourings
