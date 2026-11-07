/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneCut
public import Thomassen.ArcPathSeparation

/-!
# Existence of the cut along `x u y` (layer B, part 7)

The cycle `x l₁ y u` of a plane near-triangulation with outer cycle `x l₁ y l₂`, through an
interior vertex `u` joined to `x` and `y` (`x ≁ y`), is cut by the registered path separation
theorem of thomassen-girth-five (`Thomassen.facial_arc_path_separation`), with the facial arc
`l₁` and the separator path `y u x`; the two sides are transported back to `V`
(`cut_separation`), and `cut_side` makes each a plane near-triangulation (`PNT.cut`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] [Fintype V] {H : SimpleGraph V} {S : Finset V}

set_option maxHeartbeats 16000000 in
-- the transport of both sides and the arc conditions exceed the default heartbeat budget
/-- **The cut separation.** -/
theorem cut_separation {x y u : V} {l₁ l₂ : List V} (hP : PNT H S (x :: (l₁ ++ y :: l₂)))
    {M : PlaneMap (indG H S)} (hM : IsNTMap (x :: (l₁ ++ y :: l₂)) M) (hl₁ : l₁ ≠ [])
    (hl₂ : l₂ ≠ []) (huS : u ∈ S) (hu : u ∉ x :: (l₁ ++ y :: l₂)) (hux : H.Adj u x)
    (huy : H.Adj u y) (hxy : ¬ H.Adj x y) :
    ∃ S₁ S₂ : Finset V, S₁ ⊆ S ∧ S₂ ⊆ S ∧ S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {x, y, u} ∧
      (∀ a ∈ S, ∀ w ∈ S, H.Adj a w → (a ∈ S₁ ∧ w ∈ S₁) ∨ (a ∈ S₂ ∧ w ∈ S₂)) ∧
      (∀ v ∈ x :: (l₁ ++ [y, u]), v ∈ S₁) ∧ (∀ v ∈ l₂, v ∈ S₂) ∧
      (∀ a ∈ S₁, ∀ v ∈ S₁, (indG H S₁).Reachable a v) ∧
      (∀ a ∈ S₂, ∀ v ∈ S₂, (indG H S₂).Reachable a v) := by
  classical
  have hnd := hP.nodup
  have hbig : x :: (l₁ ++ y :: l₂) = (x :: (l₁ ++ [y])) ++ l₂ := by simp
  have hndA : (x :: (l₁ ++ [y])).Nodup := by
    have := hnd; rw [hbig] at this; exact (List.nodup_append.mp this).1
  have huA : u ∉ x :: (l₁ ++ [y]) := fun h => hu (by rw [hbig]; exact List.mem_append_left _ h)
  have hxl₁ : x ∉ l₁ := fun h => (List.nodup_cons.mp hndA).1 (by simp [h])
  have hyl₁ : y ∉ l₁ := fun h =>
    (List.nodup_append.mp (List.nodup_cons.mp hndA).2).2.2 y h y (by simp) rfl
  have hul₁ : u ∉ l₁ := fun h => huA (by simp [h])
  set L := x :: (l₁ ++ [y, u]) with hL
  have hC : L = (x :: (l₁ ++ [y])) ++ [u] := by simp [hL]
  have hndL : L.Nodup := by
    rw [hC, List.nodup_append]
    exact ⟨hndA, List.nodup_singleton u, fun a ha b hb hab => huA (by
      simp only [List.mem_singleton] at hb; rw [← hb, ← hab]; exact ha)⟩
  set k := L.length with hk
  have hk3 : 3 ≤ k := by simp [hk, hL]
  have : NeZero k := ⟨by omega⟩
  have hLS : ∀ v ∈ L, v ∈ S := by
    intro v hv
    rw [hC, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hP.subset v (by rw [hbig]; exact List.mem_append_left _ hv)
    · rw [List.mem_singleton.mp hv]; exact huS
  -- pairs of the new cycle
  have hyu : CycSucc L y u := Or.inl ⟨x :: l₁, [], by simp [hL]⟩
  have hwrap : CycSucc L u x := Or.inr ⟨l₁ ++ [y], by simp [hL]⟩
  have hbigL : ∀ a b, CycSucc L a b → b ≠ u → b ≠ x → CycSucc (x :: (l₁ ++ y :: l₂)) a b := by
    intro a b h hbu hbx
    rcases h with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
    · rw [hC] at hAB
      obtain ⟨B', hB'⟩ := consec_of_append_single hAB.symm hbu
      exact Or.inl ⟨A, B' ++ l₂, by rw [hbig, hB']; simp⟩
    · simp only [hL, List.cons.injEq] at hMm
      exact absurd hMm.1.symm hbx
  have hadjL : ∀ a b, CycSucc L a b → H.Adj a b := by
    intro a b h
    by_cases hbu : b = u
    · subst hbu
      rw [CycSucc.unique_left hndL h hyu]; exact huy.symm
    by_cases hbx : b = x
    · subst hbx
      rw [CycSucc.unique_left hndL h hwrap]; exact hux
    exact hP.adj (hbigL a b h hbu hbx)
  let _ : Fintype (S : Set V) := Fintype.ofFinite _
  set G' := H.induce (S : Set V) with hG'
  set M' := Thomassen.subtypePlaneMap (S : Set V) M with hM'
  -- the cycle `x l₁ y u` as a map from `ZMod k`
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
  have hcvnat : ∀ n : ℕ, n < k → cv (n : ZMod k) = L.getD n x := by
    intro n hn
    simp only [cv, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  have hcvl₁ : ∀ m : ℕ, m < l₁.length → cv ((m + 1 : ℕ) : ZMod k) = l₁.getD m x := by
    intro m hm
    rw [hcvnat _ (by simp [hk, hL]; omega), hL, List.getD_cons_succ,
      List.getD_append _ _ _ _ hm]
  have hAidx : ∀ m : ℕ, m < l₁.length → cv ((m + 1 : ℕ) : ZMod k) ∈ l₁ := by
    intro m hm
    rw [hcvl₁ m hm, List.getD_eq_getElem _ _ hm]
    exact List.getElem_mem _
  have hcvm1 : cv (-1) = u := by
    have h := hsucc (-1)
    rw [neg_add_cancel, hcv0] at h
    exact CycSucc.unique_left hndL h hwrap
  have hcvj : cv (-1 - 1) = y := by
    have h := hsucc (-1 - 1)
    rw [sub_add_cancel, hcvm1] at h
    exact CycSucc.unique_left hndL h hyu
  have hcv1 : cv 1 ∈ l₁ := by
    have := hAidx 0 (List.length_pos_of_ne_nil hl₁)
    simpa using this
  have hcvjprev : cv (-1 - 1 - 1) ∈ l₁ := by
    rcases l₁.eq_nil_or_concat with h | ⟨l₀, w, hw⟩
    · exact absurd h hl₁
    have hwy : CycSucc L w y := Or.inl ⟨x :: l₀, [u], by simp [hL, hw]⟩
    have h := hsucc (-1 - 1 - 1)
    rw [sub_add_cancel, hcvj] at h
    rw [CycSucc.unique_left hndL h hwy, hw]
    simp
  have hc : Grotzsch.IsCycleMap G' cm :=
    ⟨fun i j h => hcvinj i j (congrArg Subtype.val h), fun i => hadjL _ _ (hsucc i)⟩
  -- the arc `l₁` and the separator `{x, y, u}`
  let A : Set (S : Set V) := {v | v.1 ∈ l₁}
  have hAC : A ⊆ Set.range cm := by
    intro v hv
    obtain ⟨m, hm, hmv⟩ := List.getElem_of_mem (show v.1 ∈ l₁ from hv)
    refine ⟨((m + 1 : ℕ) : ZMod k), Subtype.ext ?_⟩
    show cv _ = v.1
    rw [hcvl₁ m hm, List.getD_eq_getElem _ _ hm, hmv]
  have hcyc : ∀ i, (Thomassen.cyclicSubgraph G' cm).Adj (cm i) (cm (i + 1)) :=
    fun i => ⟨hc.2 i, i, Or.inl ⟨rfl, rfl⟩⟩
  have hB3 : ∀ p ∈ Set.range cm \ A, p = cm 0 ∨ p = cm (-1 - 1) ∨ p = cm (-1) := by
    rintro p ⟨⟨i, rfl⟩, hpA⟩
    have hpA' : cv i ∉ l₁ := hpA
    have hmem := hcvL i
    simp only [hL, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h
    · left; exact Subtype.ext (h.trans hcv0.symm)
    · exact absurd h hpA'
    · right; left; exact Subtype.ext (h.trans hcvj.symm)
    · right; right; exact Subtype.ext (h.trans hcvm1.symm)
  have hx0 : cm 0 ∈ Set.range cm \ A := ⟨⟨0, rfl⟩, by show cv 0 ∉ l₁; rw [hcv0]; exact hxl₁⟩
  have hyj : cm (-1 - 1) ∈ Set.range cm \ A :=
    ⟨⟨_, rfl⟩, by show cv _ ∉ l₁; rw [hcvj]; exact hyl₁⟩
  have hum1 : cm (-1) ∈ Set.range cm \ A :=
    ⟨⟨_, rfl⟩, by show cv _ ∉ l₁; rw [hcvm1]; exact hul₁⟩
  have hc0m1 : (Thomassen.cyclicSubgraph G' cm).Adj (cm (-1)) (cm 0) := by
    have := hcyc (-1); rwa [neg_add_cancel] at this
  have hcjm1 : (Thomassen.cyclicSubgraph G' cm).Adj (cm (-1 - 1)) (cm (-1)) := by
    have := hcyc (-1 - 1); rwa [sub_add_cancel] at this
  have hBreach : ∀ p ∈ Set.range cm \ A,
      RIn (Thomassen.cyclicSubgraph G' cm) (Set.range cm \ A) (cm 0) p := by
    intro p hp
    rcases hB3 p hp with rfl | rfl | rfl
    · exact RIn.refl _
    · exact (RIn.single hc0m1.symm hx0 hum1).tail hcjm1.symm hum1 hyj
    · exact RIn.single hc0m1.symm hx0 hum1
  have hBconn : ConnSet (Thomassen.cyclicSubgraph G' cm) (Set.range cm \ A) :=
    ⟨⟨_, hx0⟩, fun a ha b hb => (hBreach a ha).symm.trans (hBreach b hb)⟩
  have hAreach : ∀ n : ℕ, 1 ≤ n → n ≤ l₁.length →
      RIn (Thomassen.cyclicSubgraph G' cm) A (cm 1) (cm (n : ZMod k)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; simp only [Nat.cast_one]; exact RIn.refl _
    | succ n hn ih =>
      intro hnl
      have h1 := ih (by omega)
      have hA1 : cm (n : ZMod k) ∈ A := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact hAidx m (by omega)
      have hA2 : cm ((n + 1 : ℕ) : ZMod k) ∈ A := hAidx n (by omega)
      have he := hcyc (n : ZMod k)
      rw [show (n : ZMod k) + 1 = ((n + 1 : ℕ) : ZMod k) by push_cast; ring] at he
      exact h1.tail he hA1 hA2
  have hAconn : ConnSet (Thomassen.cyclicSubgraph G' cm) A := by
    have hrA : ∀ a ∈ A, RIn (Thomassen.cyclicSubgraph G' cm) A (cm 1) a := by
      intro a ha
      obtain ⟨m, hm, hmv⟩ := List.getElem_of_mem (show a.1 ∈ l₁ from ha)
      have e : cm ((m + 1 : ℕ) : ZMod k) = a := by
        apply Subtype.ext
        show cv _ = a.1
        rw [hcvl₁ m hm, List.getD_eq_getElem _ _ hm, hmv]
      rw [← e]
      exact hAreach (m + 1) (by omega) (by omega)
    exact ⟨⟨cm 1, hcv1⟩, fun a ha b hb => (hrA a ha).symm.trans (hrA b hb)⟩
  have hBedge : ∀ {p q}, p ∈ Set.range cm \ A → q ∈ Set.range cm \ A → G'.Adj p q →
      (Thomassen.cyclicSubgraph G' cm).Adj p q := by
    intro p q hp hq hpq
    have hxy' : ¬ G'.Adj (cm 0) (cm (-1 - 1)) := by
      intro h
      have h' : H.Adj (cv 0) (cv (-1 - 1)) := h
      rw [hcv0, hcvj] at h'
      exact hxy h'
    rcases hB3 p hp with rfl | rfl | rfl <;> rcases hB3 q hq with rfl | rfl | rfl
    · exact (G'.irrefl hpq).elim
    · exact absurd hpq hxy'
    · exact hc0m1.symm
    · exact absurd hpq.symm hxy'
    · exact (G'.irrefl hpq).elim
    · exact hcjm1
    · exact hc0m1
    · exact hcjm1.symm
    · exact (G'.irrefl hpq).elim
  -- the face permutation of the transported map
  have hfp : ∀ e : G'.Dart, M'.facePerm e = Thomassen.induceDartEquiv H (S : Set V)
      (M.facePerm ((Thomassen.induceDartEquiv H (S : Set V)).symm e)) := by
    intro e; rw [hM', Thomassen.subtypePlaneMap_facePerm, Equiv.permCongr_apply]
  -- the arc `l₁` follows the outer face
  have hArc : Thomassen.IsFacialCycleAlong M' hc A := by
    intro i hi
    have hi' : cv i ∈ l₁ := hi
    have hcvi_u : cv i ≠ u := fun h => hul₁ (h ▸ hi')
    have hcvi_x : cv i ≠ x := fun h => hxl₁ (h ▸ hi')
    have hcvi1_u : cv (i + 1) ≠ u := by
      intro h
      have h' := hsucc i
      rw [h] at h'
      exact hyl₁ (CycSucc.unique_left hndL h' hyu ▸ hi')
    have hcvi1_x : cv (i + 1) ≠ x := by
      intro h
      have h' := hsucc i
      rw [h] at h'
      exact hul₁ (CycSucc.unique_left hndL h' hwrap ▸ hi')
    let d₀ : (indG H S).Dart := ⟨(cv (i - 1), cv i), indG_adj_of
      (hadjL _ _ (by simpa using hsucc (i - 1))) (hLS _ (hcvL _)) (hLS _ (hcvL _))⟩
    have hd₀ : IsOuter (x :: (l₁ ++ y :: l₂)) d₀ := by
      have := hbigL _ _ (hsucc (i - 1)) (by simpa using hcvi_u) (by simpa using hcvi_x)
      simp only [sub_add_cancel] at this
      exact this
    have hf := hM.1 d₀ hd₀
    have hffst : (M.facePerm d₀).fst = cv i := face_fst' M d₀
    have hfsnd : (M.facePerm d₀).snd = cv (i + 1) := by
      have h1 : CycSucc (x :: (l₁ ++ y :: l₂)) (cv i) (M.facePerm d₀).snd := by
        have h : CycSucc (x :: (l₁ ++ y :: l₂)) (M.facePerm d₀).fst (M.facePerm d₀).snd := hf
        rwa [hffst] at h
      exact CycSucc.unique hnd h1 (hbigL _ _ (hsucc i) hcvi1_u hcvi1_x)
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
  -- the root dart and the vertices of `l₂` on the outer face
  have hcv1u : cv 1 ≠ u := fun h => hul₁ (h ▸ hcv1)
  have hcv1x : cv 1 ≠ x := fun h => hxl₁ (h ▸ hcv1)
  let o₀ : (indG H S).Dart := ⟨(x, cv 1), indG_adj_of
    (by have := hadjL _ _ (hsucc 0); rwa [hcv0, zero_add] at this) (hLS _ (by simp [hL]))
    (hLS _ (hcvL _))⟩
  have ho₀ : IsOuter (x :: (l₁ ++ y :: l₂)) o₀ := by
    have := hbigL _ _ (hsucc 0) (by rwa [zero_add]) (by rwa [zero_add])
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
    rw [hC, List.mem_append] at hvL
    rcases hvL with hvL | hvL
    · have := hnd; rw [hbig] at this
      exact (List.nodup_append.mp this).2.2 v hvL v hv rfl
    · rw [List.mem_singleton.mp hvL] at hv
      exact hu (by simp [hv])
  have houtside : ∃ v, Thomassen.OnOuterFace M'
      (Grotzsch.toDart Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc 0)) v ∧
      v ∉ Set.range cm := by
    obtain ⟨w, l₂', rfl⟩ := List.exists_cons_of_ne_nil hl₂
    refine ⟨⟨w, Finset.mem_coe.mpr (hl₂S w (by simp))⟩, hon w (by simp), ?_⟩
    rintro ⟨i, hi⟩
    have hw : cv i = w := congrArg Subtype.val hi
    exact hdisj w (by simp) (by rw [← hw]; exact hcvL i)
  obtain ⟨S', T', -, -, hcover, hinter, hedges, hSconn, hTconn, hSC, hkeep, -, -⟩ :=
    Thomassen.facial_arc_path_separation M' hc hk3 A hAC hArc hAconn hBconn hBedge
      (show cv 0 ∉ l₁ by rw [hcv0]; exact hxl₁) hcv1 (show cv (-1) ∉ l₁ by rw [hcvm1]; exact hul₁)
      (-1 - 1) (show cv (-1 - 1) ∉ l₁ by rw [hcvj]; exact hyl₁) hcvjprev hconn houtside
  have hxS : x ∈ S := hLS x (by simp [hL])
  have hyS : y ∈ S := hLS y (by simp [hL])
  -- the two sides in `V`
  let inS' : V → Prop := fun v => ∃ h : v ∈ S, (⟨v, Finset.mem_coe.mpr h⟩ : (S : Set V)) ∈ S'
  let inT' : V → Prop := fun v => ∃ h : v ∈ S, (⟨v, Finset.mem_coe.mpr h⟩ : (S : Set V)) ∈ T'
  have hmem1 : ∀ v, v ∈ S.filter inS' ↔ v ∈ S ∧ inS' v := fun v => Finset.mem_filter
  have hmem2 : ∀ v, v ∈ S.filter inT' ↔ v ∈ S ∧ inT' v := fun v => Finset.mem_filter
  have hsep : ∀ (v : V) (hv : v ∈ S), cm 0 = ⟨v, Finset.mem_coe.mpr hv⟩ ∨
      cm (-1 - 1) = ⟨v, Finset.mem_coe.mpr hv⟩ ∨ cm (-1) = ⟨v, Finset.mem_coe.mpr hv⟩ →
      v ∈ S.filter inS' ∩ S.filter inT' := by
    intro v hv h
    have hm : (⟨v, Finset.mem_coe.mpr hv⟩ : (S : Set V)) ∈ S' ∩ T' := by
      rw [hinter]
      rcases h with h | h | h <;> rw [← h]
      · exact hx0
      · exact hyj
      · exact hum1
    exact Finset.mem_inter.mpr ⟨(hmem1 v).2 ⟨hv, hv, hm.1⟩, (hmem2 v).2 ⟨hv, hv, hm.2⟩⟩
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
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      rw [Finset.mem_inter, hmem1, hmem2] at hv
      obtain ⟨⟨hvS, h1⟩, -, h2⟩ := hv
      obtain ⟨_, hS'⟩ := h1
      obtain ⟨_, hT'⟩ := h2
      have hST : (⟨v, Finset.mem_coe.mpr hvS⟩ : (S : Set V)) ∈ S' ∩ T' := ⟨hS', hT'⟩
      rw [hinter] at hST
      rcases hB3 _ hST with h | h | h <;> have h' := congrArg Subtype.val h
      · left; simpa [cm, hcv0] using h'
      · right; left; simpa [cm, hcvj] using h'
      · right; right; simpa [cm, hcvm1] using h'
    · rintro (rfl | rfl | rfl)
      · exact hsep v hxS (Or.inl (Subtype.ext hcv0))
      · exact hsep v hyS (Or.inr (Or.inl (Subtype.ext hcvj)))
      · exact hsep v huS (Or.inr (Or.inr (Subtype.ext hcvm1)))
  · intro a ha w hw haw
    have := hedges (x := ⟨a, Finset.mem_coe.mpr ha⟩) (y := ⟨w, Finset.mem_coe.mpr hw⟩) haw
    rcases this with ⟨p, q⟩ | ⟨p, q⟩
    · exact Or.inl ⟨(hmem1 a).2 ⟨ha, ha, p⟩, (hmem1 w).2 ⟨hw, hw, q⟩⟩
    · exact Or.inr ⟨(hmem2 a).2 ⟨ha, ha, p⟩, (hmem2 w).2 ⟨hw, hw, q⟩⟩
  · intro v hv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    have hcvj' : cv (j : ZMod k) = v := by
      rw [hcvnat j hj, List.getD_eq_getElem _ _ hj]
      exact hjv
    have hm := hSC (cm (j : ZMod k)) ⟨_, rfl⟩
    have e : cm (j : ZMod k) = ⟨v, Finset.mem_coe.mpr (hLS v hv)⟩ := Subtype.ext hcvj'
    rw [e] at hm
    exact (hmem1 v).2 ⟨hLS v hv, hLS v hv, hm⟩
  · intro v hv
    refine (hmem2 v).2 ⟨hl₂S v hv, hl₂S v hv, hkeep _ (hon v hv) ?_⟩
    intro hvA
    exact hdisj v hv (by simp [hL, show v ∈ l₁ from hvA])
  · intro a ha v hv
    obtain ⟨haS, h1⟩ := (hmem1 a).1 ha
    obtain ⟨hvS, h2⟩ := (hmem1 v).1 hv
    obtain ⟨_, ha'⟩ := h1
    obtain ⟨_, hv'⟩ := h2
    let f : G'.induce S' →g indG H (S.filter inS') :=
      ⟨fun p => p.1.1, fun {p q} hpq => ⟨hpq,
        Finset.mem_coe.mpr ((hmem1 _).2 ⟨Finset.mem_coe.mp p.1.2, Finset.mem_coe.mp p.1.2, p.2⟩),
        Finset.mem_coe.mpr ((hmem1 _).2 ⟨Finset.mem_coe.mp q.1.2, Finset.mem_coe.mp q.1.2, q.2⟩)⟩⟩
    exact (hSconn.preconnected ⟨_, ha'⟩ ⟨_, hv'⟩).map f
  · intro a ha v hv
    obtain ⟨haS, h1⟩ := (hmem2 a).1 ha
    obtain ⟨hvS, h2⟩ := (hmem2 v).1 hv
    obtain ⟨_, ha'⟩ := h1
    obtain ⟨_, hv'⟩ := h2
    let f : G'.induce T' →g indG H (S.filter inT') :=
      ⟨fun p => p.1.1, fun {p q} hpq => ⟨hpq,
        Finset.mem_coe.mpr ((hmem2 _).2 ⟨Finset.mem_coe.mp p.1.2, Finset.mem_coe.mp p.1.2, p.2⟩),
        Finset.mem_coe.mpr ((hmem2 _).2 ⟨Finset.mem_coe.mp q.1.2, Finset.mem_coe.mp q.1.2, q.2⟩)⟩⟩
    exact (hTconn.preconnected ⟨_, ha'⟩ ⟨_, hv'⟩).map f

/-- **The interface field `cut`** for plane near-triangulations. -/
theorem PNT.cut {x y u : V} {l₁ l₂ : List V} (h : PNT H S (x :: (l₁ ++ y :: l₂)))
    (huS : u ∈ S) (hu : u ∉ x :: (l₁ ++ y :: l₂)) (hux : H.Adj u x) (huy : H.Adj u y)
    (hxy : ¬ H.Adj x y) :
    ∃ S₁ S₂ : Finset V, PNT H S₁ (x :: (l₁ ++ [y, u])) ∧ PNT H S₂ (y :: (l₂ ++ [x, u])) ∧
      S₁ ∪ S₂ = S ∧ S₁ ∩ S₂ = {x, y, u} ∧
      ∀ a ∈ S₁, ∀ w ∈ S₂, H.Adj a w → a ∈ S₂ ∨ w ∈ S₁ := by
  have hl₁ : l₁ ≠ [] := by
    rintro rfl
    exact hxy (h.adj (Or.inl ⟨[], l₂, by simp⟩))
  have hl₂ : l₂ ≠ [] := by
    rintro rfl
    exact hxy (h.adj (Or.inr ⟨l₁, by simp⟩)).symm
  obtain ⟨M, hM⟩ := h.2.2.2.2.2
  obtain ⟨S₁, S₂, hS₁, hS₂, hcov, hint, hedges, hL, hl₂in, hr₁, hr₂⟩ :=
    cut_separation h hM hl₁ hl₂ huS hu hux huy hxy
  have hnd := h.nodup
  have hxl₂ : x ∉ l₂ := fun hx => (List.nodup_cons.mp hnd).1 (by simp [hx])
  have hyl₂ : y ∉ l₂ := by
    have : (y :: l₂).Nodup := (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.1
    exact (List.nodup_cons.mp this).1
  have hxl₁ : x ∉ l₁ := fun hx => (List.nodup_cons.mp hnd).1 (by simp [hx])
  have hyl₁ : y ∉ l₁ := fun hy =>
    (List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.2 y hy y (by simp) rfl
  have hul₁ : u ∉ l₁ := fun h' => hu (by simp [h'])
  have hul₂ : u ∉ l₂ := fun h' => hu (by simp [h'])
  have hcross : ∀ a ∈ S₁, ∀ w ∈ S₂, H.Adj a w → a ∈ S₂ ∨ w ∈ S₁ := by
    intro a ha w hw haw
    rcases hedges a (hS₁ ha) w (hS₂ hw) haw with ⟨-, hw1⟩ | ⟨ha2, -⟩
    · exact Or.inr hw1
    · exact Or.inl ha2
  have hinter : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = y ∨ v = u := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this
    simpa using this
  have hin₂ : ∀ v, v = x ∨ v = y ∨ v = u → v ∈ S₂ := by
    intro v hv
    have : v ∈ S₁ ∩ S₂ := by rw [hint]; simpa using hv
    exact (Finset.mem_inter.mp this).2
  refine ⟨S₁, S₂, ?_, ?_, hcov, hint, hcross⟩
  · refine cut_side h hM hl₁ hl₂ hu hux huy hxy hS₁ hcov hint hcross hL (fun v hv hv1 => ?_) hr₁
    rcases hinter v hv1 (hl₂in v hv) with rfl | rfl | rfl
    · exact hxl₂ hv
    · exact hyl₂ hv
    · exact hul₂ hv
  · have e : x :: (l₁ ++ y :: l₂) = (x :: l₁) ++ (y :: l₂) := by simp
    have h' : PNT H S (y :: (l₂ ++ x :: l₁)) := by
      have := (e ▸ h : PNT H S ((x :: l₁) ++ (y :: l₂))).rot_append
      simpa using this
    have hM' : IsNTMap (y :: (l₂ ++ x :: l₁)) M := by
      have := isNTMap_rot_append (e ▸ hM : IsNTMap ((x :: l₁) ++ (y :: l₂)) M)
      simpa using this
    have hu' : u ∉ y :: (l₂ ++ x :: l₁) := by
      simp only [List.mem_cons, List.mem_append, not_or] at hu ⊢
      tauto
    refine cut_side h' hM' hl₂ hl₁ hu' huy hux (fun h'' => hxy h''.symm) hS₂
      (by rw [Finset.union_comm]; exact hcov)
      (by rw [Finset.inter_comm, hint, Finset.insert_comm])
      (fun a ha w hw haw => (hcross w hw a ha haw.symm).symm) (fun v hv => ?_)
      (fun v hv hv2 => ?_) hr₂
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | hv | rfl | rfl
      · exact hin₂ _ (Or.inr (Or.inl rfl))
      · exact hl₂in v hv
      · exact hin₂ _ (Or.inl rfl)
      · exact hin₂ _ (Or.inr (Or.inr rfl))
    · rcases hinter v (hL v (by simp [hv])) hv2 with rfl | rfl | rfl
      · exact hxl₁ hv
      · exact hyl₁ hv
      · exact hul₁ hv

end ThomassenManyColourings
