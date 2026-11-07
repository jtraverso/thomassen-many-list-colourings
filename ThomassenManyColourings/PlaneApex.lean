/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneDelete

/-!
# Two apices over an outer edge (layer B, part 9)

Let `x y` be an edge of the outer cycle `x y l` of a plane near-triangulation and `u ≠ w` interior
vertices joined to `x` and `y`. Turning around `x` from `(x, y)`, one of the darts `(x, u)`,
`(x, w)` comes first, say `(x, q)` before `(x, p)` (`rot_order`). Cut along the triangle `x y p`
by the registered Jordan separation of thomassen-girth-five (`Thomassen.cycle_sides_cover`,
`Thomassen.cycle_sides_no_crossing`): the outer face lies on the side of the dart `(x, y)`, while
`q` and the inner face at `(y, x)` lie on the side of `(x, p)` (`Thomassen.inSubface`,
`Thomassen.cycle_original_face_subset_side`). That side is a plane near-triangulation with outer
cycle `x y p` containing `q`, closed under neighbours off the triangle (`apex_core`, `PNT.apex2`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

theorem permCongr_pow_apply {α β : Type*} (e : α ≃ β) (R : Perm α) (n : ℕ) (d : α) :
    ((e.permCongr R) ^ n) (e d) = e ((R ^ n) d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Equiv.permCongr_apply, Equiv.symm_apply_apply, pow_succ',
      Perm.mul_apply]

/-- Turning from `a`, the dart `b` comes before `g` when `a` comes before `b` from `g`. -/
theorem perm_before {α : Type*} (R : Perm α) {g a b : α} {i j : ℕ} (hi : (R ^ i) g = a)
    (hi0 : 0 < i) (hj : (R ^ j) g = b) (hjmin : ∀ m < j, (R ^ m) g ≠ b) (hij : i < j) :
    ∃ n, (R ^ n) a = b ∧ ∀ m < n, (R ^ m) a ≠ g ∧ (R ^ m) a ≠ b := by
  have hadd : ∀ m k, (R ^ m) ((R ^ k) g) = (R ^ (m + k)) g := by
    intro m k; rw [← Perm.mul_apply, ← pow_add]
  refine ⟨j - i, by rw [← hi, hadd, Nat.sub_add_cancel hij.le, hj], fun m hm => ⟨?_, ?_⟩⟩
  · intro he
    rw [← hi, hadd] at he
    have h' := hadd (j - (m + i)) (m + i)
    rw [he, show j - (m + i) + (m + i) = j by omega, hj] at h'
    exact hjmin _ (by omega) h'
  · intro he
    rw [← hi, hadd] at he
    exact hjmin _ (by omega) he

omit [DecidableEq V] in
/-- Of two darts `a, b` at the tail of `g`, one comes first when turning from `g`. -/
theorem rot_order {G : SimpleGraph V} [Finite G.Dart] (M : PlaneMap G) {g a b : G.Dart}
    (ha : a.fst = g.fst) (hb : b.fst = g.fst) (hga : g ≠ a) (hgb : g ≠ b) (hab : a ≠ b) :
    (∃ n, (M.rot ^ n) a = b ∧ ∀ m < n, (M.rot ^ m) a ≠ g ∧ (M.rot ^ m) a ≠ b) ∨
      (∃ n, (M.rot ^ n) b = a ∧ ∀ m < n, (M.rot ^ m) b ≠ g ∧ (M.rot ^ m) b ≠ a) := by
  classical
  have hexa : ∃ n, (M.rot ^ n) g = a :=
    (M.isRotationSystem.sameCycle g a ha.symm).exists_nat_pow_eq
  have hexb : ∃ n, (M.rot ^ n) g = b :=
    (M.isRotationSystem.sameCycle g b hb.symm).exists_nat_pow_eq
  have hi := Nat.find_spec hexa
  have hj := Nat.find_spec hexb
  have hne : Nat.find hexa ≠ Nat.find hexb := by
    intro e
    rw [e] at hi
    exact hab (hi.symm.trans hj)
  have hi0 : 0 < Nat.find hexa := Nat.pos_of_ne_zero (fun e => hga (by
    have h' := hi; rw [e, pow_zero, Perm.one_apply] at h'; exact h'))
  have hj0 : 0 < Nat.find hexb := Nat.pos_of_ne_zero (fun e => hgb (by
    have h' := hj; rw [e, pow_zero, Perm.one_apply] at h'; exact h'))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact Or.inl (perm_before M.rot hi hi0 hj (fun m hm => Nat.find_min hexb hm) hlt)
  · exact Or.inr (perm_before M.rot hj hj0 hi (fun m hm => Nat.find_min hexa hm) hlt)

omit [DecidableEq V] in
theorem cycSucc_three {x y p a b : V} (h : CycSucc [x, y, p] a b) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = p) ∨ (a = p ∧ b = x) := by
  rcases h with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
  · rcases A with _ | ⟨a₁, _ | ⟨a₂, A⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at hAB
      exact Or.inl ⟨hAB.1.symm, hAB.2.1.symm⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hAB
      exact Or.inr (Or.inl ⟨hAB.2.1.symm, hAB.2.2.1.symm⟩)
    · simp only [List.cons_append, List.cons.injEq] at hAB
      have := congrArg List.length hAB.2.2
      simp at this
      omega
  · simp only [List.cons.injEq] at hMm
    have h' : [y] ++ [p] = Mm ++ [a] := hMm.2
    obtain ⟨-, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h2
    exact Or.inr (Or.inr ⟨h2.symm, hMm.1.symm⟩)

omit [DecidableEq V] in
theorem tri_pairs {x y p a b : V} (ha : a = x ∨ a = y ∨ a = p) (hb : b = x ∨ b = y ∨ b = p)
    (hab : a ≠ b) : CycSucc [x, y, p] a b ∨ CycSucc [x, y, p] b a := by
  have h1 : CycSucc [x, y, p] x y := cycSucc_cons_cons _ _ _
  have h2 : CycSucc [x, y, p] y p := Or.inl ⟨[x], [], rfl⟩
  have h3 : CycSucc [x, y, p] p x := Or.inr ⟨[y], rfl⟩
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | exact Or.inl h1 | exact Or.inl h2 | exact Or.inl h3
    | exact Or.inr h1 | exact Or.inr h2 | exact Or.inr h3

omit [DecidableEq V] in
/-- A cycle neighbour of `c 0` is `c 1` or `c (-1)`. -/
theorem cyclic_adj_zero {W : Type*} {G : SimpleGraph W} {k : ℕ} {c : ZMod k → W}
    (hc : Grotzsch.IsCycleMap G c) {z : W} (h : (Thomassen.cyclicSubgraph G c).Adj (c 0) z) :
    z = c 1 ∨ z = c (-1) := by
  obtain ⟨-, i, hi | hi⟩ := h
  · have e : (0 : ZMod k) = i := hc.inj hi.1
    subst e
    left; simpa using hi.2
  · have e : (0 : ZMod k) = i + 1 := hc.inj hi.1
    right
    rw [hi.2, show i = -1 by linear_combination -e]

variable [Fintype V] {H : SimpleGraph V} {S : Finset V}

set_option maxHeartbeats 16000000 in
-- the Jordan separation, its transport and the piece conditions exceed the default budget
/-- **The inner apex.** If turning around `x` from `(x, q)` reaches `(x, p)` before `(x, y)`, the
side of the triangle `x y p` away from the outer face is a near-triangulation containing `q`. -/
theorem apex_core {x y p q : V} {l : List V} (h : PNT H S (x :: y :: l)) (hl : l ≠ [])
    {M : PlaneMap (indG H S)} (hM : IsNTMap (x :: y :: l) M) (hpS : p ∈ S) (hqS : q ∈ S)
    (hp : p ∉ x :: y :: l) (hq : q ∉ x :: y :: l) (hqp : q ≠ p) (hpx : H.Adj p x)
    (hpy : H.Adj p y) {dg dq dp : (indG H S).Dart} (hdg : dg.fst = x ∧ dg.snd = y)
    (hdq : dq.fst = x ∧ dq.snd = q) (hdp : dp.fst = x ∧ dp.snd = p)
    (hpos : ∃ n, (M.rot ^ n) dq = dp ∧ ∀ m < n, (M.rot ^ m) dq ≠ dg ∧ (M.rot ^ m) dq ≠ dp) :
    ∃ S₁ : Finset V, PNT H S₁ [x, y, p] ∧ S₁ ⊆ S ∧ q ∈ S₁ ∧ p ∈ S₁ ∧
      ∀ v ∈ S₁, v ∉ [x, y, p] → v ∉ x :: y :: l ∧ ∀ z ∈ S, H.Adj v z → z ∈ S₁ := by
  classical
  have hnd := h.nodup
  have hxS : x ∈ S := h.subset x (by simp)
  have hyS : y ∈ S := h.subset y (by simp)
  have hxy : H.Adj x y := h.adj_cons
  have hlen3 : 3 ≤ (x :: y :: l).length := by
    obtain ⟨z, l', rfl⟩ := List.exists_cons_of_ne_nil hl; simp
  have hxl : x ∉ l := fun e => (List.nodup_cons.mp hnd).1 (by simp [e])
  have hyl : y ∉ l := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hpx' : p ≠ x := fun e => hp (by simp [e])
  have hpy' : p ≠ y := fun e => hp (by simp [e])
  have hpl : p ∉ l := fun e => hp (by simp [e])
  have hqx' : q ≠ x := fun e => hq (by simp [e])
  have hqy' : q ≠ y := fun e => hq (by simp [e])
  have hxy' : x ≠ y := hxy.ne
  let _ : Fintype (S : Set V) := Fintype.ofFinite _
  set G' := H.induce (S : Set V) with hG'
  set M' := Thomassen.subtypePlaneMap (S : Set V) M with hM'
  let E := Thomassen.induceDartEquiv H (S : Set V)
  let x' : (S : Set V) := ⟨x, Finset.mem_coe.mpr hxS⟩
  let y' : (S : Set V) := ⟨y, Finset.mem_coe.mpr hyS⟩
  let p' : (S : Set V) := ⟨p, Finset.mem_coe.mpr hpS⟩
  let q' : (S : Set V) := ⟨q, Finset.mem_coe.mpr hqS⟩
  let c : ZMod 3 → (S : Set V) := ![x', y', p']
  have hc0 : c 0 = x' := rfl
  have hc1 : c 1 = y' := rfl
  have hcm1 : c (-1) = p' := rfl
  have hc : Grotzsch.IsCycleMap G' c := by
    constructor
    · intro i j hij
      have hval : (c i).1 = (c j).1 := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp [c, x', y', p'] at hval ⊢ <;> tauto
    · intro i
      fin_cases i
      · exact hxy
      · exact hpy.symm
      · exact hpx
  have hk : 3 ≤ 3 := le_rfl
  have hconn : G'.Preconnected := by
    intro a b
    obtain ⟨w⟩ := h.2.2.2.2.1 a.1 (Finset.mem_coe.mp a.2) b.1 (Finset.mem_coe.mp b.2)
    exact induce_reachable_of_walk w (Finset.mem_coe.mp a.2) (Finset.mem_coe.mp b.2)
  have hrot : ∀ (n : ℕ) (d : (indG H S).Dart), (M'.rot ^ n) (E d) = E ((M.rot ^ n) d) :=
    fun n d => permCongr_pow_apply E M.rot n d
  have hrange : ∀ v' : (S : Set V), v' ∈ Set.range c ↔ v'.1 = x ∨ v'.1 = y ∨ v'.1 = p := by
    intro v'
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; left; rfl
      · right; right; rfl
    · rintro (e | e | e)
      · exact ⟨0, Subtype.ext (by rw [e]; rfl)⟩
      · exact ⟨1, Subtype.ext (by rw [e]; rfl)⟩
      · exact ⟨-1, Subtype.ext (by rw [e]; rfl)⟩
  set F := Thomassen.subfaceSide M' Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc 0)
    with hF
  set B := Thomassen.subfaceSide M' Thomassen.cyclicSubgraph_le (Thomassen.cycleBackward hc 0)
    with hB
  have hinter : F ∩ B = Set.range c := Thomassen.cycle_sides_inter M' hc hk
  have hcB : ∀ v' ∈ Set.range c, v' ∈ B := fun v' hv =>
    Or.inl (by rw [Thomassen.cycle_subface_backward M' hc hk]; exact hv)
  have hstay : ∀ v' z' : (S : Set V), v' ∈ B → v' ∉ Set.range c → G'.Adj v' z' → z' ∈ B := by
    intro v' z' hv hvc hvz
    rcases Thomassen.cycle_sides_no_crossing M' hc hk hconn hvz with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (by rw [← hinter]; exact ⟨h1, hv⟩) hvc
    · exact h2
  -- the outer face lies on the side of `(x, y)`
  let dxy : (indG H S).Dart := PNT.mkDart hxS hyS hxy
  have hEdxy : E dxy = Grotzsch.toDart Thomassen.cyclicSubgraph_le (Thomassen.cycleForward hc 0) :=
    dart_ext' rfl rfl
  have hlout' : ∀ z (hz : z ∈ S), z ∈ l → (⟨z, Finset.mem_coe.mpr hz⟩ : (S : Set V)) ∉ B := by
    intro z hz hzl hzB
    have hzc : z ∈ x :: y :: l := by simp [hzl]
    obtain ⟨w, hzw⟩ := exists_cycSucc h.two_le hzc
    let e₀ : (indG H S).Dart := ⟨(z, w), indG_adj_of (h.adj hzw) (h.subset z hzw.mem.1)
      (h.subset w hzw.mem.2)⟩
    have hon : Thomassen.OnOuterFace M dxy z :=
      ⟨e₀, outer_sameCycle h hM (cycSucc_cons_cons x y l) hzw, rfl⟩
    have hon' : Thomassen.OnOuterFace M' (E dxy) ⟨z, Finset.mem_coe.mpr hz⟩ :=
      (Thomassen.subtypePlaneMap_onOuterFace_iff (S : Set V) M dxy _).mpr hon
    have hzF : (⟨z, Finset.mem_coe.mpr hz⟩ : (S : Set V)) ∈ F := by
      rw [hEdxy] at hon'
      exact Thomassen.cycle_original_face_subset_side M' hc hk _ (SameCycle.refl _ _)
        ⟨0, by simp, fun m hm => absurd hm (Nat.not_lt_zero _)⟩ _ hon'
    have hzc' := (hrange _).1 (by rw [← hinter]; exact ⟨hzF, hzB⟩)
    rcases hzc' with e | e | e
    · exact hxl (e ▸ hzl)
    · exact hyl (e ▸ hzl)
    · exact hpl (e ▸ hzl)
  -- `q` lies on the side of `(x, p)`
  obtain ⟨n, hn, hmin⟩ := hpos
  have hEdp : E dp = Grotzsch.toDart Thomassen.cyclicSubgraph_le
      (Thomassen.cycleBackward hc 0) := by
    apply dart_ext'
    · exact Subtype.ext hdp.1
    · exact Subtype.ext hdp.2
  have hEq : (E dq).snd = q' := Subtype.ext hdq.2
  have hqoff : q' ∉ Grotzsch.subVerts (Thomassen.cyclicSubgraph G' c) := by
    rw [Thomassen.cyclicSubgraph_subVerts hc, hrange]
    rintro (e | e | e)
    · exact hqx' e
    · exact hqy' e
    · exact hqp e
  have hnext : Grotzsch.IsNextH M' Thomassen.cyclicSubgraph_le (E dq)
      (Thomassen.cycleBackward hc 0) := by
    refine ⟨n, by rw [hrot, hn, hEdp], fun m hm hin => ?_⟩
    rw [hrot] at hin
    set d₁ := (M.rot ^ m) dq with hd₁
    have hf : (E d₁).fst = c 0 := by
      apply Subtype.ext
      show d₁.fst = x
      rw [hd₁, Grotzsch.rot_pow_fst]
      exact hdq.1
    have hin' : (Thomassen.cyclicSubgraph G' c).Adj (c 0) (E d₁).snd := by
      have := hin; unfold Grotzsch.InH at this; rwa [hf] at this
    have hd₁f : d₁.fst = x := by rw [hd₁, Grotzsch.rot_pow_fst]; exact hdq.1
    rcases cyclic_adj_zero hc hin' with e | e
    · exact (hmin m hm).1 (dart_ext' (hd₁f.trans hdg.1.symm)
        ((congrArg Subtype.val e).trans hdg.2.symm))
    · exact (hmin m hm).2 (dart_ext' (hd₁f.trans hdp.1.symm)
        ((congrArg Subtype.val e).trans hdp.2.symm))
  have hqB : q' ∈ B := by
    refine Or.inr ⟨hqoff, E dq, Thomassen.cycleBackward hc 0, ?_, by rw [hEq]; exact hqoff,
      hnext, SameCycle.refl _ _, by rw [hEq]⟩
    rw [Thomassen.cyclicSubgraph_subVerts hc]
    exact ⟨0, Subtype.ext hdq.1.symm⟩
  -- the inner face at `(y, x)` lies on the side of `(x, p)`
  let dyx : (indG H S).Dart := dxy.symm
  have hEdyx : E dyx = Grotzsch.toDart Thomassen.cyclicSubgraph_le
      (Thomassen.cycleBackward hc 1) := dart_ext' rfl rfl
  have htS : (M.facePerm dyx).snd ∈ S := Finset.mem_coe.mp (M.facePerm dyx).adj.2.2
  have htB : (⟨(M.facePerm dyx).snd, Finset.mem_coe.mpr htS⟩ : (S : Set V)) ∈ B := by
    have hon : Thomassen.OnOuterFace M dyx (M.facePerm dyx).snd :=
      ⟨M.facePerm (M.facePerm dyx),
        sameCycle_apply_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl _ _)),
        face_fst' M _⟩
    have hon' := (Thomassen.subtypePlaneMap_onOuterFace_iff (S : Set V) M dyx
      ⟨(M.facePerm dyx).snd, Finset.mem_coe.mpr htS⟩).mpr hon
    rw [hEdyx] at hon'
    have h1 := Thomassen.cycle_original_face_subset_side M' hc hk _
      (e := Thomassen.cycleBackward hc 1) (SameCycle.refl _ _)
      ⟨0, by simp, fun m hm => absurd hm (Nat.not_lt_zero _)⟩ _ hon'
    exact (Thomassen.mem_subfaceSide_congr M' Thomassen.cyclicSubgraph_le
      (Thomassen.cycle_backward_sameCycle (Grotzsch.restrictMap M' Thomassen.cyclicSubgraph_le)
        hc hk 1) _).mpr h1
  -- the piece
  let S₁ : Finset V := S.filter (fun v => ∃ hv : v ∈ S, (⟨v, Finset.mem_coe.mpr hv⟩ :
    (S : Set V)) ∈ B)
  have hS₁ : ∀ v (hv : v ∈ S), v ∈ S₁ ↔ (⟨v, Finset.mem_coe.mpr hv⟩ : (S : Set V)) ∈ B := by
    intro v hv
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, _, hB'⟩; exact hB'
    · intro hB'; exact ⟨hv, hv, hB'⟩
  have hS₁S : S₁ ⊆ S := Finset.filter_subset _ _
  have hmemS : ∀ v, v ∈ S₁ → v ∈ S := fun v hv => hS₁S hv
  have hxS₁ : x ∈ S₁ := (hS₁ x hxS).2 (hcB _ ((hrange _).2 (Or.inl rfl)))
  have hyS₁ : y ∈ S₁ := (hS₁ y hyS).2 (hcB _ ((hrange _).2 (Or.inr (Or.inl rfl))))
  have hpS₁ : p ∈ S₁ := (hS₁ p hpS).2 (hcB _ ((hrange _).2 (Or.inr (Or.inr rfl))))
  have hqS₁ : q ∈ S₁ := (hS₁ q hqS).2 hqB
  have htS₁ : (M.facePerm dyx).snd ∈ S₁ := (hS₁ _ htS).2 htB
  have hlout : ∀ z ∈ l, z ∉ S₁ := fun z hz hz1 =>
    hlout' z (hmemS z hz1) hz ((hS₁ z (hmemS z hz1)).1 hz1)
  -- vertices of the piece joined to a vertex outside it are on the triangle
  have hsep : ∀ a z, a ∈ S₁ → z ∈ S → z ∉ S₁ → H.Adj a z → a = x ∨ a = y ∨ a = p := by
    intro a z ha hz hz1 haz
    by_contra hc'
    have hac : (⟨a, Finset.mem_coe.mpr (hmemS a ha)⟩ : (S : Set V)) ∉ Set.range c :=
      fun h' => hc' ((hrange _).1 h')
    exact hz1 ((hS₁ z hz).2 (hstay _ ⟨z, Finset.mem_coe.mpr hz⟩
      ((hS₁ a (hmemS a ha)).1 ha) hac haz))
  have hyx_not : ¬ CycSucc (x :: y :: l) y x := fun h' =>
    cycSucc_succ_ne_pred hnd hlen3 (cycSucc_cons_cons x y l) h' rfl
  have hsubR : ∀ d : (indG H S₁).Dart, PieceR M (x :: y :: l) hS₁S d →
      CycSucc [x, y, p] d.fst d.snd ∨ CycSucc [x, y, p] d.snd d.fst := by
    intro d hd
    have hdf : d.fst ∈ S₁ := Finset.mem_coe.mp d.adj.2.1
    have hds : d.snd ∈ S₁ := Finset.mem_coe.mp d.adj.2.2
    have hne : d.fst ≠ d.snd := d.adj.1.ne
    by_cases ho : IsOuter (x :: y :: l) (Grotzsch.toDart (restrict_mono hS₁S) d)
    · have ho' : CycSucc (x :: y :: l) d.fst d.snd := ho
      have hxy2 : ∀ v ∈ x :: y :: l, v ∈ S₁ → v = x ∨ v = y := by
        intro v hv hv1
        simp only [List.mem_cons] at hv
        rcases hv with e | e | e
        · exact Or.inl e
        · exact Or.inr e
        · exact absurd hv1 (hlout v e)
      rcases hxy2 _ ho'.mem.1 hdf with e1 | e1 <;> rcases hxy2 _ ho'.mem.2 hds with e2 | e2
      · exact absurd (e1.trans e2.symm) hne
      · left; rw [e1, e2]; exact cycSucc_cons_cons _ _ _
      · rw [e1, e2] at ho'; exact absurd ho' hyx_not
      · exact absurd (e1.trans e2.symm) hne
    · have hz := hd.resolve_left ho
      obtain ⟨hbz, hza, hzS⟩ := tri_adj hM _ ho
      exact tri_pairs (hsep _ _ hdf hzS hz hza.symm) (hsep _ _ hds hzS hz hbz) hne
  have hadj₁ : ∀ a b, CycSucc [x, y, p] a b → H.Adj a b := by
    intro a b hab
    rcases cycSucc_three hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hpy.symm
    · exact hpx
  have hR : ∀ a' b' : (S : Set V), RIn G' B a' b' → (indG H S₁).Reachable a'.1 b'.1 := by
    intro a' b' hr
    induction hr with
    | refl => rfl
    | @tail b₀ c₀ _ hst ih =>
      exact ih.trans (indG_adj_of (S₁ := S₁) (show H.Adj b₀.1 c₀.1 from hst.1)
        ((hS₁ _ (Finset.mem_coe.mp b₀.2)).2 hst.2.1)
        ((hS₁ _ (Finset.mem_coe.mp c₀.2)).2 hst.2.2)).reachable
  have hreach₁ : ∀ a ∈ S₁, ∀ b ∈ S₁, (indG H S₁).Reachable a b := by
    intro a ha b hb
    have hcs := Thomassen.subfaceSide_connSet M' Thomassen.cyclicSubgraph_le
      (Thomassen.cycleBackward hc 0)
    exact hR ⟨a, Finset.mem_coe.mpr (hmemS a ha)⟩ ⟨b, Finset.mem_coe.mpr (hmemS b hb)⟩
      (hcs.2 _ ((hS₁ a (hmemS a ha)).1 ha) _ ((hS₁ b (hmemS b hb)).1 hb))
  have hnd₁ : [x, y, p].Nodup := by
    simp [List.nodup_cons, hxy', hpx'.symm, hpy'.symm]
  have hsub₁ : ∀ v ∈ [x, y, p], v ∈ S₁ := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hxS₁
    · exact hyS₁
    · exact hpS₁
  let dxy₁ : (indG H S₁).Dart := ⟨(x, y), indG_adj_of hxy hxS₁ hyS₁⟩
  refine ⟨S₁, piece_PNT h hM hS₁S hnd₁ (by simp) hsub₁ hadj₁ hreach₁
    ⟨dxy₁, cycSucc_cons_cons _ _ _, Or.inl (cycSucc_cons_cons x y l)⟩ hsubR
    ⟨x, y, cycSucc_cons_cons _ _ _, fun d hd hdf hds => ?_⟩, hS₁S, hqS₁, hpS₁, ?_⟩
  · have hdx := hds
    rcases hd with ho | hz
    · have ho' : CycSucc (x :: y :: l) d.fst d.snd := ho
      rw [hdf, hdx] at ho'
      exact hyx_not ho'
    · have e : Grotzsch.toDart (restrict_mono hS₁S) d = dyx := dart_ext' hdf hdx
      rw [e] at hz
      exact hz htS₁
  · intro v hv hvn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn
    obtain ⟨hvx, hvy, hvp⟩ := hvn
    refine ⟨?_, fun z hz hvz => ?_⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨hvx, hvy, fun hvl => hlout v hvl hv⟩
    · by_contra hz1
      rcases hsep v z hv hz hz1 hvz with e | e | e
      · exact hvx e
      · exact hvy e
      · exact hvp e

/-- **The interface field `apex2`** for plane near-triangulations. -/
theorem PNT.apex2 {x y u w : V} {l : List V} (h : PNT H S (x :: y :: l)) (huS : u ∈ S)
    (hwS : w ∈ S) (hu : u ∉ x :: y :: l) (hw : w ∉ x :: y :: l) (huw : u ≠ w)
    (hux : H.Adj u x) (huy : H.Adj u y) (hwx : H.Adj w x) (hwy : H.Adj w y) :
    ∃ (S₁ : Finset V) (p : V), (p = u ∨ p = w) ∧ PNT H S₁ [x, y, p] ∧ S₁ ⊆ S ∧ u ∈ S₁ ∧
      w ∈ S₁ ∧ ∀ v ∈ S₁, v ∉ [x, y, p] → v ∉ x :: y :: l ∧ ∀ z ∈ S, H.Adj v z → z ∈ S₁ := by
  classical
  have hl : l ≠ [] := by
    rintro rfl
    have hS := h.two
    rw [hS] at huS
    simp only [Finset.mem_insert, Finset.mem_singleton] at huS
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    rcases huS with e | e
    · exact hu.1 e
    · exact hu.2 e
  obtain ⟨M, hM⟩ := h.2.2.2.2.2
  have hxS : x ∈ S := h.subset x (by simp)
  have hyS : y ∈ S := h.subset y (by simp)
  have huy' : u ≠ y := fun e => hu (by simp [e])
  have hwy' : w ≠ y := fun e => hw (by simp [e])
  let dg : (indG H S).Dart := PNT.mkDart hxS hyS h.adj_cons
  let du : (indG H S).Dart := PNT.mkDart hxS huS hux.symm
  let dw : (indG H S).Dart := PNT.mkDart hxS hwS hwx.symm
  have hgu : dg ≠ du := fun e => huy' (congrArg (fun d : (indG H S).Dart => d.snd) e).symm
  have hgw : dg ≠ dw := fun e => hwy' (congrArg (fun d : (indG H S).Dart => d.snd) e).symm
  have huw' : du ≠ dw := fun e => huw (congrArg (fun d : (indG H S).Dart => d.snd) e)
  rcases rot_order M (g := dg) (a := du) (b := dw) rfl rfl hgu hgw huw' with hpos | hpos
  · obtain ⟨S₁, hP, hsub, hq, hp, hrest⟩ := apex_core h hl hM hwS huS hw hu huw hwx hwy
      (dg := dg) (dq := du) (dp := dw) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hpos
    exact ⟨S₁, w, Or.inr rfl, hP, hsub, hq, hp, hrest⟩
  · obtain ⟨S₁, hP, hsub, hq, hp, hrest⟩ := apex_core h hl hM huS hwS hu hw huw.symm hux huy
      (dg := dg) (dq := dw) (dp := du) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hpos
    exact ⟨S₁, u, Or.inl rfl, hP, hsub, hp, hq, hrest⟩

end ThomassenManyColourings
