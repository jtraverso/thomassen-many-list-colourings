/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneCutSep

/-!
# Deleting an outer vertex without chords (layer B, part 8)

Let `v a … b` be the outer cycle of a plane near-triangulation and `v` incident with no chord. The
darts at `v`, listed backwards by the rotation from `(v, b)`, are `(v, u₀), …, (v, uₙ)` with
`u₀ = b` and `uₙ = a` (`fanD`); consecutive ones bound the inner triangles `uᵢ v uᵢ₊₁`, so the
graph without `v` is a plane near-triangulation with outer cycle `a … b u₁ … uₙ₋₁`
(`PNT.delete`). When `v a b` is the whole graph the result is the edge `a b`.
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

section Fan

variable {G : SimpleGraph V} (M : PlaneMap G)

omit [DecidableEq V] in
theorem rotInv_fst (e : G.Dart) : (M.rot⁻¹ e).fst = e.fst := by
  have h := M.isRotationSystem.fst_apply (M.rot⁻¹ e)
  have h1 : M.rot (M.rot⁻¹ e) = e := by simp
  rw [h1] at h
  exact h.symm

/-- The darts at the tail of `o`, backwards along the rotation. -/
def fanD (o : G.Dart) (i : ℕ) : G.Dart := (M.rot⁻¹ ^ i) o

omit [DecidableEq V] in
theorem fanD_zero (o : G.Dart) : fanD M o 0 = o := rfl

omit [DecidableEq V] in
theorem fanD_succ (o : G.Dart) (i : ℕ) : fanD M o (i + 1) = M.rot⁻¹ (fanD M o i) := by
  simp only [fanD, pow_succ', Perm.mul_apply]

omit [DecidableEq V] in
theorem rot_fanD_succ (o : G.Dart) (i : ℕ) : M.rot (fanD M o (i + 1)) = fanD M o i := by
  rw [fanD_succ]; simp

omit [DecidableEq V] in
theorem fanD_fst (o : G.Dart) : ∀ i, (fanD M o i).fst = o.fst
  | 0 => rfl
  | i + 1 => by rw [fanD_succ, rotInv_fst]; exact fanD_fst o i

omit [DecidableEq V] in
theorem fanD_add (o : G.Dart) (k i : ℕ) : fanD M o (k + i) = (M.rot⁻¹ ^ k) (fanD M o i) := by
  simp only [fanD, pow_add, Perm.mul_apply]

omit [DecidableEq V] in
theorem fanD_period {o : G.Dart} {n : ℕ} (hp : fanD M o (n + 1) = o) (m : ℕ) :
    fanD M o m = fanD M o (m % (n + 1)) := by
  have hq : ∀ q, fanD M o ((n + 1) * q) = o := by
    intro q
    simp only [fanD, pow_mul]
    exact Perm.pow_apply_eq_self_of_apply_eq_self hp q
  conv_lhs => rw [← Nat.mod_add_div m (n + 1)]
  rw [fanD_add, hq]
  rfl

omit [DecidableEq V] in
theorem fan_cover [Finite G.Dart] {o : G.Dart} {n : ℕ} (hp : fanD M o (n + 1) = o) (d : G.Dart)
    (hd : d.fst = o.fst) : ∃ i ≤ n, fanD M o i = d := by
  have hsc : SameCycle M.rot⁻¹ o d :=
    sameCycle_inv.mpr (M.isRotationSystem.sameCycle o d hd.symm)
  obtain ⟨m, hm⟩ := hsc.exists_nat_pow_eq
  refine ⟨m % (n + 1), Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos n)), ?_⟩
  rw [← fanD_period M hp]
  exact hm

omit [DecidableEq V] in
theorem fan_inj_lt {o t : G.Dart} {n : ℕ} (hn : fanD M o n = t)
    (hmin : ∀ m < n, fanD M o m ≠ t) {i j : ℕ} (hij : i < j) (hj : j ≤ n)
    (h : fanD M o i = fanD M o j) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + i := ⟨j - i, by omega⟩
  have e1 : fanD M o (k + i) = (M.rot⁻¹ ^ k) (fanD M o i) := fanD_add M o k i
  rw [← h] at e1
  have e2 : (M.rot⁻¹ ^ k) o = o := by
    apply (M.rot⁻¹ ^ i).injective
    have hc : (M.rot⁻¹ ^ i) ((M.rot⁻¹ ^ k) o) = (M.rot⁻¹ ^ k) ((M.rot⁻¹ ^ i) o) := by
      rw [← Perm.mul_apply, ← Perm.mul_apply, pow_mul_comm]
    rw [hc]
    exact e1.symm
  have e3 : fanD M o n = fanD M o (n - k) := by
    calc fanD M o n = fanD M o ((n - k) + k) := by congr 1; omega
      _ = (M.rot⁻¹ ^ (n - k)) (fanD M o k) := fanD_add M o _ _
      _ = fanD M o (n - k) := by rw [show fanD M o k = o from e2]; rfl
  exact hmin (n - k) (by omega) (e3.symm.trans hn)

omit [DecidableEq V] in
theorem fan_inj {o t : G.Dart} {n : ℕ} (hn : fanD M o n = t)
    (hmin : ∀ m < n, fanD M o m ≠ t) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (h : fanD M o i = fanD M o j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (fan_inj_lt M hn hmin hij hj h).elim
  · exact hij
  · exact (fan_inj_lt M hn hmin hij hi h.symm).elim

omit [DecidableEq V] in
/-- A rotation `2`-cycle contains every dart at its tail. -/
theorem rot_two_cycle [Finite G.Dart] {e₁ e₂ : G.Dart} (h1 : M.rot e₁ = e₂) (h2 : M.rot e₂ = e₁)
    (e : G.Dart) (he : e.fst = e₁.fst) : e = e₁ ∨ e = e₂ := by
  obtain ⟨m, hm⟩ := (M.isRotationSystem.sameCycle e₁ e he.symm).exists_nat_pow_eq
  have key : ∀ m : ℕ, (M.rot ^ m) e₁ = e₁ ∨ (M.rot ^ m) e₁ = e₂ := by
    intro m
    induction m with
    | zero => left; rfl
    | succ m ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih with h | h <;> rw [h]
      · right; exact h1
      · left; exact h2
  rw [← hm]
  exact key m

end Fan

omit [DecidableEq V] in
/-- An index of a consecutive pair. -/
theorem cycSucc_index {L : List V} (hnd : L.Nodup) (h2 : 2 ≤ L.length) {p q : V}
    (h : CycSucc L p q) (e : V) :
    ∃ j < L.length, L.getD j e = p ∧ L.getD ((j + 1) % L.length) e = q := by
  obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem h.mem.1
  refine ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, hjp], ?_⟩
  have h' := cycSucc_getD L h2 e j hj
  rw [List.getD_eq_getElem _ _ hj, hjp] at h'
  exact CycSucc.unique hnd h' h

variable [Fintype V] {H : SimpleGraph V} {S : Finset V}

set_option maxHeartbeats 16000000 in
-- the fan analysis and the degenerate triangle exceed the default heartbeat budget
/-- **Deleting an outer vertex without chords**, for the outer cycle `v a l₀' b`. -/
theorem delete_aux {v a b : V} {l₀' : List V} (h : PNT H S (v :: a :: (l₀' ++ [b])))
    (hch : ∀ z ∈ a :: (l₀' ++ [b]), H.Adj v z → z = a ∨ z = b) :
    ∃ us : List V, (∀ w ∈ us, w ∈ S ∧ w ∉ v :: a :: (l₀' ++ [b])) ∧
      (∀ z ∈ S, H.Adj v z → z = a ∨ z = b ∨ z ∈ us) ∧
      PNT H (S.erase v) (a :: (l₀' ++ [b]) ++ us) ∧ ∀ w ∈ us, H.Adj v w := by
  classical
  set C := v :: a :: (l₀' ++ [b]) with hC
  have hnd := h.nodup
  have hvl : v ∉ a :: (l₀' ++ [b]) := (List.nodup_cons.mp hnd).1
  have hndl : (a :: (l₀' ++ [b])).Nodup := (List.nodup_cons.mp hnd).2
  have hab : a ≠ b := fun e => (List.nodup_cons.mp hndl).1 (by simp [e])
  have hva : v ≠ a := fun e => hvl (by simp [e])
  have hvb : v ≠ b := fun e => hvl (by simp [e])
  have hvS : v ∈ S := h.subset v (by simp [hC])
  have haS : a ∈ S := h.subset a (by simp [hC])
  have hbS : b ∈ S := h.subset b (by simp [hC])
  have hCva : CycSucc C v a := cycSucc_cons_cons _ _ _
  have hCbv : CycSucc C b v := Or.inr ⟨a :: l₀', by simp [hC]⟩
  obtain ⟨M, hM⟩ := h.2.2.2.2.2
  let oa : (indG H S).Dart := PNT.mkDart hvS haS (h.adj hCva)
  let ob : (indG H S).Dart := PNT.mkDart hvS hbS (h.adj hCbv).symm
  have hF1 : M.rot ob = oa := by
    have ho : IsOuter C ob.symm := hCbv
    have hf := hM.1 _ ho
    have e : M.facePerm ob.symm = M.rot ob := by
      rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm]
    rw [← e]
    apply PNT.dart_eq
    · rw [PNT.face_fst]; rfl
    · have h1 : CycSucc C v (M.facePerm ob.symm).snd := by
        have h' : CycSucc C (M.facePerm ob.symm).fst (M.facePerm ob.symm).snd := hf
        rwa [PNT.face_fst] at h'
      exact CycSucc.unique hnd h1 hCva
  -- the fan at `v`
  let D := fanD M ob
  let u : ℕ → V := fun i => (D i).snd
  have hDfst : ∀ i, (D i).fst = v := fun i => fanD_fst M ob i
  have hex : ∃ n, D n = oa :=
    (sameCycle_inv.mpr (M.isRotationSystem.sameCycle ob oa rfl)).exists_nat_pow_eq
  let n := Nat.find hex
  have hn : D n = oa := Nat.find_spec hex
  have hmin : ∀ m < n, D m ≠ oa := fun m hm => Nat.find_min hex hm
  have hn1 : 1 ≤ n := by
    by_contra h0
    have h0' : n = 0 := by omega
    have : D 0 = oa := h0' ▸ hn
    exact hab (congrArg (fun d : (indG H S).Dart => d.snd) this).symm
  have hper : D (n + 1) = ob := by
    show fanD M ob (n + 1) = ob
    rw [fanD_succ]
    exact Perm.inv_eq_iff_eq.mpr (hn.trans hF1.symm)
  have hu0 : u 0 = b := rfl
  have hun : u n = a := by show (D n).snd = a; rw [hn]; rfl
  have huinj : ∀ i j, i ≤ n → j ≤ n → u i = u j → i = j := fun i j hi hj e =>
    fan_inj M hn hmin hi hj (PNT.dart_eq ((hDfst i).trans (hDfst j).symm) e)
  have huS : ∀ i, u i ∈ S := fun i => Finset.mem_coe.mp (D i).adj.2.2
  have hvu : ∀ i, H.Adj v (u i) := fun i => by
    have := (D i).adj.1; rwa [hDfst i] at this
  have huv : ∀ i, u i ≠ v := fun i e => (hvu i).ne e.symm
  have hcover : ∀ z ∈ S, H.Adj v z → ∃ i ≤ n, u i = z := by
    intro z hz hvz
    obtain ⟨i, hi, e⟩ := fan_cover M hper (PNT.mkDart hvS hz hvz) rfl
    exact ⟨i, hi, by show (D i).snd = z; rw [show D i = _ from e]; rfl⟩
  -- the inner triangles `uᵢ v uᵢ₊₁`
  have htri : ∀ i < n, ∃ d : (indG H S).Dart, d.fst = u i ∧ d.snd = u (i + 1) ∧
      M.facePerm (D i) = d ∧ M.facePerm d = (D (i + 1)).symm := by
    intro i hi
    have hne : ¬ IsOuter C (D (i + 1)).symm := by
      intro ho
      have ho' : CycSucc C (D (i + 1)).snd (D (i + 1)).fst := ho
      rw [hDfst] at ho'
      have e := CycSucc.unique_left hnd ho' hCbv
      have := huinj (i + 1) 0 (by omega) (by omega) (e.trans hu0.symm)
      omega
    have h3 := hM.2 _ hne
    rw [facePerm_pow_three] at h3
    have he1 : M.facePerm (D (i + 1)).symm = D i := by
      rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm]
      exact rot_fanD_succ M ob i
    rw [he1] at h3
    refine ⟨M.facePerm (D i), face_fst' M _, ?_, rfl, h3⟩
    rw [← face_fst' M (M.facePerm (D i)), h3]
    rfl
  have htriAdj : ∀ i < n, H.Adj (u i) (u (i + 1)) := by
    intro i hi
    obtain ⟨d, h1, h2, -, -⟩ := htri i hi
    have := d.adj.1
    rwa [h1, h2] at this
  -- the new cycle `P ++ F`, with `P = a l₀'` and `F = u₀ … uₙ₋₁`
  let us : List V := (List.range (n - 1)).map (fun i => u (i + 1))
  let P : List V := a :: l₀'
  let F : List V := (List.range n).map u
  have hmemus : ∀ w, w ∈ us ↔ ∃ i, i < n - 1 ∧ u (i + 1) = w := by
    intro w; simp [us]
  have hC₁ : a :: (l₀' ++ [b]) ++ us = P ++ F := by
    obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [us, P, F, hn', List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_sub_cancel]
    rw [hu0]
    simp [Function.comp_def]
  have hlenF : F.length = n := by simp [F]
  have hFget : ∀ i < n, F.getD i a = u i := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hlenF]; exact hi)]
    simp [F]
  have hLget_P : ∀ j < P.length, (P ++ F).getD j a = P.getD j a := fun j hj =>
    List.getD_append _ _ _ _ hj
  have hLget_F : ∀ i < n, (P ++ F).getD (P.length + i) a = u i := by
    intro i hi
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, hFget i hi]
  have hlen : (P ++ F).length = P.length + n := by simp [hlenF]
  have hL0 : (P ++ F).getD 0 a = a := by simp [P]
  have hus_out : ∀ w ∈ us, w ∉ C := by
    intro w hw hwC
    obtain ⟨i, hi, rfl⟩ := (hmemus w).1 hw
    rw [hC, List.mem_cons] at hwC
    rcases hwC with hwv | hwl
    · exact huv _ hwv
    · rcases hch _ hwl (hvu _) with e | e
      · have := huinj _ _ (by omega) le_rfl (e.trans hun.symm); omega
      · have := huinj _ _ (by omega) (by omega) (e.trans hu0.symm); omega
  have hndL : (P ++ F).Nodup := by
    rw [← hC₁, List.nodup_append]
    refine ⟨hndl, ?_, ?_⟩
    · refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
      have := huinj (x + 1) (y + 1) (by simp at hx; omega) (by simp at hy; omega) e
      omega
    · intro x hx y hy hxy
      exact hus_out y hy (by rw [← hxy]; exact List.mem_cons_of_mem _ hx)
  have hvL : v ∉ P ++ F := by
    rw [← hC₁, List.mem_append]
    rintro (h' | h')
    · exact hvl h'
    · obtain ⟨i, -, e⟩ := (hmemus v).1 h'
      exact huv _ e
  have hL2 : 2 ≤ (P ++ F).length := by rw [hlen]; simp [P]; omega
  -- pairs of the new cycle
  have hpairF : ∀ i < n, CycSucc (P ++ F) (u i) (u (i + 1)) := by
    intro i hi
    have h' := cycSucc_getD (P ++ F) hL2 a (P.length + i) (by rw [hlen]; omega)
    rw [hLget_F i hi] at h'
    by_cases hi1 : i + 1 < n
    · rw [hlen, Nat.mod_eq_of_lt (by omega), show P.length + i + 1 = P.length + (i + 1) by ring,
        hLget_F _ hi1] at h'
      exact h'
    · have hin : i + 1 = n := by omega
      rw [hlen, show P.length + i + 1 = P.length + n by omega, Nat.mod_self, hL0] at h'
      rw [hin, hun]
      exact h'
  have hCP : C = v :: (P ++ [b]) := by simp [hC, P]
  have hclass : ∀ p q, CycSucc (P ++ F) p q →
      (CycSucc C p q ∧ p ≠ v ∧ q ≠ v) ∨ ∃ i < n, p = u i ∧ q = u (i + 1) := by
    intro p q hpq
    obtain ⟨j, hj, hp, hq⟩ := cycSucc_index hndL hL2 hpq a
    have hpv : p ≠ v := fun e => hvL (e ▸ hpq.mem.1)
    have hqv : q ≠ v := fun e => hvL (e ▸ hpq.mem.2)
    by_cases hjP : j < P.length
    · left
      refine ⟨?_, hpv, hqv⟩
      have hj1 : (j + 1) % (P ++ F).length = j + 1 := Nat.mod_eq_of_lt (by rw [hlen]; omega)
      rw [hj1] at hq
      have hlenC : C.length = P.length + 2 := by simp [hCP]
      have key := cycSucc_getD C (by rw [hlenC]; omega) a (j + 1) (by rw [hlenC]; omega)
      rw [hlenC, Nat.mod_eq_of_lt (by omega)] at key
      have e1 : C.getD (j + 1) a = p := by
        rw [hCP, List.getD_cons_succ, List.getD_append _ _ _ _ hjP, ← hp, hLget_P j hjP]
      have e2 : C.getD (j + 1 + 1) a = q := by
        rw [hCP, List.getD_cons_succ]
        by_cases hj2 : j + 1 < P.length
        · rw [List.getD_append _ _ _ _ hj2, ← hq, hLget_P _ hj2]
        · have hjP' : j + 1 = P.length := by omega
          rw [hjP', List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, ← hq, hjP']
          have h0 := hLget_F 0 (by omega)
          rw [Nat.add_zero] at h0
          rw [h0, hu0]
          rfl
      rw [e1, e2] at key
      exact key
    · right
      obtain ⟨i, rfl⟩ : ∃ i, j = P.length + i := ⟨j - P.length, by omega⟩
      have hi : i < n := by rw [hlen] at hj; omega
      refine ⟨i, hi, by rw [← hp, hLget_F i hi], ?_⟩
      rw [← hq, hlen]
      by_cases hi1 : i + 1 < n
      · rw [Nat.mod_eq_of_lt (by omega), show P.length + i + 1 = P.length + (i + 1) by ring,
          hLget_F _ hi1]
      · have hin : i + 1 = n := by omega
        rw [show P.length + i + 1 = P.length + n by omega, Nat.mod_self, hL0, hin, hun]
  have hadj₁ : ∀ p q, CycSucc (P ++ F) p q → H.Adj p q := by
    intro p q hpq
    rcases hclass p q hpq with ⟨h', -, -⟩ | ⟨i, hi, rfl, rfl⟩
    · exact h.adj h'
    · exact htriAdj i hi
  have hOuterC : ∀ p q, CycSucc C p q → p ≠ v → q ≠ v → CycSucc (P ++ F) p q := by
    intro p q hpq hp hq
    rcases hpq with ⟨A, B, hAB⟩ | ⟨Mm, hMm⟩
    · rcases A with _ | ⟨x, A'⟩
      · simp only [hC, List.nil_append, List.cons.injEq] at hAB
        exact absurd hAB.1.symm hp
      · have hl : a :: (l₀' ++ [b]) = A' ++ p :: q :: B := by
          simp only [hC, List.cons_append, List.cons.injEq] at hAB
          exact hAB.2
        rw [← hC₁, hl]
        exact Or.inl ⟨A', B ++ us, by simp⟩
    · simp only [hC, List.cons.injEq] at hMm
      exact absurd hMm.1.symm hq
  have hSv : S.erase v ⊆ S := Finset.erase_subset v S
  have hmemE : ∀ z, z ∈ S → z ≠ v → z ∈ S.erase v := fun z hz hzv =>
    Finset.mem_erase.mpr ⟨hzv, hz⟩
  have hsub₁ : ∀ z ∈ P ++ F, z ∈ S.erase v := by
    intro z hz
    refine hmemE z ?_ (fun e => hvL (e ▸ hz))
    rw [← hC₁, List.mem_append] at hz
    rcases hz with hz | hz
    · exact h.subset z (List.mem_cons_of_mem _ hz)
    · obtain ⟨i, -, rfl⟩ := (hmemus z).1 hz
      exact huS _
  -- connectivity without `v`
  have hfan : ∀ k ≤ n, (indG H (S.erase v)).Reachable (u (n - k)) (u n) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have he : (indG H (S.erase v)).Adj (u (n - (k + 1))) (u (n - k)) := by
        have h' := htriAdj (n - (k + 1)) (by omega)
        rw [show n - (k + 1) + 1 = n - k by omega] at h'
        exact indG_adj_of h' (hmemE _ (huS _) (huv _)) (hmemE _ (huS _) (huv _))
      exact he.reachable.trans (ih (by omega))
  have hreach_a : ∀ z ∈ S.erase v, (indG H (S.erase v)).Reachable z a := by
    have key : ∀ (z w : V) (p : (indG H S).Walk z w), w = a → z ≠ v → z ∈ S →
        (indG H (S.erase v)).Reachable z a := by
      intro z w p
      induction p with
      | nil => intro hw _ _; rw [hw]
      | @cons z z' w hzz' p ih =>
        intro hw hzv hzS
        by_cases hz'v : z' = v
        · have hvz : H.Adj v z := by rw [← hz'v]; exact hzz'.1.symm
          obtain ⟨i, hi, rfl⟩ := hcover z hzS hvz
          have := hfan (n - i) (by omega)
          rw [show n - (n - i) = i by omega, hun] at this
          exact this
        · have hz'S : z' ∈ S := Finset.mem_coe.mp hzz'.2.2
          exact (indG_adj_of hzz'.1 (hmemE z hzS hzv) (hmemE z' hz'S hz'v)).reachable.trans
            (ih hw hz'v hz'S)
    intro z hz
    obtain ⟨hzv, hzS⟩ := Finset.mem_erase.mp hz
    obtain ⟨p⟩ := h.2.2.2.2.1 z hzS a haS
    exact key z a p rfl hzv hzS
  have hreach₁ : ∀ x ∈ S.erase v, ∀ y ∈ S.erase v, (indG H (S.erase v)).Reachable x y :=
    fun x hx y hy => (hreach_a x hx).trans (hreach_a y hy).symm
  -- the result
  have hPNT : PNT H (S.erase v) (P ++ F) := by
    by_cases h3 : 3 ≤ (P ++ F).length
    · -- the generic case: a piece
      have hne : ∀ z ∈ S.erase v, z ≠ v := fun z hz => Finset.ne_of_mem_erase hz
      have hsubR' : ∀ d : (indG H (S.erase v)).Dart, PieceR M C hSv d →
          CycSucc (P ++ F) d.fst d.snd := by
        intro d hd
        have hdf : d.fst ∈ S.erase v := Finset.mem_coe.mp d.adj.2.1
        have hds : d.snd ∈ S.erase v := Finset.mem_coe.mp d.adj.2.2
        by_cases ho : IsOuter C (Grotzsch.toDart (restrict_mono hSv) d)
        · exact hOuterC _ _ ho (hne _ hdf) (hne _ hds)
        have hz := hd.resolve_left ho
        set td := Grotzsch.toDart (restrict_mono (H := H) hSv) d with htd
        set e1 := M.facePerm td with he1
        have he1S : e1.snd ∈ S := Finset.mem_coe.mp e1.adj.2.2
        have he1v : e1.snd = v := by
          by_contra hne'
          exact hz (hmemE _ he1S hne')
        have he1f : e1.fst = d.snd := face_fst' M td
        have h3' := hM.2 _ ho
        rw [facePerm_pow_three] at h3'
        obtain ⟨j, hj, hDj⟩ := fan_cover M hper e1.symm (by
          show e1.snd = v; exact he1v)
        rcases j with _ | j'
        · exfalso
          apply ho
          have he1o : IsOuter C e1 := by
            have e : e1 = ob.symm := by
              rw [← SimpleGraph.Dart.symm_symm e1, ← hDj]; rfl
            rw [e]; exact hCbv
          have := h.outer_inv hM he1o
          rw [he1] at this
          simpa using this
        · have he2 : M.facePerm e1 = D j' := by
            rw [PlaneMap.facePerm_apply, ← hDj]
            exact rot_fanD_succ M ob j'
          rw [← he1, he2] at h3'
          have hf : d.fst = u j' := by
            have := face_fst' M (D j')
            rw [h3'] at this
            exact this
          have hs : d.snd = u (j' + 1) := by
            rw [← he1f]
            show e1.symm.snd = (fanD M ob (j' + 1)).snd
            rw [hDj]
          rw [hf, hs]
          exact hpairF j' (by omega)
      have hsubR : ∀ d : (indG H (S.erase v)).Dart, PieceR M C hSv d →
          CycSucc (P ++ F) d.fst d.snd ∨ CycSucc (P ++ F) d.snd d.fst :=
        fun d hd => Or.inl (hsubR' d hd)
      obtain ⟨q, haq⟩ := exists_cycSucc h.two_le (show a ∈ C by simp [hC])
      have hqv : q ≠ v := by
        rintro rfl
        exact hab (CycSucc.unique_left hnd haq hCbv)
      have haE : a ∈ S.erase v := hmemE a haS (Ne.symm hva)
      have hqE : q ∈ S.erase v := hmemE q (h.subset q haq.mem.2) hqv
      have haqL : CycSucc (P ++ F) a q := hOuterC a q haq (Ne.symm hva) hqv
      let dq : (indG H (S.erase v)).Dart := ⟨(a, q), indG_adj_of (h.adj haq) haE hqE⟩
      refine piece_PNT h hM hSv hndL h3 hsub₁ hadj₁ hreach₁ ⟨dq, haqL, Or.inl haq⟩ hsubR
        ⟨a, q, haqL, fun d hd hdf hds => ?_⟩
      have h' := hsubR' d hd
      rw [hdf, hds] at h'
      exact cycSucc_succ_ne_pred hndL h3 haqL h' rfl
    · -- the degenerate case: the triangle `v a b` is the whole graph
      have hP1 : P.length = 1 := by
        have : 1 ≤ P.length := by simp [P]
        rw [hlen] at h3; omega
      have hn1' : n = 1 := by rw [hlen] at h3; omega
      have hl₀ : l₀' = [] := by
        rcases l₀' with _ | ⟨w, l⟩
        · rfl
        · simp [P] at hP1
      have hCab : CycSucc C a b := Or.inl ⟨[v], [], by simp [hC, hl₀]⟩
      have hu1 : u 1 = a := hn1' ▸ hun
      obtain ⟨d₀, hd₀f, hd₀s, hd₀1, hd₀2⟩ := htri 0 (by omega)
      rw [hu0] at hd₀f
      rw [zero_add, hu1] at hd₀s
      have hD1 : D 1 = oa := hn1' ▸ hn
      rw [hD1] at hd₀2
      have hab' : H.Adj a b := h.adj hCab
      let dab : (indG H S).Dart := PNT.mkDart haS hbS hab'
      let dav : (indG H S).Dart := oa.symm
      let dba : (indG H S).Dart := dab.symm
      let dbv : (indG H S).Dart := ob.symm
      have hd₀ : d₀ = dba := PNT.dart_eq hd₀f hd₀s
      -- the rotation at `a`
      have ra1 : M.rot dav = dab := by
        have hf := hM.1 oa hCva
        have e : M.facePerm oa = M.rot dav := by
          rw [PlaneMap.facePerm_apply]
        rw [← e]
        apply PNT.dart_eq
        · rw [PNT.face_fst]; rfl
        · have h1 : CycSucc C a (M.facePerm oa).snd := by
            have h' : CycSucc C (M.facePerm oa).fst (M.facePerm oa).snd := hf
            rwa [PNT.face_fst] at h'
          exact CycSucc.unique hnd h1 hCab
      have ra2 : M.rot dab = dav := by
        have e : M.facePerm dba = M.rot dab := by
          rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm]
        rw [← e, ← hd₀, hd₀2]
      -- the rotation at `b`
      have rb1 : M.rot dba = dbv := by
        have hf := hM.1 dab hCab
        have e : M.facePerm dab = M.rot dba := by
          rw [PlaneMap.facePerm_apply]
        rw [← e]
        apply PNT.dart_eq
        · rw [PNT.face_fst]; rfl
        · have h1 : CycSucc C b (M.facePerm dab).snd := by
            have h' : CycSucc C (M.facePerm dab).fst (M.facePerm dab).snd := hf
            rwa [PNT.face_fst] at h'
          exact CycSucc.unique hnd h1 hCbv
      have rb2 : M.rot dbv = dba := by
        have e : M.facePerm (D 0) = M.rot dbv := by
          rw [PlaneMap.facePerm_apply]; rfl
        rw [← e, hd₀1, hd₀]
      -- every vertex other than `v` is `a` or `b`
      have hclosed : ∀ x y, x = a ∨ x = b → (indG H S).Adj x y → y ≠ v → y = a ∨ y = b := by
        intro x y hx hxy hyv
        let dxy : (indG H S).Dart := ⟨(x, y), hxy⟩
        rcases hx with rfl | rfl
        · rcases rot_two_cycle M ra1 ra2 dxy rfl with e | e
          · exact absurd (congrArg (fun d : (indG H S).Dart => d.snd) e) hyv
          · right; exact congrArg (fun d : (indG H S).Dart => d.snd) e
        · rcases rot_two_cycle M rb1 rb2 dxy rfl with e | e
          · left; exact congrArg (fun d : (indG H S).Dart => d.snd) e
          · exact absurd (congrArg (fun d : (indG H S).Dart => d.snd) e) hyv
      have hall : ∀ z ∈ S.erase v, z = a ∨ z = b := by
        intro z hz
        obtain ⟨p⟩ := hreach₁ a (hmemE a haS (Ne.symm hva)) z hz
        have key : ∀ (x y : V) (p : (indG H (S.erase v)).Walk x y), x = a ∨ x = b →
            y = a ∨ y = b := by
          intro x y p
          induction p with
          | nil => exact id
          | @cons x x' y hxx' p ih =>
            intro hx
            apply ih
            have hx'E : x' ∈ S.erase v := Finset.mem_coe.mp hxx'.2.2
            exact hclosed x x' hx ⟨hxx'.1, Finset.mem_coe.mpr (hSv (Finset.mem_coe.mp hxx'.2.1)),
              Finset.mem_coe.mpr (hSv hx'E)⟩ (Finset.ne_of_mem_erase hx'E)
        exact key a z p (Or.inl rfl)
      -- every dart is outer
      have hL : P ++ F = [a, b] := by simp [P, F, hl₀, hn1', hu0]
      have houter : ∀ d : (indG H (S.erase v)).Dart, IsOuter (P ++ F) d := by
        intro d
        have hne := d.adj.1.ne
        have hf := hall _ (Finset.mem_coe.mp d.adj.2.1)
        have hs := hall _ (Finset.mem_coe.mp d.adj.2.2)
        show CycSucc (P ++ F) d.fst d.snd
        rw [hL]
        rcases hf with hf | hf <;> rcases hs with hs | hs <;> rw [hf, hs] <;> rw [hf, hs] at hne
        · exact absurd rfl hne
        · exact cycSucc_cons_cons a b []
        · exact Or.inr ⟨[], rfl⟩
        · exact absurd rfl hne
      exact ⟨hndL, hL2, hsub₁, hadj₁, hreach₁, Grotzsch.restrictMap M (restrict_mono hSv),
        fun d _ => houter _, fun d hd => absurd (houter d) hd⟩
  refine ⟨us, fun w hw => ⟨?_, hus_out w hw⟩, fun z hz hvz => ?_, hC₁ ▸ hPNT, fun w hw => ?_⟩
  · obtain ⟨i, -, rfl⟩ := (hmemus w).1 hw
    exact huS _
  · obtain ⟨i, hi, rfl⟩ := hcover z hz hvz
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · right; left; rfl
    · by_cases hin : i = n
      · left; rw [hin, hun]
      · right; right
        exact (hmemus _).2 ⟨i - 1, by omega, by rw [Nat.sub_add_cancel hi0]⟩
  · obtain ⟨i, -, rfl⟩ := (hmemus w).1 hw
    exact hvu _

/-- **The interface field `delete`** for plane near-triangulations. -/
theorem PNT.delete {v : V} {l : List V} (h : PNT H S (v :: l)) (h3 : 3 ≤ (v :: l).length)
    (hch : ∀ z ∈ l, H.Adj v z → l.head? = some z ∨ l.getLast? = some z) :
    ∃ us : List V, (∀ u ∈ us, u ∈ S ∧ u ∉ v :: l) ∧
      (∀ z ∈ S, H.Adj v z → l.head? = some z ∨ l.getLast? = some z ∨ z ∈ us) ∧
      PNT H (S.erase v) (l ++ us) ∧ ∀ u ∈ us, H.Adj v u := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil (show l ≠ [] by rintro rfl; simp at h3)
  obtain ⟨l₀', b, rfl⟩ : ∃ l₀' b, l' = l₀' ++ [b] := by
    rcases l'.eq_nil_or_concat with rfl | ⟨L, b, rfl⟩
    · simp at h3
    · exact ⟨L, b, by simp⟩
  have hhead : (a :: (l₀' ++ [b])).head? = some a := rfl
  have hlast : (a :: (l₀' ++ [b])).getLast? = some b := by
    rw [← List.cons_append, List.getLast?_append]
    simp
  obtain ⟨us, h1, h2, h3', h4⟩ := delete_aux h (fun z hz hvz => by
    rcases hch z hz hvz with e | e
    · rw [hhead] at e; exact Or.inl (Option.some_injective _ e).symm
    · rw [hlast] at e; exact Or.inr (Option.some_injective _ e).symm)
  refine ⟨us, h1, fun z hz hvz => ?_, h3', h4⟩
  rw [hhead, hlast]
  rcases h2 z hz hvz with rfl | rfl | h'
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr h')

end ThomassenManyColourings
