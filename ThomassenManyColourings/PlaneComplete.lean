/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneInstance
public import LeanPool.K5MinorFreeChoosability.Wagner.EdgeAdd
public import LeanPool.K5MinorFreeChoosability.Wagner.Glue
public import LeanPool.K5MinorFreeChoosability.Wagner.SmallPlanar
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-!
# Completion to a near-triangulation (layer B, part 12)

Every finite planar graph with at least three vertices is a spanning subgraph of a plane
near-triangulation whose outer cycle is a triangle (`exists_PNT_supergraph`). Take a planar
supergraph `H` with the most edges. It is connected: an edge between two components can be added
by gluing plane maps along one vertex (`isPlanar_sup_of_le_one`). Two vertices on a common face
are adjacent: otherwise the edge can be added inside the face (`exists_planeMap_addEdge`). So the
vertices of a face form a clique; restricting the map to that clique, Euler's formula
(`PlaneMap.euler`) leaves no room for a face of length four or more (`face_three_of_clique`).
Hence every face is a triangle, and any face can be taken as the outer one.
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- Strict counting of classes: if every class has at least `k` elements and one has more, then
`k * numClasses s < |α|`. -/
theorem mul_numClasses_lt {α : Type*} [Finite α] (s : Setoid α) (k : ℕ)
    (hk : ∀ a, k ≤ Nat.card {b // s a b}) (a₀ : α) (h₀ : k + 1 ≤ Nat.card {b // s a₀ b}) :
    k * numClasses s + 1 ≤ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := Quotient.mk s) (s := (Finset.univ : Finset α)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hfib' : ∀ a : α, Nat.card {b // s a b} ≤
      (Finset.univ.filter fun b => Quotient.mk s b = Quotient.mk s a).card := by
    intro a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact Quotient.sound (s.symm hb)
  have hfib : ∀ q : Quotient s, k ≤ (Finset.univ.filter fun a => Quotient.mk s a = q).card := by
    intro q
    induction q using Quotient.inductionOn with
    | h a => exact (hk a).trans (hfib' a)
  have hlt : ∑ _q : Quotient s, k < ∑ q : Quotient s,
      (Finset.univ.filter fun a => Quotient.mk s a = q).card :=
    Finset.sum_lt_sum (fun q _ => hfib q) ⟨Quotient.mk s a₀, Finset.mem_univ _,
      by have := h₀.trans (hfib' a₀); omega⟩
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  simp only [numClasses, Nat.card_eq_fintype_card]
  rw [Finset.card_univ] at hsum
  rw [mul_comm]
  omega

/-- A rotation system has at most one cycle per vertex. -/
theorem cycleCount_rot_le {W : Type*} [Finite W] {G : SimpleGraph W} (M : PlaneMap G) :
    cycleCount M.rot ≤ Nat.card W := by
  classical
  have := Fintype.ofFinite W
  unfold cycleCount numClasses
  refine Nat.card_le_card_of_injective
    (Quotient.lift (fun d : G.Dart => d.fst) fun a b (h : SameCycle M.rot a b) => ?_) ?_
  · obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn, Grotzsch.rot_pow_fst]
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b => exact Quotient.sound (M.isRotationSystem.sameCycle a b hxy)

set_option maxHeartbeats 4000000 in
-- the transport to the clique and the Euler count exceed the default heartbeat budget
/-- **A face spanning a clique is a triangle.** If all vertices of the face of `d` lie in a
clique `W` with at least three vertices, the face has length three. -/
theorem face_three_of_clique [Fintype V] [DecidableEq V] {G₀ : SimpleGraph V}
    (M : PlaneMap G₀) (d : G₀.Dart) (W : Finset V)
    (hface : ∀ e, SameCycle M.facePerm d e → e.fst ∈ W)
    (hclique : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → G₀.Adj a b) (hw : 3 ≤ W.card) :
    (M.facePerm ^ 3) d = d := by
  classical
  by_contra hne
  have hKle : restrict G₀ (W : Set V) ≤ G₀ := restrict_le G₀ _
  set MK := Grotzsch.restrictMap M hKle with hMK
  have hsnd : ∀ e, SameCycle M.facePerm d e → e.snd ∈ W := by
    intro e he
    have := hface (M.facePerm e) (he.trans (sameCycle_apply_right.mpr (SameCycle.refl _ _)))
    rwa [face_fst'] at this
  have hstepK : ∀ e : (restrict G₀ (W : Set V)).Dart,
      SameCycle M.facePerm d (Grotzsch.toDart hKle e) →
      Grotzsch.toDart hKle (MK.facePerm e) = M.facePerm (Grotzsch.toDart hKle e) := by
    intro e he
    have h1 : SameCycle M.facePerm d (M.facePerm (Grotzsch.toDart hKle e)) :=
      he.trans (sameCycle_apply_right.mpr (SameCycle.refl _ _))
    exact restrictMap_facePerm_eq M hKle e ⟨(M.facePerm (Grotzsch.toDart hKle e)).adj,
      Finset.mem_coe.mpr (hface _ h1), Finset.mem_coe.mpr (hsnd _ h1)⟩
  let dK : (restrict G₀ (W : Set V)).Dart := ⟨d.toProd, d.adj,
    Finset.mem_coe.mpr (hface d (SameCycle.refl _ _)),
    Finset.mem_coe.mpr (hsnd d (SameCycle.refl _ _))⟩
  have hpowK : ∀ n : ℕ, Grotzsch.toDart hKle ((MK.facePerm ^ n) dK) = (M.facePerm ^ n) d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, hstepK _ (by rw [ih]; exact ⟨n, by simp⟩), ih, pow_succ',
        Perm.mul_apply]
  -- the clique as a vertex type
  set MW := Thomassen.subtypePlaneMap (W : Set V) MK with hMW
  set E := Thomassen.induceDartEquiv G₀ (W : Set V)
  have hφW : ∀ x, MW.facePerm (E x) = E (MK.facePerm x) := by
    intro x
    rw [hMW, Thomassen.subtypePlaneMap_facePerm, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have hpowW : ∀ n : ℕ, (MW.facePerm ^ n) (E dK) = E ((MK.facePerm ^ n) dK) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, hφW, pow_succ', Perm.mul_apply]
  set dW := E dK with hdW
  have hne3 : (MW.facePerm ^ 3) dW ≠ dW := by
    intro h
    rw [hpowW] at h
    have h' := E.injective h
    exact hne ((hpowK 3).symm.trans (by rw [h']; rfl))
  have hcardW : Nat.card (W : Set V) = W.card := by simp
  have hw1 : ∀ v : (W : Set V),
      W.card - 1 ≤ Nat.card {u // (G₀.induce (W : Set V)).Adj v u} := by
    intro v
    have hl := le_natCard_of_list (P := fun u : (W : Set V) => (G₀.induce (W : Set V)).Adj v u)
      (Finset.univ.erase v).toList (Finset.nodup_toList _) (by
        intro u hu
        rw [Finset.mem_toList, Finset.mem_erase] at hu
        exact hclique v.1 (Finset.mem_coe.mp v.2) u.1 (Finset.mem_coe.mp u.2)
          (fun e => hu.1 (Subtype.ext e).symm))
    rw [Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcardW] at hl
    exact hl
  have hdeg2 : ∀ v, 2 ≤ Nat.card {u // (G₀.induce (W : Set V)).Adj v u} := fun v => by
    have := hw1 v; omega
  have h3all : ∀ e, 3 ≤ Nat.card {b // (SameCycle.setoid MW.facePerm) e b} := fun e =>
    three_le_card_face MW.isRotationSystem hdeg2 e
  have h4 : 3 + 1 ≤ Nat.card {e // (SameCycle.setoid MW.facePerm) dW e} := by
    have n1 : MW.facePerm dW ≠ dW := face_ne_self MW.isRotationSystem dW
    have n2 : MW.facePerm (MW.facePerm dW) ≠ dW := face_face_ne_self MW.isRotationSystem hdeg2 dW
    have n3 : MW.facePerm (MW.facePerm (MW.facePerm dW)) ≠ dW := by
      intro h; apply hne3; rw [facePerm_pow_three]; exact h
    have m1 : MW.facePerm (MW.facePerm dW) ≠ MW.facePerm dW :=
      face_ne_self MW.isRotationSystem (MW.facePerm dW)
    have m2 : MW.facePerm (MW.facePerm (MW.facePerm dW)) ≠ MW.facePerm dW :=
      face_face_ne_self MW.isRotationSystem hdeg2 (MW.facePerm dW)
    have m3 : MW.facePerm (MW.facePerm (MW.facePerm dW)) ≠ MW.facePerm (MW.facePerm dW) :=
      face_ne_self MW.isRotationSystem (MW.facePerm (MW.facePerm dW))
    refine le_natCard_of_list [dW, MW.facePerm dW, MW.facePerm (MW.facePerm dW),
      MW.facePerm (MW.facePerm (MW.facePerm dW))] ?_ ?_
    · simp [Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm m1, Ne.symm m2, Ne.symm m3]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact SameCycle.refl _ _
      · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
      · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
      · exact sameCycle_apply_right.2 (sameCycle_apply_right.2
          (sameCycle_apply_right.2 (SameCycle.refl _ _)))
  have hlt := mul_numClasses_lt (SameCycle.setoid MW.facePerm) 3 h3all dW h4
  have hlt' : 3 * MW.numFaces + 1 ≤ Nat.card (G₀.induce (W : Set V)).Dart := hlt
  have heul := MW.euler
  have hD := card_dart_eq_two_mul (G₀.induce (W : Set V))
  have hE := card_edgeSet_eq_cycleCount (G := G₀.induce (W : Set V))
  have hK1 : 1 ≤ numComponents MW.rot (dartSymm (G₀.induce (W : Set V))) := by
    have : Nonempty (G₀.induce (W : Set V)).Dart := ⟨dW⟩
    exact one_le_numComponents _ _
  have hσ : (W.card - 1) * cycleCount MW.rot ≤ Nat.card (G₀.induce (W : Set V)).Dart :=
    mul_numClasses_le _ _ fun e =>
      (hw1 e.fst).trans (card_neighbor_le_card_sameCycle MW.isRotationSystem e)
  have hc := cycleCount_rot_le MW
  rw [hcardW] at hc
  -- arithmetic: `(w - 1) c ≤ D ≤ 6 c - 14` and `c ≤ w` are incompatible
  set c := cycleCount MW.rot with hcdef
  set w := W.card with hwdef
  clear_value c w
  have hD' : (Nat.card (G₀.induce (W : Set V)).Dart : ℤ) ≤ 6 * c - 14 := by
    have := hK1
    zify at hlt' hD hE this
    omega
  have hσ' : ((w : ℤ) - 1) * c ≤ Nat.card (G₀.induce (W : Set V)).Dart := by
    have h1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
    have := hσ
    zify at this
    rwa [h1] at this
  have hfin : ((w : ℤ) - 1) * c ≤ 6 * c - 14 := hσ'.trans hD'
  rcases le_or_gt w 6 with h6 | h6
  · interval_cases w <;> omega
  · have : (6 : ℤ) * c ≤ ((w : ℤ) - 1) * c :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    omega

/-- `H` with the edge `u v` added. -/
def addE (H : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := H.Adj a b ∨ (a ≠ b ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)))
  symm := ⟨fun a b h => by
    rcases h with h | ⟨hne, h | h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, Or.inr ⟨h.2, h.1⟩⟩
    · exact Or.inr ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨hne, -⟩
    · exact H.loopless.irrefl a h
    · exact hne rfl⟩

theorem addE_adj {H : SimpleGraph V} {u v : V} (huv : u ≠ v) (a b : V) :
    (addE H u v).Adj a b ↔ H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨by rw [h.1, h.2]; exact huv, Or.inl h⟩
    · exact Or.inr ⟨by rw [h.1, h.2]; exact huv.symm, Or.inr h⟩

theorem indG_univ_adj [Fintype V] {H : SimpleGraph V} (a b : V) :
    (indG H Finset.univ).Adj a b ↔ H.Adj a b :=
  ⟨fun h => h.1, fun h => ⟨h, by simp, by simp⟩⟩

theorem indG_univ [Fintype V] (H : SimpleGraph V) : indG H Finset.univ = H := by
  ext a b
  exact indG_univ_adj a b

set_option maxHeartbeats 4000000 in
-- the gluing of the two pieces exceeds the default heartbeat budget
/-- An edge between two components of a planar graph keeps it planar. -/
theorem isPlanar_addE_of_not_reachable [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hH : IsPlanar H) {u v : V} (hr : ¬ H.Reachable u v) : IsPlanar (addE H u v) := by
  classical
  have huv : u ≠ v := fun e => hr (e ▸ SimpleGraph.Reachable.refl _)
  obtain ⟨MH⟩ := hH
  let A : Finset V := Finset.univ.filter (H.Reachable u)
  have hmemA : ∀ z, z ∈ A ↔ H.Reachable u z := fun z => by simp [A]
  have huA : u ∈ A := (hmemA u).2 (SimpleGraph.Reachable.refl _)
  have hvA : v ∉ A := fun h => hr ((hmemA v).1 h)
  -- the single edge
  let Ge : SimpleGraph V := addE ⊥ u v
  have hGe : IsPlanar Ge := isPlanar_of_card_le_four (S := {u, v}) (fun a b h => by
      rcases (addE_adj huv a b).1 h with h | h | h
      · exact absurd h (by simp)
      · simp [h.1]
      · simp [h.1]) (Finset.card_le_two.trans (by norm_num))
  obtain ⟨MGe⟩ := hGe
  -- the component of `u` plus the edge
  let GA : SimpleGraph V := restrict H (A : Set V)
  let MA := Grotzsch.restrictMap MH (restrict_le H (A : Set V))
  have hP1 : IsPlanar (GA ⊔ Ge) := isPlanar_sup_of_le_one (A := A) (B := {u, v})
    (fun a b h => Finset.mem_coe.mp h.2.1)
    (fun a b h => by
      rcases (addE_adj huv a b).1 h with h | h | h
      · exact absurd h (by simp)
      · simp [h.1]
      · simp [h.1]) MA MGe (by
      intro p hp q hq
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with ⟨hpA, rfl | rfl⟩ <;> rcases hq with ⟨hqA, rfl | rfl⟩
      · rfl
      · exact absurd hqA hvA
      · exact absurd hpA hvA
      · rfl)
  obtain ⟨MP1⟩ := hP1
  -- the rest
  let GB : SimpleGraph V := restrict H ((Aᶜ : Finset V) : Set V)
  let MB := Grotzsch.restrictMap MH (restrict_le H ((Aᶜ : Finset V) : Set V))
  have hP2 : IsPlanar ((GA ⊔ Ge) ⊔ GB) := isPlanar_sup_of_le_one (A := insert v A) (B := Aᶜ)
    (fun a b h => by
      rcases h with h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_coe.mp h.2.1)
      · rcases (addE_adj huv a b).1 h with h | h | h
        · exact absurd h (by simp)
        · rw [h.1]; exact Finset.mem_insert_of_mem huA
        · rw [h.1]; exact Finset.mem_insert_self _ _)
    (fun a b h => Finset.mem_coe.mp h.2.1) MP1 MB (by
      intro p hp q hq
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_compl] at hp hq
      rcases hp with ⟨rfl | hpA, hpA'⟩ <;> rcases hq with ⟨rfl | hqA, hqA'⟩
      · rfl
      · exact absurd hqA hqA'
      · exact absurd hpA hpA'
      · exact absurd hpA hpA')
  have heq : (GA ⊔ Ge) ⊔ GB = addE H u v := by
    ext a b
    simp only [SimpleGraph.sup_adj]
    rw [addE_adj huv, addE_adj huv]
    constructor
    · rintro ((h | h | h | h) | h)
      · exact Or.inl h.1
      · exact absurd h (by simp)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h.1
    · rintro (h | h | h)
      · by_cases ha : a ∈ A
        · have hb : b ∈ A := (hmemA b).2 (((hmemA a).1 ha).trans h.reachable)
          exact Or.inl (Or.inl ⟨h, Finset.mem_coe.mpr ha, Finset.mem_coe.mpr hb⟩)
        · have hb : b ∉ A := fun hb => ha ((hmemA a).2 (((hmemA b).1 hb).trans h.symm.reachable))
          exact Or.inr ⟨h, Finset.mem_coe.mpr (Finset.mem_compl.mpr ha),
            Finset.mem_coe.mpr (Finset.mem_compl.mpr hb)⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  rw [← heq]
  exact hP2

set_option maxHeartbeats 16000000 in
-- the maximality argument and the face analysis exceed the default heartbeat budget
/-- **Completion.** A finite planar graph with at least three vertices is a spanning subgraph of
a plane near-triangulation whose outer cycle is a triangle. -/
theorem exists_PNT_supergraph [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : IsPlanar G)
    (h3 : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ∃ x a b : V, PNT H Finset.univ [x, a, b] := by
  classical
  -- a planar supergraph with the most edges
  obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun H : SimpleGraph V => G ≤ H ∧ IsPlanar H)
    (fun H => H.edgeFinset.card)
    ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨-, hGH, hHp⟩ := Finset.mem_filter.mp hHmem
  have hmax : ∀ u v, u ≠ v → ¬ H.Adj u v → ¬ IsPlanar (addE H u v) := by
    intro u v huv hna hp
    have hle : H < addE H u v := by
      refine lt_of_le_of_ne (fun a b h => Or.inl h) (fun e => hna ?_)
      rw [e]
      exact Or.inr ⟨huv, Or.inl ⟨rfl, rfl⟩⟩
    have h1 := hHmax (addE H u v)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGH.trans hle.le, hp⟩)
    have h2 : H.edgeFinset.card < (addE H u v).edgeFinset.card :=
      Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hle)
    omega
  -- `H` is connected
  have hconn : ∀ u v, H.Reachable u v := by
    intro u v
    by_contra hr
    have huv : u ≠ v := fun e => hr (e ▸ SimpleGraph.Reachable.refl _)
    exact hmax u v huv (fun h => hr h.reachable) (isPlanar_addE_of_not_reachable hHp hr)
  -- a plane map of `H`
  have hHp' : IsPlanar (indG H Finset.univ) := by rw [indG_univ]; exact hHp
  obtain ⟨M⟩ := hHp'
  -- two vertices on a common face are adjacent
  have hcorner : ∀ p q : (indG H Finset.univ).Dart, SameCycle M.facePerm p q →
      p.fst ≠ q.fst → H.Adj p.fst q.fst := by
    intro p q hpq hne
    by_contra hna
    apply hmax p.fst q.fst hne hna
    have hadj : ∀ a b, (addE H p.fst q.fst).Adj a b ↔ (indG H Finset.univ).Adj a b ∨
        (a = p.fst ∧ b = q.fst) ∨ (a = q.fst ∧ b = p.fst) := by
      intro a b
      rw [addE_adj hne, indG_univ_adj]
    obtain ⟨P, -⟩ := exists_planeMap_addEdge M hadj (fun h => hna h.1) p q rfl rfl hpq
    exact ⟨P⟩
  have hrotφ : ∀ x : (indG H Finset.univ).Dart, M.rot x = M.facePerm x.symm := by
    intro x; rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm]
  -- no face turns back at a vertex of degree one
  have hnoleaf : ∀ d : (indG H Finset.univ).Dart, (M.facePerm d).snd ≠ d.fst := by
    intro d hd
    have e1 : M.facePerm d = d.symm := dart_ext' (face_fst' M d) hd
    have hfix1 : M.rot d.symm = d.symm := by rw [hrotφ, SimpleGraph.Dart.symm_symm, e1]
    set e := M.facePerm d.symm with he
    have hef : e.fst = d.fst := face_fst' M _
    by_cases hy : e.snd = d.snd
    · have e2 : e = d := dart_ext' hef hy
      have hfix2 : M.rot d = d := by rw [hrotφ]; exact e2
      have hall : ∀ z, z = d.fst ∨ z = d.snd := by
        intro z
        obtain ⟨p⟩ := hconn d.fst z
        have key : ∀ (a b : V) (p : H.Walk a b), (a = d.fst ∨ a = d.snd) →
            b = d.fst ∨ b = d.snd := by
          intro a b p
          induction p with
          | nil => exact id
          | @cons a a' b hab p ih =>
            intro ha
            apply ih
            let x : (indG H Finset.univ).Dart := ⟨(a, a'), (indG_univ_adj a a').2 hab⟩
            rcases ha with rfl | rfl
            · have := rot_fixed_unique M hfix2 (e' := x) rfl
              exact Or.inr (congrArg (fun y : (indG H Finset.univ).Dart => y.snd) this)
            · have := rot_fixed_unique M hfix1 (e' := x) rfl
              exact Or.inl (congrArg (fun y : (indG H Finset.univ).Dart => y.snd) this)
        exact key _ _ p (Or.inl rfl)
      have hsub : (Finset.univ : Finset V) ⊆ {d.fst, d.snd} := by
        intro z _
        rcases hall z with rfl | rfl <;> simp
      have := Finset.card_le_card hsub
      rw [Finset.card_univ] at this
      have := this.trans Finset.card_le_two
      omega
    · have hsame : SameCycle M.facePerm d.symm (M.facePerm e) :=
        sameCycle_apply_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl _ _))
      have hne' : d.symm.fst ≠ (M.facePerm e).fst := by
        rw [face_fst']
        exact Ne.symm hy
      have hadj := hcorner _ _ hsame hne'
      rw [face_fst'] at hadj
      let x : (indG H Finset.univ).Dart := ⟨(d.snd, e.snd), (indG_univ_adj _ _).2 hadj⟩
      have := rot_fixed_unique M hfix1 (e' := x) rfl
      have hx : e.snd = d.fst := congrArg (fun y : (indG H Finset.univ).Dart => y.snd) this
      exact e.adj.1.ne (hef.trans hx.symm)
  -- every face is a triangle
  have htri : ∀ d : (indG H Finset.univ).Dart, (M.facePerm ^ 3) d = d := by
    intro d
    let W : Finset V := Finset.univ.filter fun v => ∃ e, SameCycle M.facePerm d e ∧ e.fst = v
    have hmemW : ∀ v, v ∈ W ↔ ∃ e, SameCycle M.facePerm d e ∧ e.fst = v := fun v => by
      simp [W]
    refine face_three_of_clique M d W (fun e he => (hmemW _).2 ⟨e, he, rfl⟩) ?_ ?_
    · intro a ha b hb hab
      obtain ⟨e₁, he₁, rfl⟩ := (hmemW a).1 ha
      obtain ⟨e₂, he₂, rfl⟩ := (hmemW b).1 hb
      exact (indG_univ_adj _ _).2 (hcorner e₁ e₂ (he₁.symm.trans he₂) hab)
    · have m0 : d.fst ∈ W := (hmemW _).2 ⟨d, SameCycle.refl _ _, rfl⟩
      have m1 : d.snd ∈ W := (hmemW _).2 ⟨M.facePerm d,
        sameCycle_apply_right.mpr (SameCycle.refl _ _), face_fst' M d⟩
      have m2 : (M.facePerm d).snd ∈ W := (hmemW _).2 ⟨M.facePerm (M.facePerm d),
        sameCycle_apply_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl _ _)),
        face_fst' M _⟩
      have n1 : d.fst ≠ d.snd := d.adj.1.ne
      have n2 : d.fst ≠ (M.facePerm d).snd := Ne.symm (hnoleaf d)
      have n3 : d.snd ≠ (M.facePerm d).snd := by
        rw [← face_fst' M d]; exact (M.facePerm d).adj.1.ne
      have hsub : ({d.fst, d.snd, (M.facePerm d).snd} : Finset V) ⊆ W := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact m0
        · exact m1
        · exact m2
      have hc3 : ({d.fst, d.snd, (M.facePerm d).snd} : Finset V).card = 3 :=
        Finset.card_eq_three.mpr ⟨_, _, _, n1, n2, n3, rfl⟩
      exact hc3 ▸ Finset.card_le_card hsub
  -- a dart
  obtain ⟨x₀, y₀, hxy₀⟩ : ∃ x y : V, x ≠ y := by
    have : 1 < Fintype.card V := by omega
    obtain ⟨x, y, h⟩ := Fintype.exists_pair_of_one_lt_card this
    exact ⟨x, y, h⟩
  obtain ⟨d⟩ : Nonempty (indG H Finset.univ).Dart := by
    obtain ⟨p⟩ := hconn x₀ y₀
    cases p with
    | nil => exact absurd rfl hxy₀
    | cons h _ => exact ⟨⟨(x₀, _), (indG_univ_adj _ _).2 h⟩⟩
  set φ := M.facePerm with hφ
  have h3d : φ (φ (φ d)) = d := by rw [← facePerm_pow_three]; exact htri d
  have f1 : (φ d).fst = d.snd := face_fst' M d
  have f2 : (φ (φ d)).fst = (φ d).snd := face_fst' M _
  have f3 : (φ (φ d)).snd = d.fst := by rw [← face_fst' M (φ (φ d)), h3d]
  refine ⟨H, hGH, d.fst, d.snd, (φ d).snd, ?_⟩
  have n1 : d.fst ≠ d.snd := d.adj.1.ne
  have n2 : d.fst ≠ (φ d).snd := Ne.symm (hnoleaf d)
  have n3 : d.snd ≠ (φ d).snd := by rw [← f1]; exact (φ d).adj.1.ne
  have o0 : IsOuter [d.fst, d.snd, (φ d).snd] d := cycSucc_cons_cons _ _ _
  have o1 : IsOuter [d.fst, d.snd, (φ d).snd] (φ d) := by
    show CycSucc _ (φ d).fst (φ d).snd
    rw [f1]; exact Or.inl ⟨[d.fst], [], rfl⟩
  have o2 : IsOuter [d.fst, d.snd, (φ d).snd] (φ (φ d)) := by
    show CycSucc _ (φ (φ d)).fst (φ (φ d)).snd
    rw [f2, f3]; exact Or.inr ⟨[d.snd], rfl⟩
  refine ⟨?_, by simp, fun v _ => Finset.mem_univ v, ?_, ?_, M, ?_, fun d' _ => htri d'⟩
  · simp [List.nodup_cons, n1, n2, n3]
  · intro p q hpq
    rcases cycSucc_three hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact d.adj.1
    · have := (φ d).adj.1; rwa [f1] at this
    · have := (φ (φ d)).adj.1; rwa [f2, f3] at this
  · intro p _ q _
    rw [indG_univ]
    exact hconn p q
  · intro d' hd'
    have hd'' : CycSucc [d.fst, d.snd, (φ d).snd] d'.fst d'.snd := hd'
    rcases cycSucc_three hd'' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : d' = d := dart_ext' h1 h2
      rw [this]; exact o1
    · have : d' = φ d := dart_ext' (h1.trans f1.symm) h2
      rw [this]; exact o2
    · have : d' = φ (φ d) := dart_ext' (h1.trans f2.symm) (h2.trans f3.symm)
      rw [this, h3d]; exact o0

end ThomassenManyColourings
