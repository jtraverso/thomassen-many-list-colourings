/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Interface
public import Thomassen.ChordSeparation

/-!
# Near-triangulations as plane maps (layer B, part 1)

`PNT H S c`: the graph `rG H S` (the edges of `H` inside `S`, a graph on `V`) is connected on
`S` and has a plane map (genus-zero rotation system, `LeanPool.K5MinorFreeChoosability.PlaneMap`)
whose face permutation maps every dart
`(c_i, c_{i+1})` of the cyclic list `c` to `(c_{i+1}, c_{i+2})` (the outer face is the cycle `c`,
traversed in the order of `c`), and whose other faces are triangles. A list of length two is a
single edge.

This file sets up the cyclic successor relation `CycSucc` and proves the elementary fields of the
interface `NTCalc` for `PNT`: `nodup`, `two_le`, `subset`, `adj_cons`, `rotate`, `reverse` (mirror
map) and `two`.
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

/-! ## The cyclic successor relation -/

/-- `v` follows `u` on the cyclic list `c`. -/
def CycSucc (c : List V) (u v : V) : Prop :=
  (∃ A B, c = A ++ u :: v :: B) ∨ ∃ M, c = v :: (M ++ [u])

omit [DecidableEq V] in
theorem cycSucc_cons_cons (x y : V) (l : List V) : CycSucc (x :: y :: l) x y :=
  Or.inl ⟨[], l, rfl⟩

omit [DecidableEq V] in
theorem CycSucc.mem {c : List V} {u v : V} (h : CycSucc c u v) : u ∈ c ∧ v ∈ c := by
  rcases h with ⟨A, B, rfl⟩ | ⟨M, rfl⟩ <;> simp

omit [DecidableEq V] in
theorem cycSucc_rotate_of {x : V} {l : List V} {u v : V} (h : CycSucc (x :: l) u v) :
    CycSucc (l ++ [x]) u v := by
  rcases h with ⟨A, B, hAB⟩ | ⟨M, hM⟩
  · rcases A with _ | ⟨a, A'⟩
    · simp only [List.nil_append, List.cons.injEq] at hAB
      obtain ⟨rfl, rfl⟩ := hAB
      exact Or.inr ⟨B, by simp⟩
    · simp only [List.cons_append, List.cons.injEq] at hAB
      obtain ⟨rfl, rfl⟩ := hAB
      exact Or.inl ⟨A', B ++ [x], by simp⟩
  · simp only [List.cons.injEq] at hM
    obtain ⟨rfl, rfl⟩ := hM
    exact Or.inl ⟨M, [], by simp⟩

omit [DecidableEq V] in
theorem cycSucc_rotate_to {x : V} {l : List V} {u v : V} (h : CycSucc (l ++ [x]) u v) :
    CycSucc (x :: l) u v := by
  rcases h with ⟨A, B, hAB⟩ | ⟨M, hM⟩
  · rcases B.eq_nil_or_concat with rfl | ⟨B', b, rfl⟩
    · have h1 : l ++ [x] = (A ++ [u]) ++ [v] := by rw [hAB]; simp
      obtain ⟨hl, hx⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, and_true] at hx
      subst hx; subst hl
      exact Or.inr ⟨A, rfl⟩
    · have h1 : l ++ [x] = (A ++ u :: v :: B') ++ [b] := by rw [hAB]; simp
      obtain ⟨hl, hx⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, and_true] at hx
      subst hx; subst hl
      exact Or.inl ⟨x :: A, B', by simp⟩
  · have h1 : l ++ [x] = (v :: M) ++ [u] := by rw [hM]; simp
    obtain ⟨hl, hx⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at hx
    subst hx; subst hl
    exact Or.inl ⟨[], M, rfl⟩

omit [DecidableEq V] in
theorem cycSucc_rotate {x : V} {l : List V} {u v : V} :
    CycSucc (x :: l) u v ↔ CycSucc (l ++ [x]) u v :=
  ⟨cycSucc_rotate_of, cycSucc_rotate_to⟩

omit [DecidableEq V] in
theorem cycSucc_reverse_of {c : List V} {u v : V} (h : CycSucc c u v) :
    CycSucc c.reverse v u := by
  rcases h with ⟨A, B, rfl⟩ | ⟨M, rfl⟩
  · exact Or.inl ⟨B.reverse, A.reverse, by simp⟩
  · exact Or.inr ⟨M.reverse, by simp⟩

omit [DecidableEq V] in
theorem cycSucc_reverse {c : List V} {u v : V} : CycSucc c.reverse u v ↔ CycSucc c v u :=
  ⟨fun h => by simpa using cycSucc_reverse_of h, cycSucc_reverse_of⟩

omit [DecidableEq V] in
/-- In a repetition-free list the prefix before an entry is determined. -/
theorem split_unique : ∀ {A A' X X' : List V} {u : V}, (A ++ u :: X).Nodup →
    A ++ u :: X = A' ++ u :: X' → A = A' ∧ X = X'
  | [], [], _, _, _, _, h => by simpa using h
  | [], a' :: A', X, X', u, hnd, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd (by simp : u ∈ A' ++ u :: X') (List.nodup_cons.mp hnd).1
  | a :: A, [], X, X', u, hnd, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd (by simp : a ∈ A ++ a :: X) (List.nodup_cons.mp hnd).1
  | a :: A, a' :: A', X, X', u, hnd, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h1, h2⟩ := split_unique (List.nodup_cons.mp hnd).2 h
    exact ⟨by rw [h1], h2⟩

omit [DecidableEq V] in
theorem not_last_of_mid {c A B : List V} {u v : V} (hnd : c.Nodup) (hc : c = A ++ u :: v :: B)
    (hl : c.getLast? = some u) : False := by
  subst hc
  have : (A ++ u :: v :: B).getLast? = (v :: B).getLast? := by
    rw [show A ++ u :: v :: B = (A ++ [u]) ++ v :: B by simp, List.getLast?_append_of_ne_nil]
    simp
  rw [this] at hl
  have hu : u ∈ v :: B := List.mem_of_mem_getLast? hl
  exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (by
    simp only [List.mem_cons] at hu ⊢; tauto)

omit [DecidableEq V] in
/-- The cyclic successor in a repetition-free list is unique. -/
theorem CycSucc.unique {c : List V} {u v v' : V} (hnd : c.Nodup) (h : CycSucc c u v)
    (h' : CycSucc c u v') : v = v' := by
  rcases h with ⟨A, B, hAB⟩ | ⟨M, hM⟩ <;> rcases h' with ⟨A', B', hAB'⟩ | ⟨M', hM'⟩
  · have := split_unique (hAB ▸ hnd) (hAB.symm.trans hAB')
    simp only [List.cons.injEq] at this
    exact this.2.1
  · exact (not_last_of_mid hnd hAB (by rw [hM', ← List.cons_append, List.getLast?_append]; simp)).elim
  · exact (not_last_of_mid hnd hAB' (by rw [hM, ← List.cons_append, List.getLast?_append]; simp)).elim
  · rw [hM] at hM'; simp only [List.cons.injEq] at hM'; exact hM'.1

omit [DecidableEq V] in
/-- The cyclic predecessor in a repetition-free list is unique. -/
theorem CycSucc.unique_left {c : List V} {u u' v : V} (hnd : c.Nodup) (h : CycSucc c u v)
    (h' : CycSucc c u' v) : u = u' :=
  CycSucc.unique (List.nodup_reverse.mpr hnd) (cycSucc_reverse_of h) (cycSucc_reverse_of h')

omit [DecidableEq V] in
/-- Every entry of a list of length at least two has a cyclic successor. -/
theorem exists_cycSucc {c : List V} (h2 : 2 ≤ c.length) {u : V} (hu : u ∈ c) :
    ∃ v, CycSucc c u v := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hu
  rcases B with _ | ⟨v, B⟩
  · rcases A with _ | ⟨a, A⟩
    · simp at h2
    · exact ⟨a, Or.inr ⟨A, by simp⟩⟩
  · exact ⟨v, Or.inl ⟨A, B, rfl⟩⟩

omit [DecidableEq V] in
/-- Every entry of a list of length at least two has a cyclic predecessor. -/
theorem exists_cycSucc_left {c : List V} (h2 : 2 ≤ c.length) {v : V} (hv : v ∈ c) :
    ∃ u, CycSucc c u v := by
  obtain ⟨u, hu⟩ := exists_cycSucc (c := c.reverse) (by simpa using h2) (List.mem_reverse.mpr hv)
  exact ⟨u, cycSucc_reverse.mp hu⟩


omit [DecidableEq V] in
/-- `CycSucc` is invariant under every rotation. -/
theorem cycSucc_rot_append : ∀ (A : List V) {B : List V} {u v : V},
    CycSucc (A ++ B) u v ↔ CycSucc (B ++ A) u v
  | [], B, u, v => by simp
  | x :: A, B, u, v => by
    rw [List.cons_append, cycSucc_rotate, List.append_assoc, cycSucc_rot_append A]
    simp

omit [DecidableEq V] in
/-- The successor of the head of a repetition-free list is its second entry. -/
theorem cycSucc_head {a b : V} {R : List V} (hnd : (a :: R).Nodup)
    (h : CycSucc (a :: R) a b) : R.head? = some b := by
  rcases h with ⟨A, B, hAB⟩ | ⟨M, hM⟩
  · rcases A with _ | ⟨a', A'⟩
    · simp only [List.nil_append, List.cons.injEq] at hAB
      rw [hAB.2]; simp
    · simp only [List.cons_append, List.cons.injEq] at hAB
      obtain ⟨rfl, hR⟩ := hAB
      exact absurd (by rw [hR]; simp) (List.nodup_cons.mp hnd).1
  · simp only [List.cons.injEq] at hM
    obtain ⟨rfl, hR⟩ := hM
    exact absurd (by rw [hR]; simp) (List.nodup_cons.mp hnd).1

omit [DecidableEq V] in
/-- The predecessor of the head of a repetition-free list is its last entry. -/
theorem cycSucc_to_head {a p : V} {R : List V} (hnd : (a :: R).Nodup)
    (h : CycSucc (a :: R) p a) : R.getLast? = some p := by
  rcases h with ⟨A, B, hAB⟩ | ⟨M, hM⟩
  · rcases A with _ | ⟨a', A'⟩
    · simp only [List.nil_append, List.cons.injEq] at hAB
      obtain ⟨rfl, hR⟩ := hAB
      exact absurd (by rw [hR]; simp) (List.nodup_cons.mp hnd).1
    · simp only [List.cons_append, List.cons.injEq] at hAB
      obtain ⟨rfl, hR⟩ := hAB
      exact absurd (by rw [hR]; simp) (List.nodup_cons.mp hnd).1
  · simp only [List.cons.injEq] at hM
    rw [hM.2]; simp

omit [DecidableEq V] in
/-- In a cycle with at least three vertices the successor and the predecessor differ. -/
theorem cycSucc_succ_ne_pred {C : List V} (hnd : C.Nodup) (h3 : 3 ≤ C.length) {a b p : V}
    (hab : CycSucc C a b) (hpa : CycSucc C p a) : p ≠ b := by
  rintro rfl
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hab.mem.1
  have hrot : ∀ u v, CycSucc (A ++ a :: B) u v ↔ CycSucc (a :: (B ++ A)) u v := by
    intro u v; rw [cycSucc_rot_append A]; simp
  have hnd' : (a :: (B ++ A)).Nodup := by
    have := (List.perm_append_comm (l₁ := A) (l₂ := a :: B)).nodup_iff.mp hnd
    simpa using this
  have h1 := cycSucc_head hnd' ((hrot _ _).1 hab)
  have h2 := cycSucc_to_head hnd' ((hrot _ _).1 hpa)
  have hBA : (B ++ A).Nodup := (List.nodup_cons.mp hnd').2
  -- head and last of `B ++ A` coincide, so it has length one
  rcases hBA' : B ++ A with _ | ⟨q, Q⟩
  · rw [hBA'] at h1; simp at h1
  · rw [hBA'] at h1 h2 hBA
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rcases Q with _ | ⟨z, Z⟩
    · have := congrArg List.length hBA'
      simp only [List.length_append, List.length_cons, List.length_nil] at this h3
      omega
    · rw [List.getLast?_cons_cons] at h2
      exact (List.nodup_cons.mp hBA).1 (List.mem_of_mem_getLast? h2)

omit [DecidableEq V] in
/-- A property of the head of a list propagated along consecutive entries holds everywhere. -/
theorem forall_of_chain {Q : V → Prop} : ∀ {l : List V},
    (∀ x, l.head? = some x → Q x) → (∀ A u v B, l = A ++ u :: v :: B → Q u → Q v) →
    ∀ x ∈ l, Q x
  | [], _, _ => by simp
  | x :: l, hh, hs => by
    have hx : Q x := hh x rfl
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · refine forall_of_chain (l := l) (fun z hz => ?_) (fun A u v B h => hs (x :: A) u v B
        (by rw [h]; simp)) y hy
      rcases l with _ | ⟨w, l'⟩
      · simp at hz
      · simp only [List.head?_cons, Option.some.injEq] at hz
        subst hz
        exact hs [] x w l' rfl hx

omit [DecidableEq V] in
/-- A property closed under the cyclic successor holds on the whole cycle once it holds at one
vertex. -/
theorem forall_of_cycSucc_closed {C : List V} {Q : V → Prop} {a₀ : V} (ha₀ : a₀ ∈ C)
    (hQ : Q a₀) (hs : ∀ u v, CycSucc C u v → Q u → Q v) : ∀ x ∈ C, Q x := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ha₀
  have hrot : ∀ u v, CycSucc (a₀ :: (B ++ A)) u v → CycSucc (A ++ a₀ :: B) u v := by
    intro u v h
    rw [cycSucc_rot_append A]
    simpa using h
  have hall := forall_of_chain (Q := Q) (l := a₀ :: (B ++ A))
    (fun x hx => by simp only [List.head?_cons, Option.some.injEq] at hx; exact hx ▸ hQ)
    (fun A' u v B' h hu => hs u v (hrot u v (Or.inl ⟨A', B', h⟩)) hu)
  intro x hx
  exact hall x (by simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)

/-! ## The mirror image of a plane map -/

section Mirror

variable {G : SimpleGraph V}

theorem cycleCount_inv_perm {D : Type*} (σ : Perm D) : cycleCount σ⁻¹ = cycleCount σ := by
  unfold cycleCount
  congr 1
  exact Setoid.ext fun _ _ => sameCycle_inv

theorem numComponents_inv_perm {D : Type*} (σ α : Perm D) :
    numComponents σ⁻¹ α = numComponents σ α := by
  unfold numComponents
  congr 1
  apply le_antisymm
  · intro a b h
    exact compSetoid_le (compSetoid σ α)
      (fun z => compSetoid_of_sameCycle_left (⟨-1, by simp⟩ : SameCycle σ z (σ⁻¹ z)))
      (compSetoid_right σ α) h
  · intro a b h
    exact compSetoid_le (compSetoid σ⁻¹ α)
      (fun z => compSetoid_of_sameCycle_left (⟨-1, by simp⟩ : SameCycle σ⁻¹ z (σ z)))
      (compSetoid_right σ⁻¹ α) h

/-- The mirror image of a plane map: the rotation reversed at every vertex. -/
def mirrorMap (M : PlaneMap G) : PlaneMap G where
  rot := M.rot⁻¹
  isRotationSystem :=
    { fst_apply := fun d => by
        have h := M.isRotationSystem.fst_apply (M.rot⁻¹ d)
        rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at h
        exact h.symm
      sameCycle := fun d e h => (M.isRotationSystem.sameCycle d e h).inv }
  eulerDefect_eq_zero := by
    have hconj : M.rot⁻¹ * dartSymm G = (dartSymm G).permCongr (M.rot * dartSymm G)⁻¹ := by
      apply Equiv.ext
      intro d
      have hs : ∀ e : G.Dart, (dartSymm G)⁻¹ e = e.symm := fun e => by
        rw [Perm.inv_eq_iff_eq]; simp [dartSymm_apply]
      have hs' : ∀ e : G.Dart, (dartSymm G).symm e = e.symm := hs
      rw [Equiv.permCongr_apply, mul_inv_rev, Perm.mul_apply, Perm.mul_apply, hs', hs]
      simp [dartSymm_apply]
    unfold eulerDefect
    rw [numComponents_inv_perm, cycleCount_inv_perm, hconj, cycleCount_permCongr,
      cycleCount_inv_perm]
    exact M.eulerDefect_eq_zero

theorem mirrorMap_facePerm (M : PlaneMap G) (d : G.Dart) :
    (mirrorMap M).facePerm d = (M.facePerm⁻¹ d.symm).symm := by
  have h : M.facePerm (M.rot⁻¹ d.symm).symm = d.symm := by
    rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm, ← Perm.mul_apply, mul_inv_cancel,
      Perm.one_apply]
  rw [← h, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply, SimpleGraph.Dart.symm_symm]
  rfl

end Mirror

/-! ## Plane near-triangulations -/

/-- The edges of `H` inside `S`, as a graph on `V`. -/
abbrev indG (H : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  restrict H (S : Set V)

/-- A dart of `H[S]` on the outer cycle `c`. -/
def IsOuter {H : SimpleGraph V} {S : Finset V} (c : List V) (d : (indG H S).Dart) : Prop :=
  CycSucc c d.fst d.snd

/-- The face conditions of a plane map of `H[S]` with outer cycle `c`. -/
def IsNTMap {H : SimpleGraph V} {S : Finset V} (c : List V) (M : PlaneMap (indG H S)) : Prop :=
  (∀ d, IsOuter c d → IsOuter c (M.facePerm d)) ∧ ∀ d, ¬ IsOuter c d → (M.facePerm ^ 3) d = d

/-- **Plane near-triangulation**: `H` inside `S` is connected, `c` is a cycle of it (an edge when
it has length two), and some plane map of it has outer face `c` and triangular inner faces. -/
def PNT (H : SimpleGraph V) (S : Finset V) (c : List V) : Prop :=
  c.Nodup ∧ 2 ≤ c.length ∧ (∀ v ∈ c, v ∈ S) ∧ (∀ u v, CycSucc c u v → H.Adj u v) ∧
    (∀ u ∈ S, ∀ v ∈ S, (indG H S).Reachable u v) ∧ ∃ M : PlaneMap (indG H S), IsNTMap c M

namespace PNT

variable {H : SimpleGraph V} {S : Finset V} {c : List V}

theorem nodup (h : PNT H S c) : c.Nodup := h.1
theorem two_le (h : PNT H S c) : 2 ≤ c.length := h.2.1
theorem subset (h : PNT H S c) : ∀ v ∈ c, v ∈ S := h.2.2.1
theorem adj (h : PNT H S c) {u v : V} (huv : CycSucc c u v) : H.Adj u v := h.2.2.2.1 u v huv

theorem adj_cons {x y : V} {l : List V} (h : PNT H S (x :: y :: l)) : H.Adj x y :=
  h.adj (cycSucc_cons_cons x y l)

theorem rotate {x : V} {l : List V} (h : PNT H S (x :: l)) : PNT H S (l ++ [x]) := by
  obtain ⟨hnd, h2, hsub, hadj, hconn, M, hout, hin⟩ := h
  have hiff : ∀ d : (indG H S).Dart, IsOuter (x :: l) d ↔ IsOuter (l ++ [x]) d :=
    fun d => cycSucc_rotate
  refine ⟨?_, by simpa using h2, fun v hv => hsub v (by simp at hv ⊢; tauto),
    fun u v huv => hadj u v (cycSucc_rotate.mpr huv), hconn, M, fun d hd => ?_, fun d hd => ?_⟩
  · have : (l ++ [x]).Perm (x :: l) := List.perm_append_singleton x l
    exact this.nodup_iff.mpr hnd
  · exact (hiff _).1 (hout d ((hiff d).2 hd))
  · exact hin d (fun h' => hd ((hiff d).1 h'))

/-- The dart of `H[S]` from `u` to `v`. -/
def mkDart {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : H.Adj u v) : (indG H S).Dart :=
  ⟨(u, v), huv, hu, hv⟩

theorem face_fst (M : PlaneMap (indG H S)) (d : (indG H S).Dart) :
    (M.facePerm d).fst = d.snd := M.isRotationSystem.fst_apply _

theorem dart_eq {d e : (indG H S).Dart} (h1 : d.fst = e.fst) (h2 : d.snd = e.snd) :
    d = e := by
  rcases d with ⟨⟨a, b⟩, h⟩
  rcases e with ⟨⟨a', b'⟩, h'⟩
  simp only at h1 h2
  subst h1; subst h2; rfl

/-- The outer darts are also closed under the inverse face permutation. -/
theorem outer_inv (h : PNT H S c) {M : PlaneMap (indG H S)} (hM : IsNTMap c M)
    {e : (indG H S).Dart} (he : IsOuter c e) : IsOuter c (M.facePerm⁻¹ e) := by
  obtain ⟨w, hw⟩ := exists_cycSucc_left h.two_le he.mem.1
  have hwS : w ∈ S := h.subset w hw.mem.1
  let p := mkDart hwS e.adj.2.1 (h.adj hw)
  have hp : IsOuter c p := hw
  have hfp := hM.1 p hp
  have heq : M.facePerm p = e := by
    apply dart_eq
    · rw [face_fst]; rfl
    · have h1 : (M.facePerm p).fst = e.fst := by rw [face_fst]; rfl
      unfold IsOuter at hfp he
      rw [h1] at hfp
      exact CycSucc.unique h.nodup hfp he
  rw [← heq, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  exact hp

theorem reverse (h : PNT H S c) : PNT H S c.reverse := by
  have h' := h
  obtain ⟨hnd, h2, hsub, hadj, hconn, M, hout, hin⟩ := h
  have hM : IsNTMap c M := ⟨hout, hin⟩
  have hiff : ∀ d : (indG H S).Dart, IsOuter c.reverse d ↔ IsOuter c d.symm :=
    fun d => cycSucc_reverse
  have hfp : ∀ d, (mirrorMap M).facePerm d = (M.facePerm⁻¹ d.symm).symm :=
    mirrorMap_facePerm M
  have hpow : ∀ n : ℕ, ∀ d, ((mirrorMap M).facePerm ^ n) d =
      ((M.facePerm⁻¹ ^ n) d.symm).symm := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      rw [pow_succ', Perm.mul_apply, ih, hfp, pow_succ', Perm.mul_apply]
      simp
  refine ⟨List.nodup_reverse.mpr hnd, by simpa using h2, fun v hv => hsub v (by simpa using hv),
    fun u v huv => (hadj v u (cycSucc_reverse.mp huv)).symm, hconn,
    mirrorMap M, fun d hd => ?_, fun d hd => ?_⟩
  · rw [hiff, hfp, SimpleGraph.Dart.symm_symm]
    exact h'.outer_inv hM ((hiff d).1 hd)
  · have hd' : ¬ IsOuter c d.symm := fun e => hd ((hiff d).2 e)
    rw [hpow, inv_pow]
    have h3 := hin d.symm hd'
    have : ((M.facePerm ^ 3)⁻¹) d.symm = d.symm := by
      rw [Perm.inv_eq_iff_eq]; exact h3.symm
    rw [this, SimpleGraph.Dart.symm_symm]

/-- The only dart at `y` of a plane map fixing `(y, x)` under the rotation. -/
theorem nbr_unique {M : PlaneMap (indG H S)} {e : (indG H S).Dart} (hfix : M.rot e = e)
    {e' : (indG H S).Dart} (he' : e'.fst = e.fst) : e' = e :=
  ((M.isRotationSystem.sameCycle e e' he'.symm).eq_of_left hfix).symm

theorem two {x y : V} (h : PNT H S [x, y]) : S = {x, y} := by
  obtain ⟨hnd, h2, hsub, hadj, hconn, M, hout, hin⟩ := h
  have hxS := hsub x (by simp)
  have hyS := hsub y (by simp)
  have hxy : H.Adj x y := hadj x y (cycSucc_cons_cons x y [])
  let dxy := mkDart hxS hyS hxy
  let dyx := mkDart hyS hxS hxy.symm
  have hsucc : ∀ u v v', CycSucc [x, y] u v → CycSucc [x, y] u v' → v = v' :=
    fun u v v' => CycSucc.unique hnd
  have oxy : IsOuter [x, y] dxy := cycSucc_cons_cons x y []
  have oyx : IsOuter [x, y] dyx := Or.inr ⟨[], rfl⟩
  -- the rotation fixes `(y, x)` and `(x, y)`
  have fix_y : M.rot dyx = dyx := by
    have h1 := hout dxy oxy
    have : M.facePerm dxy = dyx := by
      apply dart_eq
      · rw [face_fst]; rfl
      · have hf : (M.facePerm dxy).fst = y := by rw [face_fst]; rfl
        unfold IsOuter at h1
        rw [hf] at h1
        exact hsucc y _ x h1 oyx
    rw [PlaneMap.facePerm_apply] at this
    exact this
  have fix_x : M.rot dxy = dxy := by
    have h1 := hout dyx oyx
    have : M.facePerm dyx = dxy := by
      apply dart_eq
      · rw [face_fst]; rfl
      · have hf : (M.facePerm dyx).fst = x := by rw [face_fst]; rfl
        unfold IsOuter at h1
        rw [hf] at h1
        exact hsucc x _ y h1 oxy
    rw [PlaneMap.facePerm_apply] at this
    exact this
  -- every vertex reachable from `x` is `x` or `y`
  have hnb : ∀ (a b : V), (indG H S).Adj a b → a = x ∨ a = y → b = x ∨ b = y := by
    intro a b hab ha
    rcases ha with ha | ha
    · have := nbr_unique fix_x (e' := ⟨(a, b), hab⟩) ha
      exact Or.inr (congrArg (fun d : (indG H S).Dart => d.snd) this)
    · have := nbr_unique fix_y (e' := ⟨(a, b), hab⟩) ha
      exact Or.inl (congrArg (fun d : (indG H S).Dart => d.snd) this)
  have hwalk : ∀ (a b : V) (p : (indG H S).Walk a b), a = x ∨ a = y → b = x ∨ b = y := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hadj' _ ih => exact fun ha => ih (hnb _ _ hadj' ha)
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    obtain ⟨p⟩ := hconn x hxS z hz
    exact hwalk _ _ p (Or.inl rfl)
  · rintro (rfl | rfl) <;> assumption

end PNT

end ThomassenManyColourings
