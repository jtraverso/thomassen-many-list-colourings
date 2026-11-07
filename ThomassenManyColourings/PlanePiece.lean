/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.FaceBracket

/-!
# Pieces of a plane near-triangulation (layer B, part 3)

For `PNT H S c` with map `M` and a subset `S₁ ⊆ S`, the restriction of `M` to the edges inside
`S₁` (`Grotzsch.restrictMap`) keeps every triangle of `M` whose three vertices lie in `S₁`
(`restrictMap_facePerm_eq`). Let `R` be the set of darts inside `S₁` that are outer darts of `M`
or whose triangle leaves `S₁` (`PieceR`). If `R` contains a forward dart of a cycle `C₁` of
`S₁`, is contained in the forward and backward darts of `C₁`, and misses some backward dart, then
`H` on `S₁` is a plane near-triangulation with outer cycle `C₁` (`piece_PNT`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- A dart fixed by the rotation is the only dart at its tail. -/
theorem rot_fixed_unique {G : SimpleGraph V} (M : PlaneMap G) {e : G.Dart} (hfix : M.rot e = e)
    {e' : G.Dart} (he' : e'.fst = e.fst) : e' = e :=
  ((M.isRotationSystem.sameCycle e e' he'.symm).eq_of_left hfix).symm

omit [DecidableEq V] [Fintype V] in
theorem face_fst' {G : SimpleGraph V} (M : PlaneMap G) (d : G.Dart) :
    (M.facePerm d).fst = d.snd := M.isRotationSystem.fst_apply _

omit [DecidableEq V] [Fintype V] in
theorem facePerm_pow_three {G : SimpleGraph V} (M : PlaneMap G) (d : G.Dart) :
    (M.facePerm ^ 3) d = M.facePerm (M.facePerm (M.facePerm d)) := by
  simp [pow_succ, Perm.mul_apply]

omit [DecidableEq V] in
/-- The restricted map follows the original face permutation whenever the next dart of the
original face stays in the subgraph. -/
theorem restrictMap_facePerm_eq {G H' : SimpleGraph V} (M : PlaneMap G) (hH : H' ≤ G)
    (d : H'.Dart) (hin : H'.Adj (M.facePerm (Grotzsch.toDart hH d)).fst
      (M.facePerm (Grotzsch.toDart hH d)).snd) :
    Grotzsch.toDart hH ((Grotzsch.restrictMap M hH).facePerm d) =
      M.facePerm (Grotzsch.toDart hH d) := by
  have h := Grotzsch.eq_of_isNextH_of_inH M hH (d := M.rot (Grotzsch.toDart hH d.symm)) hin
    (Grotzsch.isNextH_rot_subRot M hH d.symm)
  rw [PlaneMap.facePerm_apply, PlaneMap.facePerm_apply]
  exact h.symm

variable {H : SimpleGraph V} {S S₁ : Finset V} {c : List V}

omit [DecidableEq V] [Fintype V] in
theorem restrict_mono (hS : S₁ ⊆ S) : indG H S₁ ≤ indG H S := fun _ _ h =>
  ⟨h.1, Finset.mem_coe.mpr (hS (Finset.mem_coe.mp h.2.1)),
    Finset.mem_coe.mpr (hS (Finset.mem_coe.mp h.2.2))⟩

/-- The darts of a piece that are outer darts of `M` or whose triangle leaves the piece. -/
def PieceR (M : PlaneMap (indG H S)) (c : List V) (hS : S₁ ⊆ S) (d : (indG H S₁).Dart) : Prop :=
  IsOuter c (Grotzsch.toDart (restrict_mono hS) d) ∨
    (M.facePerm (Grotzsch.toDart (restrict_mono hS) d)).snd ∉ S₁

omit [DecidableEq V] in
theorem indG_adj_of {u v : V} (huv : H.Adj u v) (hu : u ∈ S₁) (hv : v ∈ S₁) :
    (indG H S₁).Adj u v :=
  ⟨huv, Finset.mem_coe.mpr hu, Finset.mem_coe.mpr hv⟩

set_option maxHeartbeats 4000000 in
/-- **Pieces**: the restriction of a near-triangulation to a piece bounded by a cycle `C₁` is a
near-triangulation with outer cycle `C₁`. -/
theorem piece_PNT (hP : PNT H S c) {M : PlaneMap (indG H S)} (hM : IsNTMap c M) (hS : S₁ ⊆ S)
    {C₁ : List V} (hnd₁ : C₁.Nodup) (h3 : 3 ≤ C₁.length) (hsub₁ : ∀ v ∈ C₁, v ∈ S₁)
    (hadj₁ : ∀ u v, CycSucc C₁ u v → H.Adj u v)
    (hreach : ∀ u ∈ S₁, ∀ v ∈ S₁, (indG H S₁).Reachable u v)
    (hone : ∃ d : (indG H S₁).Dart, CycSucc C₁ d.fst d.snd ∧ PieceR M c hS d)
    (hsubR : ∀ d : (indG H S₁).Dart, PieceR M c hS d →
      CycSucc C₁ d.fst d.snd ∨ CycSucc C₁ d.snd d.fst)
    (hmiss : ∃ a b, CycSucc C₁ a b ∧
      ∀ d : (indG H S₁).Dart, PieceR M c hS d → d.fst = b → d.snd ≠ a) :
    PNT H S₁ C₁ := by
  classical
  set M₁ := Grotzsch.restrictMap M (restrict_mono hS) with hM₁
  set φ := M₁.facePerm with hφ
  set td := Grotzsch.toDart (restrict_mono (H := H) hS) with htd
  have hφfst : ∀ d, (φ d).fst = d.snd := fun d => face_fst' M₁ d
  -- triangles inside the piece are kept
  have hstep : ∀ d, ¬ PieceR M c hS d → td (φ d) = M.facePerm (td d) ∧ ¬ PieceR M c hS (φ d) := by
    intro d hd
    simp only [PieceR, not_or, not_not] at hd
    have hin : (indG H S₁).Adj (M.facePerm (td d)).fst (M.facePerm (td d)).snd := by
      refine ⟨(M.facePerm (td d)).adj.1, ?_, Finset.mem_coe.mpr hd.2⟩
      rw [face_fst']
      exact d.adj.2.2
    have he := restrictMap_facePerm_eq M (restrict_mono hS) d hin
    change td (φ d) = M.facePerm (td d) at he
    refine ⟨he, ?_⟩
    rintro (ho | hno)
    · change IsOuter c (td (φ d)) at ho
      rw [he] at ho
      have := hP.outer_inv hM ho
      rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at this
      exact hd.1 this
    · change (M.facePerm (td (φ d))).snd ∉ S₁ at hno
      rw [he] at hno
      have h3' := hM.2 (td d) hd.1
      have hfst := face_fst' M (M.facePerm (M.facePerm (td d)))
      rw [← facePerm_pow_three, h3'] at hfst
      rw [← hfst] at hno
      exact hno (Finset.mem_coe.mp d.adj.2.1)
  -- the set `R` is invariant
  have hRinv : ∀ d, PieceR M c hS d → PieceR M c hS (φ d) := by
    intro d hd
    by_contra hn
    let Rc := (Finset.univ : Finset (indG H S₁).Dart).filter (fun e => ¬ PieceR M c hS e)
    have hmaps : ∀ e ∈ Rc, φ e ∈ Rc := fun e he => by
      simp only [Rc, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact (hstep e he).2
    have himg := image_eq_of_mapsTo φ Rc hmaps
    have hmem : φ d ∈ Rc := by simp only [Rc, Finset.mem_filter, Finset.mem_univ, true_and]; exact hn
    rw [← himg] at hmem
    obtain ⟨e, he, hed⟩ := Finset.mem_image.mp hmem
    have := φ.injective hed
    subst this
    simp only [Rc, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact he hd
  -- every forward dart of `C₁` lies in `R`
  have hfwd : ∀ d : (indG H S₁).Dart, CycSucc C₁ d.fst d.snd → PieceR M c hS d := by
    obtain ⟨d₀, hd₀f, hd₀R⟩ := hone
    let Q : V → Prop := fun a => ∀ d : (indG H S₁).Dart, d.fst = a →
      CycSucc C₁ d.fst d.snd → PieceR M c hS d
    have hQ0 : Q d₀.fst := by
      intro d hd hdf
      have : d = d₀ := dart_ext' hd (CycSucc.unique hnd₁ (hd ▸ hdf) hd₀f)
      rw [this]; exact hd₀R
    have hs : ∀ u v, CycSucc C₁ u v → Q u → Q v := by
      intro u v huv hu d hdv hdf
      let e : (indG H S₁).Dart :=
        ⟨(u, v), indG_adj_of (hadj₁ u v huv) (hsub₁ u huv.mem.1) (hsub₁ v huv.mem.2)⟩
      have heR : PieceR M c hS e := hu e rfl huv
      have hφR := hRinv e heR
      have h1 : (φ e).fst = v := hφfst e
      rcases hsubR (φ e) hφR with hf | hb
      · have : φ e = d := dart_ext' (h1.trans hdv.symm)
          (CycSucc.unique hnd₁ (h1 ▸ hf) (hdv ▸ hdf))
        rw [← this]; exact hφR
      · exfalso
        have h2 : (φ e).snd = u := CycSucc.unique_left hnd₁ (h1 ▸ hb) huv
        have hfix : M₁.rot e.symm = e.symm := by
          have : φ e = e.symm := dart_ext' h1 h2
          rwa [hφ, PlaneMap.facePerm_apply] at this
        obtain ⟨w, hvw⟩ := exists_cycSucc (by omega) huv.mem.2
        let f : (indG H S₁).Dart :=
          ⟨(v, w), indG_adj_of (hadj₁ v w hvw) (hsub₁ v hvw.mem.1) (hsub₁ w hvw.mem.2)⟩
        have hfe := rot_fixed_unique M₁ hfix (e' := f) rfl
        have hw : w = u := congrArg (fun z : (indG H S₁).Dart => z.snd) hfe
        exact cycSucc_succ_ne_pred hnd₁ h3 hvw huv hw.symm
    intro d hdf
    exact forall_of_cycSucc_closed hd₀f.mem.1 hQ0 hs d.fst hdf.mem.1 d rfl hdf
  -- the bracket: `R` is exactly the set of forward darts
  let R := (Finset.univ : Finset (indG H S₁).Dart).filter (fun e => PieceR M c hS e)
  have hRmem : ∀ e, e ∈ R ↔ PieceR M c hS e := fun e => by simp [R]
  have hbr := bracket_fwd φ hφfst R (fun d hd => (hRmem _).2 (hRinv d ((hRmem d).1 hd))) C₁ hnd₁ h3
    (fun u v huv => indG_adj_of (hadj₁ u v huv) (hsub₁ u huv.mem.1) (hsub₁ v huv.mem.2))
    (fun d hd => (hRmem d).2 (hfwd d hd)) (fun d hd => hsubR d ((hRmem d).1 hd))
    (by
      obtain ⟨a, b, hab, hm⟩ := hmiss
      exact ⟨a, b, hab, fun r hr => hm r ((hRmem r).1 hr)⟩)
  have hRfwd : ∀ d, PieceR M c hS d ↔ CycSucc C₁ d.fst d.snd :=
    fun d => ⟨fun h => hbr d ((hRmem d).2 h), hfwd d⟩
  refine ⟨hnd₁, by omega, hsub₁, hadj₁, hreach, M₁, fun d hd => ?_, fun d hd => ?_⟩
  · exact (hRfwd _).1 (hRinv d ((hRfwd d).2 hd))
  · have hd' : ¬ PieceR M c hS d := fun h => hd ((hRfwd d).1 h)
    obtain ⟨e1, n1⟩ := hstep d hd'
    obtain ⟨e2, n2⟩ := hstep (φ d) n1
    obtain ⟨e3, -⟩ := hstep (φ (φ d)) n2
    apply Grotzsch.toDart_injective (restrict_mono hS)
    change td ((φ ^ 3) d) = td d
    rw [facePerm_pow_three, e3, e2, e1, ← facePerm_pow_three]
    have hno : ¬ IsOuter c (td d) := fun h => hd' (Or.inl h)
    exact hM.2 (td d) hno

end ThomassenManyColourings
