/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneNT

/-!
# Recognising a face from a dart count (layer B, part 2)

Let `φ` be a permutation of the darts of a finite graph with `(φ d).fst = d.snd` (a face
permutation), `C` a cycle with at least three vertices, and `R` a `φ`-invariant set of darts
containing every forward dart `(c_i, c_{i+1})` of `C` and contained in the forward and backward
darts of `C`. At every vertex `φ` maps the darts of `R` entering it bijectively onto the darts of
`R` leaving it, so a backward dart of `C` in `R` forces the previous backward dart. If some
backward dart is missing, `R` consists of forward darts only (`bracket_fwd`), and `φ` runs along
`C` (`bracket_step`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem dart_ext' {d e : G.Dart} (h1 : d.fst = e.fst) (h2 : d.snd = e.snd) : d = e := by
  rcases d with ⟨⟨a, b⟩, h⟩
  rcases e with ⟨⟨a', b'⟩, h'⟩
  simp only at h1 h2
  subst h1; subst h2; rfl

section Bracket

variable [Fintype G.Dart] (φ : Perm G.Dart) (hφ : ∀ d, (φ d).fst = d.snd) (R : Finset G.Dart)
  (hR : ∀ d ∈ R, φ d ∈ R) (C : List V)

include hR in
omit [DecidableEq V] [Fintype G.Dart] in
/-- A permutation mapping a finite set into itself maps it onto itself. -/
theorem image_eq_of_mapsTo [DecidableEq G.Dart] : R.image φ = R := by
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    exact hR d hd
  · rw [Finset.card_image_of_injective _ φ.injective]

include hφ hR in
/-- At every vertex, as many darts of `R` enter as leave. -/
theorem card_in_eq_card_out (v : V) :
    (R.filter (fun d => d.snd = v)).card = (R.filter (fun d => d.fst = v)).card := by
  classical
  have himg : (R.filter (fun d => d.snd = v)).image φ = R.filter (fun d => d.fst = v) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨d, ⟨hd, hdv⟩, rfl⟩
      exact ⟨hR d hd, by rw [hφ, hdv]⟩
    · rintro ⟨he, hev⟩
      have : e ∈ R.image φ := by rw [image_eq_of_mapsTo φ R hR]; exact he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp this
      exact ⟨d, ⟨hd, by rw [← hφ]; exact hev⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injective _ φ.injective]

include hφ hR in
/-- **Propagation**: a backward dart `(b, a)` in `R` forces the backward dart `(a, p)`, where `p`
precedes `a`. -/
theorem bwd_prev (hnd : C.Nodup) (h3 : 3 ≤ C.length)
    (hfwd : ∀ d : G.Dart, CycSucc C d.fst d.snd → d ∈ R)
    (hsub : ∀ d ∈ R, CycSucc C d.fst d.snd ∨ CycSucc C d.snd d.fst)
    {a b p : V} (hab : CycSucc C a b) (hpa : CycSucc C p a) (hGpa : G.Adj p a)
    (hba : ∃ r ∈ R, r.fst = b ∧ r.snd = a) : ∃ r ∈ R, r.fst = a ∧ r.snd = p := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨r, hr, hrb, hra⟩ := hba
  have hpb := cycSucc_succ_ne_pred hnd h3 hab hpa
  let dpa : G.Dart := ⟨(p, a), hGpa⟩
  have hdpa : dpa ∈ R := hfwd dpa hpa
  have hin : 1 < (R.filter (fun d => d.snd = a)).card := by
    apply Finset.one_lt_card.mpr
    refine ⟨dpa, Finset.mem_filter.mpr ⟨hdpa, rfl⟩, r, Finset.mem_filter.mpr ⟨hr, hra⟩, ?_⟩
    intro e
    have : dpa.fst = r.fst := congrArg (fun d : G.Dart => d.fst) e
    exact hpb (this.trans hrb)
  have hout : (R.filter (fun d => d.fst = a)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro d hd e he
    simp only [Finset.mem_filter] at hd he
    have hsnd : ∀ f ∈ R, f.fst = a → CycSucc C a f.snd := by
      intro f hf hfa
      rcases hsub f hf with h | h
      · rw [hfa] at h; exact h
      · rw [hfa] at h
        exact absurd (CycSucc.unique_left hnd h hpa) (hno f hf hfa)
    exact dart_ext' (hd.2.trans he.2.symm)
      (CycSucc.unique hnd (hsnd d hd.1 hd.2) (hsnd e he.1 he.2))
  have := card_in_eq_card_out φ hφ R hR a
  omega

include hφ hR in
/-- **Recognition of a face**: if some backward dart of `C` is missing from `R`, then `R`
consists of forward darts of `C`. -/
theorem bracket_fwd (hnd : C.Nodup) (h3 : 3 ≤ C.length)
    (hadjC : ∀ u v, CycSucc C u v → G.Adj u v)
    (hfwd : ∀ d : G.Dart, CycSucc C d.fst d.snd → d ∈ R)
    (hsub : ∀ d ∈ R, CycSucc C d.fst d.snd ∨ CycSucc C d.snd d.fst)
    (hmiss : ∃ a b, CycSucc C a b ∧ ∀ r ∈ R, r.fst = b → r.snd ≠ a) :
    ∀ d ∈ R, CycSucc C d.fst d.snd := by
  intro d hd
  rcases hsub d hd with h | h
  · exact h
  exfalso
  obtain ⟨a₀, b₀, h₀, hm⟩ := hmiss
  let Q : V → Prop := fun a => ∀ b, CycSucc C a b → ∀ r ∈ R, r.fst = b → r.snd ≠ a
  have hQ0 : Q a₀ := by
    intro b hb
    rw [CycSucc.unique hnd hb h₀]
    exact hm
  have hs : ∀ u v, CycSucc C u v → Q u → Q v := by
    intro u v huv hu w hvw r hr hrw hrv
    obtain ⟨r', hr', hr'v, hr'u⟩ := bwd_prev φ hφ R hR C hnd h3 hfwd hsub hvw huv
      (hadjC u v huv) ⟨r, hr, hrw, hrv⟩
    exact hu v huv r' hr' hr'v hr'u
  have hall := forall_of_cycSucc_closed h₀.mem.1 hQ0 hs
  exact hall d.snd h.mem.1 d.fst h d hd rfl rfl

include hφ hR in
/-- Under the hypotheses of `bracket_fwd`, `φ` maps every dart of `R` to the next forward dart. -/
theorem bracket_step (hnd : C.Nodup) (h3 : 3 ≤ C.length)
    (hadjC : ∀ u v, CycSucc C u v → G.Adj u v)
    (hfwd : ∀ d : G.Dart, CycSucc C d.fst d.snd → d ∈ R)
    (hsub : ∀ d ∈ R, CycSucc C d.fst d.snd ∨ CycSucc C d.snd d.fst)
    (hmiss : ∃ a b, CycSucc C a b ∧ ∀ r ∈ R, r.fst = b → r.snd ≠ a)
    {d : G.Dart} (hd : d ∈ R) : CycSucc C (φ d).fst (φ d).snd ∧ (φ d).fst = d.snd :=
  ⟨bracket_fwd φ hφ R hR C hnd h3 hadjC hfwd hsub hmiss (φ d) (hR d hd), hφ d⟩

end Bracket

end ThomassenManyColourings
