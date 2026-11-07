/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PathFacts

/-!
# Generalized wheels fill a near-triangulation without separating triangles

A *region* of a near-triangulation `S₀` (outer cycle `C₀`) is a vertex set `S ⊆ S₀` with outer
cycle `c` whose vertices off `c` are interior vertices of `S₀` with all their neighbours in `S`.
Pieces of chord and cut decompositions of a region are regions. If no triangle region has a
vertex strictly inside (no separating triangle), then a near-triangulation containing a
generalized wheel with the same outer cycle consists of the wheel's vertices only, and has no
wheel on a triangle (`K4` block).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V]

/-- `S` with outer cycle `c` is a region of `S₀` with outer cycle `C₀`. -/
def Region (H : SimpleGraph V) (S₀ : Finset V) (C₀ : List V) (S : Finset V) (c : List V) :
    Prop :=
  S ⊆ S₀ ∧ ∀ u ∈ S, u ∉ c → u ∉ C₀ ∧ ∀ w ∈ S₀, H.Adj u w → w ∈ S

omit [DecidableEq V] in
theorem Region.refl (H : SimpleGraph V) (S₀ : Finset V) (C₀ : List V) :
    Region H S₀ C₀ S₀ C₀ :=
  ⟨subset_rfl, fun _ _ hu => ⟨hu, fun _ hw _ => hw⟩⟩

/-- A piece of a decomposition of a region is a region. -/
theorem Region.piece {H : SimpleGraph V} {S₀ S S₁ S₂ : Finset V} {C₀ c c₁ c₂ : List V}
    (hR : Region H S₀ C₀ S c) (hU : S₁ ∪ S₂ = S) (hI : ∀ v ∈ S₁, v ∈ S₂ → v ∈ c₁)
    (hX : ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁)
    (hc : ∀ v ∈ c, v ∈ c₁ ∨ v ∈ c₂) (hc₂ : ∀ v ∈ c₂, v ∈ S₂) :
    Region H S₀ C₀ S₁ c₁ := by
  have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
  refine ⟨hS₁.trans hR.1, fun u hu huc => ?_⟩
  have huc' : u ∉ c := by
    intro h
    rcases hc u h with h1 | h2
    · exact huc h1
    · exact huc (hI u hu (hc₂ u h2))
  obtain ⟨h1, h2⟩ := hR.2 u (hS₁ hu) huc'
  refine ⟨h1, fun w hw huw => ?_⟩
  rcases Finset.mem_union.mp (hU ▸ h2 w hw huw) with h | h
  · exact h
  · rcases hX u hu w h huw with h' | h'
    · exact absurd (hI u hu h') huc
    · exact h'

/-- The other piece of a decomposition of a region is a region. -/
theorem Region.piece' {H : SimpleGraph V} {S₀ S S₁ S₂ : Finset V} {C₀ c c₁ c₂ : List V}
    (hR : Region H S₀ C₀ S c) (hU : S₁ ∪ S₂ = S) (hI : ∀ v ∈ S₁, v ∈ S₂ → v ∈ c₂)
    (hX : ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁)
    (hc : ∀ v ∈ c, v ∈ c₁ ∨ v ∈ c₂) (hc₁ : ∀ v ∈ c₁, v ∈ S₁) :
    Region H S₀ C₀ S₂ c₂ :=
  hR.piece (S₂ := S₁) (c₂ := c₁) (by rw [Finset.union_comm]; exact hU)
    (fun v h2 h1 => hI v h1 h2)
    (fun u hu w hw huw => (hX w hw u hu huw.symm).symm)
    (fun v hv => (hc v hv).symm) hc₁

omit [DecidableEq V] in
/-- Centres of a block are joined to every vertex of its path. -/
theorem Block.centre_adj {H : SimpleGraph V} {m : ℕ} {x : V} {P : List V} {U : Finset V}
    (h : Block H m x P U) : ∀ u ∈ U, ∀ y ∈ P, H.Adj u y := by
  cases h with
  | tri => simp
  | wheel _ _ _ hu => intro u hu'; simp at hu'; subst hu'; exact hu

namespace NTCalc

variable (T : NTCalc V)

/-- No triangle region of `S₀` has a vertex strictly inside. -/
def NoSepTri (H : SimpleGraph V) (S₀ : Finset V) (C₀ : List V) : Prop :=
  ∀ (S₁ : Finset V) (p q r : V), T.NT H S₁ [p, q, r] → Region H S₀ C₀ S₁ [p, q, r] →
    ∀ u ∈ S₁, u = p ∨ u = q ∨ u = r

variable {T}
variable {H : SimpleGraph V} {S₀ : Finset V} {C₀ : List V}

/-- **No two apexes on an outer edge**: without separating triangles, at most one interior
vertex is joined to both ends of an outer edge. -/
theorem two_apex (hN : T.NoSepTri H S₀ C₀) {S : Finset V} {x y u w : V} {l : List V}
    (hNT : T.NT H S (x :: y :: l)) (hR : Region H S₀ C₀ S (x :: y :: l)) (huS : u ∈ S)
    (hwS : w ∈ S) (hu : u ∉ x :: y :: l) (hw : w ∉ x :: y :: l) (hux : H.Adj u x)
    (huy : H.Adj u y) (hwx : H.Adj w x) (hwy : H.Adj w y) : u = w := by
  by_contra hne
  obtain ⟨S₁, p, hp, hNT₁, hsub, huS₁, hwS₁, hcl⟩ :=
    T.apex2 hNT huS hwS hu hw hne hux huy hwx hwy
  have hR₁ : Region H S₀ C₀ S₁ [x, y, p] := by
    refine ⟨hsub.trans hR.1, fun v hv hvc => ?_⟩
    obtain ⟨h1, h2⟩ := hcl v hv hvc
    obtain ⟨h3, h4⟩ := hR.2 v (hsub hv) h1
    exact ⟨h3, fun z hz hvz => h2 z (h4 z hz hvz) hvz⟩
  have hF := hN S₁ x y p hNT₁ hR₁
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu hw
  rcases hp with rfl | rfl
  · rcases hF w hwS₁ with e | e | e
    · exact hw.1 e
    · exact hw.2.1 e
    · exact hne e.symm
  · rcases hF u huS₁ with e | e | e
    · exact hu.1 e
    · exact hu.2.1 e
    · exact hne e

/-- A fan (a vertex `z` joined to every vertex of the path `Q`) fills its region. -/
theorem fan_fill (hN : T.NoSepTri H S₀ C₀) (z : V) :
    ∀ (n : ℕ) (Q : List V) (S : Finset V), Q.length = n → T.NT H S (z :: Q) →
    Region H S₀ C₀ S (z :: Q) → Q.IsChain H.Adj → (∀ q ∈ Q, H.Adj z q) →
    ∀ w ∈ S, w = z ∨ w ∈ Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q S hn hNT hR hQ hz
  have h2 := T.two_le hNT
  match Q, hNT, hR, hQ, hz, hn with
  | [], _, _, _, _, _ => simp at h2
  | [q], hNT, _, _, _, _ =>
    intro w hw
    rw [T.two hNT] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [List.mem_singleton]
    exact hw
  | [q₁, q₂], hNT, hR, _, _, _ =>
    intro w hw
    have := hN S z q₁ q₂ hNT hR w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact this
  | q₁ :: q₂ :: q₃ :: R, hNT, hR, hQ, hz, hn =>
    obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord (x := z) (y := q₂) (l₁ := [q₁])
      (l₂ := q₃ :: R) (by simpa using hNT) (by simp) (by simp) (hz q₂ (by simp))
    have h₁' : T.NT H S₁ [z, q₁, q₂] := by simpa using h₁
    have h₂' : T.NT H S₂ (z :: q₂ :: q₃ :: R) := T.rotate_back (by simpa using h₂)
    have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = z ∨ v = q₂ := by
      intro v h1 h2
      have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hI] at this; simpa using this
    have hR₁ : Region H S₀ C₀ S₁ [z, q₁, q₂] := by
      refine hR.piece (c₂ := z :: q₂ :: q₃ :: R) hU ?_ hX ?_ (fun v hv => T.subset h₂' v hv)
      · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl <;> simp
      · intro v hv; simp only [List.mem_cons] at hv ⊢; tauto
    have hR₂ : Region H S₀ C₀ S₂ (z :: q₂ :: q₃ :: R) := by
      refine hR.piece' (c₁ := [z, q₁, q₂]) hU ?_ hX ?_ (fun v hv => T.subset h₁' v hv)
      · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl <;> simp
      · intro v hv; simp only [List.mem_cons] at hv ⊢; tauto
    have hQ' : (q₂ :: q₃ :: R).IsChain H.Adj := (List.isChain_cons_cons.mp hQ).2
    have F₂ := ih (n - 1) (by simp at hn; omega) (q₂ :: q₃ :: R) S₂ (by simp at hn ⊢; omega)
      h₂' hR₂ hQ' (fun q hq => hz q (List.mem_cons_of_mem _ hq))
    intro w hw
    rcases Finset.mem_union.mp (hU ▸ hw) with h | h
    · have := hN S₁ z q₁ q₂ h₁' hR₁ w h
      simp only [List.mem_cons]; tauto
    · rcases F₂ w h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- A wheel block fills its region. (Induction on the path: a chord `x p₁` cuts off the triangle
`x p₀ p₁`; otherwise cut along `x u p₁` into two fans centred at `u`.) -/
theorem wheel_fill (hN : T.NoSepTri H S₀ C₀) {x u : V} :
    ∀ (n : ℕ) (P : List V) (S : Finset V), P.length = n →
    T.NT H S (x :: P) → Region H S₀ C₀ S (x :: P) → 2 ≤ P.length →
    P.IsChain H.Adj → (∀ y ∈ P, H.Adj u y) → H.Adj u x →
    (∀ y ∈ P.getLast?, H.Adj x y) → u ∈ S → u ∉ x :: P →
    ∀ w ∈ S, w = x ∨ w = u ∨ w ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P S hn hNT hR hP2 hpath huP hux hl huS hu
  match P, hn, hNT, hR, hP2, hpath, huP, hl, hu with
  | [], _, _, _, h, _, _, _, _ => simp at h
  | [_], _, _, _, h, _, _, _, _ => simp at h
  | [p₀, p₁], _, hNT, hR, _, _, _, _, _ =>
    intro w hw
    have := hN S x p₀ p₁ hNT hR w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
  | p₀ :: p₁ :: p₂ :: R, hn, hNT, hR, _, hpath, huP, hl, hu =>
    have hxp₀ : H.Adj x p₀ := T.adj_cons hNT
    have hp₀p₁ : H.Adj p₀ p₁ := (List.isChain_cons_cons.mp hpath).1
    have hpath' : (p₁ :: p₂ :: R).IsChain H.Adj := (List.isChain_cons_cons.mp hpath).2
    by_cases hxp₁ : H.Adj x p₁
    · -- the chord `x p₁`
      obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord (x := x) (y := p₁) (l₁ := [p₀])
        (l₂ := p₂ :: R) (by simpa using hNT) (by simp) (by simp) hxp₁
      have h₁' : T.NT H S₁ [x, p₀, p₁] := by simpa using h₁
      have h₂' : T.NT H S₂ (x :: p₁ :: p₂ :: R) := T.rotate_back (by simpa using h₂)
      have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = p₁ := by
        intro v h1 h2
        have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
        rw [hI] at this; simpa using this
      have hR₁ : Region H S₀ C₀ S₁ [x, p₀, p₁] := by
        refine hR.piece (c₂ := x :: p₁ :: p₂ :: R) hU ?_ hX ?_ (fun v hv => T.subset h₂' v hv)
        · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl <;> simp
        · intro v hv; simp only [List.mem_cons] at hv ⊢; tauto
      have hR₂ : Region H S₀ C₀ S₂ (x :: p₁ :: p₂ :: R) := by
        refine hR.piece' (c₁ := [x, p₀, p₁]) hU ?_ hX ?_ (fun v hv => T.subset h₁' v hv)
        · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl <;> simp
        · intro v hv; simp only [List.mem_cons] at hv ⊢; tauto
      have F₁ := hN S₁ x p₀ p₁ h₁' hR₁
      have hu' : u ∉ x :: p₁ :: p₂ :: R := by
        intro h; apply hu; simp only [List.mem_cons] at h ⊢; tauto
      have huS₂ : u ∈ S₂ := by
        rcases Finset.mem_union.mp (hU ▸ huS) with h | h
        · exfalso; apply hu
          rcases F₁ u h with e | e | e <;> simp [e]
        · exact h
      have F₂ := ih (n - 1) (by simp at hn; omega) (p₁ :: p₂ :: R) S₂ (by simp at hn ⊢; omega)
        h₂' hR₂ (by simp) hpath' (fun y hy => huP y (List.mem_cons_of_mem _ hy)) hux
        (by simpa using hl) huS₂ hu'
      intro w hw
      rcases Finset.mem_union.mp (hU ▸ hw) with h | h
      · rcases F₁ w h with e | e | e <;> simp [e]
      · rcases F₂ w h with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ e))
    · -- cut along `x u p₁`: two fans centred at `u`
      obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := x) (y := p₁) (u := u) (l₁ := [p₀])
        (l₂ := p₂ :: R) (by simpa using hNT) huS (by simpa using hu) hux
        (huP p₁ (by simp)) hxp₁
      have h₁' : T.NT H S₁ (u :: [x, p₀, p₁]) := T.rotate_back (by simpa using h₁)
      have h₂' : T.NT H S₂ (u :: (p₁ :: p₂ :: R ++ [x])) := T.rotate_back (by simpa using h₂)
      have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = p₁ ∨ v = u := by
        intro v h1 h2
        have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
        rw [hI] at this; simpa using this
      have hR₁ : Region H S₀ C₀ S₁ (u :: [x, p₀, p₁]) := by
        refine hR.piece (c₂ := u :: (p₁ :: p₂ :: R ++ [x])) hU ?_ hX ?_
          (fun v hv => T.subset h₂' v hv)
        · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
        · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
      have hR₂ : Region H S₀ C₀ S₂ (u :: (p₁ :: p₂ :: R ++ [x])) := by
        refine hR.piece' (c₁ := u :: [x, p₀, p₁]) hU ?_ hX ?_ (fun v hv => T.subset h₁' v hv)
        · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
        · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
      have F₁ := fan_fill hN u _ [x, p₀, p₁] S₁ rfl h₁' hR₁ (by
        simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact ⟨hxp₀, hp₀p₁⟩) (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hux
        · exact huP _ (by simp)
        · exact huP _ (by simp))
      have hchain : (p₁ :: p₂ :: R ++ [x]).IsChain H.Adj := by
        rw [List.isChain_append]
        refine ⟨hpath', by simp, ?_⟩
        intro y hy z hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
        subst hz
        have : y ∈ (p₀ :: p₁ :: p₂ :: R).getLast? := by
          rw [List.getLast?_cons_cons]; exact hy
        exact (hl y this).symm
      have F₂ := fan_fill hN u _ (p₁ :: p₂ :: R ++ [x]) S₂ rfl h₂' hR₂ hchain (by
        intro q hq
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact huP q (List.mem_cons_of_mem _ hq)
        · exact hux)
      intro w hw
      rcases Finset.mem_union.mp (hU ▸ hw) with h | h
      · rcases F₁ w h with e | e
        · exact Or.inr (Or.inl e)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at e ⊢; tauto
      · rcases F₂ w h with e | e
        · exact Or.inr (Or.inl e)
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at e ⊢; tauto

/-- A block fills its region, and is not a wheel on a triangle. -/
theorem block_fill (hN : T.NoSepTri H S₀ C₀) {m : ℕ} {x : V} {P : List V} {U : Finset V}
    (hB : Block H m x P U) {S : Finset V} (hNT : T.NT H S (x :: P))
    (hR : Region H S₀ C₀ S (x :: P)) (hU : ∀ u ∈ U, u ∈ S ∧ u ∉ x :: P) :
    (∀ w ∈ S, w = x ∨ w ∈ P ∨ w ∈ U) ∧ Block H 3 x P U := by
  cases hB with
  | @tri a b hxa hxb hab =>
    refine ⟨fun w hw => ?_, Block.tri hxa hxb hab⟩
    have := hN S x a b hNT hR w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
  | @wheel P u hP2 hm hpath huP hux hh hl =>
    have huS := (hU u (by simp)).1
    have hu := (hU u (by simp)).2
    have F := wheel_fill hN _ P S rfl hNT hR hP2 hpath huP hux hl huS hu
    refine ⟨fun w hw => ?_, ?_⟩
    · rcases F w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (by simp [h]))
      · exact Or.inr (Or.inl h)
    · have h3 : 3 ≤ P.length := by
        by_contra hlt
        obtain ⟨p, q, rfl⟩ : ∃ p q, P = [p, q] := by
          match P, hP2, hlt with
          | [p, q], _, _ => exact ⟨p, q, rfl⟩
          | [], h, _ => simp at h
          | [_], h, _ => simp at h
          | _ :: _ :: _ :: _, _, h => simp at h
        have := hN S x p q hNT hR u huS
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
        tauto
      exact Block.wheel hP2 h3 hpath huP hux hh hl

/-- **A generalized wheel fills its region**: every vertex is the major vertex, on the path or a
centre, and there is no wheel on a triangle. -/
theorem gw_fill (hN : T.NoSepTri H S₀ C₀) {m : ℕ} {x : V} {P : List V} {U : Finset V}
    (hW : GW H m x P U) : ∀ {S : Finset V}, T.NT H S (x :: P) → Region H S₀ C₀ S (x :: P) →
    (∀ u ∈ U, u ∈ S ∧ u ∉ x :: P) → (∀ w ∈ S, w = x ∨ w ∈ P ∨ w ∈ U) ∧ GW H 3 x P U := by
  induction hW with
  | one hB =>
    intro S hNT hR hU
    obtain ⟨h1, h2⟩ := block_fill hN hB hNT hR hU
    exact ⟨h1, GW.one h2⟩
  | @cons P Q b U U' hB hrest ih =>
    intro S hNT hR hUU
    have hPne : P ≠ [] := by
      intro h; subst h; have := hB.two_le; simp at this
    have hQne : Q ≠ [] := by
      intro h; subst h; have := hrest.two_le; simp at this
    have hxb : H.Adj x b := hB.adj_last b (by simp)
    obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord hNT hPne hQne hxb
    have h₂' : T.NT H S₂ (x :: b :: Q) := T.rotate_back (by simpa using h₂)
    have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = b := by
      intro v h1 h2
      have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hI] at this; simpa using this
    have hnd := T.nodup hNT
    have hxP : x ∉ P ++ b :: Q := (List.nodup_cons.mp hnd).1
    have hnd2 := (List.nodup_cons.mp hnd).2
    have hbP : b ∉ P := by
      intro h
      exact (List.nodup_append.mp hnd2).2.2 b h b (by simp) rfl
    have hbQ : b ∉ Q := (List.nodup_cons.mp (List.nodup_append.mp hnd2).2.1).1
    have hPQ : ∀ v ∈ P, v ∉ Q := fun v hv hq =>
      (List.nodup_append.mp hnd2).2.2 v hv v (List.mem_cons_of_mem _ hq) rfl
    have hPside : ∀ v ∈ P, v ∉ S₂ := by
      intro v hv h2
      rcases hmem v (T.subset h₁ v (by simp [hv])) h2 with rfl | rfl
      · exact hxP (List.mem_append_left _ hv)
      · exact hbP hv
    have hQside : ∀ v ∈ Q, v ∉ S₁ := by
      intro v hv h1
      rcases hmem v h1 (T.subset h₂' v (by simp [hv])) with rfl | rfl
      · exact hxP (by simp [hv])
      · exact hbQ hv
    have hR₁ : Region H S₀ C₀ S₁ (x :: (P ++ [b])) := by
      refine hR.piece (c₂ := x :: b :: Q) hU ?_ hX ?_ (fun v hv => T.subset h₂' v hv)
      · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl <;> simp
      · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
    have hR₂ : Region H S₀ C₀ S₂ (x :: b :: Q) := by
      refine hR.piece' (c₁ := x :: (P ++ [b])) hU ?_ hX ?_ (fun v hv => T.subset h₁ v hv)
      · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl <;> simp
      · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
    have hS₁ : ∀ v ∈ S₁, v ∈ S := fun v hv => hU ▸ Finset.mem_union_left _ hv
    have hS₂ : ∀ v ∈ S₂, v ∈ S := fun v hv => hU ▸ Finset.mem_union_right _ hv
    have hside : ∀ v ∈ S, v ∉ S₁ → v ∈ S₂ := fun v hv h1 =>
      (Finset.mem_union.mp (hU ▸ hv)).resolve_left h1
    have hU₁ : ∀ u ∈ U, u ∈ S₁ ∧ u ∉ x :: (P ++ [b]) := by
      intro u hu
      obtain ⟨huS, hun⟩ := hUU u (Finset.mem_union_left _ hu)
      obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hPne
      have hup : H.Adj u p := hB.centre_adj u hu p (by simp)
      refine ⟨?_, fun h => hun ?_⟩
      · by_contra h1
        rcases hX p (T.subset h₁ p (by simp)) u (hside u huS h1) hup.symm with h | h
        · exact hPside p (by simp) h
        · exact h1 h
      · simp only [List.mem_cons, List.mem_append] at h ⊢; tauto
    have hU₂ : ∀ u ∈ U', u ∈ S₂ ∧ u ∉ x :: b :: Q := by
      intro u hu
      obtain ⟨huS, hun⟩ := hUU u (Finset.mem_union_right _ hu)
      obtain ⟨q, hq, huq⟩ := hrest.centre_adj_tail u hu
      refine ⟨?_, fun h => hun ?_⟩
      · by_contra h2
        have h1 : u ∈ S₁ := by
          by_contra h1; exact h2 (hside u huS h1)
        rcases hX u h1 q (T.subset h₂' q (by simp [hq])) huq with h | h
        · exact h2 h
        · exact hQside q hq h
      · simp only [List.mem_cons, List.mem_append] at h ⊢; tauto
    obtain ⟨F₁, B₃⟩ := block_fill hN hB h₁ hR₁ hU₁
    obtain ⟨F₂, W₃⟩ := ih h₂' hR₂ hU₂
    refine ⟨fun w hw => ?_, GW.cons B₃ W₃⟩
    rcases Finset.mem_union.mp (hU ▸ hw) with h | h
    · rcases F₁ w h with h' | h' | h'
      · exact Or.inl h'
      · simp only [List.mem_append, List.mem_singleton] at h'
        right; left; simp only [List.mem_append, List.mem_cons]; tauto
      · exact Or.inr (Or.inr (Finset.mem_union_left _ h'))
    · rcases F₂ w h with h' | h' | h'
      · exact Or.inl h'
      · right; left; simp only [List.mem_append]; exact Or.inr h'
      · exact Or.inr (Or.inr (Finset.mem_union_right _ h'))

end NTCalc

end ThomassenManyColourings
