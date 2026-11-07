/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2D

/-!
# Theorem 4, Case 2: the graph `G − v_{k-1}` (Subcase 2.2, `m = k − 2`)

`u` interior, joined to `v_{k-2}, v_{k-1}, c` only on the outer path (and not to `x`). Deleting
`w = v_{k-1}` (with two colours of `L(w) \ {g c}` removed from `L(u)`) gives `G'` with outer path
`a v₃ … v_{k-2} u c`. This file proves the properties of `G'` needed to apply Case 1 to it:

* `chordless_fan`: its outer path is chordless;
* `c12_fan`: Claim 12 holds in `G'`, given a vertex `u'` joined to `u` and `v_{k-2}` and a vertex
  `t` joined to `x, c, u, u'` (a separating path `p y u` with `y ≠ u'` would separate `u'` from `t`);
* `noGWR_fan`: `G'` satisfies the hypothesis of Case 1 (the last vertex before `c` of such a path
  would be joined to `c` and to a vertex before `w`, hence to `w`, hence equal to `u`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
/-- Regions of a region are regions. -/
theorem Region.trans {H : SimpleGraph V} {S₀ S₂ S₁ : Finset V} {C₀ c₂ c₁ : List V}
    (h₂ : Region H S₀ C₀ S₂ c₂) (h₁ : Region H S₂ c₂ S₁ c₁) : Region H S₀ C₀ S₁ c₁ := by
  refine ⟨h₁.1.trans h₂.1, fun v hv hvc => ?_⟩
  obtain ⟨h1, h2⟩ := h₁.2 v hv hvc
  obtain ⟨h3, h4⟩ := h₂.2 v (h₁.1 hv) h1
  exact ⟨h3, fun z hz hvz => h2 z (h4 z hz hvz) hvz⟩

omit [DecidableEq V] in
/-- Suffixes after a vertex of a repetition-free list agree. -/
theorem suffix_eq_of_nodup {X Y X' Y' : List V} {v : V} (hnd : (X ++ v :: Y).Nodup)
    (h : X ++ v :: Y = X' ++ v :: Y') : X = X' ∧ Y = Y' := by
  induction X generalizing X' with
  | nil =>
    rcases X' with _ | ⟨x', X''⟩
    · simp at h; exact ⟨rfl, h⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hnd
  | cons x X ih =>
    rcases X' with _ | ⟨x', X''⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hnd
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h'⟩ := h
      obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mp hnd).2 h'
      exact ⟨by rw [h1], h2⟩

namespace NTCalc

variable {T : NTCalc V}

theorem Thm4Lt.mono {n₀ s₀ n₁ s₁ : ℕ} {t₀ t₁ : Bool} (h : T.Thm4Lt C n₀ s₀ t₀) (hn : n₁ < n₀) :
    T.Thm4Lt C n₁ s₁ t₁ := by
  intro H S x P a c L g t3 hNT hh hlex
  apply h H S x P a c L g t3 hNT hh
  left
  rcases hlex with h' | ⟨h', -⟩
  · omega
  · omega

theorem NoSepTri.of_region {H : SimpleGraph V} {S₀ S₂ : Finset V} {C₀ c₂ : List V}
    (hN : T.NoSepTri H S₀ C₀) (hR : Region H S₀ C₀ S₂ c₂) : T.NoSepTri H S₂ c₂ :=
  fun S₁ p q r hNT hR₁ => hN S₁ p q r hNT (hR.trans hR₁)

omit [DecidableEq C] in
set_option maxHeartbeats 16000000 in
/-- The outer path `A v_m u c` of `G − w` is chordless. -/
theorem Case1Hyp.chordless_fan {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A : List V}
    {vm w u : V} (hP : a :: (Q ++ [c]) = A ++ [vm, w, c]) (hu : u ∉ x :: a :: (Q ++ [c]))
    (hmin : ∀ q ∈ A, ¬ H.Adj u q) :
    ∀ y z, y ∈ A ++ [vm, u, c] → z ∈ A ++ [vm, u, c] → H.Adj y z →
      ConsecIn (A ++ [vm, u, c]) y z := by
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hPnd' : (A ++ [vm, w, c]).Nodup := hP ▸ hPnd
  have hconsec : ∀ (B D : List V) (y z : V), ConsecIn (B ++ y :: z :: D) y z := by
    intro B D y z
    exact ConsecIn.append_left (Or.inl ⟨rfl, rfl⟩)
  have key : ∀ y z, y ∈ A ++ [vm] → z ∈ A ++ [vm, u, c] → z ≠ u → H.Adj y z →
      ConsecIn (A ++ [vm, u, c]) y z := by
    intro y z hy hz hzu hyz
    have hyP : y ∈ a :: (Q ++ [c]) := by
      rw [hP]; simp only [List.mem_append, List.mem_singleton] at hy; simp; tauto
    have hzP : z ∈ a :: (Q ++ [c]) := by
      rw [hP]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp; tauto
    have hcons := hc.chordless y z hyP hzP hyz
    rw [hP] at hcons
    by_cases hzc : z = c
    · exfalso
      rw [hzc] at hcons
      have hdc : A ++ [vm, w, c] = (A ++ [vm, w]) ++ c :: [] := by simp
      rw [hdc] at hcons
      rcases ConsecIn.nbr (hdc ▸ hPnd') hcons.symm with h' | h'
      · rw [show A ++ [vm, w] = (A ++ [vm]) ++ [w] by simp, List.getLast?_concat] at h'
        simp only [Option.some.injEq] at h'
        have := (List.nodup_append.mp (show ((A ++ [vm]) ++ [w] ++ [c]).Nodup by
          simpa using hPnd')).1
        exact (List.nodup_append.mp this).2.2 y hy y (by simp [h']) rfl
      · simp at h'
    · have hz' : z ∈ A ++ [vm] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        tauto
      have h1 := ConsecIn.infix (A := []) (Q := A ++ [vm]) (B := [w, c])
        (by simpa using hPnd') hy hz' (by simpa using hcons)
      rw [show A ++ [vm, u, c] = (A ++ [vm]) ++ [u, c] by simp]
      exact ConsecIn.append_right h1
  intro y z hy hz hyz
  have hyc : ∀ v ∈ A ++ [vm, u, c], v ≠ u → v ≠ c → v ∈ A ++ [vm] := by
    intro v hv hvu hvc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    tauto
  by_cases hyu : y = u
  · subst hyu
    by_cases hzc : z = c
    · subst hzc
      rw [show A ++ [vm, y, z] = (A ++ [vm]) ++ y :: z :: [] by simp]
      exact hconsec _ [] y z
    · have hz' : z ∈ A ++ [vm] := by
        have := hyc z hz hyz.ne.symm hzc
        exact this
      rcases List.mem_append.mp hz' with hzA | hzv
      · exact absurd hyz (hmin z hzA)
      · simp at hzv; subst hzv
        exact (hconsec A [c] z y).symm
  · by_cases hyc' : y = c
    · subst hyc'
      by_cases hzu : z = u
      · subst hzu
        rw [show A ++ [vm, z, y] = (A ++ [vm]) ++ z :: y :: [] by simp]
        exact (hconsec _ [] z y).symm
      · exact (key z y (hyc z hz hzu hyz.ne.symm) hy hyu hyz.symm).symm
    · by_cases hzu : z = u
      · subst hzu
        have hy' := hyc y hy hyu hyc'
        rcases List.mem_append.mp hy' with hyA | hyv
        · exact absurd hyz.symm (hmin y hyA)
        · simp at hyv; subst hyv
          exact hconsec A [c] y z
      · exact key y z (hyc y hy hyu hyc') hz hzu hyz

omit [DecidableEq C] in
set_option maxHeartbeats 32000000 in
/-- **Claim 12 in `G − w`.** -/
theorem Case1Hyp.c12_fan {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A : List V}
    {vm w u u' t : V} (hP : a :: (Q ++ [c]) = A ++ [vm, w, c]) {S₂ : Finset V}
    (hNT₂ : T.NT H S₂ (x :: (A ++ [vm, u, c]))) (hS₂m : ∀ v, v ∈ S₂ ↔ v ∈ S ∧ v ≠ w)
    (hR₂ : Region H S (x :: a :: (Q ++ [c])) S₂ (x :: (A ++ [vm, u, c])))
    (hwnb : ∀ z ∈ S, z ∉ x :: a :: (Q ++ [c]) → H.Adj w z → z = u)
    (hu : u ∉ x :: a :: (Q ++ [c])) (hmin : ∀ q ∈ A, ¬ H.Adj u q)
    (hu'S : u' ∈ S) (hu' : u' ∉ x :: a :: (Q ++ [c])) (hu'u : u' ≠ u) (hu'vm : H.Adj u' vm)
    (htS : t ∈ S) (ht : t ∉ x :: a :: (Q ++ [c])) (htx : H.Adj t x) (htc : H.Adj t c)
    (htu : H.Adj t u) (htu' : H.Adj t u') :
    C12 H S₂ (x :: (A ++ [vm, u, c])) (A ++ [vm, u, c]) := by
  classical
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  have hPnd' : (A ++ [vm, w, c]).Nodup := hP ▸ hPnd
  have hP'nd : (A ++ [vm, u, c]).Nodup := (List.nodup_cons.mp (T.nodup hNT₂)).2
  have huP : u ∉ A ++ [vm, w, c] := fun h => hu (List.mem_cons_of_mem _ (hP ▸ h))
  have huA : u ∉ A := fun h => huP (by simp [h])
  have hvmu : vm ≠ u := fun e => huP (by simp [e])
  have hcu : c ≠ u := fun e => huP (by simp [e])
  -- replacing `u` by `w` turns the outer path of `G'` into that of `G`
  let σ : V → V := fun v => if v = u then w else v
  have hσ : (A ++ [vm, u, c]).map σ = a :: (Q ++ [c]) := by
    rw [hP]
    simp only [List.map_append, List.map_cons, List.map_nil, σ, ite_true, hvmu, hcu, ite_false]
    congr 1
    exact (List.map_congr_left (g := fun v => v) (fun v hv => by
      simp [show v ≠ u from fun e => huA (by rw [← e]; exact hv)])).trans (List.map_id' A)
  have hσne : ∀ v, v ≠ u → σ v = v := fun v hv => by simp [σ, hv]
  -- interior vertices of `G'` are interior vertices of `G`, and are not `u`
  have hint : ∀ y ∈ S₂, y ∉ x :: (A ++ [vm, u, c]) → y ∈ S ∧ y ∉ x :: a :: (Q ++ [c]) ∧ y ≠ u :=
    fun y hy hyn => ⟨((hS₂m y).1 hy).1, (hR₂.2 y hy hyn).1, fun e => hyn (by simp [e])⟩
  intro y hyS hyn A₁ B D p p' hdec hyp hyp' m hm
  obtain ⟨hyS', hyn', hyu⟩ := hint y hyS hyn
  -- the decomposition mapped to `G`
  have hdecG : a :: (Q ++ [c]) = A₁.map σ ++ σ p :: (B.map σ ++ σ p' :: D.map σ) := by
    rw [← hσ, hdec]; simp
  have hdec₀ : A ++ [vm, u, c] = (A ++ [vm]) ++ u :: [c] := by simp
  by_cases hpu : p = u
  · -- then `B = []`
    exfalso
    rw [hpu] at hdec
    have := (suffix_eq_of_nodup (hdec₀ ▸ hP'nd) (hdec₀.symm.trans hdec)).2
    rcases B with _ | ⟨b, B'⟩
    · simp at hm
    · simp at this
  by_cases hp'u : p' = u
  · -- the cut along `p y u`
    rw [hp'u] at hdec hyp'
    have hs := suffix_eq_of_nodup (hdec₀ ▸ hP'nd) (hdec₀.symm.trans
      (show A ++ [vm, u, c] = (A₁ ++ p :: B) ++ u :: D by rw [hdec]; simp))
    have hpre : A ++ [vm] = A₁ ++ p :: B := hs.1
    have hD : [c] = D := hs.2
    have hBne : B ≠ [] := by intro h; rw [h] at hm; simp at hm
    have hvmB : B.getLast? = some vm := by
      have := congrArg List.getLast? hpre
      rw [List.getLast?_concat, show A₁ ++ p :: B = (A₁ ++ [p]) ++ B by simp,
        List.getLast?_append_of_ne_nil _ hBne] at this
      exact this.symm
    obtain ⟨B', hB'⟩ : ∃ B', B = B' ++ [vm] := ⟨B.dropLast, eq_dropLast_append_of_getLast? hvmB⟩
    have hnd2 : (A₁ ++ p :: B).Nodup := by
      rw [← hpre]
      exact (List.nodup_append.mp (show ((A ++ [vm]) ++ [w, c]).Nodup by simpa using hPnd')).1
    have hvmB : vm ∈ B := List.mem_of_mem_getLast? hvmB
    have hpB : p ∉ B := (List.nodup_cons.mp (List.nodup_append.mp hnd2).2.1).1
    have hvmp : vm ≠ p := fun e => hpB (e ▸ hvmB)
    have hpA : p ∈ A := by
      have : p ∈ A ++ [vm] := by rw [hpre]; simp
      rcases List.mem_append.mp this with h | h
      · exact h
      · simp at h; exact absurd h.symm hvmp
    have hpPA : H.Adj p u → False := fun h => hmin p hpA h.symm
    -- rotate and cut
    have hrot : T.NT H S₂ (p :: (B ++ u :: (c :: x :: A₁))) := by
      have := T.rotate_append (A := x :: A₁) (B := p :: (B ++ u :: [c]))
        (by rw [show x :: A₁ ++ p :: (B ++ u :: [c]) = x :: (A ++ [vm, u, c]) by
          rw [hdec, ← hD]; simp]; exact hNT₂)
      simpa using this
    have hcycm : ∀ v, v ∈ p :: (B ++ u :: (c :: x :: A₁)) ↔ v ∈ x :: (A ++ [vm, u, c]) := by
      intro v; rw [hdec, ← hD]; simp; tauto
    obtain ⟨R₁, R₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := p) (y := u) (u := y) (l₁ := B)
      (l₂ := c :: x :: A₁) hrot hyS (fun h => hyn ((hcycm y).1 h)) hyp hyp' hpPA
    have hmem : ∀ v, v ∈ R₁ → v ∈ R₂ → v = p ∨ v = u ∨ v = y := by
      intro v h1 h2
      have : v ∈ R₁ ∩ R₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hI] at this; simpa using this
    have hvmR₁ : vm ∈ R₁ := T.subset h₁ vm (by rw [hB']; simp)
    have hpP : p ∈ a :: (Q ++ [c]) := by rw [hP]; simp [hpA]
    have hvmP : vm ∈ a :: (Q ++ [c]) := by rw [hP]; simp
    have hvmR₂ : vm ∉ R₂ := by
      intro h
      rcases hmem vm hvmR₁ h with e | e | e
      · exact hvmp e
      · exact hvmu e
      · exact hyn' (by rw [← e]; exact List.mem_cons_of_mem _ hvmP)
    have hxR₂ : x ∈ R₂ := T.subset h₂ x (by simp)
    have hxR₁ : x ∉ R₁ := by
      intro h
      rcases hmem x h hxR₂ with e | e | e
      · exact hxP (by rw [e]; exact hpP)
      · exact hu (by simp [← e])
      · exact hyn' (by simp [← e])
    have hu'S₂ : u' ∈ S₂ := (hS₂m u').2 ⟨hu'S, fun e => hu' (by
      rw [e, hP]; simp)⟩
    have htS₂ : t ∈ S₂ := (hS₂m t).2 ⟨htS, fun e => ht (by rw [e, hP]; simp)⟩
    have hu'R₁ : u' ∈ R₁ := by
      rcases Finset.mem_union.mp (hU ▸ hu'S₂) with h | h
      · exact h
      · rcases hX vm hvmR₁ u' h hu'vm.symm with h' | h'
        · exact absurd h' hvmR₂
        · exact h'
    have htR₂ : t ∈ R₂ := by
      rcases Finset.mem_union.mp (hU ▸ htS₂) with h | h
      · rcases hX t h x hxR₂ htx with h' | h'
        · exact h'
        · exact absurd h' hxR₁
      · exact h
    have hu'P : u' ∉ a :: (Q ++ [c]) := fun h => hu' (List.mem_cons_of_mem _ h)
    have htP : t ∉ a :: (Q ++ [c]) := fun h => ht (List.mem_cons_of_mem _ h)
    rcases hX u' hu'R₁ t htR₂ htu'.symm with h | h
    · -- `u' = y`
      rcases hmem u' hu'R₁ h with e | e | e
      · exact absurd (e ▸ hpP) hu'P
      · exact absurd e hu'u
      · rw [← e]
        rw [hB'] at hm
        rcases List.mem_append.mp hm with hm' | hm'
        · have hdecP : a :: (Q ++ [c]) = A₁ ++ p :: (B' ++ vm :: [w, c]) := by
            rw [hP]; rw [show A ++ [vm, w, c] = (A ++ [vm]) ++ [w, c] by simp, hpre, hB']; simp
          exact hc.c12 u' hu'S hu' A₁ B' [w, c] p vm hdecP (e ▸ hyp) hu'vm m hm'
        · simp at hm'; rw [hm']; exact hu'vm
    · -- `t = y`: then `t ~ p, c`, hence `t ~ w`, so `t = u`
      exfalso
      rcases hmem t h htR₂ with e | e | e
      · exact htP (e ▸ hpP)
      · rw [e] at htu; exact H.loopless.irrefl _ htu
      · have hdecP : a :: (Q ++ [c]) = A₁ ++ p :: ((B ++ [w]) ++ c :: []) := by
          rw [hP]; rw [show A ++ [vm, w, c] = (A ++ [vm]) ++ [w, c] by simp, hpre]; simp
        have hytw := hc.c12 y hyS' hyn' A₁ (B ++ [w]) [] p c hdecP hyp (e ▸ htc) w (by simp)
        exact hyu (hwnb y hyS' hyn' hytw.symm)
  -- otherwise use Claim 12 in `G` on the mapped decomposition
  have hσp := hσne p hpu
  have hσp' := hσne p' hp'u
  rw [hσp, hσp'] at hdecG
  have hall := hc.c12 y hyS' hyn' (A₁.map σ) (B.map σ) (D.map σ) p p' hdecG hyp hyp'
  by_cases hmu : m = u
  · exfalso
    have := hall w (List.mem_map.mpr ⟨m, hm, by rw [hmu]; simp [σ]⟩)
    exact hyu (hwnb y hyS' hyn' this.symm)
  · have := hall (σ m) (List.mem_map.mpr ⟨m, hm, rfl⟩)
    rwa [hσne m hmu] at this

omit [DecidableEq C] in
set_option maxHeartbeats 16000000 in
/-- **`G − w` satisfies the hypothesis of Case 1.** -/
theorem Case1Hyp.noGWR_fan {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A Q' : List V}
    {vm w u : V} (hP : a :: (Q ++ [c]) = A ++ [vm, w, c])
    (hQ' : a :: (Q' ++ [c]) = A ++ [vm, u, c]) {S₂ : Finset V}
    (hS₂m : ∀ v, v ∈ S₂ ↔ v ∈ S ∧ v ≠ w)
    (hR₂ : Region H S (x :: a :: (Q ++ [c])) S₂ (x :: (A ++ [vm, u, c])))
    (hwnb : ∀ z ∈ S, z ∉ x :: a :: (Q ++ [c]) → H.Adj w z → z = u) :
    NoGWR H S₂ x a c Q' := by
  classical
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hQ2 := hc.two
  rintro ⟨PW, U, hGW, hndW, hhW, hlW, hmemW, -⟩
  have hPW := eq_dropLast_append_of_getLast? hlW
  have hne : PW.dropLast ≠ [] := by
    intro h
    rw [h] at hPW
    rw [hPW] at hhW
    simp at hhW
    -- `c = a` is impossible
    have : a ∈ Q ++ [c] := by rw [← hhW]; simp
    exact (List.nodup_cons.mp hPnd).1 this
  set z := PW.dropLast.getLast hne with hz
  have hPW' : PW = PW.dropLast.dropLast ++ [z, c] := by
    conv_lhs => rw [hPW, ← List.dropLast_append_getLast hne]
    simp [hz]
  have hzc : H.Adj z c := by
    have hch := hGW.isPath
    rw [hPW'] at hch
    have := (List.isChain_append.mp hch).2.1
    exact (List.isChain_cons_cons.mp this).1
  have hzW : z ∈ PW := by rw [hPW']; simp
  rcases hmemW z hzW with hza | hzc' | ⟨hzS, hzn, q₁, hq₁, q₂, hq₂, h12, hzq₁, hzq₂⟩
  · -- `a ~ c` is a chord of `G`
    rw [hza] at hzc
    have := hc.chordless a c (by simp) (by simp) hzc
    obtain ⟨q, Q'', hQq⟩ := List.exists_cons_of_ne_nil (show Q ≠ [] by
      intro h; rw [h] at hQ2; simp at hQ2)
    rw [hQq] at this hPnd
    exact ConsecIn.not_ends (M := q :: Q'') (List.cons_ne_nil _ _) hPnd this
  · rw [hzc'] at hzc; exact H.loopless.irrefl _ hzc
  · -- a neighbour of `z` before `w`
    have hzint : z ∈ S ∧ z ∉ x :: a :: (Q ++ [c]) := ⟨((hS₂m z).1 hzS).1, (hR₂.2 z hzS (by
      rw [← hQ']; exact hzn)).1⟩
    have hzu : z ≠ u := fun e => hzn (by
      have : u ∈ a :: (Q' ++ [c]) := by rw [hQ']; simp
      rw [e]; exact List.mem_cons_of_mem _ this)
    obtain ⟨q, hqQ', hqu, hzq⟩ : ∃ q ∈ Q', q ≠ u ∧ H.Adj z q := by
      by_cases h : q₁ = u
      · exact ⟨q₂, hq₂, fun e => h12 (h.trans e.symm), hzq₂⟩
      · exact ⟨q₁, hq₁, h, hzq₁⟩
    -- `q` lies in `A ++ [vm]`
    have hAne : A ≠ [] := by
      intro h; rw [h] at hP
      have := congrArg List.length hP; simp at this; omega
    have hqAv : q ∈ A ++ [vm] := by
      obtain ⟨a', A', hA⟩ := List.exists_cons_of_ne_nil hAne
      rw [hA] at hQ'
      simp only [List.cons_append, List.cons.injEq] at hQ'
      have hQ'' : Q' = A' ++ [vm, u] :=
        List.append_cancel_right (show Q' ++ [c] = (A' ++ [vm, u]) ++ [c] by rw [hQ'.2]; simp)
      rw [hQ''] at hqQ'
      rw [hA]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hqQ' ⊢
      tauto
    obtain ⟨A₁, B₀, hAB⟩ := List.append_of_mem hqAv
    have hdecP : a :: (Q ++ [c]) = A₁ ++ q :: ((B₀ ++ [w]) ++ c :: []) := by
      rw [hP, show A ++ [vm, w, c] = (A ++ [vm]) ++ [w, c] by simp, hAB]; simp
    have hzw := hc.c12 z hzint.1 hzint.2 A₁ (B₀ ++ [w]) [] q c hdecP hzq hzc w (by simp)
    exact hzu (hwnb z hzint.1 hzint.2 hzw.symm)

end NTCalc

end ThomassenManyColourings
