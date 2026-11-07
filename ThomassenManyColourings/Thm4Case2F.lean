/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2E

/-!
# Theorem 4, Case 2: Subcase 2.2 with `u_{q-1}` joined to `v_{k-2}`

`u = u_q` is joined to `v_{k-2}, v_{k-1}, c` only (on the outer path), not to `x`; `u' = u_{q-1}`
is joined to `u` and `v_{k-2}`, and the centre `t` of the last wheel is joined to `x, c, u, u'`.
Delete `w = v_{k-1}`, give `u` three colours of `L(u) \ {α, β}` (`α, β ∈ L(w) \ {g c}`), and apply
**Case 1** to `G − w`: it gives `2^{(n'+1)/9 - r'/3}` colourings with `n' = n − 1`, `r' ≤ r`, and
every one extends to `w`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable {T : NTCalc V}

set_option maxHeartbeats 64000000 in
/-- **Subcase 2.2, `u_{q-1} ~ v_{k-2}`.** -/
theorem Case1Hyp.case2_c1 {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A : List V}
    {vm w u u' t : V} (hP : a :: (Q ++ [c]) = A ++ [vm, w, c]) (huS : u ∈ S)
    (hu : u ∉ x :: a :: (Q ++ [c])) (hum : H.Adj u vm) (huw : H.Adj u w) (huc : H.Adj u c)
    (hux : ¬ H.Adj u x) (hmin : ∀ q ∈ A, ¬ H.Adj u q)
    (hu'S : u' ∈ S) (hu' : u' ∉ x :: a :: (Q ++ [c])) (hu'u : u' ≠ u) (hu'vm : H.Adj u' vm)
    (htS : t ∈ S) (ht : t ∉ x :: a :: (Q ++ [c])) (htx : H.Adj t x) (htc : H.Adj t c)
    (htu : H.Adj t u) (htu' : H.Adj t u')
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  intro hne hexc
  show Bound4 (ExtSet H S [c, x, a] L g).ncard (nCount S [c, x, a]) (rCount S [c, x, a] L)
  have hh := hc.hyp
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  have hPnd' : (A ++ [vm, w, c]).Nodup := hP ▸ hPnd
  have hcQ : c ∉ Q := fun h => (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.2 c h c
    (by simp) rfl
  have haQ : a ∉ Q := fun h => (List.nodup_cons.mp hPnd).1 (List.mem_append_left _ h)
  have hxQ : x ∉ Q := fun h => hxP (by simp [h])
  have huQ : u ∉ Q := fun h => hu (by simp [h])
  have hAne : A ≠ [] := by
    intro h; rw [h] at hP
    have := congrArg List.length hP; have := hc.two; simp at *; omega
  obtain ⟨a', A', hA⟩ := List.exists_cons_of_ne_nil hAne
  have ha' : a' = a := by rw [hA] at hP; simp at hP; exact hP.1.symm
  subst a'
  -- positions: `Q = A' ++ [vm, w]`
  have hQeq : Q = A' ++ [vm, w] := by
    rw [hA] at hP; simp only [List.cons_append, List.cons.injEq, true_and] at hP
    exact List.append_cancel_right (show Q ++ [c] = (A' ++ [vm, w]) ++ [c] by rw [hP]; simp)
  have hwQ : w ∈ Q := by rw [hQeq]; simp
  have hvmQ : vm ∈ Q := by rw [hQeq]; simp
  have hA'Q : ∀ v ∈ A', v ∈ Q := fun v hv => by rw [hQeq]; simp [hv]
  -- cut off the fan `u v_{k-2} w c`
  have hPf : a :: (Q ++ [c]) = A ++ vm :: ([w] ++ [c]) := by rw [hP]; simp
  obtain ⟨S₂, hNT₂, hS₂m, hR₂, hnbM⟩ := hc.fan_cut hPf (by simp) huS hu hum
    (by simpa using huw) huc
  have hS₂m' : ∀ v, v ∈ S₂ ↔ v ∈ S ∧ v ≠ w := by intro v; rw [hS₂m]; simp
  have hwnb : ∀ z ∈ S, z ∉ x :: a :: (Q ++ [c]) → H.Adj w z → z = u := by
    intro z hz hzn hwz
    rcases hnbM w (by simp) z hz hwz with h | h | h | h
    · simp at h; exact absurd (by rw [h]; simp [hwQ]) hzn
    · exact h
    · exact absurd (by rw [h]; simp) hzn
    · exact absurd (by rw [h]; simp [hvmQ]) hzn
  -- two colours of `w` and three colours for `u`
  have hw3 : (L w).card = 3 := hc.three w hwQ
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.mp (show 1 < ((L w).erase (g c)).card by
    have := Finset.pred_card_le_card_erase (s := L w) (a := g c); omega)
  rw [Finset.mem_erase] at hα hβ
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  obtain ⟨L3, hL3sub, hL3card⟩ := Finset.exists_subset_card_eq (s := ((L u).erase α).erase β)
    (n := 3) (by
      have := Finset.pred_card_le_card_erase (s := L u) (a := α)
      have := Finset.pred_card_le_card_erase (s := (L u).erase α) (a := β)
      omega)
  set L' : V → Finset C := fun v => if v = u then L3 else L v with hL'
  have hL'u : L' u = L3 := by simp [hL']
  have hL'ne : ∀ v, v ≠ u → L' v = L v := fun v hv => by simp [hL', hv]
  have hL'sub : ∀ v, L' v ⊆ L v := by
    intro v; by_cases hv : v = u
    · rw [hv, hL'u]; exact hL3sub.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    · rw [hL'ne v hv]
  -- `G − w` as an instance of Case 1
  set Q' := A' ++ [vm, u] with hQ'def
  have hQ' : a :: (Q' ++ [c]) = A ++ [vm, u, c] := by rw [hA]; simp [hQ'def]
  have hNT' : T.NT H S₂ (x :: a :: (Q' ++ [c])) := by rw [hQ']; exact hNT₂
  have hR' : Region H S (x :: a :: (Q ++ [c])) S₂ (x :: a :: (Q' ++ [c])) := by
    rw [hQ']; exact hR₂
  have hint : ∀ v ∈ S₂, v ∉ x :: a :: (Q' ++ [c]) → v ∈ S ∧ v ∉ x :: a :: (Q ++ [c]) ∧ v ≠ u :=
    fun v hv hvn => ⟨((hS₂m' v).1 hv).1, (hR'.2 v hv hvn).1, fun e => hvn (by simp [e, hQ'def])⟩
  have hQ'mem : ∀ q ∈ Q', q = u ∨ q ∈ Q := by
    intro q hq
    simp only [hQ'def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq
    · exact Or.inr (hA'Q q hq)
    · exact Or.inr (hq ▸ hvmQ)
    · exact Or.inl hq
  have hc' : T.Case1Hyp H S₂ x a c Q' L' g := by
    have htwo'' : 2 ≤ (a :: (Q' ++ [c])).length := by
      simp only [List.length_cons, List.length_append, List.length_nil]; omega
    refine ⟨hNT', ⟨rfl, getLast?_cons_append_singleton a c Q', htwo'', hh.xa, hh.xc, hh.ac, ?_,
      ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy hyn
      change y ∉ [c, x, a] at hyn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn
      have hyQ' : y ∈ Q' := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with h | h | h
        · exact absurd h hyn.2.2
        · exact h
        · exact absurd h hyn.1
      rcases hQ'mem y hyQ' with rfl | hyQ
      · rw [hL'u, hL3card]
      · rw [hL'ne y (fun e => huQ (e ▸ hyQ)), hc.three y hyQ]
    · intro y hy hyn
      obtain ⟨hyS, hyn', hyu⟩ := hint y hy hyn
      rw [hL'ne y hyu]; exact hh.five y hyS hyn'
    · simp [hQ'def]
    · rw [hQ']; exact hc.chordless_fan hP hu hmin
    · intro q hq
      rcases hQ'mem q hq with rfl | hqQ
      · exact fun h => hux h.symm
      · exact hc.xfree q hqQ
    · intro q hq
      rcases hQ'mem q hq with rfl | hqQ
      · rw [hL'u, hL3card]
      · rw [hL'ne q (fun e => huQ (e ▸ hqQ)), hc.three q hqQ]
    · exact NoSepTri.of_region hc.nosep hR'
    · rw [hQ']
      exact hc.c12_fan hP hNT₂ hS₂m' hR₂ hwnb hu hmin hu'S hu' hu'u hu'vm htS ht htx htc htu
        htu'
    · intro v hv hvn
      obtain ⟨hvS, hvn', -⟩ := hint v hv hvn
      exact hc.nohub v hvS hvn'
  have hgw' : NoGWR H S₂ x a c Q' := hc.noGWR_fan hP hQ' hS₂m' hR₂ hwnb
  -- counts
  have hwS : w ∈ S := T.subset hc.nt w (by simp [hwQ])
  have hwpc : w ∉ [c, x, a] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun e => hcQ (e ▸ hwQ), fun e => hxQ (e ▸ hwQ), fun e => haQ (e ▸ hwQ)⟩
  have hn : nCount S [c, x, a] = nCount S₂ [c, x, a] + 1 := by
    unfold nCount
    rw [← Finset.card_insert_of_notMem (a := w) (by simp [hS₂m'])]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, hS₂m']
    constructor
    · rintro ⟨hv, hvn⟩
      by_cases hvw : v = w
      · exact Or.inl hvw
      · exact Or.inr ⟨⟨hv, hvw⟩, hvn⟩
    · rintro (rfl | ⟨⟨hv, -⟩, hvn⟩)
      · exact ⟨hwS, hwpc⟩
      · exact ⟨hv, hvn⟩
  have hr : rCount S₂ [c, x, a] L' ≤ rCount S [c, x, a] L := by
    unfold rCount
    have hwF : w ∈ S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3) :=
      Finset.mem_filter.mpr ⟨hwS, hwpc, hw3⟩
    have hsub : S₂.filter (fun v => v ∉ [c, x, a] ∧ (L' v).card = 3) ⊆
        insert u ((S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)).erase w) := by
      intro v hv
      simp only [Finset.mem_filter] at hv
      by_cases hvu : v = u
      · exact Finset.mem_insert.mpr (Or.inl hvu)
      · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨((hS₂m' v).1 hv.1).2, ?_⟩)
        rw [hL'ne v hvu] at hv
        exact Finset.mem_filter.mpr ⟨((hS₂m' v).1 hv.1).1, hv.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le u ((S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)).erase w)
    rw [Finset.card_erase_of_mem hwF] at h2
    have : 1 ≤ (S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)).card :=
      Finset.card_pos.mpr ⟨w, hwF⟩
    omega
  -- Case 1 for `G − w`
  have ih' : T.Thm4Lt C (nCount S₂ (pcList true x a c))
      (nCount S₂ (pcList true x a c) - rCount S₂ (pcList true x a c) L') true :=
    ih.mono (by show nCount S₂ [c, x, a] < nCount S [c, x, a]; omega)
  have hB := hc'.case1 hgw' ih'
  -- every colouring of `G − w` extends to `w`
  have hextend : ∀ φ ∈ ExtSet H S₂ [c, x, a] L' g, ∃ f ∈ ExtSet H S [c, x, a] L g,
      ∀ v ∈ S₂, f v = φ v := by
    intro φ hφ
    obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
    have huS₂ : u ∈ S₂ := (hS₂m' u).2 ⟨huS, fun e => huQ (e ▸ hwQ)⟩
    have hφu : φ u ∈ L3 := by
      rw [← hL'u]
      exact hφ2 u huS₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hu (by simp [e]), fun e => hu (by simp [e]), fun e => hu (by simp [e])⟩)
    have hφu' := hL3sub hφu
    simp only [Finset.mem_erase] at hφu'
    have hφc : φ c = g c := hφ1 c (Or.inr (by simp))
    have hcol : ColFrom (φ u) (φ vm) ([w].map L) (φ c) := by
      rw [List.map_singleton, hφc, show [L w] = [] ++ [L w] by simp]
      exact colFrom_two_last (by simp) hα.2 hβ.2 hαβ hα.1 hβ.1
        (fun e => hφu'.2.1 e.symm) (fun e => hφu'.1 e.symm)
    obtain ⟨f, hf1, hf2, hf3⟩ := hc.fan_extend hPf hu hnbM φ hcol
    refine ⟨f, ⟨fun v hv => ?_, fun v hv hvn => ?_, fun p hp q hq hpq => ?_⟩,
      fun v hv => hf1 v (by simp [((hS₂m' v).1 hv).2])⟩
    · have hvw : v ∉ [w] := by
        simp only [List.mem_singleton]
        rintro rfl
        rcases hv with hv | hv
        · exact hv hwS
        · exact hwpc hv
      rw [hf1 v hvw]
      exact hφ1 v (by
        rcases hv with hv | hv
        · exact Or.inl (fun h => hv ((hS₂m' v).1 h).1)
        · exact Or.inr hv)
    · by_cases hvw : v ∈ [w]
      · exact hf2 v hvw
      · rw [hf1 v hvw]
        exact hL'sub v (hφ2 v ((hS₂m' v).2 ⟨hv, by simpa using hvw⟩) hvn)
    · by_cases hpM : p ∈ [w]
      · exact hf3 p hpM q hq hpq
      by_cases hqM : q ∈ [w]
      · exact (hf3 q hqM p hp hpq.symm).symm
      rw [hf1 p hpM, hf1 q hqM]
      exact hφ3 p ((hS₂m' p).2 ⟨hp, by simpa using hpM⟩) q ((hS₂m' q).2 ⟨hq, by simpa using hqM⟩)
        hpq
  choose! ext hext1 hext2 using hextend
  have hN : (ExtSet H S₂ [c, x, a] L' g).ncard ≤ (ExtSet H S [c, x, a] L g).ncard := by
    refine Set.ncard_le_ncard_of_injOn ext (fun φ hφ => hext1 φ hφ) ?_
      (extSet_finite H S [c, x, a] L g)
    intro φ hφ φ' hφ' he
    funext v
    by_cases hv : v ∈ S₂
    · rw [← hext2 φ hφ v hv, ← hext2 φ' hφ' v hv, he]
    · rw [hφ.1 v (Or.inl hv), hφ'.1 v (Or.inl hv)]
  exact bound4_gain hB hN (by omega)

end NTCalc

end ThomassenManyColourings
