/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2G

/-!
# Theorem 4, Case 2: the dispatcher

Under `Case1Hyp`, if the hypothesis `NoGWR` of Case 1 fails there is a generalized wheel on a
path `a u₁ … u_q c` through interior vertices joined to at least two vertices of `Q`. Let
`u = u_q` and let `v_m` be the first vertex of `a Q` joined to `u`; by Claim 12, `u` is joined to
every vertex between `v_m` and `c`. Then:

* `x ~ u`: Subcase 2.1 (`case2_xu`);
* at least two vertices strictly between `v_m` and `c`: Subcase 2.2a (`case2_del`);
* otherwise `v_m = v_{k-2}`; the last block of the generalized wheel is a wheel with centre `t`
  joined to `x, c, u, u_{q-1}` (`GW.front` on the reversed wheel), and `u_{q-1} ~ v_{k-2}` gives
  `case2_c1`, while `u_{q-1} ≁ v_{k-2}` gives `case2_c2`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

section Lists

omit [DecidableEq V] in
/-- Consecutive entries of a chain are related. -/
theorem chain_adj_mid {R : V → V → Prop} {l A B : List V} {y z : V} (h : l.IsChain R)
    (hl : l = A ++ y :: z :: B) : R y z := by
  subst hl
  induction A with
  | nil => exact (List.isChain_cons_cons.mp h).1
  | cons p A ih => exact ih h.tail

omit [DecidableEq V] in
/-- The first entry of a list satisfying a predicate. -/
theorem exists_first_split (p : V → Prop) [DecidablePred p] :
    ∀ l : List V, (∃ y ∈ l, p y) → ∃ A y B, l = A ++ y :: B ∧ p y ∧ ∀ z ∈ A, ¬ p z
  | [], ⟨_, hy, _⟩ => absurd hy (by simp)
  | b :: l, h => by
    by_cases hb : p b
    · exact ⟨[], b, l, rfl, hb, by simp⟩
    · obtain ⟨y, hy, hpy⟩ := h
      have hyl : y ∈ l := by
        rcases List.mem_cons.mp hy with rfl | h
        · exact absurd hpy hb
        · exact h
      obtain ⟨A, z, B, hl, hz, hA⟩ := exists_first_split p l ⟨y, hyl, hpy⟩
      refine ⟨b :: A, z, B, by simp [hl], hz, fun z' hz' => ?_⟩
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hb
      · exact hA z' hz'

end Lists

section Wheels

variable {H : SimpleGraph V} {m : ℕ} {x : V}

/-- A generalized wheel on two vertices is a triangle or a wheel with a centre joined to both. -/
theorem GW.pair {a c : V} {U : Finset V} (h : GW H m x [a, c] U) :
    H.Adj a c ∨ ∃ t ∈ U, H.Adj t a ∧ H.Adj t c ∧ H.Adj t x := by
  generalize hP : [a, c] = P at h
  cases h with
  | one hB =>
    cases hB with
    | tri hxa hxb hab =>
      simp only [List.cons.injEq, and_true] at hP
      obtain ⟨rfl, rfl⟩ := hP
      exact Or.inl hab
    | @wheel P t _ _ _ hadj hux _ _ =>
      subst hP
      exact Or.inr ⟨t, Finset.mem_singleton_self t, hadj a (by simp), hadj c (by simp), hux⟩
  | cons hB hrest =>
    have h1 := hB.two_le
    have h2 := hrest.two_le
    have := congrArg List.length hP
    simp only [List.length_append, List.length_cons, List.length_nil] at this h1 h2
    omega

/-- The front block of a block on `a v R`: `x ~ v`, or a centre joined to `a`, `v`, the next
vertex and `x`. -/
theorem Block.front {a v : V} {R : List V} {U : Finset V} (h : Block H m x (a :: v :: R) U) :
    H.Adj x v ∨ ∃ w R', R = w :: R' ∧ ∃ t ∈ U, H.Adj t a ∧ H.Adj t v ∧ H.Adj t w ∧ H.Adj t x := by
  cases R with
  | nil => exact Or.inl (h.adj_last v (by simp))
  | cons w R' =>
    right
    generalize hP : a :: v :: w :: R' = P at h
    cases h with
    | tri => simp at hP
    | @wheel P t _ _ _ hadj hux _ _ =>
      subst hP
      exact ⟨w, R', rfl, t, Finset.mem_singleton_self t, hadj a (by simp), hadj v (by simp),
        hadj w (by simp), hux⟩

/-- The front block of a generalized wheel on `a v R`. -/
theorem GW.front {a v : V} {R : List V} {U : Finset V} (h : GW H m x (a :: v :: R) U) :
    H.Adj x v ∨ ∃ w R', R = w :: R' ∧ ∃ t ∈ U, H.Adj t a ∧ H.Adj t v ∧ H.Adj t w ∧ H.Adj t x := by
  generalize hP : a :: v :: R = P at h
  cases h with
  | one hB => subst hP; exact hB.front
  | @cons P' Q b U₁ U₂ hB hrest =>
    have h2 := hB.two_le
    obtain ⟨p, P'', rfl⟩ : ∃ p P'', P' = p :: P'' := by
      rcases P' with _ | ⟨p, P''⟩
      · simp at h2
      · exact ⟨p, P'', rfl⟩
    simp only [List.cons_append, List.cons.injEq] at hP
    obtain ⟨rfl, hP⟩ := hP
    rcases P'' with _ | ⟨q, P'''⟩
    · simp only [List.nil_append, List.cons.injEq] at hP
      obtain ⟨rfl, -⟩ := hP
      exact Or.inl (hB.adj_last _ (by simp))
    · simp only [List.cons_append, List.cons.injEq] at hP
      obtain ⟨rfl, hR⟩ := hP
      have hB' : Block H m x (a :: v :: (P''' ++ [b])) U₁ := by simpa using hB
      rcases hB'.front with h | ⟨w, R', hw, t, ht, h1, h2, h3, h4⟩
      · exact Or.inl h
      · right
        refine ⟨w, (P''' ++ b :: Q).tail, ?_, t, Finset.mem_union_left _ ht, h1, h2, h3, h4⟩
        rw [← hR]
        rcases P''' with _ | ⟨w', P4⟩ <;> simp_all

end Wheels

namespace NTCalc

variable {T : NTCalc V}

set_option maxHeartbeats 16000000 in
/-- **Case 2 of Theorem 4**: `Case1Hyp` without `NoGWR`. -/
theorem Case1Hyp.case2 {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g)
    (hgw : ¬ NoGWR H S x a c Q)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  unfold NoGWR at hgw
  obtain ⟨PW, U, hGW, hPWnd, hhead, hlast, hPWv, hU⟩ := not_not.mp hgw
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hQne : Q ≠ [] := by intro h; have := hc.two; rw [h] at this; simp at this
  -- `PW = R ++ [u, c]`
  have h2 := hGW.two_le
  have hPWc := eq_dropLast_append_of_getLast? hlast
  have hD : PW.dropLast ≠ [] := by
    intro h; rw [h] at hPWc; rw [hPWc] at h2; simp at h2
  set R := PW.dropLast.dropLast with hRdef
  set u := PW.dropLast.getLast hD with hudef
  have hPW : PW = R ++ [u, c] := by
    conv_lhs => rw [hPWc, ← List.dropLast_append_getLast hD]
    simp [hRdef, hudef]
  have hmemPW : ∀ y, y ∈ R ++ [u, c] → y ∈ PW := fun y hy => hPW ▸ hy
  have hPWnd' : (R ++ [u, c]).Nodup := hPW ▸ hPWnd
  have huc_ne : u ≠ c := by
    have : [u, c].Nodup := hPWnd'.sublist (List.sublist_append_right _ _)
    simpa using this
  -- `u` is not `a`
  have hua : u ≠ a := by
    intro hua
    have hR : R = [] := by
      rcases hR' : R with _ | ⟨r, R'⟩
      · rfl
      · exfalso
        rw [hPW, hR'] at hhead
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hhead
        rw [hR', hhead, hua] at hPWnd'
        simp at hPWnd'
    rw [hPW, hR, hua] at hGW
    rcases GW.pair (by simpa using hGW) with hac | ⟨t, ht, hta, htc, htx⟩
    · have hcon := hc.chordless a c (by simp) (by simp) hac
      have hnd' : (a :: (Q ++ [c])).Nodup := hPnd
      exact ConsecIn.not_ends hQne hnd' hcon
    · obtain ⟨htS, htn⟩ := hU t ht
      exact hc.nohub t htS htn ⟨htc, htx, hta⟩
  obtain ⟨huS, hu, q₁, hq₁, q₂, hq₂, hq₁₂, huq₁, huq₂⟩ :=
    (hPWv u (hmemPW u (by simp))).resolve_left hua |>.resolve_left huc_ne
  have huc : H.Adj u c := chain_adj_mid hGW.isPath (A := R) (B := []) (by rw [hPW])
  -- the first neighbour `v_m` of `u` on `a Q`
  obtain ⟨A, vm, M, haQ, hum, hmin⟩ :=
    exists_first_split (fun q => H.Adj u q) (a :: Q) ⟨q₁, by simp [hq₁], huq₁⟩
  have hP : a :: (Q ++ [c]) = A ++ vm :: (M ++ [c]) := by
    rw [← List.cons_append, haQ]; simp
  have huM : ∀ q ∈ M, H.Adj u q := fun q hq =>
    hc.c12 u huS hu A M [] vm c (by rw [hP]) hum huc q hq
  have hQmem : ∀ q ∈ Q, H.Adj u q → q = vm ∨ q ∈ M := by
    intro q hq huq
    have : q ∈ A ++ vm :: M := by rw [← haQ]; exact List.mem_cons_of_mem a hq
    rcases List.mem_append.mp this with h | h
    · exact absurd huq (hmin q h)
    · exact List.mem_cons.mp h
  have hMne : M ≠ [] := by
    intro hM
    have e1 := hQmem q₁ hq₁ huq₁
    have e2 := hQmem q₂ hq₂ huq₂
    simp only [hM, List.not_mem_nil, or_false] at e1 e2
    exact hq₁₂ (e1.trans e2.symm)
  by_cases hux : H.Adj u x
  · exact hc.case2_xu hP hMne huS hu hum huM huc hux hmin ih
  by_cases hM2 : 2 ≤ M.length
  · exact hc.case2_del hP hM2 huS hu hum huM huc hmin ih
  -- `M = [w]`
  obtain ⟨w, hMw⟩ : ∃ w, M = [w] := by
    rcases M with _ | ⟨w, _ | ⟨w', M'⟩⟩
    · exact absurd rfl hMne
    · exact ⟨w, rfl⟩
    · simp at hM2
  subst hMw
  have hP' : a :: (Q ++ [c]) = A ++ [vm, w, c] := by rw [hP]; simp
  have huw : H.Adj u w := huM w (by simp)
  -- the last block of the generalized wheel
  have hrev := hGW.reverse
  rw [hPW] at hrev
  have hrev' : GW H 2 x (c :: u :: R.reverse) U := by simpa using hrev
  rcases hrev'.front with hxu | ⟨u', R', hR', t, ht, htc, htu, htu', htx⟩
  · exact absurd hxu.symm hux
  have hRe : R = R'.reverse ++ [u'] := by
    have := congrArg List.reverse hR'; simpa using this
  have hPW2 : PW = R'.reverse ++ [u', u, c] := by rw [hPW, hRe]; simp
  have hPWnd2 : (R'.reverse ++ [u', u, c]).Nodup := hPW2 ▸ hPWnd
  have hu'u : u' ≠ u := by
    have : [u', u, c].Nodup := hPWnd2.sublist (List.sublist_append_right _ _)
    simp at this; exact this.1.1
  have hu'c : u' ≠ c := by
    have : [u', u, c].Nodup := hPWnd2.sublist (List.sublist_append_right _ _)
    simp at this; exact this.1.2
  obtain ⟨htS, htn⟩ := hU t ht
  have hu'a : u' ≠ a := by
    rintro rfl
    exact hc.nohub t htS htn ⟨htc, htx, htu'⟩
  obtain ⟨hu'S, hu', p₁, hp₁, p₂, hp₂, hp₁₂, hu'p₁, hu'p₂⟩ :=
    (hPWv u' (by rw [hPW2]; simp)).resolve_left hu'a |>.resolve_left hu'c
  have hu'uu : H.Adj u' u :=
    chain_adj_mid hGW.isPath (A := R'.reverse) (B := [c]) (by rw [hPW2])
  by_cases hu'vm : H.Adj u' vm
  · exact hc.case2_c1 hP' huS hu hum huw huc hux hmin hu'S hu' hu'u hu'vm htS htn htx htc htu
      htu' ih
  -- a neighbour of `u'` strictly before `v_m`
  have hkey : ∀ q ∈ Q, H.Adj u' q → q ≠ w → q ∈ A := by
    intro q hq hu'q hqw
    have : q ∈ A ++ [vm, w] := by
      rw [show A ++ [vm, w] = A ++ vm :: [w] from rfl, ← haQ]; exact List.mem_cons_of_mem a hq
    rcases List.mem_append.mp this with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact absurd hu'q hu'vm
      · exact absurd rfl hqw
  obtain ⟨vi, hviA, hu'vi⟩ : ∃ vi ∈ A, H.Adj u' vi := by
    by_cases hp₁w : p₁ = w
    · exact ⟨p₂, hkey p₂ hp₂ hu'p₂ (fun e => hp₁₂ (hp₁w.trans e.symm)), hu'p₂⟩
    · exact ⟨p₁, hkey p₁ hp₁ hu'p₁ hp₁w, hu'p₁⟩
  obtain ⟨P₀, M₀, hAs⟩ := List.append_of_mem hviA
  exact hc.case2_c2 hP' huS hu hum huw huc hmin hu'S hu' hu'u hu'uu hAs hu'vi hu'vm ih

end NTCalc

end ThomassenManyColourings
