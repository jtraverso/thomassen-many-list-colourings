/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1F

/-!
# Theorem 4, Case 1

If no path `v₂ u₁ … u_q v_k` of interior vertices joined to at least two vertices of
`Q = v₃ … v_{k-1}` closes, with `v₁`, a generalized wheel (`NoGWR`), then `G` has at least
`2^{(n+1)/9 - r/3}` colourings (`case1`): colour the cut vertices of the broken wheel string in
one of the ways given by `case1_family`, delete `Q`, apply induction to the rest (with the lists of
the interior neighbours of the cut vertices reduced), and extend (`Case1Hyp.extend`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The hypothesis of Case 1: no generalized wheel on a path from `a` to `c` through interior
vertices joined to at least two vertices of `Q`. -/
def NoGWR (H : SimpleGraph V) (S : Finset V) (x a c : V) (Q : List V) : Prop :=
  ¬ ∃ (PW : List V) (U : Finset V), GW H 2 x PW U ∧ PW.Nodup ∧ PW.head? = some a ∧
    PW.getLast? = some c ∧
    (∀ y ∈ PW, y = a ∨ y = c ∨ (y ∈ S ∧ y ∉ x :: a :: (Q ++ [c]) ∧
      ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ ≠ q₂ ∧ H.Adj y q₁ ∧ H.Adj y q₂)) ∧
    ∀ u ∈ U, u ∈ S ∧ u ∉ x :: a :: (Q ++ [c])

omit [DecidableEq V] in
theorem mem_interleave : ∀ (ks : List V) (Bs : List (List V)), ks.length = Bs.length + 1 →
    ∀ v ∈ interleave ks Bs, v ∈ ks ∨ v ∈ Bs.flatten
  | [k], [], _, v, hv => Or.inl (by simpa [interleave] using hv)
  | k :: k' :: ks, B :: Bs, hl, v, hv => by
    have hv' : v ∈ k :: (B ++ interleave (k' :: ks) Bs) := hv
    simp only [List.mem_cons, List.mem_append] at hv'
    rcases hv' with h | h | h
    · left; simp [h]
    · right; simp [h]
    · rcases mem_interleave (k' :: ks) Bs (by simpa using hl) v h with h' | h'
      · left; exact List.mem_cons_of_mem _ h'
      · right; simp only [List.flatten_cons, List.mem_append]; right; exact h'
  | [], _, hl, _, _ => by simp at hl
  | [_], _ :: _, hl, _, _ => by simp at hl
  | _ :: _ :: _, [], hl, _, _ => by simp at hl

omit [DecidableEq V] [DecidableEq C] in
theorem forall₂_mem_of {f : V → C} {K : V → Finset C} : ∀ {ks : List V} {cs : List C},
    List.Forall₂ (fun k col => f k = col) ks cs → List.Forall₂ (· ∈ ·) cs (ks.map K) →
    ∀ k ∈ ks, f k ∈ K k
  | [], [], _, _ => by simp
  | _ :: _, _ :: _, List.Forall₂.cons h₁ r₁, List.Forall₂.cons h₂ r₂ => by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [h₁]; exact h₂
    · exact forall₂_mem_of r₁ r₂ k hk

namespace NTCalc

variable {T : NTCalc V}

set_option maxHeartbeats 64000000 in
/-- **Case 1** of Theorem 4. -/
theorem Case1Hyp.case1 {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g)
    (hgw : NoGWR H S x a c Q)
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Bound4 (ExtSet H S [c, x, a] L g).ncard (nCount S [c, x, a] + 1) (rCount S [c, x, a] L) := by
  classical
  have hh := hc.hyp
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  have hQnd : Q.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).1
  have haQ : a ∉ Q := fun h => (List.nodup_cons.mp hPnd).1 (List.mem_append_left _ h)
  have hcQ : c ∉ Q := fun h => (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.2 c h c
    (by simp) rfl
  have hxQ : x ∉ Q := fun h => hxP (by simp [h])
  have hQne : Q ≠ [] := by intro h; have := hc.two; rw [h] at this; simp at this
  have hQS : ∀ q ∈ Q, q ∈ S := fun q hq => T.subset hc.nt q (by simp [hq])
  have hpcQ : ∀ q ∈ Q, q ∉ [c, x, a] := by
    intro q hq h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact hcQ hq
    · exact hxQ hq
    · exact haQ hq
  -- delete `Q`
  obtain ⟨Y, S', hS'm, hNT', hY, hYc⟩ := T.strip H hc.nt hc.two hc.chordless hc.xfree
    hc.nosep hc.c12 Q [] [] S (by simp) (by simpa using hc.nt) (fun v => by simp) (by simp)
    (fun _ => rfl) (by simp) (by simp)
  -- the ends of `Q`
  set q₁ := Q.head hQne with hq₁
  set qr := Q.getLast hQne with hqr
  have hq₁Q : q₁ ∈ Q := List.head_mem hQne
  have hqrQ : qr ∈ Q := List.getLast_mem hQne
  have hq₁r : q₁ ≠ qr := by
    intro e
    obtain ⟨q, Q', hQ'⟩ := List.exists_cons_of_ne_nil hQne
    have hQ'ne : Q' ≠ [] := by
      intro h; have := hc.two; rw [hQ', h] at this; simp at this
    have h1 : q₁ = q := by rw [hq₁]; simp [hQ']
    have h2 : qr ∈ Q' := by
      rw [hqr]; simp only [hQ', List.getLast_cons hQ'ne]; exact List.getLast_mem hQ'ne
    rw [hQ'] at hQnd
    exact (List.nodup_cons.mp hQnd).1 (h1 ▸ e ▸ h2)
  -- split `Q` at the cut vertices
  set pK : V → Prop := fun q => q = q₁ ∨ q = qr ∨ ∃ y₁ ∈ S, ∃ y₂ ∈ S,
    y₁ ∉ x :: a :: (Q ++ [c]) ∧ y₂ ∉ x :: a :: (Q ++ [c]) ∧ y₁ ≠ y₂ ∧ H.Adj q y₁ ∧ H.Adj q y₂
    with hpK
  obtain ⟨ks, Bs, hQi, hlen, hhd, hlst, hksK, hBsK⟩ := exists_interleave pK Q.length Q rfl hQne
    (by intro h hh'; left; rw [List.head?_eq_some_head hQne] at hh'; simp at hh'; rw [← hh'])
    (by intro z hz; right; left; rw [List.getLast?_eq_some_getLast hQne] at hz; simp at hz
        rw [← hz])
  have hksQ : ∀ k ∈ ks, k ∈ Q := fun k hk => hQi ▸ mem_interleave_of_mem_ks ks Bs hlen k hk
  have hBsQ : ∀ b ∈ Bs.flatten, b ∈ Q := fun b hb =>
    hQi ▸ mem_interleave_of_mem_flatten ks Bs hlen b hb
  have hksnd : ks.Nodup := (hQi ▸ hQnd).sublist (ks_sublist_interleave ks Bs hlen)
  have hQmem : ∀ v ∈ Q, v ∈ ks ∨ v ∈ Bs.flatten := fun v hv =>
    mem_interleave ks Bs hlen v (hQi ▸ hv)
  have hksBs : ∀ k ∈ ks, k ∉ Bs.flatten :=
    interleave_disj ks Bs hlen (hQi ▸ hQnd)
  obtain ⟨k₀, ks', hks⟩ : ∃ k₀ ks', ks = k₀ :: ks' := by
    rcases ks with _ | ⟨k₀, ks'⟩
    · simp at hlen
    · exact ⟨k₀, ks', rfl⟩
  have hk₀ : k₀ = q₁ := by
    rw [hks, List.head?_eq_some_head hQne] at hhd; simpa using hhd
  have hBsne : Bs ≠ [] := by
    intro h
    subst h
    rw [hks] at hlen
    obtain rfl : ks' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    have : Q = [k₀] := by rw [hQi, hks]; rfl
    have := hc.two; rw [‹Q = [k₀]›] at this; simp at this
  have hks'ne : ks' ≠ [] := by
    intro h; rw [hks, h] at hlen
    apply hBsne; apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons, List.length_nil] at hlen; omega
  have hlast' : ks'.getLast? = some qr := by
    rw [hks, List.getLast?_cons_of_ne_nil hks'ne, List.getLast?_eq_some_getLast hQne] at hlst
    exact hlst
  have hs : ks'.length = Bs.length := by rw [hks] at hlen; simpa using hlen
  -- the lists of the cut vertices
  set Kl : V → Finset C := fun k => if k = q₁ then (L k).erase (g a)
    else if k = qr then (L k).erase (g c) else L k with hKl
  have hKlsub : ∀ k, Kl k ⊆ L k := by
    intro k; simp only [hKl]
    split_ifs
    · exact Finset.erase_subset _ _
    · exact Finset.erase_subset _ _
    · exact subset_rfl
  have hL3 : ∀ q ∈ Q, (L q).card = 3 := hc.three
  obtain ⟨F, hFm, hFc⟩ := case1_family (Kl k₀) (ks'.map Kl) (Bs.map (fun B => B.map L))
    (by simp [hs])
    (by
      intro I hI M hM
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hI
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hM
      rw [hL3 b (hBsQ b (List.mem_flatten.mpr ⟨B, hB, hb⟩))])
    (by
      simp only [hKl, hk₀, ite_true]
      have := Finset.pred_card_le_card_erase (s := L q₁) (a := g a)
      rw [hL3 q₁ hq₁Q] at this; omega)
    (by
      intro K hK
      rw [← List.map_dropLast] at hK
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hK
      have hkks' : k ∈ ks' := List.mem_of_mem_dropLast hk
      have hk1 : k ≠ q₁ := by
        intro e; rw [hks] at hksnd
        exact (List.nodup_cons.mp hksnd).1 (by rw [hk₀, ← e]; exact hkks')
      have hkr : k ≠ qr := by
        intro e
        have hnd' : ks'.Nodup := (List.nodup_cons.mp (hks ▸ hksnd)).2
        have hl' := eq_dropLast_append_of_getLast? hlast'
        rw [hl'] at hnd'
        exact (List.nodup_append.mp hnd').2.2 k hk qr (by simp) e
      simp only [hKl, hk1, hkr, ite_false]
      rw [hL3 k (hksQ k (by rw [hks]; exact List.mem_cons_of_mem _ hkks'))])
    (by
      intro K hK
      rw [List.getLast?_map, hlast'] at hK
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hK
      subst hK
      simp only [hKl, Ne.symm hq₁r, ite_false, ite_true]
      have := Finset.pred_card_le_card_erase (s := L qr) (a := g c)
      rw [hL3 qr hqrQ] at this; omega)
  -- the set of cut vertices satisfies `Case1KOK`
  have hKOK : Case1KOK H S x a c Q ks.toFinset := by
    intro k hk
    rw [List.mem_toFinset] at hk
    have hkQ := hksQ k hk
    obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hkQ
    have hPj : (a :: (Q ++ [c]))[j + 1]'(by simp; omega) = k := by
      rw [List.getElem_cons_succ, List.getElem_append_left hj]; exact hjk
    refine ⟨j + 1, by simp; omega, hPj, by omega, by simp; omega, ?_⟩
    rcases hksK k hk with h | h | h
    · left
      have e : Q[j] = Q[0]'(by omega) := by rw [hjk, h, hq₁, List.head_eq_getElem]
      have := (List.Nodup.getElem_inj_iff hQnd).mp e
      omega
    · right; left
      have e : Q[j] = Q[Q.length - 1]'(by omega) := by
        rw [hjk, h, hqr, List.getLast_eq_getElem]
      have := (List.Nodup.getElem_inj_iff hQnd).mp e
      simp; omega
    · right; right; exact h
  -- counts of `G`
  have hS'Q : ∀ v, v ∈ S' ↔ v ∈ S ∧ v ∉ Q := hS'm
  have hn : nCount S [c, x, a] = nCount S' [c, x, a] + Q.length := by
    unfold nCount
    rw [← List.toFinset_card_of_nodup hQnd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_union, List.mem_toFinset, hS'Q]
      constructor
      · rintro ⟨hv, hvn⟩
        by_cases hvQ : v ∈ Q
        · exact Or.inr hvQ
        · exact Or.inl ⟨⟨hv, hvQ⟩, hvn⟩
      · rintro (⟨⟨hv, -⟩, hvn⟩ | hvQ)
        · exact ⟨hv, hvn⟩
        · exact ⟨hQS v hvQ, hpcQ v hvQ⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter, hS'Q] at h1
      exact h1.1.2 (List.mem_toFinset.mp h2)
  have hr : rCount S [c, x, a] L = Q.length := by
    unfold rCount
    rw [← List.toFinset_card_of_nodup hQnd]
    congr 1
    ext v
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hv, hvn, h3⟩
      by_contra hvQ
      have := hh.five v hv (by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at hvn ⊢
        exact ⟨hvn.2.1, hvn.2.2, hvQ, hvn.1⟩)
      omega
    · intro hvQ
      exact ⟨hQS v hvQ, hpcQ v hvQ, hL3 v hvQ⟩
  -- interior vertices of `G'`
  have hint' : ∀ v ∈ S', v ∉ [c, x, a] → v ∉ x :: a :: (Q ++ [c]) := by
    intro v hv hvn hvc
    have hvQ := ((hS'Q v).1 hv).2
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hvn hvc
    tauto
  have hYS' : ∀ y ∈ Y, y ∈ S' := fun y hy =>
    (hS'Q y).2 ⟨(hY y hy).1, fun h => (hY y hy).2.1 (by simp [h])⟩
  have hYpc : ∀ y ∈ Y, y ∉ [c, x, a] := fun y hy h =>
    (hY y hy).2.1 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> simp [h])
  have hL5Y : ∀ y ∈ Y, 5 ≤ (L y).card := fun y hy => hh.five y (hY y hy).1 (hY y hy).2.1
  have hksS : ∀ k ∈ ks, k ∉ S' := fun k hk h => ((hS'Q k).1 h).2 (hksQ k hk)
  have hksx : x ∉ ks := fun h => hxQ (hksQ x h)
  have hksa : a ∉ ks := fun h => haQ (hksQ a h)
  have hksc : c ∉ ks := fun h => hcQ (hksQ c h)
  have hκlen : ∀ κs ∈ F, ks.length = κs.length := by
    intro κs hκ
    have := (hFm κs hκ).1.length_eq
    rw [hks]; simpa using this.symm
  have hκK : ∀ κs ∈ F, List.Forall₂ (· ∈ ·) κs (ks.map Kl) := by
    intro κs hκ; rw [hks]; simpa using (hFm κs hκ).1
  -- the reduced lists of `G'`
  let L' : List C → V → Finset C := fun κs y =>
    if y ∈ Y then (L y).filter (fun col => ∀ k ∈ ks, H.Adj y k → updL g ks κs k ≠ col) else L y
  have hL'sub : ∀ κs y, L' κs y ⊆ L y := by
    intro κs y; simp only [L']; split_ifs
    · exact Finset.filter_subset _ _
    · exact subset_rfl
  have hL'card : ∀ κs, ∀ y ∈ Y,
      (L y).card ≤ (L' κs y).card + (ks.toFinset.filter (fun k => H.Adj y k)).card := by
    intro κs y hy
    have hsub : (L y) \ ((ks.toFinset.filter (fun k => H.Adj y k)).image (updL g ks κs)) ⊆
        L' κs y := by
      intro col hcol
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter, List.mem_toFinset,
        not_exists, not_and] at hcol
      simp only [L', hy, ite_true, Finset.mem_filter]
      exact ⟨hcol.1, fun k hk hyk e => hcol.2 k ⟨hk, hyk⟩ e⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.le_card_sdiff ((ks.toFinset.filter (fun k => H.Adj y k)).image
      (updL g ks κs)) (L y)
    have h3 := Finset.card_image_le (s := ks.toFinset.filter (fun k => H.Adj y k))
      (f := updL g ks κs)
    omega
  -- the bound and the extension, for each admissible colouring of the cut vertices
  have hper : ∀ κs ∈ F,
      Bound4 (ExtSet H S' [c, x, a] (L' κs) (updL g ks κs)).ncard (nCount S' [c, x, a])
        Bs.length ∧
      ∀ φ ∈ ExtSet H S' [c, x, a] (L' κs) (updL g ks κs), ∃ f ∈ ExtSet H S [c, x, a] L g,
        (∀ v ∈ S', f v = φ v) ∧ ∀ k ∈ ks, f k = updL g ks κs k := by
    intro κs hκ
    set gk := updL g ks κs with hgk
    have hgk2 : List.Forall₂ (fun k col => gk k = col) ks κs :=
      updL_forall₂ g ks κs hksnd (hκlen κs hκ)
    have hgkK : ∀ k ∈ ks, gk k ∈ Kl k := forall₂_mem_of hgk2 (hκK κs hκ)
    have hgko : ∀ v, v ∉ ks → gk v = g v := updL_of_not_mem g ks κs
    -- the hypotheses of Theorem 4 for `G'`
    have hthree : ∀ y ∈ Y, 3 ≤ (L' κs y).card := by
      intro y hy
      have := hL'card κs y hy
      have := (hc.K_nbrs hKOK (hY y hy).1 (hY y hy).2.1).1
      have := hL5Y y hy
      omega
    have hh' : Thm4Hyp H S' x (a :: (Y ++ [c])) a c (L' κs) gk true := by
      refine ⟨rfl, getLast?_cons_append_singleton a c Y, by simp,
        by rw [hgko x hksx, hgko a hksa]; exact hh.xa,
        fun _ => by rw [hgko x hksx, hgko c hksc]; exact hh.xc rfl,
        fun _ h => by rw [hgko a hksa, hgko c hksc]; exact hh.ac rfl h, ?_, ?_⟩
      · intro y hy hyn
        change y ∉ [c, x, a] at hyn
        have hyY : y ∈ Y := by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
            at hy hyn
          tauto
        exact hthree y hyY
      · intro y hy hyn
        have hyY : y ∉ Y := fun h => hyn (by simp [h])
        simp only [L', hyY, ite_false]
        exact hh.five y ((hS'Q y).1 hy).1 (hint' y hy (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
            at hyn ⊢
          tauto))
    -- `G'` has a colouring
    have hne : (ExtSet H S' [c, x, a] (L' κs) gk).Nonempty := by
      have hxY : x ∉ a :: (Y ++ [c]) := (List.nodup_cons.mp (T.nodup hNT')).1
      rcases T.thm3 H hNT' ⟨hh'.head, hh'.last, hh'.two_le, ⟨hh'.xa, hh'.xc rfl, hh'.ac rfl⟩,
          fun y hy hya hyc => hh'.three y hy (by
            show y ∉ [c, x, a]
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨hyc, fun e => hxY (e ▸ hy), hya⟩), hh'.five⟩ with h | h
      · exact extSet_nonempty_iff.mpr h
      · exfalso
        obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := h
        apply hgw
        refine ⟨PW, U, hGW, hndW, hhW, hlW, ?_, ?_⟩
        · intro y hy
          by_cases hya : y = a
          · exact Or.inl hya
          by_cases hyc : y = c
          · exact Or.inr (Or.inl hyc)
          right; right
          have hyY : y ∈ Y := by
            have := hsubW y hy
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
            tauto
          have h3 := hLW y hy hya hyc
          have hcard := hL'card κs y hyY
          have h5 := hL5Y y hyY
          obtain ⟨k₁, hk₁, k₂, hk₂, h12⟩ := Finset.one_lt_card.mp
            (show 1 < (ks.toFinset.filter (fun k => H.Adj y k)).card by omega)
          simp only [Finset.mem_filter, List.mem_toFinset] at hk₁ hk₂
          exact ⟨(hY y hyY).1, (hY y hyY).2.1, k₁, hksQ k₁ hk₁.1, k₂, hksQ k₂ hk₂.1, h12,
            hk₁.2, hk₂.2⟩
        · intro u hu
          obtain ⟨huS', hun⟩ := hUW u hu
          exact ⟨((hS'Q u).1 huS').1, hint' u huS' (by
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
              at hun ⊢
            tauto)⟩
    -- no exceptional vertex
    have hexc : ¬ Exc4 H S' x a c (L' κs) gk true := by
      rintro ⟨-, u, hu, hun, -, huc, hux, hua, -⟩
      exact hc.nohub u ((hS'Q u).1 hu).1 (hint' u hu hun) ⟨huc, hux, hua⟩
    -- induction
    have hlt : nCount S' [c, x, a] < nCount S [c, x, a] := by
      rw [hn]; have := List.length_pos_iff.mpr hQne; omega
    have hB := ih H S' x (a :: (Y ++ [c])) a c (L' κs) gk true hNT' hh'
      (Or.inl (by show nCount S' [c, x, a] < nCount S [c, x, a]; exact hlt)) hne hexc
    change Bound4 (ExtSet H S' [c, x, a] (L' κs) gk).ncard (nCount S' [c, x, a])
      (rCount S' [c, x, a] (L' κs)) at hB
    -- at most `s` vertices with three colours in `G'`
    have hr' : rCount S' [c, x, a] (L' κs) ≤ Bs.length := by
      set P := a :: (Q ++ [c]) with hPdef
      have hPnd' : P.Nodup := hPnd
      have hlenP : P.length = Q.length + 2 := by simp [hPdef]
      have hPl : (a :: (Q ++ [c])).length = P.length := rfl
      -- the position of `q_r`
      obtain ⟨m, hm⟩ : ∃ m, Q.length = m + 1 := ⟨Q.length - 1, by
        have := List.length_pos_iff.mpr hQne; omega⟩
      have hqrP : P[m + 1]'(by omega) = qr := by
        simp only [hPdef, List.getElem_cons_succ]
        rw [List.getElem_append_left (by omega), hqr, List.getLast_eq_getElem]
        congr 1; omega
      have hqrks : qr ∈ ks := by
        rw [hks]; exact List.mem_cons_of_mem _ (List.mem_of_mem_getLast? hlast')
      -- vertices with three colours in `G'`
      set A3 := S'.filter (fun v => v ∉ [c, x, a] ∧ (L' κs v).card = 3) with hA3
      have hA3prop : ∀ v ∈ A3, ∃ i, i + 2 < P.length ∧ P.getD i a ∈ ks.toFinset ∧
          H.Adj v (P.getD i a) ∧ H.Adj v (P.getD (i + 1) a) ∧ v ∈ S ∧
          v ∉ x :: a :: (Q ++ [c]) := by
        intro v hv
        rw [hA3, Finset.mem_filter] at hv
        obtain ⟨hvS', hvn, h3⟩ := hv
        have hvY : v ∈ Y := by
          by_contra hvY
          simp only [L', hvY, ite_false] at h3
          have := hh.five v ((hS'Q v).1 hvS').1 (hint' v hvS' hvn)
          omega
        have hcard := hL'card κs v hvY
        have h5 := hL5Y v hvY
        obtain ⟨i, hi, hiK, hi2, -, hA1, hA2⟩ :=
          (hc.K_nbrs hKOK (hY v hvY).1 (hY v hvY).2.1).2 (by omega)
        refine ⟨i, hi2, ?_, ?_, ?_, (hY v hvY).1, (hY v hvY).2.1⟩
        · rw [List.getD_eq_getElem _ _ (by omega)]; exact hiK
        · rw [List.getD_eq_getElem _ _ (by omega)]; exact hA1
        · rw [List.getD_eq_getElem _ _ hi]; exact hA2
      let idx : V → ℕ := fun v => if h : ∃ i, i + 2 < P.length ∧ P.getD i a ∈ ks.toFinset ∧
          H.Adj v (P.getD i a) ∧ H.Adj v (P.getD (i + 1) a) then Classical.choose h else 0
      have hidx : ∀ v ∈ A3, idx v + 2 < P.length ∧ P.getD (idx v) a ∈ ks.toFinset ∧
          H.Adj v (P.getD (idx v) a) ∧ H.Adj v (P.getD (idx v + 1) a) := by
        intro v hv
        obtain ⟨i, h1, h2, h3, h4, -, -⟩ := hA3prop v hv
        have hex : ∃ i, i + 2 < P.length ∧ P.getD i a ∈ ks.toFinset ∧
            H.Adj v (P.getD i a) ∧ H.Adj v (P.getD (i + 1) a) := ⟨i, h1, h2, h3, h4⟩
        simp only [idx, hex, ↓reduceDIte]
        exact Classical.choose_spec hex
      set Idx := (Finset.range P.length).filter
        (fun i => i + 2 < P.length ∧ P.getD i a ∈ ks.toFinset) with hIdx
      have h1 : A3.card ≤ Idx.card := by
        apply Finset.card_le_card_of_injOn idx
        · intro v hv
          have := hidx v hv
          simp only [hIdx, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
          exact ⟨by omega, this.1, this.2.1⟩
        · intro v hv w hw he
          have hv' := hidx v hv
          have hw' := hidx w hw
          obtain ⟨_, -, -, -, -, hvS, hvn⟩ := hA3prop v hv
          obtain ⟨_, -, -, -, -, hwS, hwn⟩ := hA3prop w hw
          rw [he] at hv'
          set i := idx w
          have hdec : P = P.take i ++ P[i]'(by omega) :: P[i + 1]'(by omega) :: P.drop (i + 2) := by
            conv_lhs => rw [list_eq_take_getElem_drop P i (by omega)]
            rw [List.drop_eq_getElem_cons (by omega)]
          rw [List.getD_eq_getElem _ _ (by omega)] at hv' hw'
          rw [List.getD_eq_getElem _ _ (by omega)] at hv' hw'
          exact hc.apex_unique hdec hvS hwS hvn hwn hv'.2.2.1 hv'.2.2.2 hw'.2.2.1 hw'.2.2.2
      have h2 : Idx.card ≤ (ks.toFinset.erase qr).card := by
        apply Finset.card_le_card_of_injOn (fun i => P.getD i a)
        · intro i hi
          simp only [hIdx, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          refine ⟨hi.2.2, fun e => ?_⟩
          rw [List.getD_eq_getElem _ _ hi.1, ← hqrP] at e
          have := (List.Nodup.getElem_inj_iff hPnd').mp e
          omega
        · intro i hi j hj e
          simp only [hIdx, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
          simp only at e
          rw [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at e
          exact (List.Nodup.getElem_inj_iff hPnd').mp e
      have h3 : (ks.toFinset.erase qr).card = Bs.length := by
        rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr hqrks),
          List.toFinset_card_of_nodup hksnd, hlen]
        simp
      unfold rCount
      rw [← hA3]
      omega
    refine ⟨?_, ?_⟩
    · unfold Bound4 at hB ⊢
      exact hB.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr'))
    · intro φ hφ
      obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
      have hφks : ∀ k ∈ ks, φ k = gk k := fun k hk => hφ1 k (Or.inl (hksS k hk))
      -- interior neighbours of cut vertices get other colours
      have hkcol : ∀ k ∈ ks, ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj k y → φ y ≠ φ k := by
        intro k hk y hyS hyn hky
        have hyY := hYc k (hksQ k hk) y hyS hyn hky
        have := hφ2 y (hYS' y hyY) (hYpc y hyY)
        simp only [L', hyY, ite_true, Finset.mem_filter] at this
        rw [hφks k hk]
        exact fun e => this.2 k hk hky.symm e.symm
      obtain ⟨⟨f, hf1, hf2, hf3⟩, hKK⟩ := hc.extend φ Bs ks κs [a] [c]
        (by rw [← hQi]; simp) hlen
        (forall₂_imp_mem hgk2 (fun k hk col h => (hφks k hk).trans h)) (hFm κs hκ).2
        (by
          intro B hB b hb y₁ hy₁ y₂ hy₂ hy₁n hy₂n hb1 hb2
          by_contra hne
          exact hBsK B hB b hb (Or.inr (Or.inr ⟨y₁, hy₁, y₂, hy₂, hy₁n, hy₂n, hne, hb1, hb2⟩)))
        hksQ hkcol
      have hflQ : ∀ v ∈ Bs.flatten, v ∈ Q := hBsQ
      have hS'fl : ∀ v ∈ S', v ∉ Bs.flatten := fun v hv h => ((hS'Q v).1 hv).2 (hflQ v h)
      have hfS' : ∀ v ∈ S', f v = φ v := fun v hv => hf1 v (hS'fl v hv)
      have hfks : ∀ k ∈ ks, f k = gk k := fun k hk => (hf1 k (hksBs k hk)).trans (hφks k hk)
      -- the neighbours of cut vertices on the outer cycle
      have hka : ∀ k ∈ ks, H.Adj k a → k = q₁ := by
        intro k hk hka
        have := hc.chordless k a (by simp [hksQ k hk]) (by simp) hka
        have h' := ConsecIn.nbr (A := []) (y := a) (B := Q ++ [c]) (by simpa using hPnd)
          (by simpa using this.symm)
        rcases h' with h' | h'
        · simp at h'
        · rw [List.head?_append_of_ne_nil _ hQne, List.head?_eq_some_head hQne] at h'
          exact (Option.some.inj h').symm
      have hkc : ∀ k ∈ ks, H.Adj k c → k = qr := by
        intro k hk hkc
        have := hc.chordless k c (by simp [hksQ k hk]) (by simp) hkc
        have h' := ConsecIn.nbr (A := a :: Q) (y := c) (B := []) (by simpa using hPnd)
          (by simpa using this.symm)
        rcases h' with h' | h'
        · rw [List.getLast?_cons, List.getLast?_eq_some_getLast hQne] at h'
          simpa using h'.symm
        · simp at h'
      have hcolS'K : ∀ k ∈ ks, ∀ w ∈ S', H.Adj k w → φ k ≠ φ w := by
        intro k hk w hw hkw
        by_cases hwn : w ∈ x :: a :: (Q ++ [c])
        · have hwQ := ((hS'Q w).1 hw).2
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hwn
          rcases hwn with rfl | rfl | hwQ' | rfl
          · exact absurd hkw.symm (hc.xfree k (hksQ k hk))
          · have := hka k hk hkw
            rw [hφks k hk, hφ1 w (Or.inr (by simp)), hgko w hksa]
            have hK := hgkK k hk
            simp only [hKl, this, ite_true] at hK
            exact Finset.ne_of_mem_erase (this ▸ hK)
          · exact absurd hwQ' hwQ
          · have := hkc k hk hkw
            rw [hφks k hk, hφ1 w (Or.inr (by simp)), hgko w hksc]
            have hK := hgkK k hk
            simp only [hKl, this, Ne.symm hq₁r, ite_false, ite_true] at hK
            exact Finset.ne_of_mem_erase (this ▸ hK)
        · exact (hkcol k hk w ((hS'Q w).1 hw).1 hwn hkw).symm
      refine ⟨f, ⟨?_, ?_, ?_⟩, hfS', hfks⟩
      · intro v hv
        have hvfl : v ∉ Bs.flatten := by
          intro h
          rcases hv with hv | hv
          · exact hv (hQS v (hflQ v h))
          · exact hpcQ v (hflQ v h) hv
        rw [hf1 v hvfl]
        have hvks : v ∉ ks := by
          intro h
          rcases hv with hv | hv
          · exact hv (hQS v (hksQ v h))
          · exact hpcQ v (hksQ v h) hv
        rw [hφ1 v (by
          rcases hv with hv | hv
          · exact Or.inl (fun h => hv ((hS'Q v).1 h).1)
          · exact Or.inr hv), hgko v hvks]
      · intro v hv hvn
        by_cases hvfl : v ∈ Bs.flatten
        · exact hf2 v hvfl
        · rw [hf1 v hvfl]
          by_cases hvQ : v ∈ Q
          · rcases hQmem v hvQ with hk | hk
            · rw [hφks v hk]; exact hKlsub v (hgkK v hk)
            · exact absurd hk hvfl
          · exact hL'sub κs v (hφ2 v ((hS'Q v).2 ⟨hv, hvQ⟩) hvn)
      · intro u hu w hw huw
        by_cases hub : u ∈ Bs.flatten
        · exact hf3 u hub w hw huw
        by_cases hwb : w ∈ Bs.flatten
        · exact (hf3 w hwb u hu huw.symm).symm
        rw [hf1 u hub, hf1 w hwb]
        have hu' : u ∈ ks ∨ u ∈ S' := by
          by_cases huQ : u ∈ Q
          · rcases hQmem u huQ with h | h
            · exact Or.inl h
            · exact absurd h hub
          · exact Or.inr ((hS'Q u).2 ⟨hu, huQ⟩)
        have hw' : w ∈ ks ∨ w ∈ S' := by
          by_cases hwQ : w ∈ Q
          · rcases hQmem w hwQ with h | h
            · exact Or.inl h
            · exact absurd h hwb
          · exact Or.inr ((hS'Q w).2 ⟨hw, hwQ⟩)
        rcases hu' with hu' | hu' <;> rcases hw' with hw' | hw'
        · exact hKK u hu' w hw' huw
        · exact hcolS'K u hu' w hw' huw
        · exact (hcolS'K w hw' u hu' huw.symm).symm
        · exact hφ3 u hu' w hw' huw
  -- counting
  set E : List C → Set (V → C) := fun κs => ExtSet H S' [c, x, a] (L' κs) (updL g ks κs)
    with hE
  let e : List C → (V → C) → (V → C) := fun κs φ =>
    if h : κs ∈ F ∧ φ ∈ E κs then Classical.choose ((hper κs h.1).2 φ h.2) else φ
  have he : ∀ κs ∈ F, ∀ φ ∈ E κs, e κs φ ∈ ExtSet H S [c, x, a] L g ∧
      (∀ v ∈ S', e κs φ v = φ v) ∧ ∀ k ∈ ks, e κs φ k = updL g ks κs k := by
    intro κs hκ φ hφ
    have hc' : κs ∈ F ∧ φ ∈ E κs := ⟨hκ, hφ⟩
    simp only [e, hc']
    exact Classical.choose_spec ((hper κs hκ).2 φ hφ)
  set M8 := minM8 (nCount S' [c, x, a]) Bs.length with hM8
  have hinj : ∀ κs ∈ F, Set.InjOn (e κs) (E κs) := by
    intro κs hκ φ hφ φ' hφ' heq
    funext v
    by_cases hv : v ∈ S'
    · rw [← (he κs hκ φ hφ).2.1 v hv, ← (he κs hκ φ' hφ').2.1 v hv, heq]
    · rw [hφ.1 v (Or.inl hv), hφ'.1 v (Or.inl hv)]
  have hcnt := ncard_ge_card_mul F (fun κs => e κs '' E κs) (ExtSet H S [c, x, a] L g)
    (extSet_finite H S [c, x, a] L g)
    (by
      intro κs hκ f hf
      obtain ⟨φ, hφ, rfl⟩ := hf
      exact (he κs hκ φ hφ).1)
    (by
      intro κs hκ κs' hκ' hne
      rw [Set.disjoint_left]
      intro f hf hf'
      obtain ⟨φ, hφ, rfl⟩ := hf
      obtain ⟨φ', hφ', heq⟩ := hf'
      apply hne
      have h1 := (he κs hκ φ hφ).2.2
      have h2 := (he κs' hκ' φ' hφ').2.2
      have h12 : ∀ k ∈ ks, updL g ks κs' k = updL g ks κs k := fun k hk => by
        rw [← h1 k hk, ← h2 k hk, heq]
      have a1 := updL_forall₂ g ks κs hksnd (hκlen κs hκ)
      have a2 := updL_forall₂ g ks κs' hksnd (hκlen κs' hκ')
      exact forall₂_eq_of_forall₂ a1
        (forall₂_imp_mem a2 (fun k hk col h => (h12 k hk).symm.trans h)))
    M8
    (by
      intro κs hκ
      rw [(hinj κs hκ).ncard_image]
      exact minM8_le (hper κs hκ).1)
  -- the final inequality
  have hQlen : Q.length = Bs.length + 1 + (Bs.map List.length).sum := by
    rw [hQi, length_interleave ks Bs hlen, hlen]
  have hFc' : 2 ^ (1 + 3 * Bs.length) ≤ F.card ^ 9 * 4 ^ Q.length := by
    have hsum : ((Bs.map (fun B => B.map L)).map List.length).sum =
        (Bs.map List.length).sum := by
      simp [Function.comp_def]
    rw [hQlen]
    have := hFc
    rw [List.length_map, hsum] at this
    exact this
  have := case1_arith hcnt (minM8_spec (nCount S' [c, x, a]) Bs.length) hFc'
  unfold Bound4
  rw [hn, hr]
  convert this using 2

end NTCalc

end ThomassenManyColourings
