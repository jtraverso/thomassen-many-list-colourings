/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim9x

/-!
# Theorem 4, Claim 9: the chord `v₁ v_{k-1}`

With `v_k, v₁, v₂` precoloured and a chord `v₁ w`, `w = v_{k-1}`, the triangle `v₁ w v_k` is a
face. Colour `w` (one way if it has three colours, two ways otherwise) and apply induction to the
rest (`v_{k-1}, v₁, v₂` precoloured). If the rest is a generalized wheel (Theorem 3's exception),
`n ≤ 3r`; the exception of Theorem 4 in the rest forces `k = 5`, counted directly.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

theorem bound4_of_two {N n r : ℕ} (hN : 2 ≤ N) (hn : n ≤ 9) : Bound4 N n r := by
  unfold Bound4
  calc 2 ^ n ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hn
    _ ≤ N ^ 9 := Nat.pow_le_pow_left hN 9
    _ ≤ N ^ 9 * 8 ^ r := Nat.le_mul_of_pos_right _ (by positivity)

omit [DecidableEq V] [DecidableEq C] in
theorem two_le_ncard {s : Set (V → C)} (hs : s.Finite) {f₁ f₂ : V → C} (h₁ : f₁ ∈ s) (h₂ : f₂ ∈ s)
    (hne : f₁ ≠ f₂) : 2 ≤ s.ncard := by
  have := Set.ncard_le_ncard (s := {f₁, f₂}) (t := s)
    (by intro f hf; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl <;> assumption) hs
  rwa [Set.ncard_pair hne] at this

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 32000000 in
/-- **Claim 9, the chord `v₁ v_{k-1}`.** -/
theorem thm4_claim9_w (H : SimpleGraph V) {S : Finset V} {x w : V} {Q : List V} {a c : V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: (Q ++ [w, c]))) (hh : Thm4Hyp H S x (Q ++ [w, c]) a c L g true)
    (hQ : Q ≠ []) (hxw : H.Adj x w)
    (hPc : ∀ u v, u ∈ Q ++ [w, c] → v ∈ Q ++ [w, c] → H.Adj u v → ConsecIn (Q ++ [w, c]) u v)
    (hN : T.NoSepTri H S (x :: (Q ++ [w, c])))
    (ih : T.Thm4Lt C (nCount S (pcList true x a c))
      (nCount S (pcList true x a c) - rCount S (pcList true x a c) L) true) :
    Thm4Concl H S x a c L g true := by
  classical
  have hpc : pcList true x a c = [c, x, a] := rfl
  intro hne hexc
  rw [hpc] at hne ⊢
  have hnd := T.nodup hNT
  have hxP := (List.nodup_cons.mp hnd).1
  have hPnd := (List.nodup_cons.mp hnd).2
  have hQd := List.nodup_append.mp hPnd
  have hwQ : w ∉ Q := fun h => hQd.2.2 w h w (by simp) rfl
  have hcQ : c ∉ Q := fun h => hQd.2.2 c h c (by simp) rfl
  have hwc : w ≠ c := by intro e; have := hQd.2.1; rw [e] at this; simp at this
  have hhead : Q.head? = some a := by
    have := hh.head; rwa [List.head?_append_of_ne_nil _ hQ] at this
  have haQ : a ∈ Q := List.mem_of_mem_head? hhead
  have hwa : w ≠ a := fun e => hwQ (e ▸ haQ)
  have hca : c ≠ a := fun e => hcQ (e ▸ haQ)
  have hxa : x ≠ a := fun e => hxP (by rw [e]; simp [haQ])
  have hxw' : x ≠ w := fun e => hxP (by rw [e]; simp)
  have hxc : x ≠ c := fun e => hxP (by rw [e]; simp)
  -- the chord
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.chord (l₁ := Q) (l₂ := [c]) (by simpa using hNT) hQ
    (by simp) hxw
  have h₁' : T.NT H S₁ (x :: (Q ++ [w])) := h₁
  have h₂' : T.NT H S₂ [w, c, x] := by simpa using h₂
  have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = x ∨ v = w := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hR₂ : Region H S (x :: (Q ++ [w, c])) S₂ [w, c, x] := by
    refine (Region.refl H S _).piece' (c₁ := x :: (Q ++ [w])) hU ?_ hX ?_
      (fun v hv => T.subset h₁' v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hR₁ : Region H S (x :: (Q ++ [w, c])) S₁ (x :: (Q ++ [w])) := by
    refine (Region.refl H S _).piece (c₂ := [w, c, x]) hU ?_ hX ?_
      (fun v hv => T.subset h₂' v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hS₂ := hN S₂ w c x h₂' hR₂
  have hcS₂ : c ∈ S₂ := T.subset h₂' c (by simp)
  have hcS₁ : c ∉ S₁ := fun h => by
    rcases hmem c h hcS₂ with e | e
    · exact hxc e.symm
    · exact hwc e.symm
  have hS : ∀ v ∈ S, v ∈ S₁ ∨ v = c := by
    intro v hv
    rcases Finset.mem_union.mp (hU ▸ hv) with h | h
    · exact Or.inl h
    · rcases hS₂ v h with e | e | e
      · exact Or.inl (e ▸ T.subset h₁' w (by simp))
      · exact Or.inr e
      · exact Or.inl (e ▸ T.subset h₁' x (by simp))
  have hS₁S : S₁ ⊆ S := fun v hv => hU ▸ Finset.mem_union_left _ hv
  have hcS : c ∈ S := hU ▸ Finset.mem_union_right _ hcS₂
  have h5 : ∀ v ∈ S, v ∉ x :: (Q ++ [w, c]) → 5 ≤ (L v).card := hh.five
  have hP' : Q ++ [w, c] = (Q ++ [w]) ++ [c] := by simp
  have hndQw : (Q ++ [w]).Nodup := (List.nodup_append.mp (hP' ▸ hPnd)).1
  have hchQw : ∀ u v, u ∈ Q ++ [w] → v ∈ Q ++ [w] → H.Adj u v → ConsecIn (Q ++ [w]) u v := by
    intro u v hu hv huv
    have h := hPc u v (by rw [hP']; exact List.mem_append_left _ hu)
      (by rw [hP']; exact List.mem_append_left _ hv) huv
    rw [hP'] at h
    exact ConsecIn.of_append_right (hP' ▸ hPnd) hu hv h
  have hwS₁ : w ∈ S₁ := T.subset h₁' w (by simp)
  have hxS₁ : x ∈ S₁ := T.subset h₁' x (by simp)
  have haS₁ : a ∈ S₁ := T.subset h₁' a (by simp [haQ])
  have hfiltn : S.filter (· ∉ [c, x, a]) = insert w (S₁.filter (· ∉ [w, x, a])) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    constructor
    · rintro ⟨hv, hvc, hvx, hva⟩
      by_cases hvw : v = w
      · exact Or.inl hvw
      · rcases hS v hv with h | h
        · exact Or.inr ⟨h, hvw, hvx, hva⟩
        · exact absurd h hvc
    · rintro (rfl | ⟨hv, hvw, hvx, hva⟩)
      · exact ⟨hS₁S hwS₁, hwc, fun e => hxw' e.symm, hwa⟩
      · exact ⟨hS₁S hv, fun e => hcS₁ (e ▸ hv), hvx, hva⟩
  have hwnot : w ∉ S₁.filter (· ∉ [w, x, a]) := by simp
  have hn : nCount S [c, x, a] = nCount S₁ [w, x, a] + 1 := by
    unfold nCount; rw [hfiltn, Finset.card_insert_of_notMem hwnot]
  have hrle : rCount S [c, x, a] L ≤ rCount S₁ [w, x, a] L + 1 := by
    unfold rCount
    calc (S.filter (fun v => v ∉ [c, x, a] ∧ (L v).card = 3)).card
        ≤ (insert w (S₁.filter (fun v => v ∉ [w, x, a] ∧ (L v).card = 3))).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_insert, List.mem_cons, List.not_mem_nil,
            or_false, not_or] at hv ⊢
          obtain ⟨hvS, ⟨hvc, hvx, hva⟩, h3⟩ := hv
          by_cases hvw : v = w
          · exact Or.inl hvw
          · rcases hS v hvS with h | h
            · exact Or.inr ⟨h, ⟨hvw, hvx, hva⟩, h3⟩
            · exact absurd h hvc
      _ ≤ _ := Finset.card_insert_le _ _
  have hrge : rCount S₁ [w, x, a] L ≤ rCount S [c, x, a] L := by
    unfold rCount
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv ⊢
    exact ⟨hS₁S hv.1, ⟨fun e => hcS₁ (e ▸ hv.1), hv.2.1.2.1, hv.2.1.2.2⟩, hv.2.2⟩
  have hrw3 : (L w).card = 3 → rCount S [c, x, a] L = rCount S₁ [w, x, a] L + 1 := by
    intro h3
    unfold rCount
    rw [← Finset.card_insert_of_notMem (a := w) (by simp)]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, List.mem_cons, List.not_mem_nil, or_false,
      not_or]
    constructor
    · rintro ⟨hv, ⟨hvc, hvx, hva⟩, h3'⟩
      by_cases hvw : v = w
      · exact Or.inl hvw
      · rcases hS v hv with h | h
        · exact Or.inr ⟨h, ⟨hvw, hvx, hva⟩, h3'⟩
        · exact absurd h hvc
    · rintro (rfl | ⟨hv, ⟨hvw, hvx, hva⟩, h3'⟩)
      · exact ⟨hS₁S hwS₁, ⟨hwc, fun e => hxw' e.symm, hwa⟩, h3⟩
      · exact ⟨hS₁S hv, ⟨fun e => hcS₁ (e ▸ hv), hvx, hva⟩, h3'⟩
  have hw3 : 3 ≤ (L w).card := by
    apply hh.three w (by simp)
    show w ∉ [c, x, a]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hwc, fun e => hxw' e.symm, hwa⟩
  by_cases hE : Exc3 H S₁ x (Q ++ [w]) a w L
  · -- (i) the rest is a generalized wheel
    by_cases hQ1 : Q.length = 1
    · -- `k = 4`: `S = {x, a, w, c}`
      obtain ⟨q, rfl⟩ : ∃ q, Q = [q] := by
        rcases Q with _ | ⟨q, _ | ⟨q', Q'⟩⟩
        · simp at hQ1
        · exact ⟨q, rfl⟩
        · simp at hQ1
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hS₁' := hN S₁ q w x (by simpa using T.rotate h₁') (by
        refine ⟨hR₁.1, fun v hv hvc => hR₁.2 v hv (fun h => hvc (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
          tauto))⟩)
      by_cases hw3' : (L w).card = 3
      · exact bound4_of_le (ncard_extSet_pos hne) (by
          have := hrw3 hw3'
          have h0 : nCount S₁ [w, x, q] = 0 := by
            unfold nCount
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro v hv hvn
            rcases hS₁' v hv with e | e | e <;> simp [e] at hvn
          omega)
      -- `w` has at least four colours and is joined to `c, x, a`
      have hqw : H.Adj q w := T.adj_cons (by simpa using T.rotate h₁')
      have hwc' : H.Adj w c := by
        have := NT_chain hNT
        simp only [List.cons_append, List.nil_append, List.isChain_cons_cons] at this
        exact this.2.2.1
      have hfree : 2 ≤ ((L w) \ {g c, g x, g q}).card := by
        have h1 := Finset.le_card_sdiff ({g c, g x, g q} : Finset C) (L w)
        have h2 := Finset.card_le_three (a := g c) (b := g x) (c := g q)
        by_contra hlt
        apply hexc
        refine ⟨rfl, w, hS₁S hwS₁, by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hwc, fun e => hxw' e.symm, hwa⟩, by omega, hwc', hxw.symm, hqw.symm, by omega⟩
      obtain ⟨γ₁, h1, γ₂, h2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < ((L w) \ {g c, g x, g q}).card)
      have mk : ∀ γ ∈ (L w) \ {g c, g x, g q}, Function.update g w γ ∈ ExtSet H S [c, x, q] L g := by
        intro γ hγ
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
        obtain ⟨hγL, hγc, hγx, hγq⟩ := hγ
        have hSv : ∀ v ∈ S, v = x ∨ v = q ∨ v = w ∨ v = c := by
          intro v hv
          rcases hS v hv with h | h
          · rcases hS₁' v h with e | e | e
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inr (Or.inl e))
            · exact Or.inl e
          · exact Or.inr (Or.inr (Or.inr h))
        refine ⟨fun v hv => ?_, fun v hv hvn => ?_, fun p hp r hr hpr => ?_⟩
        · have hvw : v ≠ w := by
            rintro rfl
            rcases hv with hv | hv
            · exact hv (hS₁S hwS₁)
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with e | e | e
              · exact hwc e
              · exact hxw' e.symm
              · exact hwa e
          exact Function.update_of_ne hvw ..
        · rcases hSv v hv with e | e | e | e
          · exfalso; apply hvn; simp [e]
          · exfalso; apply hvn; simp [e]
          · rw [e, Function.update_self]; exact hγL
          · exfalso; apply hvn; simp [e]
        · have upd : ∀ v, v ≠ w → Function.update g w γ v = g v := fun v hv =>
            Function.update_of_ne hv ..
          rcases hSv p hp with e | e | e | e <;> rcases hSv r hr with e' | e' | e' | e' <;>
            rw [e, e'] at hpr ⊢ <;>
            simp only [Function.update_self, upd x hxw', upd q (Ne.symm hwa),
              upd c (Ne.symm hwc)] <;>
            first
            | exact absurd hpr (H.loopless.irrefl _)
            | exact hh.xa | exact hh.xa.symm | exact hh.xc rfl | exact (hh.xc rfl).symm
            | exact hh.ac rfl hpr | exact (hh.ac rfl hpr.symm).symm
            | exact Ne.symm hγx | exact hγx | exact Ne.symm hγq | exact hγq
            | exact Ne.symm hγc | exact hγc
      have hne12 : Function.update g w γ₁ ≠ Function.update g w γ₂ := by
        intro e; have := congrFun e w; simp at this; exact h12 this
      have h0 : nCount S₁ [w, x, q] = 0 := by
        unfold nCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v hv hvn
        rcases hS₁' v hv with e | e | e <;> simp [e] at hvn
      exact bound4_of_two (two_le_ncard (extSet_finite H S [c, x, q] L g) (mk γ₁ h1) (mk γ₂ h2)
        hne12) (by rw [hn, h0]; norm_num)
    · -- `|Q| ≥ 2`: the generalized wheel has at most `|Q| - 1` centres
      have hQ2 : 2 ≤ Q.length := by
        have := List.length_pos_iff.mpr hQ; omega
      obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, hLW⟩ := hE
      have hPW : PW = Q ++ [w] := path_eq_of_chordless _ _ hndQw hndW hsubW
        (by rw [hhW, List.head?_append_of_ne_nil _ hQ, hhead]) (by rw [hlW, List.getLast?_concat])
        hGW.isPath hchQw
      subst hPW
      obtain ⟨hfill, hG3⟩ := gw_fill hN hGW h₁' hR₁ hUW
      have hcU := hG3.card_add_two_le
      simp only [List.length_append, List.length_singleton] at hcU
      have hQnd : Q.Nodup := (List.nodup_append.mp hndQw).1
      have haQ' : a ∈ Q.toFinset := List.mem_toFinset.mpr haQ
      have hcardQ : (Q.toFinset.erase a).card = Q.length - 1 := by
        rw [Finset.card_erase_of_mem haQ', List.toFinset_card_of_nodup hQnd]
      have hn₁ : nCount S₁ [w, x, a] ≤ (Q.length - 1) + U.card := by
        unfold nCount
        calc (S₁.filter (· ∉ [w, x, a])).card ≤ (Q.toFinset.erase a ∪ U).card := by
              apply Finset.card_le_card
              intro z hz
              simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
                not_or] at hz
              obtain ⟨hzS, hzw, hzx, hza⟩ := hz
              simp only [Finset.mem_union, Finset.mem_erase, List.mem_toFinset]
              rcases hfill z hzS with e | e | e
              · exact absurd e hzx
              · left; refine ⟨hza, ?_⟩
                simp only [List.mem_append, List.mem_singleton] at e
                rcases e with e | e
                · exact e
                · exact absurd e hzw
              · exact Or.inr e
          _ ≤ (Q.toFinset.erase a).card + U.card := Finset.card_union_le _ _
          _ = _ := by rw [hcardQ]
      have hr₁ : Q.length - 1 ≤ rCount S₁ [w, x, a] L := by
        unfold rCount
        rw [← hcardQ]
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_erase, List.mem_toFinset] at hz
        obtain ⟨hza, hzQ⟩ := hz
        have hzw : z ≠ w := fun e => hwQ (e ▸ hzQ)
        simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨T.subset h₁' z (by simp [hzQ]), ⟨hzw, fun e => hxP (by rw [← e]; simp [hzQ]), hza⟩,
          hLW z (List.mem_append_left _ hzQ) hza hzw⟩
      exact bound4_of_le (ncard_extSet_pos hne) (by omega)
  -- (ii) colour `w` and apply induction to the rest
  have hxa' : H.Adj x a := by
    have := NT_chain hNT
    obtain ⟨q, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    simp only [List.cons_append, List.isChain_cons_cons] at this
    exact this.1
  have hnaw : ¬ H.Adj a w := by
    intro haw
    apply hE
    have hcons := hPc w a (by simp) (by simp [haQ]) haw.symm
    rw [show Q ++ [w, c] = Q ++ w :: [c] from rfl] at hcons
    rcases ConsecIn.nbr (by simpa using hPnd) hcons with h | h
    · have hQa := eq_single_of_head_last (List.nodup_append.mp hndQw).1 hhead h
      subst hQa
      exact ⟨[a, w], ∅, GW.one (Block.tri hxa' hxw haw), by simp [hwa.symm],
        rfl, rfl, fun y hy => by simpa using hy, by simp,
        fun y hy h1 h2 => by simp at hy; tauto⟩
    · simp at h; exact absurd h hca
  have hrw4 : (L w).card ≠ 3 → rCount S [c, x, a] L = rCount S₁ [w, x, a] L := by
    intro h3
    unfold rCount
    congr 1
    ext v
    simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · rintro ⟨hv, ⟨hvc, hvx, hva⟩, h3'⟩
      have hvw : v ≠ w := fun e => h3 (e ▸ h3')
      rcases hS v hv with h | h
      · exact ⟨h, ⟨hvw, hvx, hva⟩, h3'⟩
      · exact absurd h hvc
    · rintro ⟨hv, ⟨hvw, hvx, hva⟩, h3'⟩
      exact ⟨hS₁S hv, ⟨fun e => hcS₁ (e ▸ hv), hvx, hva⟩, h3'⟩
  by_cases hspec : ∃ u ∈ S₁, u ∉ [w, x, a] ∧ (L u).card = 4 ∧ H.Adj u w ∧ H.Adj u x ∧ H.Adj u a
  · -- the exception of Theorem 4 in the rest: `P = a u w c`, counted directly
    obtain ⟨u, huS₁, hun, hu4, huw, hux, hua⟩ := hspec
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hun
    obtain ⟨huw', hux', hua'⟩ := hun
    have huc : u ≠ c := fun e => hcS₁ (e ▸ huS₁)
    have huQ : u ∈ Q := by
      by_contra hn
      have := hh.five u (hS₁S huS₁) (by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
        exact ⟨hux', hn, huw', huc⟩)
      omega
    -- `Q = [a, u]`
    obtain ⟨A, B, hAB⟩ := List.append_of_mem huQ
    have hPAB : Q ++ [w, c] = A ++ u :: (B ++ [w, c]) := by rw [hAB]; simp
    have hndAB : (A ++ u :: (B ++ [w, c])).Nodup := hPAB ▸ hPnd
    have hAne : A ≠ [] := by
      rintro rfl; simp only [List.nil_append] at hAB hhead
      rw [hAB] at hhead; simp at hhead; exact hua' hhead
    have hAhead : A.head? = some a := by
      rw [hAB, List.head?_append_of_ne_nil _ hAne] at hhead; exact hhead
    have hcua := hPc u a (by simp [huQ]) (by simp [haQ]) hua
    rw [hPAB] at hcua
    have hA : A = [a] := by
      rcases ConsecIn.nbr hndAB hcua with h | h
      · exact eq_single_of_head_last (List.nodup_append.mp hndAB).1 hAhead h
      · exfalso
        exact (List.nodup_append.mp hndAB).2.2 a (List.mem_of_mem_head? hAhead) a
          (List.mem_cons_of_mem _ (List.mem_of_mem_head? h)) rfl
    have hcuw := hPc u w (by simp [huQ]) (by simp) huw
    rw [hPAB] at hcuw
    have hB : B = [] := by
      rcases ConsecIn.nbr hndAB hcuw with h | h
      · rw [hA] at h; simp at h; exact absurd h.symm hwa
      · rcases B with _ | ⟨b, B'⟩
        · rfl
        · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
          exfalso; apply hwQ; rw [hAB, ← h]; simp
    subst hA; subst hB
    simp only [List.singleton_append] at hAB
    subst hAB
    -- `S = {x, a, u, w, c}`
    have h₁'' : T.NT H S₁ (x :: ([a] ++ u :: [w])) := by simpa using h₁'
    obtain ⟨T₁, T₂, ht₁, ht₂, hUT, hIT, hXT⟩ := T.chord h₁'' (by simp) (by simp) hux.symm
    have hmemT : ∀ v, v ∈ T₁ → v ∈ T₂ → v = x ∨ v = u := by
      intro v h1 h2
      have : v ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hIT] at this; simpa using this
    have ht₁' : T.NT H T₁ [x, a, u] := by simpa using ht₁
    have ht₂' : T.NT H T₂ [u, w, x] := by simpa using ht₂
    have hRT₁ : Region H S (x :: ([a, u] ++ [w, c])) T₁ [x, a, u] := by
      refine hR₁.piece (c₂ := [u, w, x]) hUT ?_ hXT ?_ (fun v hv => T.subset ht₂' v hv)
      · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
      · intro v hv; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢
        tauto
    have hRT₂ : Region H S (x :: ([a, u] ++ [w, c])) T₂ [u, w, x] := by
      refine hR₁.piece' (c₁ := [x, a, u]) hUT ?_ hXT ?_ (fun v hv => T.subset ht₁' v hv)
      · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
      · intro v hv; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢
        tauto
    have hF₁ := hN T₁ x a u ht₁' hRT₁
    have hF₂ := hN T₂ u w x ht₂' hRT₂
    have hSv : ∀ v ∈ S, v = x ∨ v = a ∨ v = u ∨ v = w ∨ v = c := by
      intro v hv
      rcases hS v hv with h | h
      · rcases Finset.mem_union.mp (hUT ▸ h) with h' | h'
        · rcases hF₁ v h' with e | e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr (Or.inl e))
        · rcases hF₂ v h' with e | e | e
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
          · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hn2 : nCount S [c, x, a] ≤ 2 := by
      unfold nCount
      calc (S.filter (· ∉ [c, x, a])).card ≤ ({u, w} : Finset V).card := by
            apply Finset.card_le_card
            intro v hv
            simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
              not_or] at hv
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases hSv v hv.1 with e | e | e | e | e
            · exact absurd e hv.2.2.1
            · exact absurd e hv.2.2.2
            · exact Or.inl e
            · exact Or.inr e
            · exact absurd e hv.2.1
        _ ≤ 2 := Finset.card_le_two
    by_cases hr1 : 1 ≤ rCount S [c, x, a] L
    · exact bound4_of_le (ncard_extSet_pos hne) (by omega)
    have hw4 : (L w).card ≠ 3 := by
      intro h3; apply hr1
      unfold rCount
      refine Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hS₁S hwS₁, ?_, h3⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hwc, fun e => hxw' e.symm, hwa⟩
    -- non-edges of the outer path `a u w c`
    have hnuc : ¬ H.Adj u c := by
      intro h
      have := hPc u c (by simp) (by simp) h
      simp [ConsecIn, hua', huw', huc, hca, Ne.symm huc, Ne.symm hwc] at this
    obtain ⟨γ₁, h1, γ₂, h2, h12⟩ := Finset.one_lt_card.mp
      (show 1 < (((L w).erase (g x)).erase (g c)).card by
        have := Finset.pred_card_le_card_erase (s := L w) (a := g x)
        have := Finset.pred_card_le_card_erase (s := (L w).erase (g x)) (a := g c)
        omega)
    have mk : ∀ γ ∈ ((L w).erase (g x)).erase (g c), ∃ f ∈ ExtSet H S [c, x, a] L g, f w = γ := by
      intro γ hγ
      simp only [Finset.mem_erase] at hγ
      obtain ⟨hγc, hγx, hγL⟩ := hγ
      obtain ⟨δ, hδ⟩ : (((L u).erase (g x)).erase (g a)).erase γ |>.Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.pred_card_le_card_erase (s := L u) (a := g x)
        have := Finset.pred_card_le_card_erase (s := (L u).erase (g x)) (a := g a)
        have := Finset.pred_card_le_card_erase (s := ((L u).erase (g x)).erase (g a)) (a := γ)
        omega
      simp only [Finset.mem_erase] at hδ
      obtain ⟨hδγ, hδa, hδx, hδL⟩ := hδ
      let f : V → C := Function.update (Function.update g w γ) u δ
      have fu : f u = δ := Function.update_self ..
      have fw : f w = γ := by
        simp only [f]; rw [Function.update_of_ne (Ne.symm huw'), Function.update_self]
      have fo : ∀ v, v ≠ u → v ≠ w → f v = g v := fun v h1 h2 => by
        simp only [f]; rw [Function.update_of_ne h1, Function.update_of_ne h2]
      refine ⟨f, ⟨fun v hv => ?_, fun v hv hvn => ?_, fun p hp q hq hpq => ?_⟩, fw⟩
      · have hvu : v ≠ u := by
          rintro rfl; rcases hv with hv | hv
          · exact hv (hS₁S huS₁)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with e | e | e
            · exact huc e
            · exact hux' e
            · exact hua' e
        have hvw : v ≠ w := by
          rintro rfl; rcases hv with hv | hv
          · exact hv (hS₁S hwS₁)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with e | e | e
            · exact hwc e
            · exact hxw' e.symm
            · exact hwa e
        exact fo v hvu hvw
      · rcases hSv v hv with e | e | e | e | e
        · exact absurd (by simp [e]) hvn
        · exact absurd (by simp [e]) hvn
        · rw [e, fu]; exact hδL
        · rw [e, fw]; exact hγL
        · exact absurd (by simp [e]) hvn
      · have fx : f x = g x := fo x (Ne.symm hux') hxw'
        have fa : f a = g a := fo a (Ne.symm hua') (Ne.symm hwa)
        have fc : f c = g c := fo c (Ne.symm huc) (Ne.symm hwc)
        rcases hSv p hp with e | e | e | e | e <;> rcases hSv q hq with e' | e' | e' | e' | e' <;>
          rw [e, e'] at hpq ⊢ <;> simp only [fx, fa, fu, fw, fc] <;>
          first
          | exact absurd hpq (H.loopless.irrefl _)
          | exact absurd hpq hnaw | exact absurd hpq.symm hnaw
          | exact absurd hpq hnuc | exact absurd hpq.symm hnuc
          | exact hh.xa | exact hh.xa.symm | exact hh.xc rfl | exact (hh.xc rfl).symm
          | exact hh.ac rfl hpq | exact (hh.ac rfl hpq.symm).symm
          | exact Ne.symm hδx | exact hδx | exact Ne.symm hδa | exact hδa
          | exact Ne.symm hγx | exact hγx | exact Ne.symm hγc | exact hγc
          | exact hδγ | exact Ne.symm hδγ
    obtain ⟨f₁, hf₁, hf₁w⟩ := mk γ₁ h1
    obtain ⟨f₂, hf₂, hf₂w⟩ := mk γ₂ h2
    have hne12 : f₁ ≠ f₂ := fun e => h12 (hf₁w ▸ hf₂w ▸ congrFun e w)
    exact bound4_of_two (two_le_ncard (extSet_finite H S [c, x, a] L g) hf₁ hf₂ hne12)
      (by omega)
  push Not at hspec
  have key : ∀ β, β ∈ L w → β ≠ g x → β ≠ g c →
      Bound4 (ExtSet H S₁ [w, x, a] L (Function.update g w β)).ncard (nCount S₁ [w, x, a])
        (rCount S₁ [w, x, a] L) ∧
      ExtSet H S₁ [w, x, a] L (Function.update g w β) ⊆ ExtSet H S [c, x, a] L g := by
    intro β hβL hβx hβc
    set gβ := Function.update g w β with hgβ
    have gw : gβ w = β := Function.update_self ..
    have gne : ∀ v, v ≠ w → gβ v = g v := fun v hv => Function.update_of_ne hv ..
    have hlastQw : (Q ++ [w]).getLast? = some w := List.getLast?_concat ..
    have hheadQw : (Q ++ [w]).head? = some a := by rw [List.head?_append_of_ne_nil _ hQ, hhead]
    have h3' : ∀ v ∈ Q ++ [w], v ≠ a → v ≠ w → 3 ≤ (L v).card := by
      intro v hv hva hvw
      have hvQ : v ∈ Q := by simpa [hvw] using hv
      apply hh.three v (by simp [hvQ])
      show v ∉ [c, x, a]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hcQ (e ▸ hvQ), fun e => hxP (by rw [← e]; simp [hvQ]), hva⟩
    have h5' : ∀ v ∈ S₁, v ∉ x :: (Q ++ [w]) → 5 ≤ (L v).card := by
      intro v hv hvc
      exact hh.five v (hS₁S hv) (fun h => hvc (by
        have hvc' : v ≠ c := fun e => hcS₁ (e ▸ hv)
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
        tauto))
    have hh₁ : Thm4Hyp H S₁ x (Q ++ [w]) a w L gβ true := by
      refine ⟨hheadQw, hlastQw, by have := List.length_pos_iff.mpr hQ; simp; omega,
        by rw [gne x hxw', gne a (Ne.symm hwa)]; exact hh.xa,
        fun _ => by rw [gne x hxw', gw]; exact Ne.symm hβx, fun _ h => absurd h hnaw,
        fun v hv hvn => h3' v hv (fun e => hvn (by simp [pcList, e]))
          (fun e => hvn (by simp [pcList, e])), h5'⟩
    have hsub : ExtSet H S₁ [w, x, a] L gβ ⊆ ExtSet H S [c, x, a] L g := by
      rintro f ⟨h1, h2, h3⟩
      have hfw : f w = β := by rw [h1 w (Or.inr (by simp)), gw]
      have hfc : f c = g c := by rw [h1 c (Or.inl hcS₁), gne c (Ne.symm hwc)]
      have hfx : f x = g x := by rw [h1 x (Or.inr (by simp)), gne x hxw']
      refine ⟨fun v hv => ?_, fun v hv hvn => ?_, fun p hp q hq hpq => ?_⟩
      · rcases hv with hv | hv
        · have hv1 : v ∉ S₁ := fun h => hv (hS₁S h)
          rw [h1 v (Or.inl hv1), gne v (fun e => hv (e ▸ hS₁S hwS₁))]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with e | e | e
          · rw [e]; exact hfc
          · rw [e]; exact hfx
          · rw [e, h1 a (Or.inr (by simp)), gne a (Ne.symm hwa)]
      · rcases hS v hv with h | h
        · by_cases hvw : v = w
          · rw [hvw, hfw]; exact hβL
          · exact h2 v h (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn ⊢
              exact ⟨hvw, hvn.2.1, hvn.2.2⟩)
        · exact absurd (by simp [h]) hvn
      · -- edges at `c` go to `x` or `w`
        have hcnb : ∀ z ∈ S, H.Adj c z → z = x ∨ z = w := by
          intro z hz hcz
          rcases hS z hz with h | h
          · rcases hX z h c hcS₂ hcz.symm with h' | h'
            · rcases hmem z h h' with e | e
              · exact Or.inl e
              · exact Or.inr e
            · exact absurd h' hcS₁
          · rw [h] at hcz; exact absurd hcz (H.loopless.irrefl _)
        rcases hS p hp with hp1 | hp1 <;> rcases hS q hq with hq1 | hq1
        · exact h3 p hp1 q hq1 hpq
        · rw [hq1] at hpq ⊢
          rcases hcnb p hp hpq.symm with e | e
          · rw [e, hfx, hfc]; exact hh.xc rfl
          · rw [e, hfw, hfc]; exact hβc
        · rw [hp1] at hpq ⊢
          rcases hcnb q hq hpq with e | e
          · rw [e, hfx, hfc]; exact (hh.xc rfl).symm
          · rw [e, hfw, hfc]; exact Ne.symm hβc
        · rw [hp1, hq1] at hpq; exact absurd hpq (H.loopless.irrefl _)
    refine ⟨?_, hsub⟩
    have hh3 : Thm3Hyp H S₁ x (Q ++ [w]) a w L gβ :=
      ⟨hheadQw, hlastQw, hh₁.two_le, ⟨hh₁.xa, hh₁.xc rfl, fun h => absurd h hnaw⟩, h3', h5'⟩
    have hne₁ : (ExtSet H S₁ [w, x, a] L gβ).Nonempty := by
      rcases T.thm3 H h₁' hh3 with h | h
      · exact extSet_nonempty_iff.mpr h
      · exact absurd h hE
    have := ih H S₁ x (Q ++ [w]) a w L gβ true h₁' hh₁ (by
      left; show nCount S₁ [w, x, a] < nCount S [c, x, a]; omega) hne₁
      (by
        rintro ⟨-, u, hu, hun, h4, huw, hux, hua, -⟩
        exact hspec u hu hun h4 huw hux hua)
    exact this
  have hBset : ∀ β ∈ ((L w).erase (g x)).erase (g c), β ∈ L w ∧ β ≠ g x ∧ β ≠ g c := by
    intro β hβ
    simp only [Finset.mem_erase] at hβ
    exact ⟨hβ.2.2, hβ.2.1, hβ.1⟩
  have hBcard := Finset.pred_card_le_card_erase (s := L w) (a := g x)
  have hBcard' := Finset.pred_card_le_card_erase (s := (L w).erase (g x)) (a := g c)
  by_cases hw3' : (L w).card = 3
  · obtain ⟨β, hβ⟩ : (((L w).erase (g x)).erase (g c)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨hB, hsub⟩ := key β (hBset β hβ).1 (hBset β hβ).2.1 (hBset β hβ).2.2
    have hle := Set.ncard_le_ncard hsub (extSet_finite H S [c, x, a] L g)
    unfold Bound4 at hB ⊢
    rw [hn, hrw3 hw3', pow_succ, pow_succ]
    calc 2 ^ nCount S₁ [w, x, a] * 2 ≤ (ExtSet H S₁ [w, x, a] L (Function.update g w β)).ncard ^ 9
          * 8 ^ rCount S₁ [w, x, a] L * 2 := Nat.mul_le_mul_right _ hB
      _ ≤ (ExtSet H S [c, x, a] L g).ncard ^ 9 * 8 ^ rCount S₁ [w, x, a] L * 8 := by
          apply Nat.mul_le_mul _ (by norm_num)
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle 9)
      _ = _ := by ring
  · obtain ⟨β₁, h1, β₂, h2, h12⟩ := Finset.one_lt_card.mp
      (show 1 < (((L w).erase (g x)).erase (g c)).card by omega)
    obtain ⟨hB1, hsub1⟩ := key β₁ (hBset β₁ h1).1 (hBset β₁ h1).2.1 (hBset β₁ h1).2.2
    obtain ⟨hB2, hsub2⟩ := key β₂ (hBset β₂ h2).1 (hBset β₂ h2).2.1 (hBset β₂ h2).2.2
    set M := minM8 (nCount S₁ [w, x, a]) (rCount S₁ [w, x, a] L)
    have hM1 := minM8_le hB1
    have hM2 := minM8_le hB2
    have hdisj : Disjoint (ExtSet H S₁ [w, x, a] L (Function.update g w β₁))
        (ExtSet H S₁ [w, x, a] L (Function.update g w β₂)) := by
      rw [Set.disjoint_left]
      intro f hf1 hf2
      have e1 := hf1.1 w (Or.inr (by simp))
      have e2 := hf2.1 w (Or.inr (by simp))
      rw [Function.update_self] at e1 e2
      exact h12 (e1.symm.trans e2)
    have hsum : (ExtSet H S₁ [w, x, a] L (Function.update g w β₁)).ncard +
        (ExtSet H S₁ [w, x, a] L (Function.update g w β₂)).ncard ≤
          (ExtSet H S [c, x, a] L g).ncard := by
      rw [← Set.ncard_union_eq hdisj (extSet_finite _ _ _ _ _) (extSet_finite _ _ _ _ _)]
      exact Set.ncard_le_ncard (Set.union_subset hsub1 hsub2) (extSet_finite H S [c, x, a] L g)
    have hspecM := minM8_spec (nCount S₁ [w, x, a]) (rCount S₁ [w, x, a] L)
    unfold Bound4
    rw [hn, hrw4 hw3', pow_succ]
    calc 2 ^ nCount S₁ [w, x, a] * 2 ≤ M ^ 9 * 8 ^ rCount S₁ [w, x, a] L * 2 :=
          Nat.mul_le_mul_right _ hspecM
      _ ≤ (2 * M) ^ 9 * 8 ^ rCount S₁ [w, x, a] L := by
          rw [mul_pow]
          have : 2 ≤ 2 ^ 9 := by norm_num
          calc M ^ 9 * 8 ^ rCount S₁ [w, x, a] L * 2 = 2 * (M ^ 9 * 8 ^ rCount S₁ [w, x, a] L) :=
                by ring
            _ ≤ 2 ^ 9 * (M ^ 9 * 8 ^ rCount S₁ [w, x, a] L) := Nat.mul_le_mul_right _ this
            _ = _ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 9)

end NTCalc

end ThomassenManyColourings
