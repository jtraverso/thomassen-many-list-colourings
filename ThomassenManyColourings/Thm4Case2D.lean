/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2C

/-!
# Theorem 4, Case 2: Subcase 2.1 (`v₁` joined to `u_q`)

`u` interior, joined to `x = v₁`, to `v_m`, to every vertex of `M = v_{m+1} … v_{k-1}` (`M ≠ []`) and
to `c`, and to no vertex before `v_m`. Cut off the fan of `u` and the (empty) triangle `u c x`,
colour `u` avoiding `g x, g c` and two colours `α, β` of `L(v_{k-1}) \ {g c}`, and apply
induction to the rest, with precoloured vertices `u, x, a`: `n` drops by `|M| + 1` and `r` by
`|M|`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable {T : NTCalc V}

set_option maxHeartbeats 64000000 in
/-- **Subcase 2.1.** -/
theorem Case1Hyp.case2_xu {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A M : List V} {vm u : V}
    (hP : a :: (Q ++ [c]) = A ++ vm :: (M ++ [c])) (hMne : M ≠ []) (huS : u ∈ S)
    (hu : u ∉ x :: a :: (Q ++ [c])) (hum : H.Adj u vm) (huM : ∀ q ∈ M, H.Adj u q)
    (huc : H.Adj u c) (hux : H.Adj u x) (hmin : ∀ q ∈ A, ¬ H.Adj u q)
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
  have hPnd' : (A ++ vm :: (M ++ [c])).Nodup := hP ▸ hPnd
  have hcQ : c ∉ Q := fun h => (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).2.2 c h c
    (by simp) rfl
  have haQ : a ∉ Q := fun h => (List.nodup_cons.mp hPnd).1 (List.mem_append_left _ h)
  have hxQ : x ∉ Q := fun h => hxP (by simp [h])
  have hPmem : ∀ v, v ∈ a :: (Q ++ [c]) ↔ v ∈ A ∨ v = vm ∨ v ∈ M ∨ v = c := by
    intro v; rw [hP]; simp
  have hinQ : ∀ v ∈ a :: (Q ++ [c]), v ≠ a → v ≠ c → v ∈ Q := by
    intro v hv hva hvc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    tauto
  have hMP : ∀ v ∈ M, v ∈ a :: (Q ++ [c]) := fun v hv => (hPmem v).2 (Or.inr (Or.inr (Or.inl hv)))
  have hMc : ∀ v ∈ M, v ≠ c := by
    intro v hv e
    have h3 := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_append.mp hPnd').2.1).2
    exact h3.2.2 v hv c (by simp) e
  -- `u` is not joined to `a` (no hub), so `vm ≠ a` and `A ≠ []`
  have hua : ¬ H.Adj u a := fun h => hc.nohub u huS hu ⟨huc, hux, h⟩
  have hAne : A ≠ [] := by
    rintro rfl
    simp at hP
    exact hua (hP.1 ▸ hum)
  have haA : A.head? = some a := by
    obtain ⟨a', A', rfl⟩ := List.exists_cons_of_ne_nil hAne
    simp at hP; simp [hP.1]
  have hMa : ∀ v ∈ M, v ≠ a := by
    intro v hv e
    have h2 := List.nodup_append.mp hPnd'
    exact h2.2.2 a (List.mem_of_mem_head? haA) a (by simp [← e, hv]) rfl
  have hMQ : ∀ v ∈ M, v ∈ Q := fun v hv => hinQ v (hMP v hv) (hMa v hv) (hMc v hv)
  have huQ : u ∉ Q := fun h => hu (by simp [h])
  have hAQ : ∀ v ∈ A, v ≠ a → v ∈ Q := fun v hv hva =>
    hinQ v ((hPmem v).2 (Or.inl hv)) hva (fun e => by
      have h2 := List.nodup_append.mp hPnd'
      exact h2.2.2 c (e ▸ hv) c (by simp) rfl)
  have hvmQ : vm ∈ Q := by
    refine hinQ vm ((hPmem vm).2 (Or.inr (Or.inl rfl))) (fun e => ?_) (fun e => ?_)
    · have h2 := List.nodup_append.mp hPnd'
      exact h2.2.2 a (List.mem_of_mem_head? haA) a (by simp [e]) rfl
    · have h3 := List.nodup_cons.mp (List.nodup_append.mp hPnd').2.1
      exact h3.1 (by simp [e])
  -- two colours of the last vertex of `M`, and a colour for `u`
  set w := M.getLast hMne with hw
  have hwM : w ∈ M := List.getLast_mem hMne
  have hw3 : (L w).card = 3 := hc.three w (hMQ w hwM)
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.mp (show 1 < ((L w).erase (g c)).card by
    have := Finset.pred_card_le_card_erase (s := L w) (a := g c); omega)
  rw [Finset.mem_erase] at hα hβ
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  obtain ⟨col, hcol⟩ : ((((L u).erase α).erase β).erase (g c)).erase (g x) |>.Nonempty := by
    apply Finset.card_pos.mp
    have := Finset.pred_card_le_card_erase (s := L u) (a := α)
    have := Finset.pred_card_le_card_erase (s := (L u).erase α) (a := β)
    have := Finset.pred_card_le_card_erase (s := ((L u).erase α).erase β) (a := g c)
    have := Finset.pred_card_le_card_erase (s := (((L u).erase α).erase β).erase (g c))
      (a := g x)
    omega
  simp only [Finset.mem_erase] at hcol
  obtain ⟨hcolx, hcolc, hcolβ, hcolα, hcolL⟩ := hcol
  -- cut off the fan, then the triangle `u c x`
  obtain ⟨S₂, hNT₂, hS₂m, hR₂, hnbM⟩ := hc.fan_cut hP hMne huS hu hum huM huc
  have hNT₂' : T.NT H S₂ (x :: ((A ++ [vm]) ++ u :: [c])) := by simpa using hNT₂
  obtain ⟨S₃, S₄, h₃, h₄, hU₃, hI₃, hX₃⟩ := T.chord hNT₂' (by simp) (by simp) hux.symm
  have h₃' : T.NT H S₃ (x :: (A ++ [vm, u])) := by simpa using h₃
  have h₄' : T.NT H S₄ [u, c, x] := by simpa using h₄
  have hmem₃ : ∀ v, v ∈ S₃ → v ∈ S₄ → v = x ∨ v = u := by
    intro v h1 h2
    have : v ∈ S₃ ∩ S₄ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI₃] at this; simpa using this
  have hR₄ : Region H S (x :: a :: (Q ++ [c])) S₄ [u, c, x] := by
    refine hR₂.piece' (c₁ := x :: (A ++ [vm, u])) hU₃ ?_ hX₃ ?_ (fun v hv => T.subset h₃' v hv)
    · intro v h1 h2; rcases hmem₃ v h1 h2 with rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢
      tauto
  have hR₃ : Region H S (x :: a :: (Q ++ [c])) S₃ (x :: (A ++ [vm, u])) := by
    refine hR₂.piece (c₂ := [u, c, x]) hU₃ ?_ hX₃ ?_ (fun v hv => T.subset h₄' v hv)
    · intro v h1 h2; rcases hmem₃ v h1 h2 with rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢
      tauto
  have hF₄ := hc.nosep S₄ u c x h₄' hR₄
  have hcS₄ : c ∈ S₄ := T.subset h₄' c (by simp)
  have hcS₃ : c ∉ S₃ := by
    intro h; rcases hmem₃ c h hcS₄ with e | e
    · exact hxP (by simp [← e])
    · exact hu (by simp [← e])
  have hS₂ : ∀ v, v ∈ S₂ ↔ v ∈ S₃ ∨ v = c := by
    intro v; constructor
    · intro hv
      rcases Finset.mem_union.mp (hU₃ ▸ hv) with h | h
      · exact Or.inl h
      · rcases hF₄ v h with rfl | rfl | rfl
        · exact Or.inl (T.subset h₃' v (by simp))
        · exact Or.inr rfl
        · exact Or.inl (T.subset h₃' v (by simp))
    · rintro (h | rfl)
      · exact hU₃ ▸ Finset.mem_union_left _ h
      · exact hU₃ ▸ Finset.mem_union_right _ hcS₄
  have hS₃S : ∀ v ∈ S₃, v ∈ S := fun v hv => ((hS₂m v).1 ((hS₂ v).2 (Or.inl hv))).1
  have hS₃M : ∀ v ∈ S₃, v ∉ M := fun v hv => ((hS₂m v).1 ((hS₂ v).2 (Or.inl hv))).2
  -- neighbours of `c`
  have hcnb : ∀ z ∈ S, H.Adj c z → z = x ∨ z = u ∨ z ∈ M := by
    intro z hz hcz
    by_cases hzM : z ∈ M
    · exact Or.inr (Or.inr hzM)
    have hz2 : z ∈ S₂ := (hS₂m z).2 ⟨hz, hzM⟩
    rcases (hS₂ z).1 hz2 with hz3 | rfl
    · rcases hX₃ z hz3 c hcS₄ hcz.symm with h | h
      · rcases hF₄ z h with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact absurd hcz (H.loopless.irrefl _)
        · exact Or.inl rfl
      · exact absurd h hcS₃
    · exact absurd hcz (H.loopless.irrefl _)
  -- the rest, with `u` precoloured
  set g'' := Function.update g u col with hg''
  have g''u : g'' u = col := Function.update_self ..
  have g''ne : ∀ v, v ≠ u → g'' v = g v := fun v hv => Function.update_of_ne hv ..
  have hux' : x ≠ u := fun e => hu (by simp [e])
  have hua' : a ≠ u := fun e => hu (by simp [e])
  have hcu' : c ≠ u := fun e => hu (by simp [e])
  set P'' := A ++ [vm, u] with hP''
  have hhead'' : P''.head? = some a := by
    rw [hP'', List.head?_append_of_ne_nil _ hAne]; exact haA
  have hlast'' : P''.getLast? = some u := by simp [hP'']
  have hh'' : Thm4Hyp H S₃ x P'' a u L g'' true := by
    refine ⟨hhead'', hlast'', ?_, ?_, fun _ => ?_, fun _ h => absurd h.symm hua, ?_, ?_⟩
    · simp only [hP'', List.length_append, List.length_cons, List.length_nil]
      have := List.length_pos_iff.mpr hAne; omega
    · rw [g''ne x hux', g''ne a hua']; exact hh.xa
    · rw [g''ne x hux', g''u]; exact Ne.symm hcolx
    · intro y hy hyn
      change y ∉ [u, x, a] at hyn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn
      have hyQ : y ∈ Q := by
        simp only [hP'', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with hy | hy | hy
        · exact hAQ y hy hyn.2.2
        · rw [hy]; exact hvmQ
        · exact absurd hy hyn.1
      rw [hc.three y hyQ]
    · intro y hy hyn
      exact hh.five y (hS₃S y hy) (hR₃.2 y hy hyn).1
  have hexc'' : ¬ Exc4 H S₃ x a u L g'' true := by
    rintro ⟨-, t, ht, htn, h4, -, htx, -, -⟩
    by_cases htQ : t ∈ Q
    · exact hc.xfree t htQ htx.symm
    · have := hh.five t (hS₃S t ht) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htn
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
        refine ⟨htn.2.1, htn.2.2, htQ, fun e => hcS₃ (e ▸ ht)⟩)
      omega
  -- counts
  have hMnd : M.Nodup := (List.nodup_append.mp (List.nodup_cons.mp
    (List.nodup_append.mp hPnd').2.1).2).1
  have huM : u ∉ M := fun h => huQ (hMQ u h)
  have huS₃ : u ∈ S₃ := T.subset h₃' u (by simp [hP''])
  have hn : nCount S [c, x, a] = nCount S₃ [u, x, a] + 1 + M.length := by
    unfold nCount
    have hu' : u ∉ S₃.filter (· ∉ [u, x, a]) := by simp
    rw [← Finset.card_insert_of_notMem hu', ← List.toFinset_card_of_nodup hMnd,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      constructor
      · rintro ⟨hv, hvc, hvx, hva⟩
        by_cases hvM : v ∈ M
        · exact Or.inr hvM
        · rcases (hS₂ v).1 ((hS₂m v).2 ⟨hv, hvM⟩) with h | h
          · by_cases hvu : v = u
            · exact Or.inl (Or.inl hvu)
            · exact Or.inl (Or.inr ⟨h, hvu, hvx, hva⟩)
          · exact absurd h hvc
      · rintro ((rfl | ⟨hv, hvu, hvx, hva⟩) | hvM)
        · exact ⟨huS, fun e => hcu' e.symm, fun e => hux' e.symm, fun e => hua' e.symm⟩
        · exact ⟨hS₃S v hv, fun e => hcS₃ (e ▸ hv), hvx, hva⟩
        · exact ⟨T.subset hc.nt v (List.mem_cons_of_mem _ (hMP v hvM)), hMc v hvM,
            fun e => hxQ (e ▸ hMQ v hvM), hMa v hvM⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      rw [List.mem_toFinset] at h2
      rcases Finset.mem_insert.mp h1 with rfl | h1
      · exact huM h2
      · exact hS₃M v (Finset.mem_filter.mp h1).1 h2
  have hrQ : Q.length ≤ rCount S [c, x, a] L := by
    unfold rCount
    rw [← List.toFinset_card_of_nodup (List.nodup_append.mp (List.nodup_cons.mp hPnd).2).1]
    apply Finset.card_le_card
    intro v hv
    rw [List.mem_toFinset] at hv
    simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨T.subset hc.nt v (by simp [hv]), ⟨fun e => hcQ (e ▸ hv), fun e => hxQ (e ▸ hv),
      fun e => haQ (e ▸ hv)⟩, hc.three v hv⟩
  have hr : rCount S₃ [u, x, a] L + M.length ≤ rCount S [c, x, a] L := by
    unfold rCount
    rw [← List.toFinset_card_of_nodup hMnd, ← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_union, Finset.mem_filter, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hv ⊢
      rcases hv with ⟨hv, ⟨hvu, hvx, hva⟩, h3⟩ | hvM
      · exact ⟨hS₃S v hv, ⟨fun e => hcS₃ (e ▸ hv), hvx, hva⟩, h3⟩
      · exact ⟨T.subset hc.nt v (List.mem_cons_of_mem _ (hMP v hvM)),
          ⟨hMc v hvM, fun e => hxQ (e ▸ hMQ v hvM), hMa v hvM⟩, hc.three v (hMQ v hvM)⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      exact hS₃M v (Finset.mem_filter.mp h1).1 (List.mem_toFinset.mp h2)
  have hlenA : A.length + M.length = Q.length := by
    have := congrArg List.length hP; simp at this; omega
  have hxP'' : x ∉ P'' := (List.nodup_cons.mp (T.nodup h₃')).1
  rcases T.thm3 H h₃' ⟨hh''.head, hh''.last, hh''.two_le, ⟨hh''.xa, hh''.xc rfl, hh''.ac rfl⟩,
      fun y hy hya hyc => hh''.three y hy (by
        show y ∉ [u, x, a]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hyc, fun e => hxP'' (e ▸ hy), hya⟩), hh''.five⟩ with hext | hE3
  swap
  · -- the exception: a generalized wheel on the whole outer path
    obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, -⟩ := hE3
    have hconsec : ∀ (B D : List V) (y z : V), ConsecIn (B ++ y :: z :: D) y z := by
      intro B D y z
      exact ConsecIn.append_left (Or.inl ⟨rfl, rfl⟩)
    have hPc'' : ∀ y z, y ∈ P'' → z ∈ P'' → H.Adj y z → ConsecIn P'' y z := by
      have key : ∀ y z, y ∈ P'' → z ∈ P'' → y ≠ u → z ≠ u → H.Adj y z → ConsecIn P'' y z := by
        intro y z hy hz hyu hzu hyz
        have hy' : y ∈ A ++ [vm] := by
          simp only [hP'', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
          tauto
        have hz' : z ∈ A ++ [vm] := by
          simp only [hP'', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          tauto
        have hyP : y ∈ a :: (Q ++ [c]) := by
          rw [hPmem]; simp only [List.mem_append, List.mem_singleton] at hy'; tauto
        have hzP : z ∈ a :: (Q ++ [c]) := by
          rw [hPmem]; simp only [List.mem_append, List.mem_singleton] at hz'; tauto
        have hcons := hc.chordless y z hyP hzP hyz
        rw [hP] at hcons
        have h1 := ConsecIn.infix (A := []) (Q := A ++ [vm]) (B := M ++ [c])
          (by simpa using hPnd') hy' hz' (by simpa using hcons)
        rw [hP'', show A ++ [vm, u] = (A ++ [vm]) ++ [u] by simp]
        exact ConsecIn.append_right h1
      intro y z hy hz hyz
      by_cases hyu : y = u
      · subst hyu
        have hz' : z ∈ A ∨ z = vm := by
          simp only [hP'', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with hz | hz | hz
          · exact Or.inl hz
          · exact Or.inr hz
          · rw [hz] at hyz; exact absurd hyz (H.loopless.irrefl _)
        rcases hz' with hz' | rfl
        · exact absurd hyz (hmin z hz')
        · rw [hP'']; exact (hconsec A [] z y).symm
      · by_cases hzu : z = u
        · subst hzu
          have hy' : y ∈ A ∨ y = vm := by
            simp only [hP'', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with hy | hy | hy
            · exact Or.inl hy
            · exact Or.inr hy
            · exact absurd hy hyu
          rcases hy' with hy' | rfl
          · exact absurd hyz.symm (hmin y hy')
          · rw [hP'']; exact hconsec A [] y z
        · exact key y z hy hz hyu hzu hyz
    have hP''nd : P''.Nodup := (List.nodup_cons.mp (T.nodup h₃')).2
    have hPW : PW = P'' := path_eq_of_chordless _ _ hP''nd hndW hsubW (by rw [hhW, hhead''])
      (by rw [hlW, hlast'']) hGW.isPath hPc''
    subst hPW
    obtain ⟨hfill, hG3⟩ := gw_fill hc.nosep hGW h₃' hR₃ hUW
    have hcU := hG3.card_add_two_le
    have hPl : P''.length = A.length + 2 := by simp [hP'']
    have hnle : nCount S [c, x, a] ≤ Q.length + 1 + U.card := by
      unfold nCount
      calc (S.filter (· ∉ [c, x, a])).card ≤ (Q.toFinset ∪ insert u U).card := by
            apply Finset.card_le_card
            intro v hv
            simp only [Finset.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
              not_or] at hv
            simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert]
            by_cases hvM : v ∈ M
            · exact Or.inl (hMQ v hvM)
            · rcases (hS₂ v).1 ((hS₂m v).2 ⟨hv.1, hvM⟩) with hv3 | hvc
              · rcases hfill v hv3 with h | h | h
                · exact absurd h hv.2.2.1
                · simp only [hP'', List.mem_append, List.mem_cons, List.not_mem_nil,
                    or_false] at h
                  rcases h with h | h | h
                  · exact Or.inl (hAQ v h hv.2.2.2)
                  · rw [h]; exact Or.inl hvmQ
                  · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
              · exact absurd hvc hv.2.1
        _ ≤ Q.toFinset.card + (insert u U).card := Finset.card_union_le _ _
        _ ≤ Q.length + (U.card + 1) :=
            Nat.add_le_add (List.toFinset_card_le Q) (Finset.card_insert_le _ _)
        _ = Q.length + 1 + U.card := by ring
    have := List.length_pos_iff.mpr hMne
    exact bound4_of_le (ncard_extSet_pos hne) (by omega)
  -- induction on the rest
  have hne'' : (ExtSet H S₃ [u, x, a] L g'').Nonempty := extSet_nonempty_iff.mpr hext
  have hB := ih H S₃ x P'' a u L g'' true h₃' hh''
    (Or.inl (by show nCount S₃ [u, x, a] < nCount S [c, x, a]; omega)) hne'' hexc''
  change Bound4 (ExtSet H S₃ [u, x, a] L g'').ncard (nCount S₃ [u, x, a])
    (rCount S₃ [u, x, a] L) at hB
  -- every colouring of the rest extends
  have hMdec : M = M.dropLast ++ [w] := (List.dropLast_append_getLast hMne).symm
  have hextend : ∀ φ ∈ ExtSet H S₃ [u, x, a] L g'', ∃ f ∈ ExtSet H S [c, x, a] L g,
      ∀ v ∈ S₃, f v = φ v := by
    intro φ hφ
    obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
    have hφu : φ u = col := by rw [hφ1 u (Or.inr (by simp)), g''u]
    have hφc : φ c = g c := by rw [hφ1 c (Or.inl hcS₃), g''ne c hcu']
    have hφx : φ x = g x := by rw [hφ1 x (Or.inr (by simp)), g''ne x hux']
    have hφa : φ a = g a := by rw [hφ1 a (Or.inr (by simp)), g''ne a hua']
    have hcolF : ColFrom (φ u) (φ vm) (M.map L) (φ c) := by
      rw [hMdec, List.map_append, List.map_singleton, hφc, hφu]
      refine colFrom_two_last (fun Lm hLm => ?_) hα.2 hβ.2 hαβ hα.1 hβ.1
        (fun e => hcolα e.symm) (fun e => hcolβ e.symm)
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hLm
      rw [hc.three m (hMQ m (List.mem_of_mem_dropLast hm))]
    obtain ⟨f, hf1, hf2, hf3⟩ := hc.fan_extend hP hu hnbM φ hcolF
    refine ⟨f, ⟨fun v hv => ?_, fun v hv hvn => ?_, fun p hp q hq hpq => ?_⟩,
      fun v hv => hf1 v (hS₃M v hv)⟩
    · have hvM : v ∉ M := by
        intro h
        rcases hv with hv | hv
        · exact hv (T.subset hc.nt v (List.mem_cons_of_mem _ (hMP v h)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with e | e | e
          · exact hMc v h e
          · exact hxQ (e ▸ hMQ v h)
          · exact hMa v h e
      rw [hf1 v hvM]
      rcases hv with hv | hv
      · have hvu : v ≠ u := fun e => hv (e ▸ huS)
        rw [hφ1 v (Or.inl (fun h => hv (hS₃S v h))), g''ne v hvu]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact hφc
        · exact hφx
        · exact hφa
    · by_cases hvM : v ∈ M
      · exact hf2 v hvM
      rw [hf1 v hvM]
      by_cases hvu : v = u
      · rw [hvu, hφu]; exact hcolL
      rcases (hS₂ v).1 ((hS₂m v).2 ⟨hv, hvM⟩) with hv3 | hvc
      · exact hφ2 v hv3 (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn ⊢
          exact ⟨hvu, hvn.2.1, hvn.2.2⟩)
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hvn
        exact absurd hvc hvn.1
    · by_cases hpM : p ∈ M
      · exact hf3 p hpM q hq hpq
      by_cases hqM : q ∈ M
      · exact (hf3 q hqM p hp hpq.symm).symm
      rw [hf1 p hpM, hf1 q hqM]
      have hcvals : ∀ z ∈ S, H.Adj c z → z ∉ M → φ c ≠ φ z := by
        intro z hz hcz hzM
        rcases hcnb z hz hcz with rfl | rfl | h
        · rw [hφc, hφx]; exact Ne.symm (hh.xc rfl)
        · rw [hφc, hφu]; exact Ne.symm hcolc
        · exact absurd h hzM
      rcases (hS₂ p).1 ((hS₂m p).2 ⟨hp, hpM⟩) with hp3 | rfl
      · rcases (hS₂ q).1 ((hS₂m q).2 ⟨hq, hqM⟩) with hq3 | rfl
        · exact hφ3 p hp3 q hq3 hpq
        · exact (hcvals p hp hpq.symm hpM).symm
      · exact hcvals q hq hpq hqM
  -- counting
  choose! ext hext1 hext2 using hextend
  have hN : (ExtSet H S₃ [u, x, a] L g'').ncard ≤ (ExtSet H S [c, x, a] L g).ncard := by
    refine Set.ncard_le_ncard_of_injOn ext (fun φ hφ => hext1 φ hφ) ?_
      (extSet_finite H S [c, x, a] L g)
    intro φ hφ φ' hφ' he
    funext v
    by_cases hv : v ∈ S₃
    · rw [← hext2 φ hφ v hv, ← hext2 φ' hφ' v hv, he]
    · rw [hφ.1 v (Or.inl hv), hφ'.1 v (Or.inl hv)]
  have := List.length_pos_iff.mpr hMne
  exact bound4_gain hB hN (by omega)

end NTCalc

end ThomassenManyColourings
