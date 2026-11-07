/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Claim3
public import ThomassenManyColourings.FanColour

/-!
# Theorem 3, Claim 4: no interior vertex is joined to both `v₂` and `v_k`

By Claim 3 such a vertex `u` is joined to the whole outer path. If `u` is joined to `v₁` the graph
is a wheel: either all inner path vertices have three colours (the exceptional configuration) or
one has four, and deleting it the induction hypothesis applies (the outside cannot contain a
generalized wheel, since the outer path is chordless). If `u` is not joined to `v₁`, the inside of
`v₂ u v_k` is a fan, coloured by `fan_colour`, and the quadrilateral `v₁ v₂ u v_k` by Theorem 2.
(The paper uses separating 4-cycles here; the direct argument avoids them.)
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
theorem getLast?_cons_append_singleton (a c : V) (M : List V) :
    (a :: (M ++ [c])).getLast? = some c := by
  rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; rfl

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 8000000 in
/-- **Claim 4, wheel case.** -/
theorem claim4_wheel (H : SimpleGraph V) {S : Finset V} {x u a c : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: (M ++ [c]))) (hh : Thm3Hyp H S x (a :: (M ++ [c])) a c L g)
    (huS : u ∈ S) (hu : u ∉ x :: a :: (M ++ [c]))
    (huP : ∀ y ∈ a :: (M ++ [c]), H.Adj u y) (hux : H.Adj u x)
    (hPc : ∀ y z, y ∈ a :: (M ++ [c]) → z ∈ a :: (M ++ [c]) → H.Adj y z →
      ConsecIn (a :: (M ++ [c])) y z)
    (hxc : ∀ y ∈ a :: (M ++ [c]), H.Adj x y → y = a ∨ y = c)
    (hN : T.NoSepTri H S (x :: a :: (M ++ [c]))) (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: (M ++ [c])) a c L := by
  classical
  have hlast := getLast?_cons_append_singleton a c M
  have hnd := T.nodup hNT
  have hPnd : (a :: (M ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hch := NT_chain hNT
  have hxa : H.Adj x a := (List.isChain_cons_cons.mp hch).1
  have hpath : (a :: (M ++ [c])).IsChain H.Adj := (List.isChain_cons_cons.mp hch).2
  have hcx : H.Adj c x := by
    have h := List.isChain_append.mp (NT_chain (T.rotate hNT))
    exact h.2.2 c (by rw [hlast]; rfl) x rfl
  have hP2 : 2 ≤ (a :: (M ++ [c])).length := by simp
  have hl : ∀ y ∈ (a :: (M ++ [c])).getLast?, H.Adj x y := by
    rw [hlast]; intro y hy; simp at hy; subst hy; exact hcx.symm
  have hB : Block H 2 x (a :: (M ++ [c])) {u} :=
    Block.wheel hP2 hP2 hpath huP hux (by intro y hy; simp at hy; subst hy; exact hxa) hl
  have hfill := wheel_fill hN _ _ S rfl hNT (Region.refl H S _) hP2 hpath huP hux hl huS hu
  by_cases h3 : ∀ y ∈ M, (L y).card = 3
  · right
    refine ⟨a :: (M ++ [c]), {u}, GW.one hB, hPnd, rfl, hlast, fun y hy => hy, ?_, ?_⟩
    · intro w hw; simp at hw; subst hw; exact ⟨huS, hu⟩
    · intro y hy hya hyc
      apply h3
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy; tauto
  push Not at h3
  obtain ⟨y, hyM, hy3⟩ := h3
  have hyP : y ∈ a :: (M ++ [c]) := by simp [hyM]
  have hnda := List.nodup_cons.mp hPnd
  have hya : y ≠ a := fun h => hnda.1 (by simp [← h, hyM])
  have hyc : y ≠ c := fun h => (List.nodup_append.mp hnda.2).2.2 y hyM c (by simp) h
  have hyx : y ≠ x := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hyP)
  have hyu : y ≠ u := fun h => hu (by simp [← h, hyP])
  have h4y : 4 ≤ (L y).card := by have := hh.three y hyP hya hyc; omega
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hyM
  -- delete `y`
  have hrotY : T.NT H S (y :: (M₂ ++ c :: x :: a :: M₁)) := by
    have := T.rotate_append (A := x :: a :: M₁) (B := y :: (M₂ ++ [c])) (by simpa using hNT)
    simpa using this
  have hlh : (M₂ ++ c :: x :: a :: M₁).head? = (M₂ ++ [c]).head? := by
    rcases M₂ with _ | ⟨w, M₂'⟩ <;> simp
  have hll : (M₂ ++ c :: x :: a :: M₁).getLast? = (a :: M₁).getLast? := by
    rw [show M₂ ++ c :: x :: a :: M₁ = (M₂ ++ [c, x]) ++ (a :: M₁) by simp,
      List.getLast?_append_of_ne_nil _ (by simp)]
  have hPy : a :: (M₁ ++ y :: M₂ ++ [c]) = (a :: M₁) ++ y :: (M₂ ++ [c]) := by simp
  obtain ⟨us, hus, hnb, hNT', -⟩ := T.delete hrotY (by simp; omega) (by
    intro z hz hyz
    simp only [List.mem_append, List.mem_cons] at hz
    by_cases hzx : z = x
    · subst hzx
      rcases hxc y hyP hyz.symm with h | h
      · exact absurd h hya
      · exact absurd h hyc
    have hzP : z ∈ a :: (M₁ ++ y :: M₂ ++ [c]) := by simp; tauto
    have hcons := hPc y z hyP hzP hyz
    rw [hPy] at hcons
    rcases ConsecIn.nbr (by rw [← hPy]; exact hPnd) hcons with h | h
    · right; rw [hll]; exact h
    · left; rw [hlh]; exact h)
  have hus_u : ∀ w ∈ us, w = u := by
    intro w hw
    obtain ⟨hwS, hwn⟩ := hus w hw
    rcases hfill w hwS with h | h | h
    · exact absurd (by simp [h]) hwn
    · exact h
    · exact absurd (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto) hwn
  have hu_us : u ∈ us := by
    rcases hnb u huS (huP y hyP).symm with h | h | h
    · exact absurd (List.mem_of_mem_head? h) (fun h' => hu (by
        simp only [List.mem_append, List.mem_cons] at h' ⊢; tauto))
    · exact absurd (List.mem_of_mem_getLast? h) (fun h' => hu (by
        simp only [List.mem_append, List.mem_cons] at h' ⊢; tauto))
    · exact h
  have hus1 : us = [u] := by
    have hnd' := (List.nodup_append.mp (T.nodup hNT')).2.1
    rcases us with _ | ⟨w, us'⟩
    · simp at hu_us
    · have hw := hus_u w (by simp)
      subst hw
      rcases us' with _ | ⟨w', us''⟩
      · rfl
      · have := hus_u w' (by simp)
        subst this
        simp at hnd'
  rw [hus1] at hNT' hnb
  have hNT'' : T.NT H (S.erase y) (x :: a :: (M₁ ++ u :: (M₂ ++ [c]))) := by
    have := T.rotate_append (A := M₂ ++ [c]) (B := x :: a :: M₁ ++ [u]) (by simpa using hNT')
    simpa using this
  have hcard : (S.erase y).card < S.card :=
    Finset.card_erase_lt_of_mem (T.subset hNT y (by simp))
  have hlast' : (a :: (M₁ ++ u :: (M₂ ++ [c]))).getLast? = some c := by
    rw [show a :: (M₁ ++ u :: (M₂ ++ [c])) = a :: (M₁ ++ u :: M₂ ++ [c]) by simp]
    exact getLast?_cons_append_singleton a c _
  have hh' : Thm3Hyp H (S.erase y) x (a :: (M₁ ++ u :: (M₂ ++ [c]))) a c L g := by
    refine ⟨rfl, hlast', by simp; omega, hh.ok, ?_, ?_⟩
    · intro w hw hwa hwc
      by_cases hwu : w = u
      · rw [hwu]; omega
      · apply hh.three w _ hwa hwc
        simp only [List.mem_cons, List.mem_append] at hw ⊢; tauto
    · intro w hw hwc
      have hwy : w ≠ y := Finset.ne_of_mem_erase hw
      apply hh.five w (Finset.mem_of_mem_erase hw)
      intro h; apply hwc
      simp only [List.mem_cons, List.mem_append] at h ⊢; tauto
  rcases ih H (S.erase y) hcard x _ a c L g hNT'' hh' with hE | hE
  · left
    obtain ⟨f, hfc, hfL, hfp⟩ := hE
    obtain ⟨n₁, hn₁⟩ : ∃ n, (M₂ ++ c :: x :: a :: M₁).head? = some n := by
      rcases M₂ with _ | ⟨w, M₂'⟩ <;> simp
    obtain ⟨n₂, hn₂⟩ : ∃ n, (M₂ ++ c :: x :: a :: M₁).getLast? = some n := by
      rw [hll]; exact ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
    obtain ⟨col, hcol, hcoln⟩ : ∃ col ∈ L y, col ∉ ({f n₁, f n₂, f u} : Finset C) := by
      by_contra hno
      push Not at hno
      have := Finset.card_le_card (show L y ⊆ {f n₁, f n₂, f u} from hno)
      have := Finset.card_le_three (a := f n₁) (b := f n₂) (c := f u)
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcoln
    refine ⟨Function.update f y col, ?_, ?_, ?_⟩
    · intro w hw
      have hwy : w ≠ y := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact Ne.symm hyc
        · exact Ne.symm hyx
        · exact Ne.symm hya
      rw [Function.update_of_ne hwy]; exact hfc w hw
    · intro w hw hwc
      by_cases hwy : w = y
      · subst hwy; rw [Function.update_self]; exact hcol
      · rw [Function.update_of_ne hwy]; exact hfL w (Finset.mem_erase.mpr ⟨hwy, hw⟩) hwc
    · refine isProperOn_update hfp ?_
      intro w hw hyw
      rcases hnb w hw hyw with h | h | h
      · rw [hn₁] at h; cases h; exact fun e => hcoln.1 e.symm
      · rw [hn₂] at h; cases h; exact fun e => hcoln.2.1 e.symm
      · simp at h; subst h; exact fun e => hcoln.2.2 e.symm
  · exfalso
    obtain ⟨P'', U, hGW, hnd'', hh'', hl'', hsub, -, hL⟩ := hE
    have hnu : u ∉ P'' := by
      intro h
      have := hL u h (fun e => hu (by simp [e])) (fun e => hu (by simp [e]))
      omega
    have hsubP : ∀ w ∈ P'', w ∈ a :: (M₁ ++ y :: M₂ ++ [c]) := by
      intro w hw
      have h1 := hsub w hw
      have h2 : w ≠ u := fun e => hnu (e ▸ hw)
      simp only [List.mem_cons, List.mem_append] at h1 ⊢; tauto
    have heq := path_eq_of_chordless _ _ hPnd hnd'' hsubP (by rw [hh'']; rfl)
      (by rw [hl'']; exact (getLast?_cons_append_singleton a c _).symm) hGW.isPath hPc
    have hyP'' : y ∈ P'' := heq ▸ hyP
    have := hsub y hyP''
    have hy1 : y ∉ M₁ := fun h => (List.nodup_append.mp hnda.2).1 |> fun hM =>
      (List.nodup_append.mp hM).2.2 y h y (by simp) rfl
    have hy2 : y ∉ M₂ := by
      have hM := (List.nodup_append.mp hnda.2).1
      exact (List.nodup_cons.mp (List.nodup_append.mp hM).2.1).1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h
    · exact hya h
    · exact hy1 h
    · exact hyu h
    · exact hy2 h
    · exact hyc h

set_option maxHeartbeats 8000000 in
/-- **Claim 4, fan case**: `u` is not joined to `v₁`. -/
theorem claim4_fan (H : SimpleGraph V) {S : Finset V} {x u a c : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: (M ++ [c]))) (hh : Thm3Hyp H S x (a :: (M ++ [c])) a c L g)
    (hM : M ≠ []) (huS : u ∈ S) (hu : u ∉ x :: a :: (M ++ [c]))
    (huP : ∀ y ∈ a :: (M ++ [c]), H.Adj u y) (hux : ¬ H.Adj u x)
    (hPc : ∀ y z, y ∈ a :: (M ++ [c]) → z ∈ a :: (M ++ [c]) → H.Adj y z →
      ConsecIn (a :: (M ++ [c])) y z)
    (hN : T.NoSepTri H S (x :: a :: (M ++ [c]))) :
    Extends H S [c, x, a] L g := by
  classical
  have hnd := T.nodup hNT
  have hPnd : (a :: (M ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hch := NT_chain hNT
  have hpath : (a :: (M ++ [c])).IsChain H.Adj := (List.isChain_cons_cons.mp hch).2
  have hua : H.Adj u a := huP a (by simp)
  have huc : H.Adj u c := huP c (by simp)
  have hrot : T.NT H S (a :: (M ++ c :: [x])) := by simpa using T.rotate hNT
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := a) (y := c) (u := u) (l₁ := M)
    (l₂ := [x]) hrot huS
    (by simp only [List.mem_cons, List.mem_append, not_or] at hu ⊢; tauto) hua huc
    (fun h => ConsecIn.not_ends hM hPnd (hPc a c (by simp) (by simp) h))
  have hInt : T.NT H S₁ (u :: a :: (M ++ [c])) := T.rotate_back (by simpa using h₁)
  have hExt : T.NT H S₂ [x, a, u, c] := by simpa using T.rotate h₂
  have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = a ∨ v = c ∨ v = u := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hS₁ : ∀ v ∈ S₁, v ∈ S := fun v hv => hU ▸ Finset.mem_union_left _ hv
  have hS₂ : ∀ v ∈ S₂, v ∈ S := fun v hv => hU ▸ Finset.mem_union_right _ hv
  have hside : ∀ v ∈ S, v ∉ S₂ → v ∈ S₁ := fun v hv h2 =>
    (Finset.mem_union.mp (hU ▸ hv)).resolve_right h2
  have hnda := List.nodup_cons.mp hPnd
  have hMside : ∀ m ∈ M, m ∉ S₂ := by
    intro m hm h2
    have h1 : m ∈ S₁ := T.subset hInt m (by simp [hm])
    rcases hmem m h1 h2 with rfl | rfl | rfl
    · exact hnda.1 (by simp [hm])
    · exact (List.nodup_append.mp hnda.2).2.2 m hm m (by simp) rfl
    · exact hu (by simp [hm])
  have hRegInt : Region H S (x :: a :: (M ++ [c])) S₁ (u :: a :: (M ++ [c])) := by
    refine (Region.refl H S _).piece (c₂ := [x, a, u, c]) hU ?_ hX ?_
      (fun v hv => T.subset hExt v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢
      tauto
  have hfill := fan_fill hN u _ (a :: (M ++ [c])) S₁ rfl hInt hRegInt hpath huP
  obtain ⟨m₁, R, rfl⟩ := List.exists_cons_of_ne_nil hM
  have hP' : a :: (m₁ :: R ++ [c]) = a :: m₁ :: (R ++ [c]) := by simp
  -- the hub colours
  have h5u : 5 ≤ (L u).card := hh.five u huS hu
  set γs := (L u) \ {g a, g c} with hγsdef
  have hγs : 3 ≤ γs.card := by
    have h1 := Finset.le_card_sdiff ({g a, g c} : Finset C) (L u)
    rw [← hγsdef] at h1
    have h2 := Finset.card_le_two (a := g a) (b := g c)
    omega
  obtain ⟨γ, hγ, f₁, h1u, h1a, h1c, h1L, h1p⟩ := fan_colour H (S₁ := S₁) (u := u) (a := a)
    (c := c) (m₁ := m₁) (R := R)
    (fun w hw => (hfill w hw).imp id (fun h => hP' ▸ h))
    (by rw [← hP']; exact T.nodup hInt)
    (fun y z hy hz hyz => hP' ▸ hPc y z (hP' ▸ hy) (hP' ▸ hz) hyz)
    L g (fun y hy => hh.three y (by simp only [List.mem_cons] at hy ⊢; simp; tauto)
      (fun e => hnda.1 (by subst e; simp only [List.mem_cons] at hy; simp; tauto))
      (fun e => by
        subst e
        rcases List.mem_cons.mp hy with h | h
        · exact (List.nodup_append.mp hnda.2).2.2 y (by simp [h]) y (by simp) rfl
        · exact (List.nodup_append.mp hnda.2).2.2 y (by simp [h]) y (by simp) rfl))
    γs hγs (by simp [hγsdef]) (by simp [hγsdef])
  have hγL : γ ∈ L u := (Finset.mem_sdiff.mp hγ).1
  have hγa : γ ≠ g a := fun e => (Finset.mem_sdiff.mp hγ).2 (by simp [e])
  have hγc : γ ≠ g c := fun e => (Finset.mem_sdiff.mp hγ).2 (by simp [e])
  -- the quadrilateral `x a u c`
  have hxu : x ≠ u := fun e => hu (by simp [e])
  have hau : a ≠ u := fun e => hu (by simp [e])
  have hcu : c ≠ u := fun e => hu (by simp [e])
  let f₀ := Function.update g u γ
  have e_u : f₀ u = γ := Function.update_self ..
  have e_x : f₀ x = g x := Function.update_of_ne hxu ..
  have e_a : f₀ a = g a := Function.update_of_ne hau ..
  have e_c : f₀ c = g c := Function.update_of_ne hcu ..
  have hok := hh.ok
  obtain ⟨f₂, h2c, h2L, h2p⟩ := T.thm2_four H _ S₂ rfl x a u c hExt L f₀
    (by
      intro p hp q hq hpq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        simp only [e_u, e_x, e_a, e_c] <;>
        first
        | exact absurd hpq (H.loopless.irrefl _)
        | exact hok.1 | exact hok.1.symm | exact hok.2.1 | exact hok.2.1.symm
        | exact hγa | exact hγa.symm | exact hγc | exact hγc.symm
        | exact absurd hpq.symm hux | exact absurd hpq hux
        | exact hok.2.2 hpq | exact (hok.2.2 hpq.symm).symm)
    (by
      intro w hw hwc
      apply hh.five w (hS₂ w hw)
      intro h
      have hwM : w ∉ m₁ :: R := fun hm => hMside w hm hw
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h hwc hwM
      tauto)
  have haS₂ : a ∈ S₂ := T.subset hExt a (by simp)
  have hcS₂ : c ∈ S₂ := T.subset hExt c (by simp)
  have hxS₂ : x ∈ S₂ := T.subset hExt x (by simp)
  have huS₂ : u ∈ S₂ := T.subset hExt u (by simp)
  refine ⟨fun w => if w ∈ S₂ then f₂ w else f₁ w, ?_, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [hcS₂, ite_true]; rw [h2c w (by simp), e_c]
    · simp only [hxS₂, ite_true]; rw [h2c w (by simp), e_x]
    · simp only [haS₂, ite_true]; rw [h2c w (by simp), e_a]
  · intro w hw hwc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hwc
    by_cases h2 : w ∈ S₂
    · simp only [h2, ite_true]
      by_cases hwu : w = u
      · subst hwu; rw [h2c w (by simp), e_u]; exact hγL
      · exact h2L w h2 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
    · simp only [h2, ite_false]
      have h1 := hside w hw h2
      rcases hfill w h1 with rfl | h
      · exact absurd huS₂ h2
      · have hwa : w ≠ a := fun e => h2 (e ▸ haS₂)
        have hwc' : w ≠ c := fun e => h2 (e ▸ hcS₂)
        exact h1L w (by
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto)
  · refine isProperOn_glue (S₁ := S₂) (S₂ := S₁) (by rw [Finset.union_comm]; exact hU)
      (fun p hp w hw hpw => (hX w hw p hp hpw.symm).symm) h2p h1p ?_
    intro w h2 h1
    rcases hmem w h1 h2 with rfl | rfl | rfl
    · rw [h1a, h2c w (by simp), e_a]
    · rw [h1c, h2c w (by simp), e_c]
    · rw [h1u, h2c w (by simp), e_u]

/-- **Claim 4**, as a reduction: an interior vertex joined to `v₂` and `v_k` yields the
conclusion of Theorem 3. -/
theorem claim4 (H : SimpleGraph V) {S : Finset V} {x u a c : V} {M : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: (M ++ [c]))) (hh : Thm3Hyp H S x (a :: (M ++ [c])) a c L g)
    (hM : M ≠ []) (huS : u ∈ S) (hu : u ∉ x :: a :: (M ++ [c]))
    (hua : H.Adj u a) (huc : H.Adj u c)
    (hPc : ∀ y z, y ∈ a :: (M ++ [c]) → z ∈ a :: (M ++ [c]) → H.Adj y z →
      ConsecIn (a :: (M ++ [c])) y z)
    (hxc : ∀ y ∈ a :: (M ++ [c]), H.Adj x y → y = a ∨ y = c)
    (hN : T.NoSepTri H S (x :: a :: (M ++ [c]))) (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: (M ++ [c])) a c L := by
  rcases T.claim3 H (P₀ := []) (P₁ := []) (vi := a) (vj := c) hNT hh hM huS hu hua huc hPc hN
    ih with h | h | hall
  · exact Or.inl h
  · exact Or.inr h
  · have huP : ∀ y ∈ a :: (M ++ [c]), H.Adj u y := by
      intro y hy
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | h | rfl
      · exact hua
      · exact hall y h
      · exact huc
    by_cases hux : H.Adj u x
    · exact T.claim4_wheel H hNT hh huS hu huP hux hPc hxc hN ih
    · exact Or.inl (T.claim4_fan H hNT hh hM huS hu huP hux hPc hN)

end NTCalc

end ThomassenManyColourings
