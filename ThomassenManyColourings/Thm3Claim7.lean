/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm3Claim5
public import ThomassenManyColourings.GWInner

/-!
# Theorem 3, Claim 7: `v₃` and `v_{k-1}` have a common interior neighbour

Suppose not. Delete `v₃` and two colours of `L(v₃) ∖ {c(v₂)}` from the lists of its interior
neighbours `u₁, …, u_q`; a colouring of `G − v₃` extends to `v₃`. Otherwise `G − v₃` contains a
generalized wheel `W` on its outer path. If some `u_i` is joined to `v_k`, Claim 3 joins it to
`v_{k-1}` too. Otherwise the last three vertices of the path of `W` are `v_{k-2}, v_{k-1}, v_k`
(no chords, no common neighbour), so a wheel centre `z` is joined to them; cutting along
`v_{k-2} z v_k` and the chord `z v_{k-1}` leaves two triangles, which are faces (no separating
triangles), so `v_{k-1}` has degree three and Claim 6 applies. (This replaces the paper's
"a generalized wheel does not have that property".)
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 16000000 in
/-- **Claim 7**, as a reduction: if no interior vertex is joined to both `v₃` and `v_{k-1}`, the
conclusion of Theorem 3 holds. -/
theorem claim7 (H : SimpleGraph V) {S : Finset V} {x a v₃ w₄ w₃ c : V} {R : List V}
    {L : V → Finset C} {g : V → C}
    (hNT : T.NT H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])))
    (hh : Thm3Hyp H S x (a :: v₃ :: (R ++ [w₄, w₃, c])) a c L g)
    (hPc : ∀ y z, y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) → z ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) →
      H.Adj y z → ConsecIn (a :: v₃ :: (R ++ [w₄, w₃, c])) y z)
    (hxc : ∀ y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]), H.Adj x y → y = a ∨ y = c)
    (hno : ∀ z ∈ S, z ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]) → H.Adj z v₃ → ¬ H.Adj z w₃)
    (hN : T.NoSepTri H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])))
    (ih : T.Thm3Below S.card C) :
    Extends H S [c, x, a] L g ∨ Exc3 H S x (a :: v₃ :: (R ++ [w₄, w₃, c])) a c L := by
  classical
  have hnd := T.nodup hNT
  have hPnd : (a :: v₃ :: (R ++ [w₄, w₃, c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: v₃ :: (R ++ [w₄, w₃, c]) := (List.nodup_cons.mp hnd).1
  have hav₃ : a ≠ v₃ := by rintro rfl; simp at hPnd
  have hv₃c : v₃ ≠ c := by rintro rfl; simp at hPnd
  have haw₃ : a ≠ w₃ := by rintro rfl; simp at hPnd
  have hac : a ≠ c := by rintro rfl; simp at hPnd
  have hw₃c : w₃ ≠ c := by
    intro e
    have := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp hPnd).2).2).2.1
    rw [e] at this; simp at this
  have hv₃P : v₃ ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by simp
  -- delete `v₃`
  have hrot : T.NT H S (v₃ :: (R ++ [w₄, w₃, c, x, a])) := by
    have := T.rotate_append (A := [x, a]) (B := v₃ :: (R ++ [w₄, w₃, c])) (by simpa using hNT)
    simpa using this
  have hlastl : (R ++ [w₄, w₃, c, x, a]).getLast? = some a := by
    rw [show R ++ [w₄, w₃, c, x, a] = (R ++ [w₄, w₃, c, x]) ++ [a] by simp]
    exact List.getLast?_concat ..
  have hheadl : (R ++ [w₄, w₃, c, x, a]).head? = (R ++ [w₄, w₃, c]).head? := by
    rcases R with _ | ⟨r, R'⟩ <;> simp
  obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp) (by
    intro z hz hv₃z
    by_cases hzx : z = x
    · rw [hzx] at hv₃z
      rcases hxc v₃ hv₃P hv₃z.symm with h | h
      · exact absurd h hav₃.symm
      · exact absurd h hv₃c
    · have hzP : z ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz ⊢; tauto
      rcases ConsecIn.nbr (A := [a]) (B := R ++ [w₄, w₃, c]) hPnd (hPc v₃ z hv₃P hzP hv₃z)
        with h | h
      · simp only [List.getLast?_singleton, Option.some.injEq] at h
        right; rw [hlastl, h]
      · left; rw [hheadl]; exact h)
  have hcyc : ∀ w, w ∉ v₃ :: (R ++ [w₄, w₃, c, x, a]) →
      w ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]) := by
    intro w hw h; apply hw
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  have hv₃S : v₃ ∈ S := T.subset hNT v₃ (by simp)
  -- lists without two colours of `L(v₃) ∖ {c(v₂)}` at the interior neighbours of `v₃`
  have h3v₃ : 3 ≤ (L v₃).card := hh.three v₃ hv₃P (Ne.symm hav₃) hv₃c
  obtain ⟨α₁, hα₁, α₂, hα₂, hα₁₂⟩ := Finset.one_lt_card.mp
    (show 1 < ((L v₃).erase (g a)).card by
      have := Finset.pred_card_le_card_erase (s := L v₃) (a := g a); omega)
  let L' : V → Finset C := fun z => if z ∈ us then ((L z).erase α₁).erase α₂ else L z
  have hL'in : ∀ z ∈ us, L' z = ((L z).erase α₁).erase α₂ := fun z hz => by simp [L', hz]
  have hL'out : ∀ z, z ∉ us → L' z = L z := fun z hz => by simp [L', hz]
  have hus3 : ∀ z ∈ us, 3 ≤ (L' z).card := by
    intro z hz
    rw [hL'in z hz]
    have h5 := hh.five z (hus z hz).1 (hcyc z (hus z hz).2)
    have := Finset.pred_card_le_card_erase (s := L z) (a := α₁)
    have := Finset.pred_card_le_card_erase (s := (L z).erase α₁) (a := α₂); omega
  have hG' : T.NT H (S.erase v₃) (x :: a :: (us ++ (R ++ [w₄, w₃, c]))) := by
    have := T.rotate_append (A := R ++ [w₄, w₃, c]) (B := x :: a :: us) (by simpa using hNT')
    simpa using this
  have hlast' : (a :: (us ++ (R ++ [w₄, w₃, c]))).getLast? = some c := by
    rw [show a :: (us ++ (R ++ [w₄, w₃, c])) = a :: ((us ++ R ++ [w₄, w₃]) ++ [c]) by simp]
    exact getLast?_cons_append_singleton a c _
  have hcl : ∀ y ∈ a :: (us ++ (R ++ [w₄, w₃, c])), y ∈ us ∨ y ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by
    intro y hy
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢; tauto
  have hh' : Thm3Hyp H (S.erase v₃) x (a :: (us ++ (R ++ [w₄, w₃, c]))) a c L' g := by
    refine ⟨rfl, hlast', by simp; omega, hh.ok, ?_, ?_⟩
    · intro y hy hya hyc
      by_cases hyu : y ∈ us
      · exact hus3 y hyu
      · rw [hL'out y hyu]
        rcases hcl y hy with h | h
        · exact absurd h hyu
        · exact hh.three y h hya hyc
    · intro y hy hyc
      have hyu : y ∉ us := fun h => hyc (by simp [h])
      rw [hL'out y hyu]
      have hyv : y ≠ v₃ := Finset.ne_of_mem_erase hy
      apply hh.five y (Finset.mem_of_mem_erase hy)
      intro h; apply hyc
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  have hcard : (S.erase v₃).card < S.card := Finset.card_erase_lt_of_mem hv₃S
  rcases ih H (S.erase v₃) hcard x _ a c L' g hG' hh' with hE | hE
  · -- a colouring of `G − v₃` extends to `v₃`
    left
    obtain ⟨f, hfc, hfL, hfp⟩ := hE
    obtain ⟨v₄, hv₄⟩ : ∃ v₄, (R ++ [w₄, w₃, c, x, a]).head? = some v₄ := by
      rcases R with _ | ⟨r, R'⟩ <;> exact ⟨_, rfl⟩
    have hfa : f a = g a := hfc a (by simp)
    have hfu : ∀ z ∈ us, f z ≠ α₁ ∧ f z ≠ α₂ := by
      intro z hz
      have hzn := hcyc z (hus z hz).2
      have h := hfL z (Finset.mem_erase.mpr ⟨fun e => (hus z hz).2 (by simp [e]), (hus z hz).1⟩)
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun e => hzn (by simp [e]), fun e => hzn (by simp [e]),
            fun e => hzn (by simp [e])⟩)
      rw [hL'in z hz] at h
      exact ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
    obtain ⟨col, hcolL, hcola, hcolv₄, hcolu⟩ : ∃ col, col ∈ L v₃ ∧ col ≠ g a ∧ col ≠ f v₄ ∧
        ∀ z ∈ us, f z ≠ col := by
      by_cases h : α₁ = f v₄
      · exact ⟨α₂, Finset.mem_of_mem_erase hα₂, Finset.ne_of_mem_erase hα₂,
          fun e => hα₁₂ (h.trans e.symm), fun z hz e => (hfu z hz).2 e⟩
      · exact ⟨α₁, Finset.mem_of_mem_erase hα₁, Finset.ne_of_mem_erase hα₁, h,
          fun z hz e => (hfu z hz).1 e⟩
    refine ⟨Function.update f v₃ col, ?_, ?_, isProperOn_update hfp ?_⟩
    · intro z hz
      have hzv : z ≠ v₃ := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h | h <;> rw [h]
        · exact hv₃c.symm
        · exact fun e => hxP (e ▸ hv₃P)
        · exact hav₃
      rw [Function.update_of_ne hzv]; exact hfc z hz
    · intro z hz hzc
      by_cases hzv : z = v₃
      · rw [hzv, Function.update_self]; exact hcolL
      · rw [Function.update_of_ne hzv]
        have h := hfL z (Finset.mem_erase.mpr ⟨hzv, hz⟩) hzc
        by_cases hzu : z ∈ us
        · rw [hL'in z hzu] at h
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
        · rwa [hL'out z hzu] at h
    · intro w hw hvw
      rcases hnb w hw hvw with h | h | h
      · rw [hv₄] at h; simp only [Option.some.injEq] at h; rw [← h]; exact Ne.symm hcolv₄
      · rw [hlastl] at h; simp only [Option.some.injEq] at h; rw [← h, hfa]; exact Ne.symm hcola
      · exact hcolu w h
  -- `G − v₃` is exceptional
  by_cases hyc : ∃ y ∈ us, H.Adj y c
  · -- an interior neighbour of `v₃` joined to `v_k` is joined to `v_{k-1}` (Claim 3)
    obtain ⟨y, hyus, hyc'⟩ := hyc
    have hyS := (hus y hyus).1
    have hyn := hcyc y (hus y hyus).2
    have hnoy := hno y hyS hyn (hadj y hyus).symm
    have e : a :: v₃ :: (R ++ [w₄, w₃, c]) = [a] ++ v₃ :: ((R ++ [w₄, w₃]) ++ c :: []) := by
      simp
    have hPnd' := hPnd
    rw [e] at hNT hh hPc hxc hN hyn hPnd' ⊢
    rcases T.claim3 H (P₀ := [a]) (vi := v₃) (M := R ++ [w₄, w₃]) (vj := c) (P₁ := []) hNT hh
      (by simp) hyS hyn (hadj y hyus).symm hyc'
      (by
        intro p q hp hq hpq
        have h := hPc p q (List.mem_append_right _ hp) (List.mem_append_right _ hq) hpq
        exact ConsecIn.of_append_left hPnd' hp hq h)
      hN ih with h | h | hall
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hall w₃ (by simp)) hnoy
  push Not at hyc
  obtain ⟨PW, U, hGW, hndW, hhW, hlW, hsubW, hUW, -⟩ := hE
  have hcP : c ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by simp
  have hw₃P : w₃ ∈ a :: v₃ :: (R ++ [w₄, w₃, c]) := by simp
  -- the neighbours of `v_k` and `v_{k-1}` on the new outer path
  have A1 : ∀ y ∈ PW, H.Adj y c → y = w₃ := by
    intro y hy hyc'
    rcases hcl y (hsubW y hy) with h | h
    · exact absurd hyc' (hyc y h)
    · have e2 : a :: v₃ :: (R ++ [w₄, w₃, c]) = (a :: v₃ :: (R ++ [w₄, w₃])) ++ c :: [] := by
        simp
      have h' := (hPc y c h hcP hyc').symm
      rw [e2] at h'
      rcases ConsecIn.nbr (by rw [← e2]; exact hPnd) h' with h1 | h1
      · rw [show a :: v₃ :: (R ++ [w₄, w₃]) = (a :: v₃ :: (R ++ [w₄])) ++ [w₃] by simp,
          List.getLast?_concat] at h1
        simp only [Option.some.injEq] at h1; exact h1.symm
      · simp at h1
  have A2 : ∀ y ∈ PW, H.Adj y w₃ → y = w₄ ∨ y = c := by
    intro y hy hyw
    rcases hcl y (hsubW y hy) with h | h
    · exact absurd hyw (hno y (hus y h).1 (hcyc y (hus y h).2) (hadj y h).symm)
    · have e2 : a :: v₃ :: (R ++ [w₄, w₃, c]) = (a :: v₃ :: (R ++ [w₄])) ++ w₃ :: [c] := by
        simp
      have h' := (hPc y w₃ h hw₃P hyw).symm
      rw [e2] at h'
      rcases ConsecIn.nbr (by rw [← e2]; exact hPnd) h' with h1 | h1
      · rw [show a :: v₃ :: (R ++ [w₄]) = (a :: v₃ :: R) ++ [w₄] by simp,
          List.getLast?_concat] at h1
        simp only [Option.some.injEq] at h1; exact Or.inl h1.symm
      · simp only [List.head?_cons, Option.some.injEq] at h1; exact Or.inr h1.symm
  have hch := hGW.isPath
  -- the path of the wheel ends with `v_{k-2} v_{k-1} v_k`
  obtain ⟨R3, hR3⟩ : ∃ R3, PW = R3 ++ [w₄, w₃, c] := by
    rcases PW.eq_nil_or_concat with h | ⟨P1, t, h⟩
    · subst h; simp at hhW
    rw [List.concat_eq_append] at h
    have ht : t = c := by rw [h, List.getLast?_concat] at hlW; simpa using hlW
    subst ht
    rcases P1.eq_nil_or_concat with h1 | ⟨P2, y, h1⟩
    · subst h1; rw [h] at hhW; simp at hhW; exact absurd hhW.symm hac
    rw [List.concat_eq_append] at h1
    subst h1
    have hyc' : H.Adj y t := by
      rw [h] at hch
      exact (List.isChain_append.mp hch).2.2 y (by simp) t rfl
    have hyw : y = w₃ := A1 y (by rw [h]; simp) hyc'
    subst hyw
    rcases P2.eq_nil_or_concat with h2 | ⟨P3, z, h2⟩
    · subst h2; rw [h] at hhW; simp at hhW; exact absurd hhW.symm haw₃
    rw [List.concat_eq_append] at h2
    subst h2
    have hzy : H.Adj z y := by
      rw [h] at hch
      have := (List.isChain_append.mp hch).1
      exact (List.isChain_append.mp this).2.2 z (by simp) y rfl
    rcases A2 z (by rw [h]; simp) hzy with hz | hz
    · subst hz; exact ⟨P3, by rw [h]; simp⟩
    · subst hz; rw [h] at hndW
      exact absurd rfl ((List.nodup_append.mp hndW).2.2 z (by simp) z (by simp))
  have hC3 : Consec3 PW w₄ w₃ c := hR3 ▸ Consec3.of_append R3 w₄ w₃ c
  have hxw₃ : ¬ H.Adj x w₃ := fun h => by
    rcases hxc w₃ hw₃P h with e | e
    · exact haw₃ e.symm
    · exact hw₃c e
  obtain ⟨z0, hz0U, hz0w₄, hz0w₃, hz0c, -⟩ := hGW.centre_of_inner hC3 hxw₃
  have hz0S : z0 ∈ S := Finset.mem_of_mem_erase (hUW z0 hz0U).1
  have hz0v : z0 ≠ v₃ := Finset.ne_of_mem_erase (hUW z0 hz0U).1
  have hz0n : z0 ∉ x :: a :: v₃ :: (R ++ [w₄, w₃, c]) := by
    intro h; apply (hUW z0 hz0U).2
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto
  -- `v_{k-1}` has degree three: cut along `v_{k-2} z0 v_k`, then along `z0 v_{k-1}`
  have hrot4 : T.NT H S (w₄ :: ([w₃] ++ c :: (x :: a :: v₃ :: R))) := by
    have := T.rotate_append (A := x :: a :: v₃ :: R) (B := [w₄, w₃, c]) (by simpa using hNT)
    simpa using this
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := w₄) (y := c) (u := z0) (l₁ := [w₃])
    (l₂ := x :: a :: v₃ :: R) hrot4 hz0S
    (by
      intro h; apply hz0n
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢; tauto)
    hz0w₄ hz0c (fun h => ConsecIn.not_gap (A := a :: v₃ :: R) (M := [w₃]) (B := []) (by simp)
      (by simpa using hPnd) (by simpa using hPc w₄ c (by simp) (by simp) h))
  have hmem1 : ∀ v, v ∈ S₁ → v ∈ S₂ → v = w₄ ∨ v = c ∨ v = z0 := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hR1 : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) S₁ [w₄, w₃, c, z0] := by
    refine (Region.refl H S _).piece (c₂ := c :: (x :: a :: v₃ :: R ++ [w₄, z0])) hU ?_ hX ?_
      (fun v hv => T.subset h₂ v hv)
    · intro v h1 h2; rcases hmem1 v h1 h2 with e | e | e <;> simp [e]
    · intro v hv
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hS1r : T.NT H S₁ (z0 :: ([w₄] ++ w₃ :: [c])) := T.rotate_back (by simpa using h₁)
  obtain ⟨T₁, T₂, ht₁, ht₂, hUT, hIT, hXT⟩ := T.chord hS1r (by simp) (by simp) hz0w₃
  have hmemT : ∀ v, v ∈ T₁ → v ∈ T₂ → v = z0 ∨ v = w₃ := by
    intro v h1 h2
    have : v ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hIT] at this; simpa using this
  have hRT₁ : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) T₁ [z0, w₄, w₃] := by
    refine hR1.piece (c₂ := [w₃, c, z0]) hUT ?_ hXT ?_ (fun v hv => T.subset ht₂ v (by simpa using hv))
    · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hRT₂ : Region H S (x :: a :: v₃ :: (R ++ [w₄, w₃, c])) T₂ [w₃, c, z0] := by
    refine hR1.piece' (c₁ := [z0, w₄, w₃]) hUT ?_ hXT ?_ (fun v hv => T.subset ht₁ v (by simpa using hv))
    · intro v h1 h2; rcases hmemT v h1 h2 with e | e <;> simp [e]
    · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; tauto
  have hF₁ := hN T₁ z0 w₄ w₃ (by simpa using ht₁) hRT₁
  have hF₂ := hN T₂ w₃ c z0 (by simpa using ht₂) hRT₂
  have hw₃S₁ : w₃ ∈ S₁ := T.subset h₁ w₃ (by simp)
  have hw₃S₂ : w₃ ∉ S₂ := by
    intro h
    rcases hmem1 w₃ hw₃S₁ h with e | e | e
    · have := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp hPnd).2).2).2.1
      rw [e] at this; simp at this
    · exact hw₃c e
    · exact hz0n (e ▸ List.mem_cons_of_mem _ hw₃P)
  have hdeg : ∀ z ∈ S, H.Adj w₃ z → z = c ∨ z = w₄ ∨ z = z0 := by
    intro z hz hwz
    have hzS₁ : z ∈ S₁ := by
      by_contra hn
      have hz2 : z ∈ S₂ := (Finset.mem_union.mp (hU ▸ hz)).resolve_left hn
      rcases hX w₃ hw₃S₁ z hz2 hwz with h | h
      · exact hw₃S₂ h
      · exact hn h
    rcases Finset.mem_union.mp (hUT ▸ hzS₁) with h | h
    · rcases hF₁ z h with e | e | e
      · exact Or.inr (Or.inr e)
      · exact Or.inr (Or.inl e)
      · rw [e] at hwz; exact absurd hwz (H.loopless.irrefl _)
    · rcases hF₂ z h with e | e | e
      · rw [e] at hwz; exact absurd hwz (H.loopless.irrefl _)
      · exact Or.inl e
      · exact Or.inr (Or.inr e)
  exact T.claim6 H (M := v₃ :: R) (u := z0) hNT hh hPc hxc hdeg hN ih

end NTCalc

end ThomassenManyColourings
