/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm1

/-!
# Extending a precoloured outer path

`NT H S (P ++ R)` with the path `P` (at least two vertices) properly precoloured. If every vertex
off `P` keeps at least three colours after removing the colours of its neighbours on `P`, and
every interior vertex has at least five colours, the precolouring extends. This replaces the
block argument in the proof of Theorem 2 of the paper.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- Two proper colourings agreeing on the common part of a separation glue to a proper
colouring. -/
theorem isProperOn_glue {H : SimpleGraph V} {S S₁ S₂ : Finset V} (hU : S₁ ∪ S₂ = S)
    (hX : ∀ u ∈ S₁, ∀ w ∈ S₂, H.Adj u w → u ∈ S₂ ∨ w ∈ S₁)
    {f₁ f₂ : V → C} (h₁ : IsProperOn H S₁ f₁) (h₂ : IsProperOn H S₂ f₂)
    (hag : ∀ x ∈ S₁, x ∈ S₂ → f₂ x = f₁ x) :
    IsProperOn H S (fun x => if x ∈ S₁ then f₁ x else f₂ x) := by
  have hside : ∀ x ∈ S, x ∉ S₁ → x ∈ S₂ := by
    intro x hx h1
    have : x ∈ S₁ ∪ S₂ := hU ▸ hx
    exact (Finset.mem_union.mp this).resolve_left h1
  intro u hu w hw huw
  by_cases hu1 : u ∈ S₁ <;> by_cases hw1 : w ∈ S₁
  · simp only [hu1, hw1, if_true]; exact h₁ u hu1 w hw1 huw
  · simp only [hu1, hw1, if_true, if_false]
    have hw2 := hside w hw hw1
    have hu2 : u ∈ S₂ := (hX u hu1 w hw2 huw).resolve_right hw1
    rw [← hag u hu1 hu2]
    exact h₂ u hu2 w hw2 huw
  · simp only [hu1, hw1, if_true, if_false]
    have hu2 := hside u hu hu1
    have hw2 : w ∈ S₂ := (hX w hw1 u hu2 huw.symm).resolve_right hu1
    rw [← hag w hw1 hw2]
    exact h₂ u hu2 w hw2 huw
  · simp only [hu1, hw1, if_false]
    exact h₂ u (hside u hu hu1) w (hside w hw hw1) huw

namespace NTCalc

variable (T : NTCalc V)

theorem rotate_append {H : SimpleGraph V} {S : Finset V} :
    ∀ {A B : List V}, T.NT H S (A ++ B) → T.NT H S (B ++ A)
  | [], B, h => by simpa using h
  | x :: A, B, h => by
    have h1 := T.rotate h
    have h2 : T.NT H S (A ++ (B ++ [x])) := by simpa using h1
    simpa using rotate_append h2

open Classical in
/-- The colours of `L x` not used on the neighbours of `x` in `P`. -/
noncomputable def freeCols (H : SimpleGraph V) (L : V → Finset C) (f₀ : V → C) (P : List V) (x : V) :
    Finset C :=
  (L x).filter fun col => ∀ y ∈ P, H.Adj x y → f₀ y ≠ col

theorem freeCols_subset (H : SimpleGraph V) (L : V → Finset C) (f₀ : V → C) (P : List V)
    (x : V) : freeCols H L f₀ P x ⊆ L x := by
  classical
  unfold freeCols
  exact Finset.filter_subset _ _

theorem mem_freeCols {H : SimpleGraph V} {L : V → Finset C} {f₀ : V → C} {P : List V} {x : V}
    {col : C} : col ∈ freeCols H L f₀ P x ↔ col ∈ L x ∧ ∀ y ∈ P, H.Adj x y → f₀ y ≠ col := by
  classical
  unfold freeCols
  exact Finset.mem_filter

theorem freeCols_mono {H : SimpleGraph V} {L : V → Finset C} {f₀ : V → C} {P P' : List V}
    (h : ∀ y ∈ P', y ∈ P) (x : V) : freeCols H L f₀ P x ⊆ freeCols H L f₀ P' x := by
  intro col hc
  rw [mem_freeCols] at hc ⊢
  exact ⟨hc.1, fun y hy hxy => hc.2 y (h y hy) hxy⟩

/-- **Lemma E.** -/
theorem lemmaE (H : SimpleGraph V) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → ∀ (P R : List V), 2 ≤ P.length →
    T.NT H S (P ++ R) → ∀ (L : V → Finset C) (f₀ : V → C),
    (∀ x ∈ P, ∀ y ∈ P, H.Adj x y → f₀ x ≠ f₀ y) →
    (∀ x ∈ S, x ∉ P → 3 ≤ (freeCols H L f₀ P x).card) →
    (∀ x ∈ S, x ∉ P ++ R → 5 ≤ (L x).card) →
    ∃ f : V → C, (∀ x ∈ P, f x = f₀ x) ∧ (∀ x ∈ S, x ∉ P → f x ∈ L x) ∧
      IsProperOn H S f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS P R hP hNT L f₀ hprop hfree h5
  have hnd := T.nodup hNT
  have hdisj : ∀ x ∈ P, x ∉ R := by
    intro x hxP hxR
    exact (List.nodup_append.mp hnd).2.2 x hxP x hxR rfl
  have hfree3 : ∀ x ∈ S, x ∉ P → 3 ≤ (L x).card := fun x hx hxP =>
    (hfree x hx hxP).trans (Finset.card_le_card (freeCols_subset H L f₀ _ x))
  rcases P with _ | ⟨p₁, _ | ⟨p₂, P''⟩⟩
  · simp at hP
  · simp at hP
  rcases P''.eq_nil_or_concat with rfl | ⟨Q', v, rfl⟩
  · -- two precoloured vertices: Theorem 1
    have hNT1 : T.NT H S (p₁ :: p₂ :: R) := by simpa using hNT
    obtain ⟨f, hfa, hfb, hfL, hfP⟩ := T.thm1 H n S hS p₁ p₂ R hNT1 L f₀
      (hprop p₁ (by simp) p₂ (by simp) (T.adj_cons hNT1))
      (fun x hx => hfree3 x (T.subset hNT1 x (by simp [hx])) (fun hxP => hdisj x hxP hx))
      (fun x hx hxc => h5 x hx (by simpa using hxc))
    refine ⟨f, ?_, ?_, hfP⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hfa
      · exact hfb
    · intro x hx hxP
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxP
      exact hfL x hx hxP.1 hxP.2
  · -- at least three precoloured vertices; `v` is the last one
    simp only [List.concat_eq_append] at hNT hprop hfree h5 hnd hdisj hfree3 hP ⊢
    set Q : List V := p₁ :: p₂ :: Q' with hQ
    have hPQ : p₁ :: p₂ :: (Q' ++ [v]) = Q ++ [v] := by simp [hQ]
    rw [hPQ] at hNT hprop hfree h5 hnd hdisj hfree3 ⊢
    have hQne : Q ≠ [] := by simp [hQ]
    have hrot : T.NT H S (v :: (R ++ Q)) := by
      have := T.rotate_append (A := Q) (B := [v] ++ R) (by simpa using hNT)
      simpa using this
    have hndr := T.nodup hrot
    have hvS : v ∈ S := T.subset hNT v (by simp)
    have hvQ : v ∉ Q := by
      intro h; simp only [List.nodup_cons, List.mem_append] at hndr; exact hndr.1 (Or.inr h)
    have hvR : v ∉ R := by
      intro h; simp only [List.nodup_cons, List.mem_append] at hndr; exact hndr.1 (Or.inl h)
    have hQR : ∀ x ∈ Q, x ∉ R := fun x hx => hdisj x (by simp [hx])
    have hQS : ∀ x ∈ Q, x ∈ S := fun x hx => T.subset hNT x (by simp [hx])
    have hRS : ∀ x ∈ R, x ∈ S := fun x hx => T.subset hNT x (by simp [hx])
    have hpropQ : ∀ x ∈ Q, ∀ y ∈ Q, H.Adj x y → f₀ x ≠ f₀ y :=
      fun x hx y hy => hprop x (by simp [hx]) y (by simp [hy])
    by_cases hch : ∃ z ∈ R ++ Q, (R ++ Q).head? ≠ some z ∧ (R ++ Q).getLast? ≠ some z ∧
        H.Adj v z
    · obtain ⟨z, hz, hzh, hzl, hvz⟩ := hch
      rcases List.mem_append.mp hz with hzR | hzQ
      · -- chord from `v` to `R`
        obtain ⟨R₁, R₂, hR⟩ := List.append_of_mem hzR
        have hR₁ : R₁ ≠ [] := by
          rintro rfl; apply hzh; simp [hR]
        have hrot' : T.NT H S (v :: (R₁ ++ z :: (R₂ ++ Q))) := by
          rw [hR] at hrot; simpa using hrot
        obtain ⟨S₁, S₂, hA, hB, hU, hI, hX⟩ :=
          T.chord hrot' hR₁ (by simp [hQne]) hvz
        have hmem : ∀ x, x ∈ S₁ → x ∈ S₂ → x = v ∨ x = z := by
          intro x h1 h2
          have : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hI] at this; simpa using this
        have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
        have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
        have hnd' := T.nodup hrot'
        have hR₁v : ∀ x ∈ R₁, x ≠ v ∧ x ≠ z := by
          intro x hx
          refine ⟨fun e => hvR (by rw [hR]; simp [← e, hx]), fun e => ?_⟩
          have : (R₁ ++ z :: R₂).Nodup := hR ▸ (List.nodup_append.mp hnd).2.1
          exact (List.nodup_append.mp this).2.2 x hx z (by simp) e
        have hR₁S₁ : ∀ x ∈ R₁, x ∈ S₁ := fun x hx => T.subset hA x (by simp [hx])
        have hR₁not : ∀ x ∈ R₁, x ∉ S₂ := by
          intro x hx h2
          rcases hmem x (hR₁S₁ x hx) h2 with e | e
          · exact (hR₁v x hx).1 e
          · exact (hR₁v x hx).2 e
        have hB' : T.NT H S₂ ((Q ++ [v]) ++ (z :: R₂)) := by
          have := T.rotate_append (A := z :: R₂) (B := Q ++ [v]) (by simpa using hB)
          simpa using this
        have hQS₂ : ∀ x ∈ Q, x ∈ S₂ := fun x hx => T.subset hB x (by simp [hx])
        have hQnot : ∀ x ∈ Q, x ∉ S₁ := by
          intro x hx h1
          rcases hmem x h1 (hQS₂ x hx) with e | e
          · exact hvQ (e ▸ hx)
          · exact hQR x hx (e ▸ hzR)
        have hcard₂ : S₂.card < n := by
          obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil R₁ hR₁
          rw [← hS]
          exact Finset.card_lt_card ⟨hS₂, fun h => hR₁not w hw (h (hR₁S₁ w hw |> hS₁))⟩
        have hcard₁ : S₁.card < n := by
          rw [← hS]
          exact Finset.card_lt_card ⟨hS₁, fun h => hQnot p₁ (by simp [hQ])
            (h (hQS p₁ (by simp [hQ])))⟩
        obtain ⟨fB, hfBP, hfBL, hfBp⟩ := ih _ hcard₂ S₂ rfl (Q ++ [v]) (z :: R₂)
          (by simp [hQ]) hB' L f₀ hprop (fun x hx hxP => hfree x (hS₂ hx) hxP)
          (by
            intro x hx hxc
            apply h5 x (hS₂ hx)
            intro hxc'
            apply hxc
            rcases List.mem_append.mp hxc' with h | h
            · exact List.mem_append_left _ h
            · rw [hR] at h
              rcases List.mem_append.mp h with h' | h'
              · exact absurd hx (hR₁not x h')
              · exact List.mem_append_right _ h')
        have hzS₂ : z ∈ S₂ := T.subset hB z (by simp)
        have hvS₂ : v ∈ S₂ := T.subset hB v (by simp)
        have hA' : T.NT H S₁ (z :: v :: R₁) := by
          apply T.rotate_back; simpa using hA
        obtain ⟨fA, hfAz, hfAv, hfAL, hfAp⟩ := T.thm1 H _ S₁ rfl z v R₁ hA' L fB
          (hfBp z hzS₂ v hvS₂ hvz.symm)
          (fun x hx => hfree3 x (hS₁ (hR₁S₁ x hx))
            (fun hxP => hdisj x hxP (by rw [hR]; simp [hx])))
          (by
            intro x hx hxc
            apply h5 x (hS₁ hx)
            intro hxc'
            rcases List.mem_append.mp hxc' with h | h
            · rcases List.mem_append.mp h with h' | h'
              · exact hQnot x h' hx
              · simp only [List.mem_singleton] at h'; exact hxc (by simp [h'])
            · rw [hR] at h
              rcases List.mem_append.mp h with h' | h'
              · exact hxc (by simp [h'])
              · rcases List.mem_cons.mp h' with h'' | h''
                · exact hxc (by simp [h''])
                · rcases hmem x hx (T.subset hB x (by simp [h''])) with e | e
                  · exact hxc (by simp [e])
                  · exact hxc (by simp [e]))
        refine ⟨fun x => if x ∈ S₂ then fB x else fA x, ?_, ?_, ?_⟩
        · intro x hx
          have : x ∈ S₂ := T.subset hB' x (List.mem_append_left _ hx)
          simp only [this, if_true]; exact hfBP x hx
        · intro x hx hxP
          by_cases h2 : x ∈ S₂
          · simp only [h2, if_true]; exact hfBL x h2 hxP
          · simp only [h2, if_false]
            have h1 : x ∈ S₁ := by
              have : x ∈ S₁ ∪ S₂ := hU ▸ hx
              exact (Finset.mem_union.mp this).resolve_right h2
            exact hfAL x h1 (fun e => h2 (e ▸ hzS₂)) (fun e => h2 (e ▸ hvS₂))
        · refine isProperOn_glue (S₁ := S₂) (S₂ := S₁) (by rw [Finset.union_comm]; exact hU)
            (fun u hu w hw huw => (hX w hw u hu huw.symm).symm) hfBp hfAp ?_
          intro x h2 h1
          rcases hmem x h1 h2 with rfl | rfl
          · exact hfAv
          · exact hfAz
      · -- chord from `v` to `Q`
        obtain ⟨Q₁, Q₂, hQs⟩ := List.append_of_mem hzQ
        have hQ₂ : Q₂ ≠ [] := by
          rintro rfl; apply hzl
          rw [hQs, ← List.append_assoc, List.getLast?_append]
          simp
        have hl₁ : R ++ Q₁ ≠ [] := by
          intro h
          obtain ⟨hR0, hQ0⟩ := List.append_eq_nil_iff.mp h
          apply hzh
          rw [hR0, List.nil_append, hQs, hQ0]
          simp
        have hrot' : T.NT H S (v :: ((R ++ Q₁) ++ z :: Q₂)) := by
          rw [hQs] at hrot; simpa using hrot
        obtain ⟨S₁, S₂, hA, hB, hU, hI, hX⟩ := T.chord hrot' hl₁ hQ₂ hvz
        have hmem : ∀ x, x ∈ S₁ → x ∈ S₂ → x = v ∨ x = z := by
          intro x h1 h2
          have : x ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hI] at this; simpa using this
        have hS₁ : S₁ ⊆ S := hU ▸ Finset.subset_union_left
        have hS₂ : S₂ ⊆ S := hU ▸ Finset.subset_union_right
        have hnd' := T.nodup hrot'
        simp only [List.nodup_cons, List.mem_append, List.mem_cons, not_or,
          List.nodup_append] at hnd'
        -- the two precoloured paths
        have hA' : T.NT H S₁ ((Q₁ ++ [z, v]) ++ R) := by
          have := T.rotate_append (A := v :: R) (B := Q₁ ++ [z]) (by simpa using hA)
          simpa using this
        have hB' : T.NT H S₂ ((z :: (Q₂ ++ [v])) ++ []) := by simpa using hB
        have hQ₁S₁ : ∀ x ∈ Q₁, x ∈ S₁ := fun x hx => T.subset hA x (by simp [hx])
        have hRS₁ : ∀ x ∈ R, x ∈ S₁ := fun x hx => T.subset hA x (by simp [hx])
        have hQ₂S₂ : ∀ x ∈ Q₂, x ∈ S₂ := fun x hx => T.subset hB x (by simp [hx])
        have hQnd : (Q₁ ++ z :: Q₂).Nodup := by
          have : (Q ++ [v]).Nodup := (List.nodup_append.mp hnd).1
          rw [hQs] at this
          exact (List.nodup_append.mp this).1
        have hQ₁v : ∀ x ∈ Q₁, x ≠ v ∧ x ≠ z := by
          intro x hx
          refine ⟨fun e => hvQ (by rw [hQs]; simp [← e, hx]), fun e => ?_⟩
          exact (List.nodup_append.mp hQnd).2.2 x hx z (by simp) e
        have hQ₂v : ∀ x ∈ Q₂, x ≠ v ∧ x ≠ z := by
          intro x hx
          refine ⟨fun e => hvQ (by rw [hQs]; simp [← e, hx]), fun e => ?_⟩
          have := (List.nodup_append.mp hQnd).2.1
          exact (List.nodup_cons.mp this).1 (e ▸ hx)
        have hRv : ∀ x ∈ R, x ≠ v ∧ x ≠ z := fun x hx =>
          ⟨fun e => hvR (e ▸ hx), fun e => hQR z hzQ (e ▸ hx)⟩
        have hnot₂ : ∀ x, x ∈ S₁ → x ≠ v → x ≠ z → x ∉ S₂ := fun x h1 hv hz h2 =>
          (hmem x h1 h2).elim hv hz
        have hnot₁ : ∀ x, x ∈ S₂ → x ≠ v → x ≠ z → x ∉ S₁ := fun x h2 hv hz h1 =>
          (hmem x h1 h2).elim hv hz
        have hcard₁ : S₁.card < n := by
          obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil Q₂ hQ₂
          rw [← hS]
          exact Finset.card_lt_card ⟨hS₁, fun h => hnot₁ w (hQ₂S₂ w hw) (hQ₂v w hw).1
            (hQ₂v w hw).2 (h (hS₂ (hQ₂S₂ w hw)))⟩
        have hcard₂ : S₂.card < n := by
          obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hl₁
          have hw1 : w ∈ S₁ := (List.mem_append.mp hw).elim (hRS₁ w) (hQ₁S₁ w)
          have hwv : w ≠ v ∧ w ≠ z := (List.mem_append.mp hw).elim (hRv w) (hQ₁v w)
          rw [← hS]
          exact Finset.card_lt_card ⟨hS₂, fun h => hnot₂ w hw1 hwv.1 hwv.2 (h (hS₁ hw1))⟩
        have hPA : ∀ y ∈ Q₁ ++ [z, v], y ∈ Q ++ [v] := by
          intro y hy; rw [hQs]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto
        have hPB : ∀ y ∈ z :: (Q₂ ++ [v]), y ∈ Q ++ [v] := by
          intro y hy; rw [hQs]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto
        obtain ⟨fA, hfAP, hfAL, hfAp⟩ := ih _ hcard₁ S₁ rfl (Q₁ ++ [z, v]) R (by simp) hA' L f₀
          (fun x hx y hy => hprop x (hPA x hx) y (hPA y hy))
          (by
            intro x hx hxP
            have hxP' : x ∉ Q ++ [v] := by
              intro h
              rw [hQs] at h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h hxP
              rcases h with (h | h | h) | h
              · exact hxP (by simp [h])
              · exact hxP (by simp [h])
              · exact hnot₂ x hx (hQ₂v x h).1 (hQ₂v x h).2 (hQ₂S₂ x h)
              · exact hxP (by simp [h])
            exact (hfree x (hS₁ hx) hxP').trans (Finset.card_le_card (freeCols_mono hPA x)))
          (by
            intro x hx hxc
            apply h5 x (hS₁ hx)
            intro h
            apply hxc
            rw [hQs] at h
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
            rcases h with ((h | h | h) | h) | h
            · simp [h]
            · exact Or.inl (Or.inr (Or.inl h))
            · exact absurd (hQ₂S₂ x h) (hnot₂ x hx (hQ₂v x h).1 (hQ₂v x h).2)
            · simp [h]
            · exact Or.inr h)
        obtain ⟨fB, hfBP, hfBL, hfBp⟩ := ih _ hcard₂ S₂ rfl (z :: (Q₂ ++ [v])) [] (by simp) hB'
          L f₀ (fun x hx y hy => hprop x (hPB x hx) y (hPB y hy))
          (by
            intro x hx hxP
            have hxP' : x ∉ Q ++ [v] := by
              intro h
              rw [hQs] at h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h hxP
              rcases h with (h | h | h) | h
              · exact hnot₁ x hx (hQ₁v x h).1 (hQ₁v x h).2 (hQ₁S₁ x h)
              · exact hxP (by simp [h])
              · exact hxP (by simp [h])
              · exact hxP (by simp [h])
            exact (hfree x (hS₂ hx) hxP').trans (Finset.card_le_card (freeCols_mono hPB x)))
          (by
            intro x hx hxc
            apply h5 x (hS₂ hx)
            intro h
            apply hxc
            rw [hQs] at h
            simp only [List.mem_append, List.mem_cons, List.append_nil, List.not_mem_nil, or_false] at h ⊢
            rcases h with ((h | h | h) | h) | h
            · exact absurd (hQ₁S₁ x h) (hnot₁ x hx (hQ₁v x h).1 (hQ₁v x h).2)
            · simp [h]
            · exact Or.inr (Or.inl h)
            · simp [h]
            · exact absurd (hRS₁ x h) (hnot₁ x hx (hRv x h).1 (hRv x h).2))
        have hzS₁ : z ∈ S₁ := T.subset hA z (by simp)
        have hvS₁ : v ∈ S₁ := T.subset hA v (by simp)
        refine ⟨fun x => if x ∈ S₁ then fA x else fB x, ?_, ?_, ?_⟩
        · intro x hx
          by_cases h1 : x ∈ S₁
          · simp only [h1, if_true]
            apply hfAP
            rw [hQs] at hx
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
            rcases hx with (h | h | h) | h
            · simp [h]
            · simp [h]
            · exact absurd (hQ₂S₂ x h) (hnot₂ x h1 (hQ₂v x h).1 (hQ₂v x h).2)
            · simp [h]
          · simp only [h1, if_false]
            apply hfBP
            rw [hQs] at hx
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
            rcases hx with (h | h | h) | h
            · exact absurd (hQ₁S₁ x h) h1
            · exact absurd (h ▸ hzS₁) h1
            · simp [h]
            · simp [h]
        · intro x hx hxP
          by_cases h1 : x ∈ S₁
          · simp only [h1, if_true]
            exact hfAL x h1 (fun h => hxP (hPA x h))
          · simp only [h1, if_false]
            have h2 : x ∈ S₂ := by
              have : x ∈ S₁ ∪ S₂ := hU ▸ hx
              exact (Finset.mem_union.mp this).resolve_left h1
            exact hfBL x h2 (fun h => hxP (hPB x h))
        · refine isProperOn_glue hU hX hfAp hfBp ?_
          intro x h1 h2
          rcases hmem x h1 h2 with rfl | rfl
          · rw [hfBP x (by simp), hfAP x (by simp)]
          · rw [hfBP x (by simp), hfAP x (by simp)]
    · -- no chord at `v`: delete it
      push_neg at hch
      obtain ⟨us, hus, hnb, hNT', -⟩ := T.delete hrot (by simp [hQ]; omega) (by
        intro z hz hvz
        by_contra hne
        push_neg at hne
        exact hch z hz hne.1 hne.2 hvz)
      have hhl : ∀ z, ((R ++ Q).head? = some z ∨ (R ++ Q).getLast? = some z) → z ∈ R ++ Q := by
        intro z h
        rcases h with h | h
        · exact List.mem_of_mem_head? h
        · exact List.mem_of_mem_getLast? h
      have hNT'' : T.NT H (S.erase v) (Q ++ (us ++ R)) := by
        have := T.rotate_append (A := R) (B := Q ++ us) (by simpa using hNT')
        simpa using this
      classical
      let L' : V → Finset C := fun x =>
        if H.Adj v x ∧ x ∉ Q ++ [v] then (L x).erase (f₀ v) else L x
      have hcard' : (S.erase v).card < n := by
        rw [← hS]; exact Finset.card_erase_lt_of_mem hvS
      have hQ2 : 2 ≤ Q.length := by simp [hQ]
      obtain ⟨f', hf'P, hf'L, hf'p⟩ := ih _ hcard' (S.erase v) rfl Q (us ++ R) hQ2 hNT'' L' f₀
        hpropQ
        (by
          intro x hx hxQ
          have hxv : x ≠ v := Finset.ne_of_mem_erase hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase hx
          have hxP : x ∉ Q ++ [v] := by simp [hxQ, hxv]
          refine (hfree x hxS hxP).trans (Finset.card_le_card ?_)
          intro col hc
          rw [mem_freeCols] at hc ⊢
          refine ⟨?_, fun y hy hxy => hc.2 y (by simp [hy]) hxy⟩
          by_cases hadj : H.Adj v x
          · have : L' x = (L x).erase (f₀ v) := if_pos ⟨hadj, hxP⟩
            rw [this]
            exact Finset.mem_erase.mpr ⟨fun e => hc.2 v (by simp) hadj.symm e.symm, hc.1⟩
          · have : L' x = L x := if_neg (fun h => hadj h.1)
            rw [this]; exact hc.1)
        (by
          intro x hx hxc
          have hxv : x ≠ v := Finset.ne_of_mem_erase hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase hx
          have hnadj : ¬ H.Adj v x := by
            intro hadj
            rcases hnb x hxS hadj with h | h | h
            · have := hhl x (Or.inl h)
              exact hxc (by simp only [List.mem_append] at this ⊢; tauto)
            · have := hhl x (Or.inr h)
              exact hxc (by simp only [List.mem_append] at this ⊢; tauto)
            · exact hxc (by simp [h])
          have : L' x = L x := if_neg (fun h => hnadj h.1)
          rw [this]
          apply h5 x hxS
          intro h
          apply hxc
          simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil,
            or_false] at h ⊢
          tauto)
      refine ⟨Function.update f' v (f₀ v), ?_, ?_, ?_⟩
      · intro x hx
        by_cases hxv : x = v
        · subst hxv; simp
        · rw [Function.update_of_ne hxv]
          exact hf'P x (by simpa [hxv] using hx)
      · intro x hx hxP
        have hxv : x ≠ v := fun e => hxP (by simp [e])
        rw [Function.update_of_ne hxv]
        have hm := hf'L x (Finset.mem_erase.mpr ⟨hxv, hx⟩) (fun h => hxP (by simp [h]))
        by_cases hadj : H.Adj v x ∧ x ∉ Q ++ [v]
        · have : L' x = (L x).erase (f₀ v) := if_pos hadj
          rw [this] at hm
          exact Finset.mem_of_mem_erase hm
        · have : L' x = L x := if_neg hadj
          rwa [this] at hm
      · have hv_nb : ∀ w ∈ S, H.Adj v w → w ≠ v → f' w ≠ f₀ v := by
          intro w hw hvw hwv
          by_cases hwP : w ∈ Q ++ [v]
          · have hwQ : w ∈ Q := by simpa [hwv] using hwP
            rw [hf'P w hwQ]
            exact (hprop v (by simp) w hwP hvw).symm
          · have hm := hf'L w (Finset.mem_erase.mpr ⟨hwv, hw⟩) (fun h => hwP (by simp [h]))
            have : L' w = (L w).erase (f₀ v) := if_pos ⟨hvw, hwP⟩
            rw [this] at hm
            exact Finset.ne_of_mem_erase hm
        intro u hu w hw huw
        by_cases hu' : u = v
        · subst hu'
          have hwv : w ≠ u := fun e => H.loopless.irrefl _ (e ▸ huw)
          rw [Function.update_self, Function.update_of_ne hwv]
          exact (hv_nb w hw huw hwv).symm
        · by_cases hw' : w = v
          · subst hw'
            rw [Function.update_self, Function.update_of_ne hu']
            exact hv_nb u hu huw.symm hu'
          · rw [Function.update_of_ne hu', Function.update_of_ne hw']
            exact hf'p u (Finset.mem_erase.mpr ⟨hu', hu⟩) w (Finset.mem_erase.mpr ⟨hw', hw⟩) huw

end NTCalc

end ThomassenManyColourings
