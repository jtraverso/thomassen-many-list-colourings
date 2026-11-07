/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1D

/-!
# Theorem 4, Case 1: enough admissible colourings of the cut vertices

With `s` blocks and `|Q| = s + 1 + Σ |B_i|`, the counting in Case 1 needs a family `F` of
admissible colourings of the cut vertices with `2^{1 + 3s} ≤ |F|^9 · 4^{|Q|}`:

* Subcase 1.1, no two consecutive triangle blocks (`NCE`): `s ≤ 1 + 2 Σ |B_i|`, and one colouring
  (Lemma 5) suffices.
* Subcase 1.2: split at the leftmost two consecutive triangle blocks; Lemma 5 on the left, a free
  colour at the middle cut vertex, and `many_strOK` on the right (`2 · 2^{t_R}` colourings).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {C : Type*} [DecidableEq C]

section NCE

variable {α : Type*}

/-- No two consecutive empty lists (no two consecutive triangle blocks). -/
def NCE : List (List α) → Prop
  | [] => True
  | B :: Bs => (B = [] → ∀ B' ∈ Bs.head?, B' ≠ []) ∧ NCE Bs

/-- Without two consecutive triangles, `s ≤ 1 + 2 Σ |B_i|`. -/
theorem nce_len : ∀ (Bs : List (List α)), NCE Bs → Bs.length ≤ 1 + 2 * (Bs.map List.length).sum
  | [], _ => by simp
  | [[]], _ => by simp
  | [] :: [] :: _, h => absurd rfl (h.1 rfl [] rfl)
  | [] :: (b :: B) :: rest, h => by
    have := nce_len rest h.2.2
    simp only [List.length_cons, List.map_cons, List.sum_cons] at this ⊢
    omega
  | (a :: A) :: Bs, h => by
    have := nce_len Bs h.2
    simp only [List.length_cons, List.map_cons, List.sum_cons] at this ⊢
    omega

/-- Without two consecutive triangles and ending with a non-triangle: `s ≤ 2 Σ |B_i|`. -/
theorem nce_len_last : ∀ (Bs : List (List α)), NCE Bs → (∀ B ∈ Bs.getLast?, B ≠ []) →
    Bs.length ≤ 2 * (Bs.map List.length).sum
  | [], _, _ => by simp
  | [[]], _, hl => absurd rfl (hl [] rfl)
  | [] :: [] :: _, h, _ => absurd rfl (h.1 rfl [] rfl)
  | [] :: (b :: B) :: rest, h, hl => by
    rcases rest with _ | ⟨B₃, rest'⟩
    · simp
    · have := nce_len_last (B₃ :: rest') h.2.2 (by
        intro B' hB'; apply hl B'
        rw [List.getLast?_cons_cons, List.getLast?_cons_cons]; exact hB')
      simp only [List.length_cons, List.map_cons, List.sum_cons] at this ⊢
      omega
  | (a :: A) :: Bs, h, hl => by
    rcases Bs with _ | ⟨B', rest⟩
    · simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    · have := nce_len_last (B' :: rest) h.2 (by
        intro B'' hB''; apply hl B''; rw [List.getLast?_cons_cons]; exact hB'')
      simp only [List.length_cons, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- The leftmost two consecutive triangles. -/
theorem split_of_not_nce : ∀ (Bs : List (List α)), ¬ NCE Bs →
    ∃ L R, Bs = L ++ [] :: [] :: R ∧ NCE L ∧ ∀ B ∈ L.getLast?, B ≠ []
  | [], h => absurd trivial h
  | B :: Bs, h => by
    by_cases hB : B = [] ∧ Bs.head? = some []
    · obtain ⟨rfl, hh⟩ := hB
      obtain ⟨R, rfl⟩ : ∃ R, Bs = [] :: R := by
        rcases Bs with _ | ⟨B', R⟩
        · simp at hh
        · simp at hh; exact ⟨R, by rw [hh]⟩
      exact ⟨[], R, rfl, trivial, by simp⟩
    · have h1 : B = [] → ∀ B' ∈ Bs.head?, B' ≠ [] := by
        intro hB0 B' hB' hB'0
        exact hB ⟨hB0, by rw [Option.mem_def] at hB'; rw [hB', hB'0]⟩
      have h2 : ¬ NCE Bs := fun h' => h ⟨h1, h'⟩
      obtain ⟨L, R, hLR, hL, hl⟩ := split_of_not_nce Bs h2
      refine ⟨B :: L, R, by rw [hLR]; rfl, ⟨?_, hL⟩, ?_⟩
      · intro hB0 B' hB' hB'0
        rcases L with _ | ⟨L₁, L'⟩
        · simp at hB'
        · apply h1 hB0 B' _ hB'0
          rw [hLR]; simpa using hB'
      · intro B' hB'
        rcases L with _ | ⟨L₁, L'⟩
        · simp at hB'
          subst hB'
          intro hB0
          apply hB ⟨hB0, by rw [hLR]; rfl⟩
        · rw [List.getLast?_cons_cons] at hB'; exact hl B' hB'

/-- Each block is a triangle (counted by `nTri`) or contributes to `Σ |B_i|`. -/
theorem len_le_nTri_add_sum {C : Type*} : ∀ (Is : List (List (Finset C))),
    Is.length ≤ nTri Is + (Is.map List.length).sum
  | [] => by simp
  | [] :: Is => by
    have := len_le_nTri_add_sum Is
    simp only [nTri, List.length_cons, List.map_cons, List.length_nil, List.sum_cons]; omega
  | (_ :: I) :: Is => by
    have := len_le_nTri_add_sum Is
    simp only [nTri, List.length_cons, List.map_cons, List.sum_cons]; omega

end NCE

omit [DecidableEq C] in
/-- Gluing admissible colourings of two strings sharing a cut vertex. -/
theorem strOK_append : ∀ (A : List C) (z : C) (B : List C) (I₁ I₂ : List (List (Finset C))),
    StrOK (A ++ [z]) I₁ → StrOK (z :: B) I₂ → StrOK (A ++ z :: B) (I₁ ++ I₂)
  | [], z, B, I₁, I₂, h₁, h₂ => by
    rcases I₁ with _ | ⟨I, I₁'⟩
    · simpa using h₂
    · exact absurd h₁ (by simp [StrOK])
  | [a], z, B, I₁, I₂, h₁, h₂ => by
    rcases I₁ with _ | ⟨I, _ | ⟨I', I₁'⟩⟩
    · exact absurd h₁ (by simp [StrOK])
    · exact ⟨h₁.1, h₂⟩
    · exact absurd h₁.2 (by simp [StrOK])
  | a :: a' :: A, z, B, I₁, I₂, h₁, h₂ => by
    rcases I₁ with _ | ⟨I, I₁'⟩
    · exact absurd h₁ (by simp [StrOK])
    · exact ⟨h₁.1, strOK_append (a' :: A) z B I₁' I₂ h₁.2 h₂⟩

set_option maxHeartbeats 16000000 in
/-- **A large family of admissible colourings of the cut vertices.** -/
theorem case1_family (K₀ : Finset C) (Ks : List (Finset C)) (Is : List (List (Finset C)))
    (hl : Ks.length = Is.length) (hI : ∀ I ∈ Is, ∀ M ∈ I, 3 ≤ M.card) (h0 : 2 ≤ K₀.card)
    (hmid : ∀ K ∈ Ks.dropLast, 3 ≤ K.card) (hlast : ∀ K ∈ Ks.getLast?, 2 ≤ K.card) :
    ∃ F : Finset (List C), (∀ κs ∈ F, List.Forall₂ (· ∈ ·) κs (K₀ :: Ks) ∧ StrOK κs Is) ∧
      2 ^ (1 + 3 * Is.length) ≤ F.card ^ 9 * 4 ^ (Is.length + 1 + (Is.map List.length).sum) := by
  classical
  by_cases hN : NCE Is
  · -- Subcase 1.1
    obtain ⟨κs, hf, hs⟩ := lemma5_string Is K₀ Ks hl hI h0 hmid hlast
    refine ⟨{κs}, by simpa using ⟨hf, hs⟩, ?_⟩
    have := nce_len Is hN
    rw [Finset.card_singleton, one_pow, one_mul,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- Subcase 1.2: the leftmost two consecutive triangles
    obtain ⟨IL, IR, hIs, hNL, hlL⟩ := split_of_not_nce Is hN
    subst hIs
    -- split the lists of the cut vertices accordingly
    have hlen : (K₀ :: Ks).length = IL.length + 2 + (IR.length + 1) := by
      simp only [List.length_cons, hl, List.length_append]; omega
    set KL := (K₀ :: Ks).take (IL.length + 1) with hKL
    obtain ⟨Kmid, KR, hrest⟩ : ∃ Kmid KR, (K₀ :: Ks).drop (IL.length + 1) = Kmid :: KR := by
      rcases h : (K₀ :: Ks).drop (IL.length + 1) with _ | ⟨Kmid, KR⟩
      · have := congrArg List.length h; rw [List.length_drop, hlen] at this; simp at this; omega
      · exact ⟨Kmid, KR, rfl⟩
    have hsplit : K₀ :: Ks = KL ++ Kmid :: KR := by
      rw [← hrest, hKL, List.take_append_drop]
    have hKLlen : KL.length = IL.length + 1 := by rw [hKL, List.length_take]; omega
    have hKRlen : KR.length = IR.length + 1 := by
      have := congrArg List.length hsplit
      simp [hKLlen] at this; simp [hl] at this ⊢; omega
    obtain ⟨KL', hKL'⟩ : ∃ KL', KL = K₀ :: KL' := by
      rw [hKL]; exact ⟨Ks.take IL.length, by simp⟩
    have hKs : Ks = KL' ++ Kmid :: KR := by
      have := hsplit; rw [hKL'] at this; simpa using this
    have hKRne : KR ≠ [] := by intro h; rw [h] at hKRlen; simp at hKRlen
    have hdrop : Ks.dropLast = KL' ++ Kmid :: KR.dropLast := by
      rw [hKs, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hKRne]
    have hlastKs : Ks.getLast? = KR.getLast? := by
      rw [hKs, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_cons_of_ne_nil hKRne]
    have hKL'mid : ∀ K ∈ KL', 3 ≤ K.card := fun K h => hmid K (by rw [hdrop]; simp [h])
    have hKmid : 3 ≤ Kmid.card := hmid Kmid (by rw [hdrop]; simp)
    obtain ⟨Kb, KR', rfl⟩ := List.exists_cons_of_ne_nil hKRne
    -- the left part (Lemma 5)
    have hKL'len : KL'.length = IL.length := by
      have := hKLlen; rw [hKL'] at this; simpa using this
    obtain ⟨κL, hfL, hsL⟩ := lemma5_string IL K₀ KL' hKL'len
      (fun I hI' => hI I (by simp [hI'])) h0
      (fun K hK => hKL'mid K (List.mem_of_mem_dropLast hK))
      (fun K hK => by have := hKL'mid K (List.mem_of_mem_getLast? hK); omega)
    -- the right part (counting)
    have hKR'len : KR'.length = IR.length := by simpa using hKRlen
    obtain ⟨FR, hFR, hFRm⟩ := many_strOK IR Kb KR' hKR'len
      (fun I hI' => hI I (by simp [hI']))
      (fun K hK => hmid K (by rw [hdrop]; simp; right; right; exact hK))
      (fun K hK => hlast K (by rw [hlastKs]; exact hK))
    -- the last colour on the left
    obtain ⟨κL₀, pL, hκL⟩ : ∃ κL₀ pL, κL = κL₀ ++ [pL] := by
      have hne : κL ≠ [] := by intro h; subst h; cases hfL
      exact ⟨κL.dropLast, κL.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    -- a middle colour for each right colouring
    have hμ : ∀ κR : List C, ∃ μ ∈ Kmid, μ ≠ pL ∧ ∀ q ∈ κR.head?, μ ≠ q := by
      intro κR
      obtain ⟨μ, hμ⟩ : ((Kmid.erase pL).erase (κR.head?.getD pL)).Nonempty :=
        Finset.card_pos.mp (by
          have := Finset.pred_card_le_card_erase (s := Kmid) (a := pL)
          have := Finset.pred_card_le_card_erase (s := Kmid.erase pL) (a := κR.head?.getD pL)
          omega)
      simp only [Finset.mem_erase] at hμ
      refine ⟨μ, hμ.2.2, hμ.2.1, fun q hq => ?_⟩
      rw [Option.mem_def] at hq
      rw [hq] at hμ
      exact hμ.1
    choose μf hμK hμp hμq using hμ
    refine ⟨FR.image (fun κR => κL ++ μf κR :: κR), ?_, ?_⟩
    · intro κs hκs
      obtain ⟨κR, hκR, rfl⟩ := Finset.mem_image.mp hκs
      obtain ⟨hfR, hsR⟩ := hFRm κR hκR
      refine ⟨?_, ?_⟩
      · rw [hsplit, hKL']
        rw [show κL ++ μf κR :: κR = κL ++ [μf κR] ++ κR by simp]
        rw [show K₀ :: KL' ++ Kmid :: Kb :: KR' = (K₀ :: KL') ++ [Kmid] ++ (Kb :: KR') by simp]
        exact List.rel_append (List.rel_append hfL
          (List.Forall₂.cons (hμK κR) List.Forall₂.nil)) hfR
      · -- `StrOK` for `κL ++ μ :: κR` along `IL ++ [] :: [] :: IR`
        obtain ⟨qR, κR', rfl⟩ : ∃ qR κR', κR = qR :: κR' := by
          rcases κR with _ | ⟨qR, κR'⟩
          · cases hfR
          · exact ⟨qR, κR', rfl⟩
        rw [hκL]
        have := strOK_append κL₀ pL (μf (qR :: κR') :: qR :: κR') IL ([] :: [] :: IR)
          (by rw [← hκL]; exact hsL)
          ⟨fun γ _ _ => Ne.symm (hμp _), fun γ _ _ => hμq _ qR rfl, hsR⟩
        simpa using this
    · rw [Finset.card_image_of_injective _ (fun κ₁ κ₂ h => by
        have := List.append_cancel_left h
        exact (List.cons.inj this).2)]
      have hcount := len_le_nTri_add_sum IR
      have hLlen := nce_len_last IL hNL hlL
      have hpow : 2 ^ (nTri IR + 1) ≤ FR.card := by rw [pow_succ]; exact hFR
      calc 2 ^ (1 + 3 * (IL ++ [] :: [] :: IR).length)
          ≤ 2 ^ (9 * (nTri IR + 1)) * 2 ^ (2 * ((IL ++ [] :: [] :: IR).length + 1 +
              ((IL ++ [] :: [] :: IR).map List.length).sum)) := by
            rw [← pow_add]
            apply Nat.pow_le_pow_right (by norm_num)
            simp only [List.length_append, List.length_cons, List.map_append, List.map_cons,
              List.sum_append, List.sum_cons, List.length_nil]
            omega
        _ = (2 ^ (nTri IR + 1)) ^ 9 * 4 ^ ((IL ++ [] :: [] :: IR).length + 1 +
              ((IL ++ [] :: [] :: IR).map List.length).sum) := by
            rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
        _ ≤ FR.card ^ 9 * 4 ^ ((IL ++ [] :: [] :: IR).length + 1 +
              ((IL ++ [] :: [] :: IR).map List.length).sum) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpow 9)

end ThomassenManyColourings
