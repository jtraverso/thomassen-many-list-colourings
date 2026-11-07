/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case2H

/-!
# Theorem 4: assembly

The induction step dispatches an instance to the reductions proved before:

* two precoloured vertices (`t3 = false`): Claim 8 (separating triangles), Claim 9 (chords of the
  path, chords at `x`), Claim 10 (a vertex with at least four colours), Claim 11 (otherwise);
* three precoloured vertices (`t3 = true`): the triangle (`thm4_k3`), Claim 8, Claim 9, Claim 10,
  the hub (`thm4_hub`), Claim 13 (`k = 4`), Claim 12, and then Case 1 / Case 2 under `Case1Hyp`.

The induction runs on `(n, n − r, t3)` lexicographically (`Lex4`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

theorem bound4_pred {N n r : ℕ} (h : Bound4 N (n + 1) r) : Bound4 N n r := by
  unfold Bound4 at h ⊢
  calc 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ _ := h

omit [DecidableEq V] in
/-- An entry strictly between two entries of a repetition-free list is not its head. -/
theorem mid_ne_head {l A B D : List V} {y z m a : V} (hnd : l.Nodup)
    (hl : l = A ++ y :: (B ++ z :: D)) (hm : m ∈ B) (ha : l.head? = some a) : m ≠ a := by
  intro e
  subst hl
  rcases A with _ | ⟨a', A'⟩
  · have hy : y = a := by simpa using ha
    have hym : y = m := hy.trans e.symm
    rw [← hym] at hm
    exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hm)
  · have ha' : a' = a := by simpa using ha
    have ham : a' = m := ha'.trans e.symm
    rw [← ham] at hm
    have hnd' : (a' :: (A' ++ y :: (B ++ z :: D))).Nodup := hnd
    exact (List.nodup_cons.mp hnd').1
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))

omit [DecidableEq V] in
/-- An entry strictly between two entries of a repetition-free list is not its last entry. -/
theorem mid_ne_last {l A B D : List V} {y z m c : V} (hnd : l.Nodup)
    (hl : l = A ++ y :: (B ++ z :: D)) (hm : m ∈ B) (hc : l.getLast? = some c) : m ≠ c := by
  have hl' : l.reverse = D.reverse ++ z :: (B.reverse ++ y :: A.reverse) := by rw [hl]; simp
  exact mid_ne_head (List.nodup_reverse.mpr hnd) hl' (List.mem_reverse.mpr hm)
    (by rw [List.head?_reverse]; exact hc)

namespace NTCalc

variable (T : NTCalc V)

set_option maxHeartbeats 16000000 in
/-- **Theorem 4, induction step.** -/
theorem thm4_step (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} {t3 : Bool} (hNT : T.NT H S (x :: P))
    (hh : Thm4Hyp H S x P a c L g t3)
    (ih : T.Thm4Lt C (nCount S (pcList t3 x a c))
      (nCount S (pcList t3 x a c) - rCount S (pcList t3 x a c) L) t3) :
    Thm4Concl H S x a c L g t3 := by
  classical
  have hnd := T.nodup hNT
  have hPnd : P.Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ P := (List.nodup_cons.mp hnd).1
  have h2 := hh.two_le
  have haP : a ∈ P := List.mem_of_mem_head? hh.head
  have hcP : c ∈ P := List.mem_of_mem_getLast? hh.last
  have hac : a ≠ c := by
    intro e
    rw [e] at hh
    have := eq_single_of_head_last hPnd hh.head hh.last
    rw [this] at h2; simp at h2
  -- the triangle
  by_cases hk3 : t3 = true ∧ P.length = 2
  · obtain ⟨rfl, hl⟩ := hk3
    have hP : P = [a, c] := by
      rcases P with _ | ⟨p, _ | ⟨q, _ | ⟨r, P'⟩⟩⟩
      · simp at hl
      · simp at hl
      · have h1 := hh.head; have h2 := hh.last
        simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
          List.getLast?_singleton] at h1 h2
        rw [h1, h2]
      · simp at hl
    subst hP
    exact T.thm4_k3 H hNT hh ih
  -- a free vertex on the path
  have hfree : ∃ y ∈ P, y ∉ pcList t3 x a c := by
    cases t3 with
    | false =>
      refine ⟨c, hcP, ?_⟩
      change c ∉ [x, a]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hxP (e ▸ hcP), fun e => hac e.symm⟩
    | true =>
      have h3 : 3 ≤ P.length := by
        by_contra hlt; exact hk3 ⟨rfl, by omega⟩
      rcases P with _ | ⟨p, _ | ⟨q, P'⟩⟩
      · simp at h2
      · simp at h2
      · refine ⟨q, by simp, ?_⟩
        change q ∉ [c, x, a]
        have hp : p = a := by simpa using hh.head
        subst hp
        have hqnd := List.nodup_cons.mp hPnd
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨fun e => ?_, fun e => hxP (by simp [e]), fun e => hqnd.1 (by simp [e])⟩
        -- `q = c` would make `c` occur twice or the path have length 2
        subst e
        rcases P' with _ | ⟨r, P''⟩
        · simp at h3
        · have hl := hh.last
          rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at hl
          have hmem := List.mem_of_mem_getLast? hl
          exact (List.nodup_cons.mp hqnd.2).1 hmem
  -- Claim 8: separating triangles
  by_cases hN : T.NoSepTri H S (x :: P)
  swap
  · unfold NoSepTri at hN
    push Not at hN
    obtain ⟨S₁, p, q, r, h₁, hR₁, u, hu, hun⟩ := hN
    exact T.thm4_claim8 H hNT hh hfree h₁ hR₁ ⟨u, hu, by simp; tauto⟩ ih
  -- Claim 9: chords of the path
  by_cases hPc : ∀ y z, y ∈ P → z ∈ P → H.Adj y z → ConsecIn P y z
  swap
  · push Not at hPc
    obtain ⟨y, z, hy, hz, hyz, hnc⟩ := hPc
    have hne : y ≠ z := fun e => H.loopless.irrefl _ (e ▸ hyz)
    obtain ⟨P₀, M, P₁, y', z', hPeq, hM, hyz'⟩ := chord_decomp hPnd hy hz hne hnc
    have hadj : H.Adj y' z' := by
      rcases hyz' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyz
      · exact hyz.symm
    subst hPeq
    exact T.thm4_claim9_path H hNT hh hM hadj ih
  -- Claim 9: chords at `x`
  by_cases hxc : ∀ y ∈ P, H.Adj x y → y = a ∨ y = c
  swap
  · push Not at hxc
    obtain ⟨y, hy, hxy, hya, hyc⟩ := hxc
    obtain ⟨P₀, P₁, hPeq⟩ := List.append_of_mem hy
    have hP₀ : P₀ ≠ [] := by
      rintro rfl
      have := hh.head; rw [hPeq] at this; simp at this; exact hya this
    have hP₁ : P₁ ≠ [] := by
      rintro rfl
      have := hh.last; rw [hPeq] at this; simp at this; exact hyc this
    cases t3 with
    | false =>
      subst hPeq
      exact T.thm4_claim9_x2 H hNT hh hP₀ hP₁ hxy ih
    | true => exact T.thm4_claim9_x H hNT hh hPc hN ⟨y, hy, hxy, hya, hyc⟩ ih
  -- Claim 10: a free vertex with at least four colours
  by_cases h4 : ∃ vi ∈ P, vi ∉ pcList t3 x a c ∧ 4 ≤ (L vi).card
  · obtain ⟨vi, hvi, hvin, h4⟩ := h4
    exact T.thm4_claim10 H hNT hh hPc hxc hN hvi hvin h4 ih
  push Not at h4
  have h3eq : ∀ y ∈ P, y ∉ pcList t3 x a c → (L y).card = 3 := fun y hy hyn => by
    have := hh.three y hy hyn; have := h4 y hy hyn; omega
  cases t3 with
  | false =>
    -- Claim 11
    exact T.thm4_claim11 H hNT hh (fun y hy hyn => h3eq y hy hyn) ih
  | true =>
  -- the path is `a Q c` with `Q ≠ []`
  have h3 : 3 ≤ P.length := by
    by_contra hlt; exact hk3 ⟨rfl, by omega⟩
  obtain ⟨Q, hPQ⟩ : ∃ Q, P = a :: (Q ++ [c]) := by
    rcases P with _ | ⟨p, P'⟩
    · simp at h2
    · have hp : p = a := by simpa using hh.head
      subst hp
      have hP' : P' ≠ [] := by rintro rfl; simp at h2
      have hl : P'.getLast? = some c := by
        have := hh.last
        rcases P' with _ | ⟨q, P''⟩
        · exact absurd rfl hP'
        · rwa [List.getLast?_cons_cons] at this
      exact ⟨P'.dropLast, by rw [eq_dropLast_append_of_getLast? hl]; simp⟩
  subst hPQ
  have hQne : Q ≠ [] := by rintro rfl; simp at h3
  have hpc : pcList true x a c = [c, x, a] := rfl
  have hQ3 : ∀ q ∈ Q, (L q).card = 3 := by
    intro q hq
    refine h3eq q (by simp [hq]) ?_
    rw [hpc]
    have hPnd' := List.nodup_cons.mp hPnd
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨fun e => ?_, fun e => hxP (by rw [← e]; simp [hq]),
      fun e => hPnd'.1 (by simp [← e, hq])⟩
    exact (List.nodup_append.mp hPnd'.2).2.2 q hq c (by simp) e
  -- the hub
  by_cases hhub : ∃ v ∈ S, v ∉ x :: a :: (Q ++ [c]) ∧ H.Adj v a ∧ H.Adj v x ∧ H.Adj v c
  · obtain ⟨v, hvS, hvn, hva, hvx, hvc⟩ := hhub
    exact T.thm4_hub H hNT hh hQne hPc hQ3 hN hvS hvn hva hvx hvc ih
  push Not at hhub
  have hnohub : ∀ u ∈ S, u ∉ x :: a :: (Q ++ [c]) → ¬ (H.Adj u c ∧ H.Adj u x ∧ H.Adj u a) :=
    fun u hu hun ⟨huc, hux, hua⟩ => hhub u hu hun hua hux huc
  -- Claim 13: `k = 4`
  by_cases hQ1 : Q.length = 1
  · obtain ⟨w, rfl⟩ : ∃ w, Q = [w] := by
      rcases Q with _ | ⟨w, _ | ⟨w', Q'⟩⟩
      · simp at hQ1
      · exact ⟨w, rfl⟩
      · simp at hQ1
    have hxw : ¬ H.Adj x w := by
      intro hxw
      have hPnd' := List.nodup_cons.mp hPnd
      rcases hxc w (by simp) hxw with e | e
      · exact hPnd'.1 (by simp [e])
      · exact (List.nodup_cons.mp hPnd'.2).1 (by simp [e])
    have hacn : ¬ H.Adj a c := fun h =>
      ConsecIn.not_ends (M := [w]) (by simp) hPnd (hPc a c (by simp) (by simp) h)
    exact T.thm4_claim13 H hNT hh hxw hacn (hQ3 w (by simp))
      (fun u hu hun => hnohub u hu (by simpa using hun)) ih
  -- Claim 12
  by_cases h12 : C12 H S (x :: a :: (Q ++ [c])) (a :: (Q ++ [c]))
  swap
  · unfold C12 at h12
    push Not at h12
    obtain ⟨u, huS, hun, A, B, D, y, z, hPeq, huy, huz, m, hmB, hum⟩ := h12
    have hBne : B ≠ [] := by rintro rfl; simp at hmB
    have hnd2 : (A ++ y :: (B ++ z :: D)).Nodup := hPeq ▸ hPnd
    have hB3 : ∀ y' ∈ B, (L y').card = 3 := by
      intro y' hy'
      refine h3eq y' (by rw [hPeq]; simp [hy']) ?_
      rw [hpc]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨mid_ne_last hPnd hPeq hy' hh.last, fun e => hxP ?_,
        mid_ne_head hPnd hPeq hy' hh.head⟩
      have hmem : y' ∈ a :: (Q ++ [c]) := by rw [hPeq]; simp [hy']
      rwa [e] at hmem
    have hQc : ∀ y₁ z₁, y₁ ∈ y :: (B ++ [z]) → z₁ ∈ y :: (B ++ [z]) → H.Adj y₁ z₁ →
        ConsecIn (y :: (B ++ [z])) y₁ z₁ := by
      have e3 : A ++ (y :: (B ++ [z])) ++ D = A ++ y :: (B ++ z :: D) := by simp
      intro y₁ z₁ hy₁ hz₁ hyz₁
      have hy₁' : y₁ ∈ a :: (Q ++ [c]) := by
        rw [hPeq, ← e3]; exact List.mem_append_left _ (List.mem_append_right _ hy₁)
      have hz₁' : z₁ ∈ a :: (Q ++ [c]) := by
        rw [hPeq, ← e3]; exact List.mem_append_left _ (List.mem_append_right _ hz₁)
      have h1 := hPc y₁ z₁ hy₁' hz₁' hyz₁
      rw [hPeq, ← e3] at h1
      exact ConsecIn.infix (by rw [e3]; exact hnd2) hy₁ hz₁ h1
    have hNT2 : T.NT H S (x :: (A ++ y :: (B ++ z :: D))) := hPeq ▸ hNT
    have hh2 : Thm4Hyp H S x (A ++ y :: (B ++ z :: D)) a c L g true := hPeq ▸ hh
    have hPc2 : ∀ y₁ z₁, y₁ ∈ A ++ y :: (B ++ z :: D) → z₁ ∈ A ++ y :: (B ++ z :: D) →
        H.Adj y₁ z₁ → ConsecIn (A ++ y :: (B ++ z :: D)) y₁ z₁ := hPeq ▸ hPc
    have hN2 : T.NoSepTri H S (x :: (A ++ y :: (B ++ z :: D))) := hPeq ▸ hN
    have hun2 : u ∉ x :: (A ++ y :: (B ++ z :: D)) := hPeq ▸ hun
    rcases T.thm4_claim12 H hNT2 hh2 hBne huS hun2 huy huz hPc2 hQc hB3 hN2
      (hnohub u huS hun) ih with h | h
    · exact h
    · exact absurd (h m hmB) hum
  -- Cases 1 and 2
  have hxfree : ∀ q ∈ Q, ¬ H.Adj x q := by
    intro q hq hxq
    have hPnd' := List.nodup_cons.mp hPnd
    rcases hxc q (by simp [hq]) hxq with e | e
    · exact hPnd'.1 (by simp [← e, hq])
    · exact (List.nodup_append.mp hPnd'.2).2.2 q hq c (by simp) e
  have hc1 : T.Case1Hyp H S x a c Q L g :=
    ⟨hNT, hh, by
      rcases Q with _ | ⟨q, _ | ⟨q', Q'⟩⟩
      · exact absurd rfl hQne
      · simp at hQ1
      · simp, hPc, hxfree, hQ3, hN, h12, hnohub⟩
  by_cases hgw : NoGWR H S x a c Q
  · intro _ _
    exact bound4_pred (hc1.case1 hgw ih)
  · exact hc1.case2 hgw ih

/-- **Theorem 4** for all instances below `(n, s, t)` in `Lex4`. -/
theorem thm4_lt : ∀ (n s : ℕ) (t : Bool), T.Thm4Lt C n s t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  have hF : T.Thm4Lt C n s false := by
    intro H S x P a c L g t3 hNT hh hlex
    refine T.thm4_step H hNT hh ?_
    rcases hlex with h | ⟨rfl, h | ⟨-, -, h⟩⟩
    · exact ihn _ h _ _
    · exact ihs _ h _
    · exact absurd h (by simp)
  intro t
  cases t with
  | false => exact hF
  | true =>
    intro H S x P a c L g t3 hNT hh hlex
    refine T.thm4_step H hNT hh ?_
    rcases hlex with h | ⟨rfl, h | ⟨rfl, rfl, -⟩⟩
    · exact ihn _ h _ _
    · exact ihs _ h _
    · exact hF

/-- **Theorem 4** (Thomassen 2007). -/
theorem thm4 (H : SimpleGraph V) {S : Finset V} {x : V} {P : List V} {a c : V}
    {L : V → Finset C} {g : V → C} {t3 : Bool} (hNT : T.NT H S (x :: P))
    (hh : Thm4Hyp H S x P a c L g t3) : Thm4Concl H S x a c L g t3 :=
  T.thm4_step H hNT hh (T.thm4_lt _ _ _)

end NTCalc

end ThomassenManyColourings
