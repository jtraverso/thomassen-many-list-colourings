/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1C

/-!
# Theorem 4, Case 1: colouring the blocks

Given colours of the cut vertices satisfying `StrOK` and a colouring of everything outside the
inner vertices of the blocks in which every interior neighbour of a cut vertex has a different
colour, the inner vertices can be coloured (`Case1Hyp.extend`): in each block the major vertex has
some colour `γ` different from the two ends, and `ColFrom` colours the inner path.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- Consecutive colours along `p, h b₁, …, h b_m, q` are distinct. -/
def ChainNe (h : V → C) : C → List V → C → Prop
  | p, [], q => p ≠ q
  | p, b :: B, q => h b ≠ p ∧ ChainNe h (h b) B q

omit [DecidableEq V] [DecidableEq C] in
theorem chainNe_congr {h h' : V → C} : ∀ {B : List V} {p q : C}, (∀ b ∈ B, h b = h' b) →
    ChainNe h p B q → ChainNe h' p B q
  | [], _, _, _, hc => hc
  | b :: B, p, q, he, hc => by
    have hb := he b List.mem_cons_self
    refine ⟨hb ▸ hc.1, ?_⟩
    rw [← hb]
    exact chainNe_congr (fun b' h' => he b' (List.mem_cons_of_mem _ h')) hc.2

omit [DecidableEq V] [DecidableEq C] in
/-- A chain colouring is proper along the path `k B k'`. -/
theorem chainNe_consec {h f : V → C} : ∀ (B : List V) (k k' : V) (p q : C), f k = p →
    f k' = q → (∀ b ∈ B, f b = h b) → ChainNe h p B q →
    ∀ u v, ConsecIn (k :: (B ++ [k'])) u v → f u ≠ f v
  | [], k, k', p, q, hk, hk', _, hc, u, v, hcons => by
    simp only [List.nil_append, ConsecIn] at hcons
    rcases hcons with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hcons
    · rw [hk, hk']; exact hc
    · rw [hk, hk']; exact Ne.symm hc
    · simp at hcons
  | b :: B, k, k', p, q, hk, hk', hB, hc, u, v, hcons => by
    have hb : f b = h b := hB b List.mem_cons_self
    simp only [List.cons_append, ConsecIn] at hcons
    rcases hcons with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hcons
    · rw [hk, hb]; exact Ne.symm hc.1
    · rw [hk, hb]; exact hc.1
    · exact chainNe_consec B b k' (h b) q hb hk' (fun b' h' => hB b' (List.mem_cons_of_mem _ h'))
        hc.2 u v (by simpa using hcons)

omit [DecidableEq C] in
/-- Realizing `ColFrom` by colours of the vertices. -/
theorem colFrom_realize (L : V → Finset C) (γ : C) : ∀ (B : List V) (p q : C), B.Nodup →
    ColFrom γ p (B.map L) q → ∃ h : V → C, (∀ b ∈ B, h b ∈ L b ∧ h b ≠ γ) ∧ ChainNe h p B q
  | [], p, q, _, hc => ⟨fun _ => p, by simp, hc⟩
  | b :: B, p, q, hnd, hc => by
    obtain ⟨e, he, heγ, hep, hrest⟩ := hc
    obtain ⟨h', h1, h2⟩ := colFrom_realize L γ B e q (List.nodup_cons.mp hnd).2 hrest
    have hbB := (List.nodup_cons.mp hnd).1
    refine ⟨Function.update h' b e, ?_, ?_⟩
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · simp [he, heγ]
      · have : b' ≠ b := fun h => hbB (by rw [← h]; exact hb')
        rw [Function.update_of_ne this]; exact h1 b' hb'
    · refine ⟨by simp [hep], ?_⟩
      rw [Function.update_self]
      exact chainNe_congr (fun b' hb' => (Function.update_of_ne
        (fun h => hbB (by rw [← h]; exact hb')) e h').symm) h2

omit [DecidableEq V] in
theorem interleave_cons_head : ∀ (ks : List V) (Bs : List (List V)) (k : V),
    ks.length = Bs.length → ∃ rest, interleave (k :: ks) Bs = k :: rest
  | [], [], k, _ => ⟨[], rfl⟩
  | k' :: ks, B :: Bs, k, _ => ⟨B ++ interleave (k' :: ks) Bs, rfl⟩
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

omit [DecidableEq V] in
theorem mem_interleave_of_mem_flatten : ∀ (ks : List V) (Bs : List (List V)),
    ks.length = Bs.length + 1 → ∀ v ∈ Bs.flatten, v ∈ interleave ks Bs
  | [_], [], _, v, hv => by simp at hv
  | k :: k' :: ks, B :: Bs, hl, v, hv => by
    simp only [List.flatten_cons, List.mem_append] at hv
    show v ∈ k :: (B ++ interleave (k' :: ks) Bs)
    rcases hv with hv | hv
    · simp [hv]
    · exact List.mem_cons_of_mem _ (List.mem_append_right _
        (mem_interleave_of_mem_flatten (k' :: ks) Bs (by simpa using hl) v hv))
  | [], _, hl, _, _ => by simp at hl
  | [_], _ :: _, hl, _, _ => by simp at hl
  | _ :: _ :: _, [], hl, _, _ => by simp at hl

omit [DecidableEq V] in
theorem mem_interleave_of_mem_ks : ∀ (ks : List V) (Bs : List (List V)),
    ks.length = Bs.length + 1 → ∀ v ∈ ks, v ∈ interleave ks Bs
  | [k], [], _, v, hv => by show v ∈ [k]; exact hv
  | k :: k' :: ks, B :: Bs, hl, v, hv => by
    show v ∈ k :: (B ++ interleave (k' :: ks) Bs)
    rcases List.mem_cons.mp hv with rfl | hv
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_append_right _
        (mem_interleave_of_mem_ks (k' :: ks) Bs (by simpa using hl) v hv))
  | [], _, hl, _, _ => by simp at hl
  | [_], _ :: _, hl, _, _ => by simp at hl
  | _ :: _ :: _, [], hl, _, _ => by simp at hl

omit [DecidableEq V] in
theorem interleave_disj : ∀ (ks : List V) (Bs : List (List V)), ks.length = Bs.length + 1 →
    (interleave ks Bs).Nodup → ∀ v ∈ ks, v ∉ Bs.flatten
  | [_], [], _, _, _, _ => by simp
  | k :: k' :: ks, B :: Bs, hl, hnd, v, hv => by
    have hnd' : (k :: (B ++ interleave (k' :: ks) Bs)).Nodup := hnd
    have hl' : (k' :: ks).length = Bs.length + 1 := by simpa using hl
    have hrest := List.nodup_append.mp (List.nodup_cons.mp hnd').2
    simp only [List.flatten_cons, List.mem_append, not_or]
    rcases List.mem_cons.mp hv with rfl | hv
    · have hk := (List.nodup_cons.mp hnd').1
      exact ⟨fun h => hk (List.mem_append_left _ h), fun h => hk (List.mem_append_right _
        (mem_interleave_of_mem_flatten _ _ hl' _ h))⟩
    · refine ⟨fun h => hrest.2.2 v h v (mem_interleave_of_mem_ks _ _ hl' v hv) rfl, ?_⟩
      exact interleave_disj (k' :: ks) Bs hl' hrest.2.1 v hv
  | [], _, hl, _, _, _ => by simp at hl
  | [_], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _ :: _, [], hl, _, _, _ => by simp at hl

namespace NTCalc

variable {T : NTCalc V}

omit [DecidableEq C] in
set_option maxHeartbeats 32000000 in
/-- **Colouring the inner vertices of the blocks.** -/
theorem Case1Hyp.extend {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) (f₀ : V → C) :
    ∀ (Bs : List (List V)) (ks : List V) (κs : List C) (A E : List V),
    a :: (Q ++ [c]) = A ++ interleave ks Bs ++ E → ks.length = Bs.length + 1 →
    List.Forall₂ (fun k col => f₀ k = col) ks κs → StrOK κs (Bs.map (fun B => B.map L)) →
    (∀ B ∈ Bs, ∀ b ∈ B, ∀ y₁ ∈ S, ∀ y₂ ∈ S, y₁ ∉ x :: a :: (Q ++ [c]) →
      y₂ ∉ x :: a :: (Q ++ [c]) → H.Adj b y₁ → H.Adj b y₂ → y₁ = y₂) →
    (∀ k ∈ ks, k ∈ Q) →
    (∀ k ∈ ks, ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj k y → f₀ y ≠ f₀ k) →
    (∃ f : V → C, (∀ v, v ∉ Bs.flatten → f v = f₀ v) ∧ (∀ b ∈ Bs.flatten, f b ∈ L b) ∧
      (∀ b ∈ Bs.flatten, ∀ z ∈ S, H.Adj b z → f b ≠ f z)) ∧
    (∀ k₁ ∈ ks, ∀ k₂ ∈ ks, H.Adj k₁ k₂ → f₀ k₁ ≠ f₀ k₂) := by
  classical
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  intro Bs
  induction Bs with
  | nil =>
    intro ks κs A E _ _ _ _ _ _ _
    refine ⟨⟨f₀, fun _ _ => rfl, by simp, by simp⟩, ?_⟩
    intro k₁ hk₁ k₂ hk₂ hadj
    rcases ks with _ | ⟨k, _ | ⟨k', ks'⟩⟩
    · simp at hk₁
    · simp at hk₁ hk₂; rw [hk₁, hk₂] at hadj; exact absurd hadj (H.loopless.irrefl _)
    · simp at *
  | cons B Bs ih =>
    intro ks κs A E hP hl hκ hs hinner hkQ hkcol
    obtain ⟨k, k', ks'', rfl⟩ : ∃ k k' ks'', ks = k :: k' :: ks'' := by
      rcases ks with _ | ⟨k, _ | ⟨k', ks''⟩⟩
      · simp at hl
      · simp at hl
      · exact ⟨k, k', ks'', rfl⟩
    obtain ⟨p, q, κs'', rfl, hfk, hfk', hκ''⟩ : ∃ p q κs'', κs = p :: q :: κs'' ∧ f₀ k = p ∧
        f₀ k' = q ∧ List.Forall₂ (fun k col => f₀ k = col) ks'' κs'' := by
      rcases hκ with _ | ⟨h1, hκ'⟩
      rcases hκ' with _ | ⟨h2, hκ''⟩
      exact ⟨_, _, _, rfl, h1, h2, hκ''⟩
    obtain ⟨hblock, hrestS⟩ := hs
    have hl' : (k' :: ks'').length = Bs.length + 1 := by simpa using hl
    obtain ⟨rest, hrest⟩ := interleave_cons_head ks'' Bs k' (by simpa using hl)
    have hP' : a :: (Q ++ [c]) = A ++ k :: (B ++ k' :: (rest ++ E)) := by
      rw [hP]; show A ++ (k :: (B ++ interleave (k' :: ks'') Bs)) ++ E = _
      rw [hrest]; simp
    have hPnd' : (A ++ k :: (B ++ k' :: (rest ++ E))).Nodup := hP' ▸ hPnd
    -- the rest of the string
    obtain ⟨⟨f', hf'1, hf'2, hf'3⟩, hKK⟩ := ih (k' :: ks'') (q :: κs'') (A ++ k :: B) E
      (by rw [hP', hrest]; simp) hl' (List.Forall₂.cons hfk' hκ'') hrestS
      (fun B' hB' => hinner B' (List.mem_cons_of_mem _ hB'))
      (fun k₁ hk₁ => hkQ k₁ (List.mem_cons_of_mem _ hk₁))
      (fun k₁ hk₁ => hkcol k₁ (List.mem_cons_of_mem _ hk₁))
    -- the block `k B k'` and its major vertex
    have hBnd : B.Nodup := by
      have := (List.nodup_append.mp hPnd').2.1
      exact (List.nodup_append.mp (List.nodup_cons.mp this).2).1
    have hkB : k ∉ B := by
      have := (List.nodup_append.mp hPnd').2.1
      exact fun h => (List.nodup_cons.mp this).1 (List.mem_append_left _ h)
    have hk'B : k' ∉ B := by
      have := (List.nodup_cons.mp (List.nodup_append.mp hPnd').2.1).2
      exact fun h => (List.nodup_append.mp this).2.2 k' h k' (by simp) rfl
    have hkQ' : k ∈ Q := hkQ k (by simp)
    have hk'Q : k' ∈ Q := hkQ k' (by simp)
    obtain ⟨w, hwS, hwn, hwk, hwk', hwB⟩ : ∃ w ∈ S, w ∉ x :: a :: (Q ++ [c]) ∧ H.Adj w k ∧
        H.Adj w k' ∧ ∀ b ∈ B, H.Adj w b ∧ ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj b y →
          y = w := by
      by_cases hB0 : B = []
      · subst hB0
        -- the apex of the outer edge `k k'`
        have hAne : A ≠ [] := by
          rintro rfl
          simp only [List.nil_append, List.cons.injEq] at hP'
          exact (List.nodup_cons.mp hPnd).1 (by rw [hP'.1]; simp [hkQ'])
        have hdec : a :: (Q ++ [c]) = A.dropLast ++ A.getLast hAne :: k :: k' :: (rest ++ E) := by
          rw [hP']
          conv_lhs => rw [← List.dropLast_append_getLast hAne]
          simp
        obtain ⟨us, hne, -, hus, -, -, hlast⟩ := hc.q_nbhd hdec
        obtain ⟨l, hl0⟩ : ∃ l, us.getLast? = some l := ⟨_, List.getLast?_eq_some_getLast hne⟩
        have hlm := List.mem_of_mem_getLast? hl0
        exact ⟨l, (hus l hlm).1, (hus l hlm).2.1, (hus l hlm).2.2.symm, hlast l hl0, by simp⟩
      · exact hc.block_major B A (rest ++ E) k k' (by rw [hP']) hB0
          (hinner B List.mem_cons_self)
    set γ := f₀ w with hγ
    have hγp : γ ≠ p := hfk ▸ hkcol k (by simp) w hwS hwn hwk.symm
    have hγq : γ ≠ q := hfk' ▸ hkcol k' (by simp) w hwS hwn hwk'.symm
    obtain ⟨h, hh1, hh2⟩ := colFrom_realize L γ B p q hBnd (by simpa using hblock γ hγp hγq)
    -- facts on membership
    have hseg : (interleave (k' :: ks'') Bs).Nodup := by
      rw [hrest]
      have h1 := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_append.mp hPnd').2.1).2).2.1
      exact (List.nodup_append.mp (List.nodup_cons.mp h1).2).1 |> fun h2 =>
        List.nodup_cons.mpr ⟨fun h3 => (List.nodup_cons.mp h1).1 (List.mem_append_left _ h3), h2⟩
    have hk'fl : k' ∉ Bs.flatten := interleave_disj (k' :: ks'') Bs hl' hseg k' (by simp)
    have hrestfl : ∀ v ∈ Bs.flatten, v ∈ rest := by
      intro v hv
      have := mem_interleave_of_mem_flatten (k' :: ks'') Bs hl' v hv
      rw [hrest] at this
      rcases List.mem_cons.mp this with h | h
      · exact absurd (h ▸ hv) hk'fl
      · exact h
    -- the parts of the outer path
    have hdisj := List.nodup_append.mp hPnd'
    have hseg2 := List.nodup_cons.mp hdisj.2.1
    have hseg3 := List.nodup_append.mp hseg2.2
    have hBrest : ∀ v ∈ B, v ∉ k' :: (rest ++ E) := fun v hv h => hseg3.2.2 v hv v h rfl
    have hBA : ∀ v ∈ B, v ∉ A := fun v hv h =>
      hdisj.2.2 v h v (List.mem_cons_of_mem _ (List.mem_append_left _ hv)) rfl
    have hflB : ∀ v ∈ Bs.flatten, v ∉ B := fun v hv hB =>
      hBrest v hB (List.mem_cons_of_mem _ (List.mem_append_left _ (hrestfl v hv)))
    have hflk : ∀ v ∈ Bs.flatten, v ≠ k := fun v hv h =>
      hseg2.1 (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (h ▸ hrestfl v hv))))
    have hkfl : k ∉ Bs.flatten := fun h => hflk k h rfl
    have hflP : ∀ v ∈ Bs.flatten, v ∈ a :: (Q ++ [c]) := by
      intro v hv; rw [hP']; simp [hrestfl v hv]
    -- the vertices of `B` are in `Q`
    have haA : a ∈ A ++ [k] := by
      rcases A with _ | ⟨a', A'⟩
      · simp at hP'; simp [hP'.1]
      · simp at hP'; simp [hP'.1]
    have hcE : c ∈ k' :: (rest ++ E) := by
      have := congrArg List.getLast? hP'
      rw [show a :: (Q ++ [c]) = (a :: Q) ++ [c] by simp, List.getLast?_concat,
        show A ++ k :: (B ++ k' :: (rest ++ E)) = (A ++ k :: B) ++ k' :: (rest ++ E) by simp,
        List.getLast?_append_of_ne_nil _ (by simp)] at this
      exact List.mem_of_mem_getLast? this.symm
    have hBQ : ∀ v ∈ B, v ∈ Q := by
      intro v hv
      have hvP : v ∈ a :: (Q ++ [c]) := by rw [hP']; simp [hv]
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hvP
      rcases hvP with h | h | h
      · exfalso
        rw [← h] at haA
        rcases List.mem_append.mp haA with h' | h'
        · exact hBA v hv h'
        · simp at h'; exact hkB (h' ▸ hv)
      · exact h
      · exfalso; rw [← h] at hcE; exact hBrest v hv hcE
    -- neighbours of the inner vertices of `B`
    have hnbB : ∀ b ∈ B, ∀ z ∈ S, H.Adj b z → z = w ∨ ConsecIn (k :: (B ++ [k'])) b z := by
      intro b hb z hzS hbz
      by_cases hzc : z ∈ x :: a :: (Q ++ [c])
      · right
        rcases List.mem_cons.mp hzc with hzx | hzP
        · rw [hzx] at hbz; exact absurd hbz.symm (hc.xfree b (hBQ b hb))
        have hcons := hc.chordless b z (by rw [hP']; simp [hb]) hzP hbz
        obtain ⟨B₁, B₂, hB12⟩ := List.append_of_mem hb
        have hP2 : a :: (Q ++ [c]) = (A ++ k :: B₁) ++ b :: (B₂ ++ k' :: (rest ++ E)) := by
          rw [hP', hB12]; simp
        have hP3 : a :: (Q ++ [c]) = A ++ (k :: (B ++ [k'])) ++ (rest ++ E) := by
          rw [hP']; simp
        rw [hP2] at hcons
        have hzseg : z ∈ k :: (B ++ [k']) := by
          rcases ConsecIn.nbr (hP2 ▸ hPnd) hcons with h | h
          · rcases B₁.eq_nil_or_concat with h1 | ⟨B₀, t, h1⟩
            · rw [h1, List.getLast?_append_of_ne_nil _ (by simp)] at h
              simp at h; simp [← h]
            · rw [h1, List.concat_eq_append,
                show A ++ k :: (B₀ ++ [t]) = (A ++ k :: B₀) ++ [t] by simp,
                List.getLast?_concat] at h
              simp at h
              rw [hB12, h1, List.concat_eq_append]; simp [← h]
          · rcases B₂ with _ | ⟨b₂, B₂'⟩
            · simp at h; simp [← h]
            · simp at h; rw [hB12]; simp [← h]
        have hcons' : ConsecIn (A ++ (k :: (B ++ [k'])) ++ (rest ++ E)) b z := by
          rw [← hP3, hP2]; exact hcons
        exact ConsecIn.infix (hP3 ▸ hPnd) (by simp [hb]) hzseg hcons'
      · left; exact (hwB b hb).2 z hzS hzc hbz
    have hwP : w ∉ a :: (Q ++ [c]) := fun h => hwn (List.mem_cons_of_mem _ h)
    have hwB' : w ∉ B := fun h => hwP (by rw [hP']; simp [h])
    have hwfl : w ∉ Bs.flatten := fun h => hwP (hflP w h)
    -- the colouring
    refine ⟨⟨fun v => if v ∈ B then h v else f' v, ?_, ?_, ?_⟩, ?_⟩
    · intro v hv
      simp only [List.flatten_cons, List.mem_append, not_or] at hv
      simp only [hv.1, ite_false]
      exact hf'1 v hv.2
    · intro b hb
      simp only [List.flatten_cons, List.mem_append] at hb
      rcases hb with hb | hb
      · simp only [hb, ite_true]; exact (hh1 b hb).1
      · simp only [hflB b hb, ite_false]; exact hf'2 b hb
    · intro b hb z hzS hbz
      simp only [List.flatten_cons, List.mem_append] at hb
      rcases hb with hb | hb
      · rcases hnbB b hb z hzS hbz with hzw | hcons
        · rw [hzw]
          simp only [hb, hwB', ite_true, ite_false]
          rw [hf'1 w hwfl]
          exact (hh1 b hb).2
        · have hfk0 : (fun v => if v ∈ B then h v else f' v) k = p := by
            simp only [hkB, ite_false]; rw [hf'1 k hkfl, hfk]
          have hfk'0 : (fun v => if v ∈ B then h v else f' v) k' = q := by
            simp only [hk'B, ite_false]; rw [hf'1 k' hk'fl, hfk']
          exact chainNe_consec (f := fun v => if v ∈ B then h v else f' v) B k k' p q hfk0
            hfk'0 (fun b' hb' => by simp [hb']) hh2 b z hcons
      · by_cases hzB : z ∈ B
        · exfalso
          have hbS : b ∈ S := T.subset hc.nt b (List.mem_cons_of_mem _ (hflP b hb))
          rcases hnbB z hzB b hbS hbz.symm with h1 | h1
          · exact hwfl (h1 ▸ hb)
          · have := (ConsecIn.mem h1).2
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
            rcases this with h2 | h2 | h2
            · exact hflk b hb h2
            · exact hflB b hb h2
            · exact hk'fl (h2 ▸ hb)
        · simp only [hflB b hb, hzB, ite_false]
          exact hf'3 b hb z hzS hbz
    · -- edges between cut vertices
      have hkk' : ∀ k₂ ∈ k' :: ks'', H.Adj k k₂ → f₀ k ≠ f₀ k₂ := by
        intro k₂ hk₂ hadj
        have hk₂r : k₂ ∈ k' :: rest := by
          rw [← hrest]; exact mem_interleave_of_mem_ks _ _ hl' k₂ hk₂
        have hcons := hc.chordless k k₂ (by rw [hP']; simp) (by
          rw [hP']; rcases List.mem_cons.mp hk₂r with h | h <;> simp [h]) hadj
        rcases List.mem_cons.mp hk₂r with rfl | hk₂r
        · by_cases hB0 : B = []
          · subst hB0
            rw [hfk, hfk']
            have := hblock γ hγp hγq
            simp only [List.map_nil] at this
            exact this
          · exfalso
            rw [hP'] at hcons
            exact ConsecIn.not_gap (A := A) (M := B) (B := rest ++ E) hB0 (hP' ▸ hPnd) hcons
        · exfalso
          obtain ⟨R₁, R₂, hR⟩ := List.append_of_mem hk₂r
          have hP4 : a :: (Q ++ [c]) = A ++ k :: ((B ++ k' :: R₁) ++ k₂ :: (R₂ ++ E)) := by
            rw [hP', hR]; simp
          rw [hP4] at hcons
          exact ConsecIn.not_gap (A := A) (M := B ++ k' :: R₁) (B := R₂ ++ E) (by simp)
            (hP4 ▸ hPnd) hcons
      intro k₁ hk₁ k₂ hk₂ hadj
      rcases List.mem_cons.mp hk₁ with h1 | hk₁
      · rw [h1] at hadj ⊢
        rcases List.mem_cons.mp hk₂ with h2 | hk₂
        · rw [h2] at hadj; exact absurd hadj (H.loopless.irrefl _)
        · exact hkk' k₂ hk₂ hadj
      · rcases List.mem_cons.mp hk₂ with h2 | hk₂
        · rw [h2] at hadj ⊢; exact Ne.symm (hkk' k₁ hk₁ hadj.symm)
        · exact hKK k₁ hk₁ k₂ hk₂ hadj

end NTCalc

end ThomassenManyColourings
