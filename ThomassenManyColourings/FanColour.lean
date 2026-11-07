/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Fill

/-!
# Colouring paths and fans

The outer cycle of a near-triangulation is a path of `H`; consecutive vertices of a chordless
path are its only adjacent pairs. A path whose inner vertices have two colours besides `γ`
can be coloured greedily from one end, and a fan (a hub joined to a chordless path with
precoloured ends) has a colouring with the hub coloured by one of any three colours avoiding the
ends.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

omit [DecidableEq V] in
theorem isChain_congr {R R' : V → V → Prop} :
    ∀ {l : List V}, (∀ a ∈ l, ∀ b ∈ l, R a b → R' a b) → l.IsChain R → l.IsChain R'
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: l, h, hc => by
    rw [List.isChain_cons_cons] at hc ⊢
    exact ⟨h a (by simp) b (by simp) hc.1, isChain_congr (fun x hx y hy => h x
      (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hc.2⟩

omit [DecidableEq V] in
theorem ConsecIn.chain {R : V → V → Prop} :
    ∀ {l : List V} {y z : V}, ConsecIn l y z → l.IsChain R → R y z ∨ R z y
  | [], _, _, h, _ => by simp [ConsecIn] at h
  | [_], _, _, h, _ => by simp [ConsecIn] at h
  | a :: b :: l, y, z, h, hc => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact Or.inl (List.isChain_cons_cons.mp hc).1
    · exact Or.inr (List.isChain_cons_cons.mp hc).1
    · exact ConsecIn.chain h (List.isChain_cons_cons.mp hc).2

/-- The neighbours of `y` along a repetition-free list are its predecessor and successor. -/
theorem ConsecIn.nbr : ∀ {A : List V} {y z : V} {B : List V}, (A ++ y :: B).Nodup →
    ConsecIn (A ++ y :: B) y z → A.getLast? = some z ∨ B.head? = some z
  | [], _, _, [], _, h => by simp [ConsecIn] at h
  | [], y, z, b :: B, hnd, h => by
    rcases h with ⟨-, rfl⟩ | ⟨rfl, rfl⟩ | h
    · right; rfl
    · simp at hnd
    · exact absurd (ConsecIn.mem h).1 (List.nodup_cons.mp hnd).1
  | [a], y, z, B, hnd, h => by
    rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩ | h
    · simp at hnd
    · left; rfl
    · have := ConsecIn.nbr (A := []) (by simpa using (List.nodup_cons.mp hnd).2) h
      exact Or.inr (by simpa using this)
  | a :: a' :: A, y, z, B, hnd, h => by
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | h
    · simp at hnd
    · simp at hnd
    · rcases ConsecIn.nbr (A := a' :: A) (List.nodup_cons.mp hnd).2 h with h1 | h1
      · left; simpa [List.getLast?_cons_cons] using h1
      · exact Or.inr h1

namespace NTCalc

variable {T : NTCalc V}

theorem chain_aux {H : SimpleGraph V} {S : Finset V} :
    ∀ (B A : List V), T.NT H S (B ++ A) → B.IsChain H.Adj
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | y :: z :: B, A, h => by
    have hyz : H.Adj y z := T.adj_cons (by simpa using h)
    have h1 := T.rotate (x := y) (l := z :: (B ++ A)) h
    rw [List.cons_append, List.append_assoc] at h1
    have h' : T.NT H S ((z :: B) ++ (A ++ [y])) := h1
    exact List.isChain_cons_cons.mpr ⟨hyz, chain_aux (z :: B) _ h'⟩

/-- Consecutive outer vertices are adjacent. -/
theorem NT_chain {H : SimpleGraph V} {S : Finset V} {c : List V} (h : T.NT H S c) :
    c.IsChain H.Adj :=
  chain_aux c [] (by simpa using h)

end NTCalc

/-- Greedy colouring of a path from its far end, avoiding `γ` and a colour `e` at the last
vertex. -/
theorem path_colour (L : V → Finset C) (γ : C) : ∀ (l : List V) (e : C), l.Nodup →
    (∀ y ∈ l, 2 ≤ ((L y).erase γ).card) →
    ∃ f : V → C, (∀ y ∈ l, f y ∈ L y ∧ f y ≠ γ) ∧ (∀ z ∈ l.getLast?, f z ≠ e) ∧
      l.IsChain (fun y z => f y ≠ f z)
  | [], e, _, _ => ⟨fun _ => e, by simp, by simp, by simp⟩
  | y :: l, e, hnd, h2 => by
    obtain ⟨f, hf, hfe, hfc⟩ := path_colour L γ l e (List.nodup_cons.mp hnd).2
      (fun z hz => h2 z (List.mem_cons_of_mem _ hz))
    have hyl : y ∉ l := (List.nodup_cons.mp hnd).1
    let nx : C := (l.head?.map f).getD e
    obtain ⟨col, hcol, hcolnx⟩ : ∃ col ∈ (L y).erase γ, col ≠ nx := by
      have := h2 y List.mem_cons_self
      obtain ⟨c1, h1, c2, h2', hne⟩ :=
        Finset.one_lt_card.mp (show 1 < ((L y).erase γ).card by omega)
      by_cases hc1 : c1 = nx
      · exact ⟨c2, h2', fun h => hne (hc1.trans h.symm)⟩
      · exact ⟨c1, h1, hc1⟩
    refine ⟨Function.update f y col, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [Function.update_self]
        exact ⟨Finset.mem_of_mem_erase hcol, Finset.ne_of_mem_erase hcol⟩
      · have hzy : z ≠ y := fun h => hyl (h ▸ hz)
        rw [Function.update_of_ne hzy]; exact hf z hz
    · intro z hz
      rcases l with _ | ⟨w, l'⟩
      · simp at hz; subst hz; rw [Function.update_self]; exact hcolnx
      · have hz' : z ∈ (w :: l').getLast? := by simpa [List.getLast?_cons_cons] using hz
        have hzy : z ≠ y := fun h => hyl (h ▸ List.mem_of_mem_getLast? hz')
        rw [Function.update_of_ne hzy]; exact hfe z hz'
    · rcases l with _ | ⟨w, l'⟩
      · simp
      · refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
        · have hwy : w ≠ y := fun h => hyl (h ▸ List.mem_cons_self)
          rw [Function.update_self, Function.update_of_ne hwy]; exact hcolnx
        · refine isChain_congr (fun p hp q hq hpq => ?_) hfc
          have hpy : p ≠ y := fun h => hyl (h ▸ hp)
          have hqy : q ≠ y := fun h => hyl (h ▸ hq)
          rw [Function.update_of_ne hpy, Function.update_of_ne hqy]; exact hpq

/-- Three candidate colours for the hub of a fan: one of them extends. -/
theorem fan_colour (H : SimpleGraph V) {S₁ : Finset V} {u a c m₁ : V} {R : List V}
    (hS : ∀ w ∈ S₁, w = u ∨ w ∈ a :: m₁ :: (R ++ [c]))
    (hnd : (u :: a :: m₁ :: (R ++ [c])).Nodup)
    (hQc : ∀ y z, y ∈ a :: m₁ :: (R ++ [c]) → z ∈ a :: m₁ :: (R ++ [c]) → H.Adj y z →
      ConsecIn (a :: m₁ :: (R ++ [c])) y z)
    (L : V → Finset C) (g : V → C) (h3 : ∀ y ∈ m₁ :: R, 3 ≤ (L y).card)
    (γs : Finset C) (hγs : 3 ≤ γs.card) (hγa : g a ∉ γs) (hγc : g c ∉ γs) :
    ∃ γ ∈ γs, ∃ f : V → C, f u = γ ∧ f a = g a ∧ f c = g c ∧ (∀ y ∈ m₁ :: R, f y ∈ L y) ∧
      IsProperOn H S₁ f := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or,
    List.nodup_append] at hnd
  obtain ⟨⟨hua, hum, huR, huc⟩, ⟨ham, haR, hac⟩, ⟨hmR, hmc⟩, hRnd, -, hRc⟩ := hnd
  have hcR : c ∉ R := fun h => hRc c h c (by simp) rfl
  -- a hub colour leaving two colours at `m₁`
  have hA2 : 2 ≤ ((L m₁).erase (g a)).card := by
    have := Finset.pred_card_le_card_erase (s := L m₁) (a := g a)
    have := h3 m₁ (by simp); omega
  set A := (L m₁).erase (g a) with hAdef
  obtain ⟨γ, hγ, hAγ⟩ : ∃ γ ∈ γs, 2 ≤ (A.erase γ).card := by
    obtain ⟨γ₁, h1, γ₂, h2, γ₃, h3', h12, h13, h23⟩ := Finset.two_lt_card.mp (show 2 < γs.card by omega)
    by_cases n1 : γ₁ ∈ A
    · by_cases n2 : γ₂ ∈ A
      · by_cases n3 : γ₃ ∈ A
        · refine ⟨γ₁, h1, ?_⟩
          have hA3 : 3 ≤ A.card := by
            have : ({γ₁, γ₂, γ₃} : Finset C) ⊆ A := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl <;> assumption
            have hc3 : ({γ₁, γ₂, γ₃} : Finset C).card = 3 :=
              Finset.card_eq_three.mpr ⟨γ₁, γ₂, γ₃, h12, h13, h23, rfl⟩
            exact hc3 ▸ Finset.card_le_card this
          have := Finset.card_erase_of_mem n1; omega
        · exact ⟨γ₃, h3', by rw [Finset.erase_eq_of_notMem n3]; exact hA2⟩
      · exact ⟨γ₂, h2, by rw [Finset.erase_eq_of_notMem n2]; exact hA2⟩
    · exact ⟨γ₁, h1, by rw [Finset.erase_eq_of_notMem n1]; exact hA2⟩
  have hγa' : γ ≠ g a := fun h => hγa (h ▸ hγ)
  have hγc' : γ ≠ g c := fun h => hγc (h ▸ hγ)
  -- colour `R` from the end at `c`
  obtain ⟨f₀, hf₀, hf₀e, hf₀c⟩ := path_colour L γ R (g c) hRnd (fun y hy => by
    have := Finset.pred_card_le_card_erase (s := L y) (a := γ)
    have := h3 y (by simp [hy]); omega)
  let nx : C := (R.head?.map f₀).getD (g c)
  obtain ⟨col, hcol, hcolnx⟩ : ∃ col ∈ A.erase γ, col ≠ nx := by
    obtain ⟨c1, h1, c2, h2', hne⟩ := Finset.one_lt_card.mp (show 1 < (A.erase γ).card by omega)
    by_cases hc1 : c1 = nx
    · exact ⟨c2, h2', fun h => hne (hc1.trans h.symm)⟩
    · exact ⟨c1, h1, hc1⟩
  have hcolγ : col ≠ γ := Finset.ne_of_mem_erase hcol
  have hcolA : col ∈ A := Finset.mem_of_mem_erase hcol
  have hcola : col ≠ g a := Finset.ne_of_mem_erase hcolA
  have hcolL : col ∈ L m₁ := Finset.mem_of_mem_erase hcolA
  let f : V → C := fun w =>
    if w = u then γ else if w = a then g a else if w = m₁ then col else if w = c then g c
    else f₀ w
  have fu : f u = γ := by simp [f]
  have fa : f a = g a := by simp [f, Ne.symm hua]
  have fm : f m₁ = col := by simp [f, Ne.symm hum, Ne.symm ham]
  have fc : f c = g c := by simp [f, Ne.symm huc, Ne.symm hac, Ne.symm hmc]
  have fR : ∀ y ∈ R, f y = f₀ y := by
    intro y hy
    have h1 : y ≠ u := fun h => huR (h ▸ hy)
    have h2 : y ≠ a := fun h => haR (h ▸ hy)
    have h3' : y ≠ m₁ := fun h => hmR (h ▸ hy)
    have h4 : y ≠ c := fun h => hcR (h ▸ hy)
    simp [f, h1, h2, h3', h4]
  refine ⟨γ, hγ, f, fu, fa, fc, ?_, ?_⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [fm]; exact hcolL
    · rw [fR y hy]; exact (hf₀ y hy).1
  -- the path is properly coloured
  have hchain : (a :: m₁ :: (R ++ [c])).IsChain (fun y z => f y ≠ f z) := by
    refine List.isChain_cons_cons.mpr ⟨by rw [fa, fm]; exact Ne.symm hcola, ?_⟩
    rcases R with _ | ⟨w, R'⟩
    · simp only [List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true]
      rw [fm, fc]; exact hcolnx
    · refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
      · rw [fm, fR w (by simp)]; exact hcolnx
      · have hRc' : (w :: R' ++ [c]).IsChain (fun y z => f y ≠ f z) := by
          rw [List.isChain_append]
          refine ⟨isChain_congr (fun p hp q hq hpq => by rw [fR p hp, fR q hq]; exact hpq) hf₀c,
            by simp, ?_⟩
          intro p hp q hq
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
          subst hq
          rw [fR p (List.mem_of_mem_getLast? hp), fc]; exact hf₀e p hp
        simpa using hRc'
  have hγne : ∀ w ∈ a :: m₁ :: (R ++ [c]), f w ≠ γ := by
    intro w hw
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | hw | rfl
    · rw [fa]; exact Ne.symm hγa'
    · rw [fm]; exact hcolγ
    · rw [fR w hw]; exact (hf₀ w hw).2
    · rw [fc]; exact Ne.symm hγc'
  intro v hv w hw hvw
  rcases hS v hv with rfl | hv'
  · rcases hS w hw with rfl | hw'
    · exact absurd hvw (H.loopless.irrefl _)
    · rw [fu]; exact (hγne w hw').symm
  · rcases hS w hw with rfl | hw'
    · rw [fu]; exact hγne v hv'
    · rcases (hQc v w hv' hw' hvw).chain hchain with h | h
      · exact h
      · exact Ne.symm h

end ThomassenManyColourings
