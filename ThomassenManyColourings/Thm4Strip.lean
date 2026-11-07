/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Claim13

/-!
# Theorem 4, Case 1: deleting the path `v₃ … v_{k-1}`

With the outer cycle `x a Q c` (`Q = v₃ … v_{k-1}`) chordless, no chord at `x`, no separating
triangle and Claim 12, the vertices of `Q` can be deleted one by one (`T.delete`): the next vertex
`q` has no chord, since a vertex `z` of the new outer path joined to `q` would be joined to the
previously deleted vertex `d` as well (Claim 12), and the last new outer vertex is the unique
apex of the outer edge `d q` (`two_apex`). The result: `S \ Q` is a near-triangulation with outer
cycle `x a Y c`, where `Y` lists the interior neighbours of `Q`.
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V]

/-- **Claim 12** as a property: an interior vertex joined to two vertices of the path `P` is joined
to every vertex between them. -/
def C12 (H : SimpleGraph V) (S : Finset V) (cyc P : List V) : Prop :=
  ∀ u ∈ S, u ∉ cyc → ∀ (A B D : List V) (y z : V), P = A ++ y :: (B ++ z :: D) →
    H.Adj u y → H.Adj u z → ∀ m ∈ B, H.Adj u m

omit [DecidableEq V] in
theorem eq_dropLast_append_of_getLast? {l : List V} {t : V} (h : l.getLast? = some t) :
    l = l.dropLast ++ [t] := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  rw [List.getLast?_eq_some_getLast hne] at h
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [Option.some.inj h]

namespace NTCalc

variable (T : NTCalc V)

theorem adj_mid {H : SimpleGraph V} {S : Finset V} {A B : List V} {u v : V}
    (h : T.NT H S (A ++ u :: v :: B)) : H.Adj u v :=
  T.adj_cons (by simpa using T.rotate_append (A := A) (B := u :: v :: B) h)

set_option maxHeartbeats 16000000 in
/-- **Deleting `Q`**, by induction on the part `Q'` not yet deleted (`D` deleted, `Y` the new
outer vertices). -/
theorem strip (H : SimpleGraph V) {S : Finset V} {x a c : V} {Q : List V}
    (hNT : T.NT H S (x :: a :: (Q ++ [c]))) (hQ2 : 2 ≤ Q.length)
    (hPc : ∀ y z, y ∈ a :: (Q ++ [c]) → z ∈ a :: (Q ++ [c]) → H.Adj y z →
      ConsecIn (a :: (Q ++ [c])) y z)
    (hxQ : ∀ q ∈ Q, ¬ H.Adj x q)
    (hN : T.NoSepTri H S (x :: a :: (Q ++ [c])))
    (hC : C12 H S (x :: a :: (Q ++ [c])) (a :: (Q ++ [c]))) :
    ∀ (Q' D Y : List V) (S' : Finset V), Q = D ++ Q' →
    T.NT H S' (x :: a :: (Y ++ Q' ++ [c])) → (∀ v, v ∈ S' ↔ v ∈ S ∧ v ∉ D) →
    (∀ y ∈ Y, y ∈ S ∧ y ∉ x :: a :: (Q ++ [c]) ∧ ∃ d ∈ D, H.Adj y d) →
    (D = [] → Y = []) → (∀ d ∈ D.getLast?, ∃ ℓ ∈ Y.getLast?, H.Adj ℓ d) →
    (∀ d ∈ D, ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj d y → y ∈ Y) →
    ∃ (Y' : List V) (S'' : Finset V), (∀ v, v ∈ S'' ↔ v ∈ S ∧ v ∉ Q) ∧
      T.NT H S'' (x :: a :: (Y' ++ [c])) ∧
      (∀ y ∈ Y', y ∈ S ∧ y ∉ x :: a :: (Q ++ [c]) ∧ ∃ q ∈ Q, H.Adj y q) ∧
      (∀ q ∈ Q, ∀ y ∈ S, y ∉ x :: a :: (Q ++ [c]) → H.Adj q y → y ∈ Y') := by
  classical
  have hnd := T.nodup hNT
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  intro Q'
  induction Q' with
  | nil =>
    intro D Y S' hQ hS' hmem hY _ _ hcomp
    simp only [List.append_nil] at hQ
    subst hQ
    refine ⟨Y, S', fun v => hmem v, by simpa using hS', fun y hy => ?_, hcomp⟩
    obtain ⟨h1, h2, d, hd, hyd⟩ := hY y hy
    exact ⟨h1, h2, d, hd, hyd⟩
  | cons q Q'' ih =>
    intro D Y S' hQ hS' hmem hY hDY hlast hcomp
    have hqQ : q ∈ Q := by rw [hQ]; simp
    -- the path `P` around `q`
    have hPq : a :: (Q ++ [c]) = (a :: D) ++ q :: (Q'' ++ [c]) := by rw [hQ]; simp
    have hPnd' : ((a :: D) ++ q :: (Q'' ++ [c])).Nodup := hPq ▸ hPnd
    have hnbP : ∀ z ∈ a :: (Q ++ [c]), H.Adj q z →
        (a :: D).getLast? = some z ∨ (Q'' ++ [c]).head? = some z := by
      intro z hz hqz
      have := hPc q z (by rw [hPq]; simp) hz hqz
      rw [hPq] at this
      exact ConsecIn.nbr hPnd' this
    -- the new outer vertex before `q` is joined to `q`
    have hℓq : ∀ ℓ ∈ Y.getLast?, H.Adj ℓ q := by
      intro ℓ hℓ
      have hY₀ := eq_dropLast_append_of_getLast? (Option.mem_def.mp hℓ)
      exact T.adj_mid (A := x :: a :: Y.dropLast) (B := Q'' ++ [c])
        (by rw [hY₀] at hS'; simpa using hS')
    -- rotate so that `q` comes first
    have hrot : T.NT H S' (q :: (Q'' ++ c :: x :: a :: Y)) := by
      have := T.rotate_append (A := x :: a :: Y) (B := q :: (Q'' ++ [c])) (by simpa using hS')
      simpa using this
    have hlhead : (Q'' ++ c :: x :: a :: Y).head? = (Q'' ++ [c]).head? := by
      rcases Q'' with _ | ⟨q', Q₃⟩ <;> rfl
    have hllast : (Q'' ++ c :: x :: a :: Y).getLast? = (a :: Y).getLast? := by
      rw [show Q'' ++ c :: x :: a :: Y = (Q'' ++ [c, x]) ++ (a :: Y) by simp,
        List.getLast?_append_of_ne_nil _ (by simp)]
    -- no chord at `q`
    have hfree : ∀ z ∈ Q'' ++ c :: x :: a :: Y, H.Adj q z →
        (Q'' ++ c :: x :: a :: Y).head? = some z ∨ (Q'' ++ c :: x :: a :: Y).getLast? = some z := by
      intro z hz hqz
      rw [hlhead, hllast]
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | hz | hz | hz | hz
      · -- `z ∈ Q''`
        rcases hnbP z (by rw [hQ]; simp [hz]) hqz with h | h
        · exfalso
          have hzA : z ∈ a :: D := List.mem_of_mem_getLast? h
          have := (List.nodup_append.mp hPnd').2.2 z hzA z (by simp [hz])
          exact this rfl
        · exact Or.inl h
      · -- `z = c`
        subst hz
        rcases hnbP z (by simp) hqz with h | h
        · exfalso
          have hzA : z ∈ a :: D := List.mem_of_mem_getLast? h
          exact (List.nodup_append.mp hPnd').2.2 z hzA z (by simp) rfl
        · exact Or.inl h
      · -- `z = x`
        subst hz; exact absurd hqz.symm (hxQ q hqQ)
      · -- `z = a`
        subst hz
        rcases hnbP z (by simp) hqz with h | h
        · by_cases hD : D = []
          · subst hD; rw [hDY rfl]; right; rfl
          · exfalso
            rw [List.getLast?_cons, List.getLast?_eq_some_getLast hD] at h
            simp only [Option.getD_some, Option.some.injEq] at h
            have : z ∈ D := h ▸ List.getLast_mem hD
            exact (List.nodup_cons.mp hPnd').1 (by simp [this])
        · exfalso
          have hz' : z ∈ Q'' ++ [c] := List.mem_of_mem_head? h
          exact (List.nodup_cons.mp hPnd').1 (by simp at hz' ⊢; tauto)
      · -- `z ∈ Y`: it is the last vertex of `Y`
        right
        obtain ⟨hzS, hzn, d, hd, hzd⟩ := hY z hz
        have hDne : D ≠ [] := by rintro rfl; rw [hDY rfl] at hz; simp at hz
        obtain ⟨d₀, hd₀⟩ : ∃ d₀, D.getLast? = some d₀ := ⟨_, List.getLast?_eq_some_getLast hDne⟩
        obtain ⟨ℓ, hℓ, hℓd₀⟩ := hlast d₀ hd₀
        have hℓ' : Y.getLast? = some ℓ := Option.mem_def.mp hℓ
        have hYne : Y ≠ [] := by rintro rfl; simp at hℓ'
        have hgoal : (a :: Y).getLast? = some ℓ := by
          rw [List.getLast?_cons, hℓ']; rfl
        suffices hzℓ : z = ℓ by rw [hgoal, hzℓ]
        -- `z` is joined to `d₀`
        have hD₀ := eq_dropLast_append_of_getLast? hd₀
        have hzd₀ : H.Adj z d₀ := by
          obtain ⟨D₁, D₂, hD12⟩ := List.append_of_mem hd
          rcases D₂.eq_nil_or_concat with h2 | ⟨D₃, t, h2⟩
          · subst h2
            have : D.getLast? = some d := by rw [hD12]; simp
            rw [hd₀] at this
            rw [Option.some.inj this]; exact hzd
          · rw [h2, List.concat_eq_append] at hD12
            have ht : D.getLast? = some t := by
              rw [hD12, show D₁ ++ d :: (D₃ ++ [t]) = (D₁ ++ d :: D₃) ++ [t] by simp,
                List.getLast?_concat]
            rw [hd₀] at ht
            rw [Option.some.inj ht]
            refine hC z hzS hzn (a :: D₁) (D₃ ++ [t]) (Q'' ++ [c]) d q ?_ hzd hqz.symm t
              (by simp)
            rw [hQ, hD12]; simp
        -- `ℓ` is joined to `d₀` and `q`: two apexes of the outer edge `d₀ q`
        obtain ⟨hℓS, hℓn, -⟩ := hY ℓ (List.mem_of_mem_getLast? hℓ')
        have hℓq' : H.Adj ℓ q := hℓq ℓ hℓ
        have hrotG : T.NT H S (d₀ :: q :: (Q'' ++ c :: x :: a :: D.dropLast)) := by
          have := T.rotate_append (A := x :: a :: D.dropLast) (B := d₀ :: q :: (Q'' ++ [c]))
            (by rw [hQ, hD₀] at hNT; simpa using hNT)
          simpa using this
        have hcyc : ∀ v, v ∈ d₀ :: q :: (Q'' ++ c :: x :: a :: D.dropLast) ↔
            v ∈ x :: a :: (Q ++ [c]) := by
          intro v; rw [hQ]; conv_rhs => rw [hD₀]
          simp; tauto
        have hReg : Region H S (x :: a :: (Q ++ [c])) S
            (d₀ :: q :: (Q'' ++ c :: x :: a :: D.dropLast)) :=
          ⟨subset_rfl, fun v _ hvc => ⟨fun h => hvc ((hcyc v).2 h), fun w hw _ => hw⟩⟩
        exact two_apex hN hrotG hReg hzS hℓS (fun h => hzn ((hcyc z).1 h))
          (fun h => hℓn ((hcyc ℓ).1 h)) hzd₀ hqz.symm hℓd₀ hℓq'
    obtain ⟨us, hus, hnb, hNT', hadj⟩ := T.delete hrot (by simp; omega) hfree
    -- `us ≠ []` when nothing was deleted before (else `a` would see the next vertex)
    have husD : D = [] → us ≠ [] := by
      rintro rfl rfl
      have hY0 := hDY rfl
      subst hY0
      obtain ⟨q₂, Q₃, rfl⟩ : ∃ q₂ Q₃, Q'' = q₂ :: Q₃ := by
        rcases Q'' with _ | ⟨q₂, Q₃⟩
        · rw [hQ] at hQ2; simp at hQ2
        · exact ⟨q₂, Q₃, rfl⟩
      have hNT'' : T.NT H (S'.erase q) ([] ++ a :: q₂ :: (Q₃ ++ [c, x])) := by
        have := T.rotate_append (A := q₂ :: (Q₃ ++ [c, x])) (B := [a]) (by simpa using hNT')
        simpa using this
      have hadq₂ := T.adj_mid hNT''
      have := hPc a q₂ (by simp) (by rw [hQ]; simp) hadq₂
      rw [hQ] at this
      exact ConsecIn.not_gap (A := []) (M := [q]) (B := Q₃ ++ [c]) (by simp)
        (by rw [hQ] at hPnd; simpa using hPnd) (by simpa using this)
    -- the recursive call
    have hmem' : ∀ v, v ∈ S'.erase q ↔ v ∈ S ∧ v ∉ D ++ [q] := by
      intro v
      rw [Finset.mem_erase, hmem v]
      simp only [List.mem_append, List.mem_singleton, not_or]
      tauto
    have hNT'' : T.NT H (S'.erase q) (x :: a :: ((Y ++ us) ++ Q'' ++ [c])) := by
      have := T.rotate_append (A := Q'' ++ [c]) (B := x :: a :: (Y ++ us)) (by simpa using hNT')
      simpa using this
    have hus' : ∀ u ∈ us, u ∈ S ∧ u ∉ x :: a :: (Q ++ [c]) := by
      intro u hu
      obtain ⟨huS', hun⟩ := hus u hu
      obtain ⟨huS, huD⟩ := (hmem u).1 huS'
      refine ⟨huS, fun h => ?_⟩
      rw [hQ] at h
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h hun
      tauto
    obtain ⟨Y', S'', h1, h2, h3, h4⟩ := ih (D ++ [q]) (Y ++ us) (S'.erase q) (by rw [hQ]; simp)
      hNT'' hmem'
      (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨a1, a2, d, hd, hyd⟩ := hY y hy
          exact ⟨a1, a2, d, by simp [hd], hyd⟩
        · obtain ⟨a1, a2⟩ := hus' y hy
          exact ⟨a1, a2, q, by simp, (hadj y hy).symm⟩)
      (by simp)
      (by
        intro d hd
        rw [List.getLast?_concat] at hd
        simp only [Option.mem_def, Option.some.injEq] at hd
        subst hd
        by_cases hus0 : us = []
        · subst hus0
          have hDne : D ≠ [] := fun h => husD h rfl
          have hYne : Y ≠ [] := by
            intro h; subst h
            obtain ⟨d₀, hd₀⟩ : ∃ d₀, D.getLast? = some d₀ :=
              ⟨_, List.getLast?_eq_some_getLast hDne⟩
            obtain ⟨ℓ, hℓ, -⟩ := hlast d₀ hd₀
            simp at hℓ
          refine ⟨Y.getLast hYne, by simp [List.getLast?_eq_some_getLast hYne], ?_⟩
          exact hℓq _ (List.getLast?_eq_some_getLast hYne)
        · refine ⟨us.getLast hus0, ?_, (hadj _ (List.getLast_mem hus0)).symm⟩
          rw [List.getLast?_append_of_ne_nil _ hus0, List.getLast?_eq_some_getLast hus0]
          rfl)
      (by
        intro d hd y hyS hyn hdy
        rcases List.mem_append.mp hd with hd | hd
        · exact List.mem_append_left _ (hcomp d hd y hyS hyn hdy)
        · simp only [List.mem_singleton] at hd
          subst hd
          have hyS' : y ∈ S' := (hmem y).2 ⟨hyS, fun h => hyn (by rw [hQ]; simp [h])⟩
          rcases hnb y hyS' hdy with h | h | h
          · exfalso; apply hyn
            rw [hlhead] at h
            have := List.mem_of_mem_head? h
            rw [hQ]; simp at this ⊢; tauto
          · rw [hllast] at h
            have := List.mem_of_mem_getLast? h
            rcases List.mem_cons.mp this with h' | h'
            · exact absurd (by simp [h']) hyn
            · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ h)
    exact ⟨Y', S'', h1, h2, h3, h4⟩

end NTCalc

end ThomassenManyColourings
