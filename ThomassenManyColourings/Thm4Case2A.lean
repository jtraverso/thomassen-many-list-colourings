/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.Thm4Case1G

/-!
# Theorem 4, Case 2: cutting off a fan at `v_k`

An interior vertex `u` joined to `v_m, v_{m+1}, …, v_{k-1}, v_k` (with `v_{m+1} … v_{k-1}`
nonempty) cuts `G` along `v_m u v_k` into the fan `u v_m … v_k` (`fan_fill`) and a region `G'`
with outer cycle `x a v₃ … v_m u c` (`Case1Hyp.fan_cut`). A colouring of `G'` in which `u` avoids
two colours `α, β` of `L(v_{k-1}) \ {g c}` extends to the fan (`colFrom_two_last`).
-/

@[expose] public section

namespace ThomassenManyColourings

variable {V : Type*} [DecidableEq V] {C : Type*} [DecidableEq C]

/-- The inner path of a fan can be coloured if its last list keeps two colours `α, β` different
from the end colour `q` and from `γ`. -/
theorem colFrom_two_last {γ p q α β : C} {Ms : List (Finset C)} {Lw : Finset C}
    (hMs : ∀ M ∈ Ms, 3 ≤ M.card) (hα : α ∈ Lw) (hβ : β ∈ Lw) (hαβ : α ≠ β) (hαq : α ≠ q)
    (hβq : β ≠ q) (hαγ : α ≠ γ) (hβγ : β ≠ γ) : ColFrom γ p (Ms ++ [Lw]) q := by
  rw [colFrom_snoc]
  obtain ⟨d, hd⟩ := ach_nonempty (γ := γ) Ms {p} hMs (Finset.singleton_nonempty p)
  by_cases hdα : d = α
  · refine ⟨β, hβ, hβγ, hβq, (colFrom_iff γ p β Ms).2 ⟨d, hd, ?_⟩⟩
    rw [hdα]; exact hαβ
  · exact ⟨α, hα, hαγ, hαq, (colFrom_iff γ p α Ms).2 ⟨d, hd, hdα⟩⟩

namespace NTCalc

variable {T : NTCalc V}

omit [DecidableEq C] in
set_option maxHeartbeats 16000000 in
/-- **Cutting off the fan of `u` at `v_k`**: the outer path is `A v_m M c` (`v_m` may be `a`). -/
theorem Case1Hyp.fan_cut {H : SimpleGraph V} {S : Finset V} {x a c : V} {Q : List V}
    {L : V → Finset C} {g : V → C} (hc : T.Case1Hyp H S x a c Q L g) {A M : List V} {vm u : V}
    (hP : a :: (Q ++ [c]) = A ++ vm :: (M ++ [c])) (hM : M ≠ []) (huS : u ∈ S)
    (hu : u ∉ x :: a :: (Q ++ [c]))
    (hum : H.Adj u vm) (huM : ∀ q ∈ M, H.Adj u q) (huc : H.Adj u c) :
    ∃ S₂ : Finset V, T.NT H S₂ (x :: (A ++ [vm, u, c])) ∧
      (∀ v, v ∈ S₂ ↔ v ∈ S ∧ v ∉ M) ∧
      Region H S (x :: a :: (Q ++ [c])) S₂ (x :: (A ++ [vm, u, c])) ∧
      ∀ v ∈ M, ∀ z ∈ S, H.Adj v z → z ∈ M ∨ z = u ∨ z = c ∨ z = vm := by
  classical
  have hnd := T.nodup hc.nt
  have hPnd : (a :: (Q ++ [c])).Nodup := (List.nodup_cons.mp hnd).2
  have hxP : x ∉ a :: (Q ++ [c]) := (List.nodup_cons.mp hnd).1
  have hPnd' : (A ++ vm :: (M ++ [c])).Nodup := hP ▸ hPnd
  -- `vm` and `c` are not adjacent
  have hvmc : ¬ H.Adj vm c := by
    intro h
    have := hc.chordless vm c (by rw [hP]; simp) (by simp) h
    rw [hP] at this
    exact ConsecIn.not_gap hM hPnd' this
  have hrot : T.NT H S (vm :: (M ++ c :: (x :: A))) := by
    have := T.rotate_append (A := x :: A) (B := vm :: (M ++ [c]))
      (by have h := hc.nt; rw [hP] at h; simpa using h)
    simpa using this
  have hcyc : ∀ v, v ∈ vm :: (M ++ c :: (x :: A)) ↔ v ∈ x :: a :: (Q ++ [c]) := by
    intro v; rw [hP]; simp; tauto
  obtain ⟨S₁, S₂, h₁, h₂, hU, hI, hX⟩ := T.cut (x := vm) (y := c) (u := u) (l₁ := M)
    (l₂ := x :: A) hrot huS (fun h => hu ((hcyc u).1 h)) hum huc hvmc
  have h₁' : T.NT H S₁ (u :: vm :: (M ++ [c])) := T.rotate_back (by simpa using h₁)
  have h₂' : T.NT H S₂ (x :: (A ++ [vm, u, c])) := by
    have := T.rotate_append (A := [c]) (B := x :: (A ++ [vm, u])) (by simpa using h₂)
    simpa using this
  have hmem : ∀ v, v ∈ S₁ → v ∈ S₂ → v = vm ∨ v = c ∨ v = u := by
    intro v h1 h2
    have : v ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hI] at this; simpa using this
  have hR₀ : Region H S (x :: a :: (Q ++ [c])) S (vm :: (M ++ c :: (x :: A))) :=
    ⟨subset_rfl, fun v _ hvc => ⟨fun h => hvc ((hcyc v).2 h), fun w hw _ => hw⟩⟩
  have hR₁ : Region H S (x :: a :: (Q ++ [c])) S₁ (u :: vm :: (M ++ [c])) := by
    refine hR₀.piece (c₂ := x :: (A ++ [vm, u, c])) hU ?_ hX ?_
      (fun v hv => T.subset h₂' v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
  have hR₂ : Region H S (x :: a :: (Q ++ [c])) S₂ (x :: (A ++ [vm, u, c])) := by
    refine hR₀.piece' (c₁ := u :: vm :: (M ++ [c])) hU ?_ hX ?_
      (fun v hv => T.subset h₁' v hv)
    · intro v h1 h2; rcases hmem v h1 h2 with rfl | rfl | rfl <;> simp
    · intro v hv; simp only [List.mem_cons, List.mem_append] at hv ⊢; tauto
  -- the fan fills its region
  have hchain : (vm :: (M ++ [c])).IsChain H.Adj := (List.isChain_cons_cons.mp (NT_chain h₁')).2
  have hF := fan_fill hc.nosep u _ (vm :: (M ++ [c])) S₁ rfl h₁' hR₁ hchain (by
    intro q hq
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | hq | rfl
    · exact hum
    · exact huM q hq
    · exact huc)
  have hQ₀M : ∀ v ∈ M, v ∉ x :: (A ++ [vm, u, c]) := by
    intro v hv h
    have hvP : v ∈ a :: (Q ++ [c]) := by rw [hP]; simp [hv]
    have h2 := List.nodup_append.mp hPnd'
    have h3 := List.nodup_cons.mp h2.2.1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h
    · exact hxP (h ▸ hvP)
    · exact h2.2.2 v h v (by simp [hv]) rfl
    · exact h3.1 (by rw [← h]; simp [hv])
    · exact hu (by rw [← h]; exact List.mem_cons_of_mem _ hvP)
    · exact (List.nodup_append.mp h3.2).2.2 v hv v (by simp [h]) rfl
  have hMS₂ : ∀ v ∈ M, v ∉ S₂ := by
    intro v hv h2
    have h1 : v ∈ S₁ := T.subset h₁' v (by simp [hv])
    rcases hmem v h1 h2 with e | e | e <;> exact hQ₀M v hv (by rw [e]; simp)
  refine ⟨S₂, h₂', fun v => ⟨fun hv => ⟨hU ▸ Finset.mem_union_right _ hv, fun hM' => hMS₂ v hM' hv⟩,
    fun ⟨hvS, hvM⟩ => ?_⟩, hR₂, ?_⟩
  · rcases Finset.mem_union.mp (hU ▸ hvS) with h | h
    · rcases hF v h with rfl | h'
      · exact T.subset h₂' v (by simp)
      · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h'
        rcases h' with rfl | h' | rfl
        · exact T.subset h₂' v (by simp)
        · exact absurd h' hvM
        · exact T.subset h₂' v (by simp)
    · exact h
  · intro v hv z hzS hvz
    have h1 : v ∈ S₁ := T.subset h₁' v (by simp [hv])
    have hz1 : z ∈ S₁ := by
      rcases Finset.mem_union.mp (hU ▸ hzS) with h | h
      · exact h
      · rcases hX v h1 z h hvz with h' | h'
        · exact absurd h' (hMS₂ v hv)
        · exact h'
    rcases hF z hz1 with rfl | h'
    · right; left; rfl
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | h' | rfl
      · right; right; right; rfl
      · left; exact h'
      · right; right; left; rfl

end NTCalc

end ThomassenManyColourings
