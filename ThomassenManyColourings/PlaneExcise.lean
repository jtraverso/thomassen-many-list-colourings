/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThomassenManyColourings.PlaneApex

/-!
# Excising the inside of a triangle (layer B, part 10)

Let `S₁ ⊆ S` carry a near-triangulation with outer cycle `p q r` whose other vertices are interior
vertices of `S` with all their neighbours in `S₁`. Deleting them leaves `T = (S \ S₁) ∪ {p, q, r}`,
with the restricted plane map (`Grotzsch.restrictMap`). Faces of the old map avoiding the deleted
vertices survive; a face through a deleted vertex is a triangle whose other two vertices lie on
`p q r`, and around each of `p, q, r` the restricted rotation skips the deleted neighbours and
lands on the next triangle vertex, so the new face is the triangle `p q r` (`PNT.excise3`).
-/

@[expose] public section

namespace ThomassenManyColourings

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] [Fintype V] {H : SimpleGraph V} {S : Finset V}

omit [DecidableEq V] [Fintype V] in
/-- Two vertices of `{p, q, r}` both different from two distinct ones coincide. -/
theorem uniq3 {p q r a b x y : V} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (ha : a = p ∨ a = q ∨ a = r) (hb : b = p ∨ b = q ∨ b = r) (hx : x = p ∨ x = q ∨ x = r)
    (hy : y = p ∨ y = q ∨ y = r) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a)
    (hyb : y ≠ b) : x = y := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | rfl | (exfalso; contradiction)

set_option maxHeartbeats 16000000 in
-- the face analysis of the restricted map exceeds the default heartbeat budget
/-- **The interface field `excise3`** for plane near-triangulations. -/
theorem PNT.excise3 {c : List V} {S₁ : Finset V} {p q r : V} (h : PNT H S c)
    (h₁ : PNT H S₁ [p, q, r]) (hS₁ : S₁ ⊆ S)
    (hint : ∀ u ∈ S₁, u ∉ [p, q, r] → u ∉ c ∧ ∀ w ∈ S, H.Adj u w → w ∈ S₁) :
    PNT H ((S \ S₁) ∪ {p, q, r}) c := by
  classical
  set T := (S \ S₁) ∪ {p, q, r} with hT
  have hpq : H.Adj p q := h₁.adj (cycSucc_cons_cons _ _ _)
  have hqr : H.Adj q r := h₁.adj (Or.inl ⟨[p], [], rfl⟩)
  have hrp : H.Adj r p := h₁.adj (Or.inr ⟨[q], rfl⟩)
  have hpq' : p ≠ q := hpq.ne
  have hqr' : q ≠ r := hqr.ne
  have hpr' : p ≠ r := hrp.ne.symm
  let in3 : V → Prop := fun v => v = p ∨ v = q ∨ v = r
  have hpS₁ : p ∈ S₁ := h₁.subset p (by simp)
  have hqS₁ : q ∈ S₁ := h₁.subset q (by simp)
  have hrS₁ : r ∈ S₁ := h₁.subset r (by simp)
  have memT : ∀ v, v ∈ T ↔ (v ∈ S ∧ v ∉ S₁) ∨ in3 v := by
    intro v
    simp only [hT, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      in3]
  have hTS : T ⊆ S := by
    intro v hv
    rcases (memT v).1 hv with ⟨hv, -⟩ | e
    · exact hv
    · rcases e with rfl | rfl | rfl
      · exact hS₁ hpS₁
      · exact hS₁ hqS₁
      · exact hS₁ hrS₁
  have in3T : ∀ v, in3 v → v ∈ T := fun v hv => (memT v).2 (Or.inr hv)
  have hS₁T : ∀ v, v ∈ S₁ → v ∈ T → in3 v := by
    intro v h1 hv
    rcases (memT v).1 hv with ⟨-, h2⟩ | e
    · exact absurd h1 h2
    · exact e
  have hnot3 : ∀ z, ¬ in3 z → z ∉ [p, q, r] := by
    intro z hz hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    exact hz hz'
  have hout : ∀ z ∈ S, z ∉ T → z ∈ S₁ ∧ ¬ in3 z := by
    intro z hz hzT
    by_cases h1 : z ∈ S₁
    · exact ⟨h1, fun e => hzT (in3T z e)⟩
    · exact absurd ((memT z).2 (Or.inl ⟨hz, h1⟩)) hzT
  have hnb : ∀ z ∈ S, z ∉ T → ∀ w ∈ S, H.Adj z w → w ∈ S₁ := by
    intro z hz hzT
    obtain ⟨h1, h3⟩ := hout z hz hzT
    exact (hint z h1 (hnot3 z h3)).2
  have hzc : ∀ z ∈ S, z ∉ T → z ∉ c := by
    intro z hz hzT
    obtain ⟨h1, h3⟩ := hout z hz hzT
    exact (hint z h1 (hnot3 z h3)).1
  have hcT : ∀ v ∈ c, v ∈ T := by
    intro v hv
    by_contra hvT
    exact hzc v (h.subset v hv) hvT hv
  have adj3 : ∀ s t, in3 s → in3 t → s ≠ t → H.Adj s t := by
    intro s t hs ht hst
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hst
      | exact hpq | exact hqr | exact hrp
      | exact hpq.symm | exact hqr.symm | exact hrp.symm
  -- connectivity of `T`
  have htri : ∀ s, in3 s → (indG H T).Reachable s p := by
    intro s hs
    rcases hs with rfl | rfl | rfl
    · rfl
    · exact (indG_adj_of hpq.symm (in3T _ (Or.inr (Or.inl rfl))) (in3T _ (Or.inl rfl))).reachable
    · exact (indG_adj_of hrp (in3T _ (Or.inr (Or.inr rfl))) (in3T _ (Or.inl rfl))).reachable
  have key : ∀ (z b : V) (w : (indG H S).Walk z b), b ∈ T →
      (z ∈ T → (indG H T).Reachable z b) ∧ (z ∉ T → (indG H T).Reachable p b) := by
    intro z b w
    induction w with
    | nil => intro hb; exact ⟨fun _ => .refl _, fun hz => absurd hb hz⟩
    | @cons z z' b hzz' w ih =>
      intro hb
      obtain ⟨ih1, ih2⟩ := ih hb
      have hzS : z ∈ S := Finset.mem_coe.mp hzz'.2.1
      have hz'S : z' ∈ S := Finset.mem_coe.mp hzz'.2.2
      constructor
      · intro hz
        by_cases hz' : z' ∈ T
        · exact (indG_adj_of hzz'.1 hz hz').reachable.trans (ih1 hz')
        · have h1 := hnb z' hz'S hz' z hzS hzz'.1.symm
          exact (htri z (hS₁T z h1 hz)).trans (ih2 hz')
      · intro hz
        by_cases hz' : z' ∈ T
        · have h1 := hnb z hzS hz z' hz'S hzz'.1
          exact (htri z' (hS₁T z' h1 hz')).symm.trans (ih1 hz')
        · exact ih2 hz'
  have hreachT : ∀ a ∈ T, ∀ b ∈ T, (indG H T).Reachable a b := by
    intro a ha b hb
    obtain ⟨w⟩ := h.2.2.2.2.1 a (hTS ha) b (hTS hb)
    exact (key a b w hb).1 ha
  -- the restricted map
  obtain ⟨M, hM⟩ := h.2.2.2.2.2
  have hH : indG H T ≤ indG H S := restrict_mono hTS
  set M' := Grotzsch.restrictMap M hH with hM'
  let td := Grotzsch.toDart hH
  have hR : ∀ d : (indG H T).Dart, (M.facePerm (td d)).snd ∈ T →
      td (M'.facePerm d) = M.facePerm (td d) := by
    intro d hd
    refine restrictMap_facePerm_eq M hH d ⟨(M.facePerm (td d)).adj.1, ?_, Finset.mem_coe.mpr hd⟩
    rw [face_fst']
    exact d.adj.2.2
  have hrotφ : ∀ x : (indG H S).Dart, M.rot x = M.facePerm x.symm := by
    intro x; rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm]
  -- a face through a deleted vertex
  have hstep : ∀ d : (indG H T).Dart, ¬ IsOuter c d → (M.facePerm (td d)).snd ∉ T →
      in3 d.fst ∧ in3 d.snd ∧ (M'.facePerm d).fst = d.snd ∧ (M'.facePerm d).snd ≠ d.fst ∧
        ¬ IsOuter c (M'.facePerm d) ∧ (M.facePerm (td (M'.facePerm d))).snd ∉ T := by
    intro d hdo hz
    set e := td d with he
    have heo : ¬ IsOuter c e := hdo
    obtain ⟨hbz, hza, hzS⟩ := tri_adj hM e heo
    have haS₁ : d.fst ∈ S₁ := hnb _ hzS hz _ (hTS (Finset.mem_coe.mp d.adj.2.1)) hza
    have hbS₁ : d.snd ∈ S₁ := hnb _ hzS hz _ (hTS (Finset.mem_coe.mp d.adj.2.2)) hbz.symm
    have ha3 : in3 d.fst := hS₁T _ haS₁ (Finset.mem_coe.mp d.adj.2.1)
    have hb3 : in3 d.snd := hS₁T _ hbS₁ (Finset.mem_coe.mp d.adj.2.2)
    -- the restricted rotation from `(b, a)`
    let N := Nat.find (Grotzsch.exists_rot_pow_inH M hH d.symm)
    have hNspec := Nat.find_spec (Grotzsch.exists_rot_pow_inH M hH d.symm)
    have hNmin : ∀ m < N, ¬ (0 < m ∧ Grotzsch.InH (indG H T) ((M.rot ^ m) (td d.symm))) :=
      fun m hm => Nat.find_min (Grotzsch.exists_rot_pow_inH M hH d.symm) hm
    have hφ' : td (M'.facePerm d) = (M.rot ^ N) (td d.symm) := by
      rw [PlaneMap.facePerm_apply]
      exact Grotzsch.subRot_apply M hH d.symm
    let g : ℕ → (indG H S).Dart := fun m => (M.rot ^ m) (td d.symm)
    have hgfst : ∀ m, (g m).fst = d.snd := fun m => Grotzsch.rot_pow_fst M m _
    have hgsucc : ∀ m, g (m + 1) = M.facePerm (g m).symm := by
      intro m
      show (M.rot ^ (m + 1)) _ = _
      rw [pow_succ', Perm.mul_apply, hrotφ]
    have hg1 : g 1 = M.facePerm e := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, hgsucc]
      congr 1
    have hoff : ∀ m, 0 < m → m < N → (g m).snd ∉ T := by
      intro m hm0 hmN hmT
      apply hNmin m hmN
      refine ⟨hm0, (g m).adj.1, ?_, Finset.mem_coe.mpr hmT⟩
      rw [hgfst]
      exact d.adj.2.2
    have hgS : ∀ m, (g m).snd ∈ S := fun m => Finset.mem_coe.mp (g m).adj.2.2
    have hnout : ∀ m, 0 < m → m < N → ¬ IsOuter c (g m).symm := by
      intro m hm0 hmN ho
      exact hzc _ (hgS m) (hoff m hm0 hmN) ho.mem.1
    have hS₁seq : ∀ m, 1 ≤ m → m ≤ N → (g m).snd ∈ S₁ := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro _
        rw [hg1]
        exact (hout _ hzS hz).1
      | succ m hm ih =>
        intro hmN
        have hmo := hnout m (by omega) (by omega)
        obtain ⟨-, hza', -⟩ := tri_adj hM _ hmo
        rw [hgsucc]
        exact hnb _ (hgS m) (hoff m (by omega) (by omega)) _
          (Finset.mem_coe.mp (M.facePerm (g m).symm).adj.2.2) hza'.symm
    have hN2 : 2 ≤ N := by
      by_contra hN
      have hN1 : N = 1 := by have := hNspec.1; omega
      have hin := hNspec.2
      have hT1 : (g 1).snd ∈ T := by
        have h' : (g N).snd ∈ T := Finset.mem_coe.mp hin.2.2
        rwa [hN1] at h'
      rw [hg1] at hT1
      exact hz hT1
    have htT : (g N).snd ∈ T := Finset.mem_coe.mp hNspec.2.2.2
    have ht3 : in3 (g N).snd := hS₁T _ (hS₁seq N (by omega) le_rfl) htT
    have hsnd : (M'.facePerm d).snd = (g N).snd := by
      have := congrArg (fun x : (indG H S).Dart => x.snd) hφ'
      exact this
    -- the face after `(b, t)` returns to the last deleted neighbour
    have hbad : (M.facePerm (td (M'.facePerm d))).snd ∉ T := by
      rw [hφ']
      obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      have hko := hnout k (by omega) (by omega)
      have h3 := hM.2 _ hko
      rw [facePerm_pow_three] at h3
      have e1 : (M.rot ^ N) (td d.symm) = M.facePerm (g k).symm := by
        rw [hk]; exact hgsucc k
      rw [e1, ← face_fst' M (M.facePerm (M.facePerm (g k).symm)), h3]
      exact hoff k (by omega) (by omega)
    refine ⟨ha3, hb3, face_fst' M' d, ?_, ?_, hbad⟩
    · -- the restricted rotation does not fix `(b, a)`
      intro hta
      have hfix : M'.rot d.symm = d.symm := by
        rw [← PlaneMap.facePerm_apply]
        exact dart_ext' (face_fst' M' d) hta
      obtain ⟨t₀, ht₀, ht₀a, ht₀b⟩ : ∃ t₀, in3 t₀ ∧ t₀ ≠ d.fst ∧ t₀ ≠ d.snd := by
        have hab : d.fst ≠ d.snd := d.adj.1.ne
        rcases ha3 with ea | ea | ea <;> rcases hb3 with eb | eb | eb <;> rw [ea, eb] at hab
        all_goals first
          | exact absurd rfl hab
          | exact ⟨p, Or.inl rfl, by rw [ea]; exact hpq', by rw [eb]; exact hpr'⟩
          | exact ⟨p, Or.inl rfl, by rw [ea]; exact hpr', by rw [eb]; exact hpq'⟩
          | exact ⟨q, Or.inr (Or.inl rfl), by rw [ea]; exact hpq'.symm, by rw [eb]; exact hqr'⟩
          | exact ⟨q, Or.inr (Or.inl rfl), by rw [ea]; exact hqr', by rw [eb]; exact hpq'.symm⟩
          | exact ⟨r, Or.inr (Or.inr rfl), by rw [ea]; exact hpr'.symm, by rw [eb]; exact hqr'.symm⟩
          | exact ⟨r, Or.inr (Or.inr rfl), by rw [ea]; exact hqr'.symm, by rw [eb]; exact hpr'.symm⟩
      let d₀ : (indG H T).Dart := ⟨(d.snd, t₀), indG_adj_of (adj3 _ _ hb3 ht₀ (Ne.symm ht₀b))
        (in3T _ hb3) (in3T _ ht₀)⟩
      have := rot_fixed_unique M' hfix (e' := d₀) rfl
      exact ht₀a (congrArg (fun x : (indG H T).Dart => x.snd) this)
    · intro ho
      have ho' : IsOuter c (td (M'.facePerm d)) := ho
      have hfo := hM.1 _ ho'
      exact hbad (hcT _ hfo.mem.2)
  refine ⟨h.nodup, h.two_le, hcT, fun u v huv => h.adj huv, hreachT, M', fun d hd => ?_,
    fun d hd => ?_⟩
  · -- outer darts stay outer
    have hd' : IsOuter c (td d) := hd
    have hf := hM.1 _ hd'
    have e := hR d (hcT _ hf.mem.2)
    have : IsOuter c (td (M'.facePerm d)) := by rw [e]; exact hf
    exact this
  · rw [facePerm_pow_three]
    have hdo : ¬ IsOuter c (td d) := hd
    by_cases hg : (M.facePerm (td d)).snd ∈ T
    · -- a surviving triangle
      have h3 := hM.2 _ hdo
      rw [facePerm_pow_three] at h3
      have e1 := hR d hg
      have hg1 : (M.facePerm (td (M'.facePerm d))).snd ∈ T := by
        rw [e1, ← face_fst' M (M.facePerm (M.facePerm (td d))), h3]
        exact d.adj.2.1
      have e2 := hR _ hg1
      rw [e1] at e2
      have hg2 : (M.facePerm (td (M'.facePerm (M'.facePerm d)))).snd ∈ T := by
        rw [e2, h3]
        exact d.adj.2.2
      have e3 := hR _ hg2
      rw [e2, h3] at e3
      exact Grotzsch.toDart_injective hH e3
    · -- the new triangle `p q r`
      obtain ⟨ha3, hb3, f1, n1, o1, b1⟩ := hstep d hd hg
      obtain ⟨-, ht3, f2, n2, o2, b2⟩ := hstep _ o1 b1
      obtain ⟨-, hs3, f3, n3, -, -⟩ := hstep _ o2 b2
      have hab : d.fst ≠ d.snd := d.adj.1.ne
      set d₁ := M'.facePerm d
      set d₂ := M'.facePerm d₁
      set d₃ := M'.facePerm d₂
      have ht₁b : d₁.snd ≠ d.snd := by rw [← f1]; exact d₁.adj.1.ne.symm
      have ht₂t₁ : d₂.snd ≠ d₁.snd := by rw [← f2]; exact d₂.adj.1.ne.symm
      have ht₂b : d₂.snd ≠ d.snd := by rw [← f1]; exact n2
      have ha : d₂.snd = d.fst := uniq3 hpq' hqr' hpr' hb3 ht3 hs3 ha3 (Ne.symm ht₁b) ht₂b ht₂t₁
        hab (Ne.symm n1)
      have ht₃a : d₃.snd ≠ d.fst := by rw [← ha, ← f3]; exact d₃.adj.1.ne.symm
      have ht₃t₁ : d₃.snd ≠ d₁.snd := by rw [← f2]; exact n3
      have hb : d₃.snd = d.snd := by
        obtain ⟨-, hu3, -, -, -, -⟩ := hstep _ (by
          intro ho
          exact (hstep _ o2 b2).2.2.2.2.1 ho) (hstep _ o2 b2).2.2.2.2.2
        exact uniq3 hpq' hqr' hpr' ha3 ht3 hu3 hb3 (Ne.symm n1) ht₃a ht₃t₁ hab.symm ht₁b.symm
      exact dart_ext' (by rw [f3, ha]) hb

end ThomassenManyColourings
