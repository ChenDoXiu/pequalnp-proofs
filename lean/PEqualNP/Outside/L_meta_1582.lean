import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  intro q m N L i0 T0 _ hm _ _ _ hmeet _ hsubset hcard
  let Dom0 (x : Fin N → Bool) : Prop :=
    (∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true
  have upward (x y : Fin N → Bool) (hx : Dom0 x)
      (hxy : ∀ v : Fin N, x v = true → y v = true) : Dom0 y := by
    rcases hx with ⟨v, hv, htrue⟩ | houtside
    · exact Or.inl ⟨v, hv, hxy v htrue⟩
    · exact Or.inr fun v hv => hxy v (houtside v hv)
  have manyOutside (t : Fin N) (ht : t ≠ i0) :
      m - 1 ≤ (T0.filter (fun v => v ∉ L t)).card := by
    have hsmall : (T0 ∩ L t).card ≤ 1 := by
      rw [← hmeet i0 t ht.symm]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hvT, hvt⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_inter.mpr ⟨hsubset hvT, hvt⟩
    rw [Finset.filter_notMem_eq_sdiff]
    have hsum := Finset.card_sdiff_add_card_inter T0 (L t)
    omega
  have coLine (t : Fin N) : Dom0 (fun v => decide (v ∉ L t)) := by
    by_cases ht : t = i0
    · subst t
      exact Or.inr fun v hv => by simp [hv]
    · have hcount := manyOutside t ht
      have hpos : 0 < (T0.filter (fun v => v ∉ L t)).card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      obtain ⟨hvT, hvt⟩ := Finset.mem_filter.mp hv
      exact Or.inl ⟨v, hvT, by simp [hvt]⟩
  refine ⟨upward, coLine, manyOutside, ?_, coLine i0, ?_, ?_⟩
  · intro x hx
    exact Or.inl ⟨x, hx, by simp⟩
  · intro r _
    exact Or.inr fun v hv => by simp [hv]
  · intro t
    constructor
    · apply decide_eq_false
      rintro ⟨v, hv, htrue⟩
      exact (of_decide_eq_true htrue) hv
    · intro p hp
      constructor
      · exact upward (fun v => decide (v ∉ L t)) (fun v => decide (v ∉ L t ∨ v = p))
          (coLine t) fun v hv => by
            have hvt : v ∉ L t := of_decide_eq_true hv
            simp [hvt]
      · apply decide_eq_true
        exact ⟨p, hp, by simp⟩
