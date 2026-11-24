import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

-- Join the two outputs with an OR when no AND reads an AND through its cone.
-- For nested ANDs, distinguish whether the upper gate feeds both outputs.
-- The wire and cone prefix calculations follow the corresponding lemmas in L_meta_1751.

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1872_2
    (knownFlat :
      let diff : Finset (Fin 13) := [0, 1, 3, 9].toFinset
      let pos (p l : Fin 13) :=
        List.ofFn (fun x : Fin 13 => decide (x = p)) ++ List.ofFn (fun x : Fin 13 => decide (x = l))
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun x : Fin 13 => decide (x ∈ Q)) ++
          List.ofFn (fun x : Fin 13 => decide (∀ p ∈ Q, p - x ∉ diff))
      let good (Q : Finset (Fin 13)) :=
        Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2

      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
        ((∀ p l : Fin 13, p - l ∈ diff → C.eval (pos p l) = true) ∧
          (∀ Q : Finset (Fin 13), good Q → C.eval (neg Q) = false)) →
        (¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) →
        64 ≤ C.size)
    (boundShared :
      let lines := singerLines3
      let ipos (p l : Fin 13) := incidenceInput [p].toFinset [l].toFinset
      let ineg (Q : Finset (Fin 13)) := incidenceInput Q (missLines lines Q)
      let wire (C : Circuit) (i : ℕ) (I : List Bool) := (C.wires I).getD i false
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C →
        a < 26 + C.size → b < 26 + C.size →
        (∀ p l : Fin 13, p ∈ lines l →
          wire C a (ipos p l) = true ∨ wire C b (ipos p l) = true) →
        (∀ Q : Finset (Fin 13), IsQuadrangle lines Q →
          wire C a (ineg Q) = false ∧ wire C b (ineg Q) = false) →
        (∀ t : Bool, ∃ p l : Fin 13, p ∈ lines l ∧ wire C a (ipos p l) = t ∧
          wire C b (ipos p l) = !t) →
        (∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
          InCone 26 C i j ∧ (∀ w ∈ [a, b], 26 + j = w ∨ (26 ≤ w ∧ InCone 26 C j (w - 26)))) →
        63 ≤ C.size)
    (boundSeparate :
      let lines := singerLines3
      let ipos (p l : Fin 13) := incidenceInput [p].toFinset [l].toFinset
      let ineg (Q : Finset (Fin 13)) := incidenceInput Q (missLines lines Q)
      let wire (C : Circuit) (i : ℕ) (I : List Bool) := (C.wires I).getD i false
      let nestedAt (C : Circuit) (j : ℕ) :=
        (gateAt C j).op = GateOp.and ∧ ∃ i, (gateAt C i).op = GateOp.and ∧ InCone 26 C i j
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C →
        a < 26 + C.size → b < 26 + C.size →
        (∀ p l : Fin 13, p ∈ lines l →
          wire C a (ipos p l) = true ∨ wire C b (ipos p l) = true) →
        (∀ Q : Finset (Fin 13), IsQuadrangle lines Q →
          wire C a (ineg Q) = false ∧ wire C b (ineg Q) = false) →
        (∀ t : Bool, ∃ p l : Fin 13, p ∈ lines l ∧ wire C a (ipos p l) = t ∧
          wire C b (ipos p l) = !t) →
        (∃ j, nestedAt C j) →
        (∀ j, nestedAt C j → ¬ (∀ w ∈ [a, b], 26 + j = w ∨ (26 ≤ w ∧ InCone 26 C j (w - 26)))) →
        63 ≤ C.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  let diff : Finset (Fin 13) := [0, 1, 3, 9].toFinset
  let pos (p l : Fin 13) :=
    List.ofFn (fun x : Fin 13 => decide (x = p)) ++ List.ofFn (fun x : Fin 13 => decide (x = l))
  let neg (Q : Finset (Fin 13)) :=
    List.ofFn (fun x : Fin 13 => decide (x ∈ Q)) ++
      List.ofFn (fun x : Fin 13 => decide (∀ p ∈ Q, p - x ∉ diff))
  let good (Q : Finset (Fin 13)) :=
    Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2

  let lines := singerLines3
  let ipos (p l : Fin 13) := incidenceInput [p].toFinset [l].toFinset
  let ineg (Q : Finset (Fin 13)) := incidenceInput Q (missLines lines Q)
  have line_iff : ∀ p l : Fin 13, p ∈ lines l ↔ p - l ∈ diff := by decide +kernel
  have quad_iff (Q : Finset (Fin 13)) : IsQuadrangle lines Q ↔ good Q := by
    have eqSet (l : Fin 13) : Q ∩ lines l = Q.filter (fun p => p - l ∈ diff) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter, line_iff]
    change (Q.card = 4 ∧ ∀ l : Fin 13, (Q ∩ lines l).card ≤ 2) ↔ _
    simp only [eqSet, good]
  have pos_eq (p l : Fin 13) : pos p l = ipos p l := by
    change _ = List.ofFn (fun x : Fin 13 => decide (x ∈ [p].toFinset)) ++
      List.ofFn (fun x : Fin 13 => decide (x ∈ [l].toFinset))
    simp only [List.mem_toFinset, List.mem_singleton, pos]
  have neg_eq (Q : Finset (Fin 13)) : neg Q = ineg Q := by
    have missing (l : Fin 13) : l ∈ missLines lines Q ↔ ∀ p ∈ Q, p - l ∉ diff := by
      change l ∈ Finset.univ.filter (fun l => Disjoint (lines l) Q) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, line_iff]
      exact ⟨fun h p hp hi => h hi hp, fun h p hi hp => h p hp hi⟩
    change _ = List.ofFn (fun x : Fin 13 => decide (x ∈ Q)) ++
      List.ofFn (fun x : Fin 13 => decide (x ∈ missLines lines Q))
    simp only [missing, neg]
  let wire (C : Circuit) (i : ℕ) (I : List Bool) := (C.wires I).getD i false
  let valid (C : Circuit) (a b : ℕ) :=
    Monotone2 C ∧ ReadsBack 26 C ∧ a < 26 + C.size ∧ b < 26 + C.size ∧
    (∀ p l : Fin 13, p ∈ lines l → wire C a (ipos p l) = true ∨ wire C b (ipos p l) = true) ∧
    (∀ Q : Finset (Fin 13), IsQuadrangle lines Q → wire C a (ineg Q) = false ∧ wire C b (ineg Q) = false) ∧
    ∀ t : Bool, ∃ p l : Fin 13, p ∈ lines l ∧ wire C a (ipos p l) = t ∧ wire C b (ipos p l) = !t
  let nestedAt (C : Circuit) (j : ℕ) :=
    (gateAt C j).op = GateOp.and ∧ ∃ i, (gateAt C i).op = GateOp.and ∧ InCone 26 C i j
  let shared (C : Circuit) (a b j : ℕ) :=
    ∀ w ∈ [a, b], 26 + j = w ∨ (26 ≤ w ∧ InCone 26 C j (w - 26))
  let nested (C : Circuit) := ∃ j, nestedAt C j
  let wiresFrom (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
      wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    exact List.foldl_append
  have length_wiresFrom (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wiresFrom]
    | cons g gs ih =>
      change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have getD_snoc_len {α : Type} (L : List α) (b d : α) (k : ℕ) (h : L.length = k) :
      (L ++ [b]).getD k d = b := by
    subst h
    simp
  have coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      have lenStep : (coneStep n cs g).length = cs.length + 1 := by
        change (cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])]).length = cs.length + 1
        simp
      rw [lenStep, List.length_cons]
      omega
  have coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
      (coneStep n cs g).getD m [] = cs.getD m [] := by
    exact List.getD_append _ _ _ _ hm
  have flat63 (C : Circuit) (a b : ℕ) (hmon : Monotone2 C) (hread : ReadsBack 26 C)
      (ha : a < 26 + C.size) (hb : b < 26 + C.size) (hflat : ¬ nested C)
      (hPos : ∀ p l : Fin 13, p - l ∈ diff → wire C a (pos p l) = true ∨ wire C b (pos p l) = true)
      (hNeg : ∀ Q : Finset (Fin 13), good Q → wire C a (neg Q) = false ∧ wire C b (neg Q) = false) :
      63 ≤ C.size := by
    let g : Gate := ⟨GateOp.or, [a, b]⟩
    let D : Circuit := ⟨C.gates ++ [g], 26 + C.gates.length⟩
    have hDSize : D.size = C.size + 1 := by
      change (C.gates ++ [g]).length = C.gates.length + 1
      simp
    have hDMon : Monotone2 D := by
      intro t ht
      change t ∈ C.gates ++ [g] at ht
      rw [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hmon t ht
      · simp [g]
    have atPrefix (i : ℕ) (hi : i < C.gates.length) : gateAt D i = gateAt C i := by
      change (C.gates ++ [g]).getD i ⟨GateOp.or, []⟩ = C.gates.getD i ⟨GateOp.or, []⟩
      exact List.getD_append _ _ _ _ hi
    have atLast : gateAt D C.gates.length = g := by
      change (C.gates ++ [g]).getD C.gates.length ⟨GateOp.or, []⟩ = g
      exact getD_snoc_len _ _ _ _ rfl
    have hDRead : ReadsBack 26 D := by
      intro j hj i hi
      by_cases hj' : j < C.gates.length
      · exact hread j hj' i (atPrefix j hj' ▸ hi)
      · change j < (C.gates ++ [g]).length at hj
        have he : j = C.gates.length := by
          simp only [List.length_append, List.length_singleton] at hj
          omega
        subst j
        rw [atLast] at hi
        change i ∈ [a,b] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
    have old (i : ℕ) (hi : (gateAt D i).op = GateOp.and) : i < C.gates.length := by
      by_contra hi'
      by_cases eq : i = C.gates.length
      · rw [eq, atLast] at hi
        cases hi
      · have ho : (C.gates ++ [g]).length ≤ i := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hx : gateAt D i = ⟨GateOp.or, []⟩ := by
          change (C.gates ++ [g]).getD i ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none ho, Option.getD_none]
        rw [hx] at hi
        cases hi
    have conePrefix (i j : ℕ) (hj : j < C.gates.length) : InCone 26 D i j ↔ InCone 26 C i j := by
      change i ∈ ((C.gates ++ [g]).foldl (coneStep 26) []).getD j [] ↔
        i ∈ (C.gates.foldl (coneStep 26) []).getD j []
      rw [List.foldl_append]
      change i ∈ (coneStep 26 (C.gates.foldl (coneStep 26) []) g).getD j [] ↔ _
      rw [coneStep_getD_lt 26 (C.gates.foldl (coneStep 26) []) g j]
      simpa only [coneFold_length, List.length_nil, Nat.zero_add] using hj
    have hDFlat : ¬ ∃ i j, (gateAt D i).op = GateOp.and ∧
        (gateAt D j).op = GateOp.and ∧ InCone 26 D i j := by
      rintro ⟨i, j, hi, hj, hcone⟩
      have hoi := old i hi
      have hoj := old j hj
      rw [atPrefix i hoi] at hi
      rw [atPrefix j hoj] at hj
      exact hflat ⟨j, hj, i, hi, (conePrefix i j hoj).mp hcone⟩
    have evalD (I : List Bool) (hi : I.length = 26) :
        D.eval I = (wire C a I || wire C b I) := by
      change (wiresFrom (C.gates ++ [g]) I).getD (26 + C.gates.length) false = _
      rw [wiresFrom_append]
      change (wiresFrom C.gates I ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom C.gates I).getD i false)]).getD
          (26 + C.gates.length) false = _
      have hlen : (wiresFrom C.gates I).length = 26 + C.gates.length := by
        rw [length_wiresFrom, hi]
      rw [getD_snoc_len _ _ _ _ hlen]
      change GateOp.or.eval [(wiresFrom C.gates I).getD a false, (wiresFrom C.gates I).getD b false] =
        ((wiresFrom C.gates I).getD a false || (wiresFrom C.gates I).getD b false)
      change ((wiresFrom C.gates I).getD a false ||
        ((wiresFrom C.gates I).getD b false || false)) = _
      simp only [Bool.or_false]
    have hLower : 64 ≤ D.size := by
      apply knownFlat D hDMon hDRead _ hDFlat
      constructor
      · intro p l he
        change D.eval (pos p l) = true
        rw [evalD _ (by simp [pos])]
        rcases hPos p l he with h | h
        · simp only [h, Bool.true_or]
        · simp only [h, Bool.or_true]
      · intro Q hq
        change D.eval (neg Q) = false
        rw [evalD _ (by simp [neg])]
        obtain ⟨h1, h2⟩ := hNeg Q hq
        rw [h1, h2]
        rfl
    omega
  have lower (C : Circuit) (a b : ℕ) (hValid : valid C a b) : 63 ≤ C.size := by
    obtain ⟨hM, hR, ha, hb, hp, hn, hexclusive⟩ := hValid
    by_cases hNest : nested C
    · by_cases hShared : ∃ j, nestedAt C j ∧ shared C a b j
      · obtain ⟨j, ⟨hj, i, hi, hij⟩, hCommon⟩ := hShared
        exact boundShared C a b hM hR ha hb hp hn hexclusive ⟨i, j, hi, hj, hij, hCommon⟩
      · exact boundSeparate C a b hM hR ha hb hp hn hexclusive hNest
          (fun j hj hCommon => hShared ⟨j, hj, hCommon⟩)
    · refine flat63 C a b hM hR ha hb hNest ?_ ?_
      · intro p l he
        rw [pos_eq]
        exact hp p l ((line_iff p l).mpr he)
      · intro Q hQ
        rw [neg_eq]
        exact hn Q ((quad_iff Q).mpr hQ)
  intro C a b hm hr ha hb
  dsimp only
  intro hp hn hA hB
  apply lower C a b
  refine ⟨hm, hr, ha, hb, ?_, ?_, ?_⟩
  · intro p l he
    rw [← pos_eq]
    exact hp p l ((line_iff p l).mp he)
  · intro Q hQ
    rw [← neg_eq]
    exact hn Q ((quad_iff Q).mp hQ)
  · intro t
    cases t
    · obtain ⟨p, l, he, hbT, haF⟩ := hB
      refine ⟨p, l, (line_iff p l).mpr he, ?_, ?_⟩ <;> rw [← pos_eq]
      · exact haF
      · exact hbT
    · obtain ⟨p, l, he, haT, hbF⟩ := hA
      refine ⟨p, l, (line_iff p l).mpr he, ?_, ?_⟩ <;> rw [← pos_eq]
      · exact haT
      · exact hbF
