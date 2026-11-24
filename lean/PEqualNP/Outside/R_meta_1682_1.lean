import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1682_1
    (hPoint :
      let inc (p w : Fin 13) : Prop := ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset, p = w + d
      let avoids (P : Finset (Fin 13)) (w : Fin 13) : Prop := ∀ p ∈ P, ¬ inc p w
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∃ g : Gate, C.gates.head? = some g ∧ (0 ∈ g.inputs)) ∧
        (∀ p w : Fin 13, inc p w →
          circuitFun 26 C (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13),
          (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ¬ (∃ w, ∀ p ∈ P, inc p w) →
          ¬ (∃ v, ∀ w, avoids P w → inc v w) →
          circuitFun 26 C (fun k => decide
            ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
              (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false))
    (hLine :
      let inc (p w : Fin 13) : Prop := ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset, p = w + d
      let avoids (P : Finset (Fin 13)) (w : Fin 13) : Prop := ∀ p ∈ P, ¬ inc p w
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∃ g : Gate, C.gates.head? = some g ∧ (13 ∈ g.inputs ∧ ∀ i ∈ g.inputs, 13 ≤ i)) ∧
        (∀ p w : Fin 13, inc p w →
          circuitFun 26 C (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13),
          (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ¬ (∃ w, ∀ p ∈ P, inc p w) →
          ¬ (∃ v, ∀ w, avoids P w → inc v w) →
          circuitFun 26 C (fun k => decide
            ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
              (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false))
    (hConstant :
      let inc (p w : Fin 13) : Prop := ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset, p = w + d
      let avoids (P : Finset (Fin 13)) (w : Fin 13) : Prop := ∀ p ∈ P, ¬ inc p w
      ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∃ g : Gate, C.gates.head? = some g ∧ (g.inputs = [] ∨ g.inputs = [26])) ∧
        (∀ p w : Fin 13, inc p w →
          circuitFun 26 C (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13),
          (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ¬ (∃ w, ∀ p ∈ P, inc p w) →
          ¬ (∃ v, ∀ w, avoids P w → inc v w) →
          circuitFun 26 C (fun k => decide
            ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
              (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false))
    : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  intro hcounter
  have hdifferenceSet : ([0, 1, 3, 9] : List (Fin 13)).toFinset =
      ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  rw [hdifferenceSet] at hPoint hLine hConstant
  let inc (p w : Fin 13) : Prop := ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d
  let avoids (P : Finset (Fin 13)) (w : Fin 13) : Prop := ∀ p ∈ P, ¬ inc p w
  let pos (p w : Fin 13) := pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 w)
  let neg (P : Finset (Fin 13)) : Fin 26 → Bool := fun k => decide
    ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))
  let positive (C : Circuit) : Prop :=
    ∀ p w : Fin 13, inc p w → circuitFun 26 C (pos p w) = true
  let negative (C : Circuit) : Prop :=
    ∀ P : Finset (Fin 13), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
      ¬ (∃ w, ∀ p ∈ P, inc p w) → ¬ (∃ v, ∀ w, avoids P w → inc v w) →
      circuitFun 26 C (neg P) = false
  obtain ⟨C, hmono, hsize, hpos, hnegRaw⟩ := hcounter
  change positive C at hpos
  have hneg : negative C := fun P hm hl hp => hnegRaw P hm ⟨hl, hp⟩
  have sep (p w : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he
    have := p.isLt
    omega
  have lineInj (a b : Fin 13) : Fin.natAdd 13 a = Fin.natAdd 13 b ↔ a = b := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      exact Fin.ext (by omega)
    · rintro rfl
      rfl
  have negPoint (P : Finset (Fin 13)) (p : Fin 13) :
      neg P (Fin.castAdd 13 p) = decide (p ∈ P) := by
    change decide ((∃ q ∈ P, Fin.castAdd 13 p = Fin.castAdd 13 q) ∨
      (∃ w, Fin.castAdd 13 p = Fin.natAdd 13 w ∧ avoids P w)) = _
    rw [decide_eq_decide]
    constructor
    · rintro (⟨q, hq, he⟩ | ⟨w, he, _⟩)
      · have h : p = q := Fin.castAdd_injective 13 13 he
        simpa only [h] using hq
      · exact (sep p w he).elim
    · intro hp
      exact Or.inl ⟨p, hp, rfl⟩
  have negLine (P : Finset (Fin 13)) (w : Fin 13) :
      neg P (Fin.natAdd 13 w) = decide (avoids P w) := by
    change decide ((∃ q ∈ P, Fin.natAdd 13 w = Fin.castAdd 13 q) ∨
      (∃ v, Fin.natAdd 13 w = Fin.natAdd 13 v ∧ avoids P v)) = _
    rw [decide_eq_decide]
    constructor
    · rintro (⟨q, _, he⟩ | ⟨v, he, h⟩)
      · exact (sep q w he.symm).elim
      · have hwv := (lineInj w v).1 he
        simpa only [hwv] using h
    · intro hw
      exact Or.inr ⟨w, rfl, hw⟩
  let shift (s : Fin 13) : Fin 26 → Fin 26 :=
    Fin.addCases (motive := fun _ => Fin 26)
      (fun p => Fin.castAdd 13 (p + s)) (fun w => Fin.natAdd 13 (w + s))
  have leftShift (s p : Fin 13) : shift s (Fin.castAdd 13 p) = Fin.castAdd 13 (p + s) := by
    exact Fin.addCases_left p
  have rightShift (s w : Fin 13) : shift s (Fin.natAdd 13 w) = Fin.natAdd 13 (w + s) := by
    exact Fin.addCases_right w
  have incShift (s p w : Fin 13) : inc (p + s) (w + s) ↔ inc p w := by
    constructor
    · rintro ⟨d, hd, he⟩
      have hs : p + s = (w + d) + s := he.trans (by ac_rfl)
      exact ⟨d, hd, add_right_cancel hs⟩
    · rintro ⟨d, hd, he⟩
      have hs : (w + d) + s = (w + s) + d := by ac_rfl
      exact ⟨d, hd, (congrArg (fun p => p + s) he).trans hs⟩
  let pre (s : Fin 13) (P : Finset (Fin 13)) :=
    Finset.univ.filter (fun p => p + s ∈ P)
  have memPre (s p : Fin 13) (P : Finset (Fin 13)) : p ∈ pre s P ↔ p + s ∈ P := by
    simp [pre]
  have avoidsShift (s w : Fin 13) (P : Finset (Fin 13)) :
      avoids (pre s P) w ↔ avoids P (w + s) := by
    constructor
    · intro h p hp hin
      have hp' : p - s ∈ pre s P := (memPre s (p - s) P).2 (by simpa using hp)
      apply h (p - s) hp'
      apply (incShift s (p - s) w).1
      simpa using hin
    · intro h p hp hin
      exact h (p + s) ((memPre s p P).1 hp) ((incShift s p w).2 hin)
  have posShift (s p w : Fin 13) :
      (fun k => pos p w (shift s k)) = pos (p - s) (w - s) := by
    funext k
    refine Fin.addCases (m := 13) (n := 13)
      (motive := fun i => pos p w (shift s i) = pos (p - s) (w - s) i)
      (fun a => ?_) (fun b => ?_) k
    · rw [leftShift]
      change decide (Fin.castAdd 13 (a + s) = Fin.castAdd 13 p ∨
        Fin.castAdd 13 (a + s) = Fin.natAdd 13 w) = decide
          (Fin.castAdd 13 a = Fin.castAdd 13 (p - s) ∨ Fin.castAdd 13 a = Fin.natAdd 13 (w - s))
      have heq : a + s = p ↔ a = p - s := eq_sub_iff_add_eq.symm
      simp only [Fin.castAdd_inj, sep, or_false, heq]
    · rw [rightShift]
      change decide (Fin.natAdd 13 (b + s) = Fin.castAdd 13 p ∨
        Fin.natAdd 13 (b + s) = Fin.natAdd 13 w) = decide
          (Fin.natAdd 13 b = Fin.castAdd 13 (p - s) ∨ Fin.natAdd 13 b = Fin.natAdd 13 (w - s))
      have heq : b + s = w ↔ b = w - s := eq_sub_iff_add_eq.symm
      simp only [(sep p (b+s)).symm, (sep (p-s) b).symm, lineInj, false_or, heq]
  have negShift (s : Fin 13) (P : Finset (Fin 13)) :
      (fun k => neg P (shift s k)) = neg (pre s P) := by
    funext k
    refine Fin.addCases (m := 13) (n := 13)
      (motive := fun i => neg P (shift s i) = neg (pre s P) i)
      (fun p => ?_) (fun w => ?_) k
    · rw [leftShift, negPoint, negPoint]
      exact decide_eq_decide.mpr (memPre s p P).symm
    · rw [rightShift, negLine, negLine]
      exact decide_eq_decide.mpr (avoidsShift s w P).symm
  let rename (s : Fin 13) (i : ℕ) : ℕ :=
    if h : i < 26 then (shift s ⟨i, h⟩).val else i
  let gateMap (s : Fin 13) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename s)⟩
  let rotate (s : Fin 13) (D : Circuit) : Circuit :=
    ⟨D.gates.map (gateMap s), rename s D.output⟩
  let execute (values : List Bool) (g : Gate) : List Bool :=
    values ++ [g.op.eval (g.inputs.map (fun i => values.getD i false))]
  have renameSmall (s : Fin 13) (i m : ℕ) (hm : 26 ≤ m) (hi : i < m) :
      rename s i < m := by
    by_cases hvalid : i < 26
    · change (if h : i < 26 then (shift s ⟨i,h⟩).val else i) < m
      rw [dite_eq_left hvalid]
      exact (shift s ⟨i,hvalid⟩).isLt.trans_le hm
    · simpa [rename, hvalid] using hi
  have foldRotate (s : Fin 13) (gates : List Gate) :
      ∀ (x y : List Bool), x.length = y.length → 26 ≤ x.length →
        (∀ i, x.getD (rename s i) false = y.getD i false) →
        ∀ i, ((gates.map (gateMap s)).foldl execute x).getD (rename s i) false =
          (gates.foldl execute y).getD i false := by
    induction gates with
    | nil => intro x y _ _ h i; exact h i
    | cons g gs ih =>
      intro x y hlen hmin heval i
      let b := g.op.eval (g.inputs.map (fun k => y.getD k false))
      have hx : execute x (gateMap s g) = x ++ [b] := by
        change x ++ [g.op.eval ((g.inputs.map (rename s)).map (fun k => x.getD k false))] = _
        rw [List.map_map]
        have hmap : g.inputs.map ((fun k => x.getD k false) ∘ rename s) =
            g.inputs.map (fun k => y.getD k false) :=
          List.map_congr_left (fun k _ => heval k)
        exact congrArg (fun v => x ++ [g.op.eval v]) hmap
      have hy : execute y g = y ++ [b] := rfl
      simp only [List.map_cons, List.foldl_cons, hx, hy]
      refine ih (x ++ [b]) (y ++ [b]) (by simp [hlen]) (by simp; omega) ?_ i
      intro k
      by_cases hk : k < x.length
      · rw [List.getD_append _ _ _ _ (renameSmall s k x.length hmin hk),
          List.getD_append _ _ _ _ (by omega)]
        exact heval k
      · have hbig : ¬ k < 26 := by omega
        simp only [rename, dite_eq_right hbig]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]
  have ofFnRead (x : Fin 26 → Bool) (i : ℕ) :
      (List.ofFn x).getD i false = if h : i < 26 then x ⟨i,h⟩ else false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases h : i < 26 <;> simp [h]
  have computeRotate (s : Fin 13) (D : Circuit) (x : Fin 26 → Bool) :
      circuitFun 26 (rotate s D) x = circuitFun 26 D (fun k => x (shift s k)) := by
    change ((D.gates.map (gateMap s)).foldl execute (List.ofFn x)).getD (rename s D.output) false =
      (D.gates.foldl execute (List.ofFn (fun k => x (shift s k)))).getD D.output false
    refine foldRotate s D.gates _ _ (by simp) (by simp) ?_ _
    intro i
    rw [ofFnRead, ofFnRead]
    by_cases hi : i < 26
    · simp [rename, hi, (shift s ⟨i,hi⟩).isLt]
    · simp [rename, hi]
  have rotatedPositive (s : Fin 13) : positive (rotate s C) := by
    intro p w h
    rw [computeRotate, posShift]
    apply hpos
    apply (incShift s (p - s) (w - s)).1
    simpa using h
  have rotatedNegative (s : Fin 13) : negative (rotate s C) := by
    intro P hmax hline hpoint
    rw [computeRotate, negShift]
    apply hneg (pre s P)
    · intro v hv
      have hout : v + s ∉ P := fun hh => hv ((memPre s v P).2 hh)
      obtain ⟨w,hwa,hwi⟩ := hmax (v + s) hout
      refine ⟨w - s, (avoidsShift s (w - s) P).2 (by simpa using hwa), ?_⟩
      apply (incShift s v (w - s)).1
      simpa using hwi
    · rintro ⟨w, h⟩
      apply hline
      refine ⟨w + s, ?_⟩
      intro p hp
      have hm : p - s ∈ pre s P := (memPre s (p - s) P).2 (by simpa using hp)
      simpa using (incShift s (p - s) w).2 (h (p - s) hm)
    · rintro ⟨v, h⟩
      apply hpoint
      refine ⟨v + s, ?_⟩
      intro w hw
      have ha : avoids (pre s P) (w - s) :=
        (avoidsShift s (w - s) P).2 (by simpa using hw)
      simpa using (incShift s v (w - s)).2 (h (w - s) ha)
  have rotateMono (s : Fin 13) : Monotone2 (rotate s C) := by
    intro g hg
    change g ∈ C.gates.map (gateMap s) at hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hmono u hu).1, by simpa [gateMap] using (hmono u hu).2⟩
  have rotateSize (s : Fin 13) : (rotate s C).size ≤ 63 := by
    change (C.gates.map (gateMap s)).length ≤ 63
    change C.gates.length ≤ 63 at hsize
    simpa using hsize
  cases hgates : C.gates with
  | nil =>
    have h0 := hpos 0 0 ⟨0, by decide, by decide⟩
    have h1 := hpos 1 1 ⟨0, by decide, by decide⟩
    change (C.gates.foldl execute (List.ofFn (pos 0 0))).getD C.output false = true at h0
    change (C.gates.foldl execute (List.ofFn (pos 1 1))).getD C.output false = true at h1
    rw [hgates, List.foldl_nil, ofFnRead] at h0 h1
    by_cases hvalid : C.output < 26
    · rw [dite_eq_left hvalid] at h0 h1
      have h : ∀ i : Fin 26, pos 0 0 i = true → pos 1 1 i = false := by decide
      rw [h _ h0] at h1
      contradiction
    · simp [hvalid] at h0
  | cons g rest =>
    have hmem : g ∈ C.gates := by rw [hgates]; exact List.mem_cons_self
    have hrotHead (s : Fin 13) : (rotate s C).gates.head? = some (gateMap s g) := by
      change (C.gates.map (gateMap s)).head? = _
      rw [hgates]
      rfl
    have pointMap (s : Fin 13) (i : ℕ) (hi : i < 13) :
        rename s i = (⟨i, hi⟩ + s : Fin 13).val := by
      have hi' : i < 26 := by omega
      change (if h : i < 26 then (shift s ⟨i,h⟩).val else i) = _
      rw [dite_eq_left hi']
      have hcut : (⟨i, hi'⟩ : Fin 26) = Fin.castAdd 13 (⟨i, hi⟩ : Fin 13) := Fin.ext rfl
      rw [hcut, leftShift]
      rfl
    have lineMap (s : Fin 13) (i : ℕ) (hi : i < 26) (hl : 13 ≤ i) :
        rename s i = 13 + (⟨i - 13, by omega⟩ + s : Fin 13).val := by
      change (if h : i < 26 then (shift s ⟨i,h⟩).val else i) = _
      rw [dite_eq_left hi]
      have hcut : (⟨i, hi⟩ : Fin 26) = Fin.natAdd 13 (⟨i - 13, by omega⟩ : Fin 13) := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      rw [hcut, rightShift]
      rfl
    by_cases hp : ∃ i ∈ g.inputs, i < 13
    · obtain ⟨i, hi, hi13⟩ := hp
      let s : Fin 13 := -(⟨i, hi13⟩ : Fin 13)
      have hz : 0 ∈ (gateMap s g).inputs := by
        change 0 ∈ g.inputs.map (rename s)
        refine List.mem_map.mpr ⟨i, hi, ?_⟩
        rw [pointMap s i hi13]
        simp [s]
      exact hPoint ⟨rotate s C, rotateMono s, rotateSize s, ⟨gateMap s g, hrotHead s, hz⟩,
        rotatedPositive s, rotatedNegative s⟩
    · have notPoint (i : ℕ) (hi : i ∈ g.inputs) : 13 ≤ i := by
        by_contra h
        exact hp ⟨i, hi, by omega⟩
      by_cases hl : ∃ i ∈ g.inputs, i < 26
      · obtain ⟨i, hi, hi26⟩ := hl
        have hi13 : 13 ≤ i := notPoint i hi
        let s : Fin 13 := -(⟨i - 13, by omega⟩ : Fin 13)
        have h13 : 13 ∈ (gateMap s g).inputs := by
          change 13 ∈ g.inputs.map (rename s)
          refine List.mem_map.mpr ⟨i, hi, ?_⟩
          rw [lineMap s i hi26 hi13]
          simp [s]
        have onlyLine : ∀ k ∈ (gateMap s g).inputs, 13 ≤ k := by
          intro k hk
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
          by_cases hav : a < 26
          · rw [lineMap s a hav (notPoint a ha)]
            omega
          · simp only [rename, dite_eq_right hav]
            omega
        exact hLine ⟨rotate s C, rotateMono s, rotateSize s, ⟨gateMap s g, hrotHead s, h13, onlyLine⟩,
          rotatedPositive s, rotatedNegative s⟩
      · let first : Gate := ⟨g.op, if g.inputs = [] then [] else [26]⟩
        let D : Circuit := ⟨first :: rest, C.output⟩
        have hFirst : first.inputs = [] ∨ first.inputs = [26] := by
          by_cases h : g.inputs = [] <;> simp [first, h]
        have hDmono : Monotone2 D := by
          intro u hu
          change u ∈ first :: rest at hu
          rcases List.mem_cons.mp hu with rfl | h
          · exact ⟨(hmono g hmem).1, by rcases hFirst with h | h <;> simp [h]⟩
          · exact hmono u (by rw [hgates]; exact List.mem_cons_of_mem g h)
        have hDsize : D.size ≤ 63 := by
          change C.gates.length ≤ 63 at hsize
          change (first :: rest).length ≤ 63
          rwa [hgates] at hsize
        have hEq (x : Fin 26 → Bool) : circuitFun 26 D x = circuitFun 26 C x := by
          have miss (k : ℕ) (hk : 26 ≤ k) : (List.ofFn x).getD k false = false := by
            rw [ofFnRead, dite_eq_right (by omega)]
          have hmiss (k : ℕ) (hk : k ∈ g.inputs) : (List.ofFn x).getD k false = false :=
            miss k (by by_contra h; exact hl ⟨k, hk, by omega⟩)
          have hfold : execute (List.ofFn x) first = execute (List.ofFn x) g := by
            change (List.ofFn x) ++ [g.op.eval (first.inputs.map (fun i => (List.ofFn x).getD i false))] =
              (List.ofFn x) ++ [g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false))]
            cases he : g.inputs with
            | nil => simp [first, he]
            | cons k ks =>
              have hk : (List.ofFn x).getD k false = false := hmiss k (by rw [he]; exact List.mem_cons_self)
              have hmap : ks.map (fun i => (List.ofFn x).getD i false) =
                  ks.map (fun _ => false) := List.map_congr_left (fun a ha =>
                    hmiss a (by rw [he]; exact List.mem_cons_of_mem k ha))
              have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
                simpa using (hmono g hmem).1
              have hfirst : first.inputs = [26] := by simp [first, he]
              simp only [hfirst, List.map_cons, List.map_nil, hk, miss 26 (by decide), hmap]
              rcases hop with hand | hor
              · rw [hand]; rfl
              · rw [hor]
                change (List.ofFn x) ++ [false] =
                  (List.ofFn x) ++ [(false :: ks.map (fun _ => false)).any id]
                simp
          change ((first :: rest).foldl execute (List.ofFn x)).getD C.output false =
            (C.gates.foldl execute (List.ofFn x)).getD C.output false
          rw [hgates, List.foldl_cons, List.foldl_cons, hfold]
        have hp' : positive D := fun p w hw => (hEq _).trans (hpos p w hw)
        have hn' : negative D := fun P hm hl hp => (hEq _).trans (hneg P hm hl hp)
        exact hConstant ⟨D, hDmono, hDsize, ⟨first, rfl, hFirst⟩, hp', hn'⟩
