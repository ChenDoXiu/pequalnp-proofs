import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1586

def writeGate (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun wire => wires.getD wire false)]

lemma runLength (gates : List Gate) (inputs : List Bool) :
    (gates.foldl writeGate inputs).length = inputs.length + gates.length := by
  induction gates generalizing inputs with
  | nil => simp
  | cons g rest ih => simp [ih, writeGate]; omega

lemma runPreserves (gates : List Gate) (inputs : List Bool) (wire : ℕ)
    (hwire : wire < inputs.length) :
    (gates.foldl writeGate inputs).getD wire false = inputs.getD wire false := by
  induction gates generalizing inputs with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih _ (by simp [writeGate]; omega)]
    exact List.getD_append _ _ _ _ hwire

def value {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (wire : ℕ) : Bool :=
  Circuit.eval ⟨gates, wire⟩ (List.ofFn x)

lemma inputValue {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (p : Fin n) :
    value gates x p = x p := by
  change (gates.foldl writeGate (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [runPreserves _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missingValue {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (wire : ℕ)
    (hwire : n + gates.length ≤ wire) : value gates x wire = false := by
  change (gates.foldl writeGate (List.ofFn x)).getD wire false = false
  exact List.getD_eq_default _ _ (by simpa [runLength] using hwire)

lemma gateValue {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (i : Fin gates.length)
    (hearlier : ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ)) :
    value gates x (n + (i : ℕ)) =
      (gates.get i).op.eval ((gates.get i).inputs.map (value gates x)) := by
  let earlier := (gates.take i).foldl writeGate (List.ofFn x)
  have hlength : earlier.length = n + (i : ℕ) := by
    simp [earlier, runLength, Nat.min_eq_left i.isLt.le]
  have hsplit : gates.foldl writeGate (List.ofFn x) =
      ((gates.get i) :: gates.drop ((i : ℕ) + 1)).foldl writeGate earlier := by
    conv_lhs => rw [← List.take_append_drop (i : ℕ) gates]
    rw [List.foldl_append, List.drop_eq_getElem_cons i.isLt]
    rfl
  have hread (a : ℕ) (ha : a ∈ (gates.get i).inputs) :
      earlier.getD a false = value gates x a := by
    change earlier.getD a false = (gates.foldl writeGate (List.ofFn x)).getD a false
    rw [hsplit]
    exact (runPreserves _ _ _ (by rw [hlength]; exact hearlier a ha)).symm
  change (gates.foldl writeGate (List.ofFn x)).getD (n + (i : ℕ)) false = _
  rw [hsplit, List.foldl_cons, runPreserves _ _ _ (by simp [writeGate, hlength])]
  unfold writeGate
  rw [List.getD_append_right _ _ _ _ (by rw [hlength]), hlength, Nat.sub_self,
    List.getD_cons_zero]
  exact congrArg ((gates.get i).op.eval) (List.map_congr_left hread)

lemma orTrue {n : ℕ} {gates : List Gate} {x : Fin n → Bool} {i : Fin gates.length}
    (hearlier : ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hor : (gates.get i).op = GateOp.or) :
    value gates x (n + (i : ℕ)) = true ↔
      ∃ a ∈ (gates.get i).inputs, value gates x a = true := by
  rw [gateValue gates x i hearlier, hor]
  simp [GateOp.eval]

lemma andTrue {n : ℕ} {gates : List Gate} {x : Fin n → Bool} {i : Fin gates.length}
    (hearlier : ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hand : (gates.get i).op = GateOp.and) :
    value gates x (n + (i : ℕ)) = true ↔
      ∀ a ∈ (gates.get i).inputs, value gates x a = true := by
  rw [gateValue gates x i hearlier, hand]
  simp [GateOp.eval]

def orClosed (gates : List Gate) (n : ℕ) (S : Set ℕ) : Prop :=
  ∀ i : Fin gates.length, n + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
    ∀ a ∈ (gates.get i).inputs, a ∈ S

def inTop (gates : List Gate) (n u wire : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → orClosed gates n S → wire ∈ S

lemma topStep {gates : List Gate} {n u a : ℕ} {i : Fin gates.length}
    (htop : inTop gates n u (n + (i : ℕ))) (hor : (gates.get i).op = GateOp.or)
    (ha : a ∈ (gates.get i).inputs) : inTop gates n u a := by
  intro S hu hclosed
  exact hclosed i (htop S hu hclosed) hor a ha

lemma topFalse {n : ℕ} {gates : List Gate} {x : Fin n → Bool} {u wire : ℕ}
    (hearlier : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hu : value gates x u = false) (hwire : inTop gates n u wire) :
    value gates x wire = false := by
  apply hwire {w | value gates x w = false} hu
  intro i hi hor a ha
  change value gates x (n + (i : ℕ)) = false at hi
  change value gates x a = false
  cases h : value gates x a with
  | false => rfl
  | true =>
    have ht := (orTrue (x := x) (hearlier i) hor).2 ⟨a, ha, h⟩
    rw [hi] at ht
    contradiction

end PEqualNP.Outside.L_meta_1586

open PEqualNP.Outside.L_meta_1586

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hops hwell hbase
  let base : Fin N → Bool := fun v => decide (v ∉ L i0)
  let rim (r : Fin N) : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = r)
  have hearlier (i : Fin gates.length) := (hwell i).2
  have hfalse (wire : ℕ) (hwire : inTop gates N u wire) : value gates base wire = false :=
    topFalse hearlier hbase hwire
  have hpoint (p : Fin N) (hp : inTop gates N u p) : p ∈ L i0 := by
    have h := hfalse p hp
    simpa [inputValue, base] using h
  refine ⟨hfalse, hpoint, ?_, ?_⟩
  · intro r _ hu
    let witness : Prop := inTop gates N u r ∨ ∃ a : ℕ, inTop gates N u a ∧
      (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      value gates (rim r) a = true
    change witness
    have find (wire : ℕ) (htop : inTop gates N u wire)
        (htrue : value gates (rim r) wire = true) : witness := by
      induction wire using Nat.strong_induction_on with
      | _ wire ih =>
        by_cases hinput : wire < N
        · let p : Fin N := ⟨wire, hinput⟩
          change inTop gates N u p at htop
          change value gates (rim r) p = true at htrue
          have hp : p = r := by simpa [inputValue, rim, hpoint p htop] using htrue
          exact Or.inl (hp ▸ htop)
        by_cases hgate : wire < N + gates.length
        · let i : Fin gates.length := ⟨wire - N, by omega⟩
          have hindex : wire = N + (i : ℕ) := by dsimp [i]; omega
          rw [hindex] at htop htrue
          rcases (hops (gates.get i) (List.get_mem gates i)).1 with hand | hor
          · exact Or.inr ⟨_, htop, ⟨i, rfl, hand⟩, htrue⟩
          · obtain ⟨a, ha, hval⟩ := (orTrue (hearlier i) hor).1 htrue
            exact ih a (by rw [hindex]; exact hearlier i a ha) (topStep htop hor ha) hval
        · exact False.elim (by simpa [missingValue gates (rim r) wire (by omega)] using htrue)
    exact find u (fun _ hu' _ => hu') hu
  · intro i a hand _ ha _ r _ htrue
    exact (andTrue (hearlier i) hand).1 htrue a ha
