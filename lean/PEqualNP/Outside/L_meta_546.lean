import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

private def insertWires (n i : ℕ) : ℕ :=
  if i < n then i else i + 2

private def shiftGate (n : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) :
    PEqualNP.CircuitLowerBounds.Gate :=
  ⟨g.op, g.inputs.map (insertWires n)⟩

private def evalGate (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma readShifted (u w : List Bool) (a b : Bool) (i : ℕ) :
    (u ++ [a, b] ++ w).getD (insertWires u.length i) false =
      (u ++ w).getD i false := by
  by_cases hi : i < u.length
  · rw [insertWires, ite_eq_left hi, List.append_assoc, List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ hi]
  · have hlen : (u ++ [a, b]).length ≤ i + 2 := by simp; omega
    rw [insertWires, ite_eq_right hi, List.getD_append_right _ _ _ _ hlen,
      List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
    have hindex : i + 2 - (u ++ [a, b]).length = i - u.length := by simp
    rw [hindex]

private lemma evalShifted (u w : List Bool) (a b : Bool)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    ∃ t : List Bool, gs.foldl evalGate (u ++ w) = u ++ t ∧
      (gs.map (shiftGate u.length)).foldl evalGate (u ++ [a, b] ++ w) =
        u ++ [a, b] ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨w, rfl, rfl⟩
  | cons gate gs ih =>
    have h : ((shiftGate u.length gate).inputs.map fun i =>
        (u ++ [a, b] ++ w).getD i false) =
        gate.inputs.map (fun i => (u ++ w).getD i false) := by
      simp only [shiftGate, List.map_map]
      exact List.map_congr_left (fun i _ => readShifted u w a b i)
    simp only [List.map_cons, List.foldl_cons, evalGate, h]
    change ∃ t, gs.foldl evalGate ((u ++ w) ++ _) = u ++ t ∧
      (gs.map (shiftGate u.length)).foldl evalGate
        (((u ++ [a, b]) ++ w) ++ _) = u ++ [a, b] ++ t
    simp only [shiftGate, List.append_assoc _ w]
    exact ih _

private lemma evalLength (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl evalGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons gate gs ih =>
    rw [List.foldl_cons, ih]
    simp [evalGate]
    omega

private lemma readLast (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

private def gadget (k a b v i : ℕ) : List PEqualNP.CircuitLowerBounds.Gate :=
  [⟨.or, [v, b]⟩, ⟨.and, [a, k]⟩, ⟨.or, [i, k + 1]⟩]

private lemma evalGadget (w : List Bool) (a b v i : ℕ) (ha : a < w.length) :
    ((gadget w.length a b v
      (if i < w.length then i else w.length + 2)).foldl evalGate w).getD (w.length + 2) false =
      (w.getD i false || (w.getD a false && (w.getD v false || w.getD b false))) := by
  let first := w.getD v false || w.getD b false
  have ha' := List.getD_append w [first] false a ha
  let second := w.getD a false && first
  have hsecond : ((w ++ [first]) ++ [second]).getD (w.length + 1) false = second := by
    simpa only [List.length_append, List.length_singleton] using readLast (w ++ [first]) second
  have hi : ((w ++ [first]) ++ [second]).getD
      (if i < w.length then i else w.length + 2) false = w.getD i false := by
    split_ifs with h
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ h]
    · rw [List.getD_eq_default _ _ (by simp),
        List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
  simp only [gadget, List.foldl_cons, List.foldl_nil, evalGate, List.map_cons, List.map_nil,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  change ((((w ++ [first]) ++
    [((w ++ [first]).getD a false && (w ++ [first]).getD w.length false)]) ++
    [_]).getD (w.length + 2) false) = _
  rw [ha', readLast]
  change (((w ++ [first] ++ [second]) ++
    [((w ++ [first] ++ [second]).getD (if i < w.length then i else w.length + 2) false ||
      (w ++ [first] ++ [second]).getD (w.length + 1) false)]).getD (w.length + 2) false) = _
  rw [hi, hsecond]
  simpa only [List.length_append, List.length_singleton] using
    readLast (w ++ [first] ++ [second]) (w.getD i false || second)

private lemma readInput {n : ℕ} (x : Fin n → Bool) (j : Fin n) (w : List Bool) :
    (List.ofFn x ++ w).getD j.val false = x j := by
  have hj : j.val < (List.ofFn x).length := by simp
  rw [List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hj]
  simp

theorem PEqualNP.Outside.L_meta_546 :
    ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool) (v : Fin n),
      PEqualNP.MetaComplexity.HasCircuitSize n g s →
      PEqualNP.MetaComplexity.HasCircuitSize (n + 2)
        (fun x : Fin (n + 2) → Bool =>
          g (fun i : Fin n => x (Fin.castAdd 2 i)) ||
            (x (Fin.natAdd n 0) && (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1)))) (s + 3) := by
  intro n s g v hg
  obtain ⟨C, hfan, hsize, heval⟩ := hg
  let k := n + 2 + C.size
  let i := insertWires n C.output
  -- An absent output is read at the end of the wire list, past the first two added gates.
  let tail := gadget k n (n + 1) v.val (if i < k then i else k + 2)
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (shiftGate n) ++ tail, k + 2⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro gate hgate
    change gate ∈ C.gates.map (shiftGate n) ++ tail at hgate
    rcases List.mem_append.mp hgate with hgate | hgate
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hgate
      exact ⟨(hfan old hold).1, by simpa [shiftGate] using (hfan old hold).2⟩
    · simp only [tail, gadget, List.mem_cons, List.not_mem_nil, or_false] at hgate
      rcases hgate with rfl | rfl | rfl <;> simp
  · simpa [D, tail, gadget, PEqualNP.CircuitLowerBounds.Circuit.size] using
      Nat.add_le_add_right hsize 3
  · intro x
    let y : Fin n → Bool := fun j => x (Fin.castAdd 2 j)
    let a := x (Fin.natAdd n 0)
    let b := x (Fin.natAdd n 1)
    let u := List.ofFn y
    have hu : u.length = n := List.length_ofFn
    have hx : List.ofFn x = u ++ [a, b] := by
      rw [List.ofFn_add]
      rfl
    obtain ⟨w, hw, hshift⟩ := evalShifted u [] a b C.gates
    rw [List.append_nil] at hw hshift
    rw [hu] at hshift
    let W := u ++ [a, b] ++ w
    have hshift' : (C.gates.map (shiftGate n)).foldl evalGate (List.ofFn x) = W := by
      rw [hx, hshift]
    have hW : W.length = k := by
      rw [← hshift', evalLength]
      simp [k, PEqualNP.CircuitLowerBounds.Circuit.size]
    have hout : W.getD i false = g y := by
      have h := readShifted u w a b C.output
      rw [hu, ← hw] at h
      exact h.trans (heval y)
    have hinput : W = List.ofFn x ++ w := by rw [hx]
    have ha : W.getD n false = a := by
      rw [hinput]
      exact readInput x (Fin.natAdd n 0) w
    have hb : W.getD (n + 1) false = b := by
      rw [hinput]
      exact readInput x (Fin.natAdd n 1) w
    have hv : W.getD v.val false = x (Fin.castAdd 2 v) := by
      rw [hinput]
      exact readInput x (Fin.castAdd 2 v) w
    change ((C.gates.map (shiftGate n) ++ tail).foldl evalGate
      (List.ofFn x)).getD (k + 2) false = (g y || (a && (x (Fin.castAdd 2 v) || b)))
    rw [List.foldl_append, hshift']
    have h := evalGadget W n (n + 1) v.val i (by rw [hW]; dsimp [k]; omega)
    rw [hW, hout, ha, hv, hb] at h
    exact h
