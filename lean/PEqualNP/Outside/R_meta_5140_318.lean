import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5140_318
    (normalize :
      let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
      let f (x : Fin 9 → Bool) :=
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (b : Bool) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        (∀ x, C.eval (w x ++ [b]) = f x) →
        ∃ D : Circuit, FanInTwo D ∧ D.size = 13 ∧ D.output = 22 ∧
          8 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) ∧
          ∀ x, D.eval (w x) = f x)
    (exactBound :
      let w (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
      let f (x : Fin 9 → Bool) :=
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ D : Circuit, FanInTwo D → D.size = 13 → D.output = 22 →
        8 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) →
        ∃ x, D.eval (w x) ≠ f x) :
  ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       ∃ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ))];         x2.eval (x6 ++ [x1]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro b C fan size
  classical
  by_contra! computes
  have agrees x := Classical.byContradiction (computes x)
  obtain ⟨D, dFan, dSize, dOutput, enough, dEval⟩ := normalize b C fan size agrees
  obtain ⟨x, hx⟩ := exactBound D dFan dSize dOutput enough
  exact hx (dEval x)
