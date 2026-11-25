/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import QuantumComputation.Algorithms.Grover.Amplitude

/-!
# Grover overshoot on two qubits

Start in the uniform superposition of four basis states with one marked state.
For each iteration count, measure once after completing the iterations.
-/

public section

open scoped Real

namespace Grover

/-- One iteration reaches the marked state. The second rotates past it, lowering the
success probability from `1` to `1 / 4`. This is Grover overshoot. -/
theorem p_succ_two_qubit_overshoot :
    p_succ 0 4 = 1 / 4 ∧ p_succ 1 4 = 1 ∧ p_succ 2 4 = 1 / 4 := by
  have angle : Real.arcsin (1 / √(4 : ℝ)) = π / 6 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num), ← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simp only [p_succ_eq_sin_sq, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, angle]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Real.sin_pi_div_six]
  · rw [show ((2 : ℝ) * 1 + 1) * (π / 6) = π / 2 by ring, Real.sin_pi_div_two, one_pow]
  · rw [show ((2 : ℝ) * 2 + 1) * (π / 6) = π - π / 6 by ring, Real.sin_pi_sub]
    norm_num [Real.sin_pi_div_six]

end Grover
