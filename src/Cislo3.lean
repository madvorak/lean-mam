import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LibrarySearch


theorem krat_dva (n : Nat) : n * 2 = n + n := by
  rw [Nat.mul_succ, Nat.mul_one]

theorem soucet_na_druhou (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

theorem soucet_na_treti (x y : ℝ) : (x + y) ^ 3 = x^3 + 3 * x^2 * y + 3 * x * y^2 + y^3 := by ring

theorem rozdil_na_treti (x y : ℝ) : (x - y) ^ 3 = x^3 - 3 * x^2 * y + 3 * x * y^2 - y^3 := by ring

theorem rozdil_patych_mocnin (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by ring

theorem plus_prevracena (x : ℝ) : x + 1/x = (x^2 + 1) / x := by
  ring_nf
  congr
  convert_to x = x * x * x⁻¹
  ring
  simp

example (x : ℝ) (predpoklad : x ≠ -1) : (x^2 + x) / (2*x + 2) = x / 2 := by
  convert_to (x * (x + 1)) / ((x + 1) * 2) = x / 2
  · ring
  · ring
  convert_to x * ((x + 1) / ((x + 1) * 2)) = x / 2
  · field_simp
  have pokraceni : (x + 1) / ((x + 1) * 2) = 1 / 2
  · rw [←div_div, div_self]
    intro prospor
    apply predpoklad
    exact eq_neg_of_add_eq_zero_left prospor
  rw [pokraceni]
  rw [mul_div, mul_one]

example (x y : ℝ) : (x + y) ^ 2 - (x - y) ^ 2 = 4 * x * y := by ring

example (x y : ℝ) (predpoklad : 3*x + y ≠ 0) : (3*x + y) ^ 5 / (3*x + y) ^ 4 = 3*x + y := by
  rw [pow_succ, ←mul_div, div_self, mul_one]
  exact pow_ne_zero 4 predpoklad

example (x y z : ℝ) (xnn : x ≠ 0) : x*y*z + 3*y*z*x - 2*z*x*y = y*x*z + x^2*z*y/x := by
  have zkratit_x : x^2*z*y/x = x*z*y
  · field_simp
    ring
  rw [zkratit_x]
  ring
