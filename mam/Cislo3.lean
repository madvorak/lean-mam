import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LibrarySearch


theorem dva_krat (n : Nat) : 2 * n = n + n := two_mul n

theorem tri_krat (n : Nat) : 3 * n = n + n + n := by
  convert_to 3 * n = 2 * n + n
  exact symm (dva_krat n)
  exact Nat.succ_mul 2 n

theorem tri_krat' (n : Nat) : 3 * n = n + n + n := by ring

theorem soucet_na_druhou (x y : ℤ) : (x + y) ^ 2 = x^2 + 2*x*y + y^2 := by ring

theorem rozdil_na_treti (x y : ℚ) : (x - y) ^ 3 = x^3 - 3*x^2*y + 3*x*y^2 - y^3 := by ring

theorem rozdil_patych_mocnin (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by ring

example (x y : ℝ) : (x + y) ^ 2 - (x - y) ^ 2 = 4 * x * y := by ring

example (n : Nat) : 2 ^ (n+3) = 8 * 2^n := by ring

example (n : Nat) (n_je_pet : n = 5) : n - 1 = 4 := by
  rw [n_je_pet]

example (n : Nat) (n_je_pet : 5 = n) : n - 1 = 4 := by
  rw [symm n_je_pet]

example (n : Nat) (n_je_pet : 5 = n) : n - 1 = 4 := by
  rw [←n_je_pet]

example (a b c : ℝ) (a_je_dva : a = 2) (b_je_tri : b = 3) (c_je_pet : c = 5) : a + b = c := by
  rw [a_je_dva, b_je_tri, c_je_pet]
  ring

example (x : ℝ) (xnn : x ≠ 0) : x^2 / x = x := by
  field_simp
  ring

theorem plus_prevracena (x : ℝ) (xnn : x ≠ 0) : x + 1/x = (x^2 + 1) / x := by
  field_simp
  ring


example (x y z : ℝ) (xy : x ≤ y) (yz : y ≤ z) : x ≤ z := Trans.simple xy yz

example (x y z : ℝ) (xy : x < y) (yz : y < z) : x < z := Trans.simple xy yz

example (x y z : ℝ) (xy : x < y) (yz : y ≤ z) : x < z := instTransLtToLTLeToLE.proof_1 xy yz

example (x y z : ℝ) (xy : x ≤ y) (yz : y < z) : x < z := xy.trans_lt yz

example (a b c d : ℝ) (abcd : a + b + c ≤ 2 * d) (ab : a ≤ b) (ac : 2 * a ≤ c) : 2 * a ≤ d := by
  linarith

example (x y : ℝ) (xy : x ≤ y) : x ≤ y + y*y := by nlinarith

example (x y : ℝ) (x_zaporne : x < 0) (y_zaporne : y < 0) : x * 7 * y > 0 := by nlinarith

example (x y : ℝ) : x*x - 2*x*y + y*y ≥ 0 := by
  convert_to (x - y) ^ 2 ≥ 0
  ring
  nlinarith

example (x : ℝ) : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 81 ≥ 0 := by
  convert_to ((2*x - 3) ^ 2) ^ 2 ≥ 0
  ring
  nlinarith

example (x : ℝ) : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 100 ≥ 0 := by
  have pomocna : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 81 ≥ 0
  · convert_to ((2*x - 3) ^ 2) ^ 2 ≥ 0
    · ring
    nlinarith
  linarith


example (x : ℝ) (xpos : x > 0) : x + 1/x ≥ 2 := by
  have : (x - 1) ^ 2 ≥ 0
  · exact pow_two_nonneg (x - 1)
  have : x^2 + 1 - 2*x ≥ 0
  · convert this
    ring
  have : x^2 + 1 ≥ 2*x
  · exact le_of_sub_nonneg this
  have : (x^2 + 1) / x ≥ (2*x) / x
  · have left_numerator_nneg : x^2 + 1 ≥ 0
    · nlinarith
    have wtf : x ≤ x
    · rfl
    exact div_le_div left_numerator_nneg this xpos wtf
  convert this
  · ring_nf
    congr
    convert_to x = x * x * x⁻¹
    ring
    simp
  · have : (2 : ℝ) = 2 * 1
    · ring
    have : 2 = 2 * (x / x)
    · convert this
      have : x ≠ 0
      · exact LT.lt.ne' xpos
      exact div_self this
    convert this
    field_simp

-- based on proof by Alex J. Best
example (x : ℝ) (xpos : x > 0) : x + 1/x ≥ 2 := by
  have xne : x ≠ 0  :=  LT.lt.ne' xpos
  suffices : (x + 1/x) * x ≥ 2 * x
  . nlinarith
  simp
  rw [RightDistribClass.right_distrib x x⁻¹ x]
  rw [inv_mul_cancel xne]
  suffices : 2 * x - 2 * x ≤ x * x + 1 - 2 * x
  . linarith
  rw [show x * x + 1 - 2 * x = (x - 1) ^ 2 by ring]
  simp
  exact pow_two_nonneg (x - 1)


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

example (x y : ℝ) (predpoklad : 3*x + y ≠ 0) : (3*x + y) ^ 5 / (3*x + y) ^ 4 = 3*x + y := by
  rw [pow_succ, ←mul_div, div_self, mul_one]
  exact pow_ne_zero 4 predpoklad

example (x y z : ℝ) (xnn : x ≠ 0) : x*y*z + 3*y*z*x - 2*z*x*y = y*x*z + x^2*z*y/x := by
  field_simp
  ring
