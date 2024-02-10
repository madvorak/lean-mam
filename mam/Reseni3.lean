import mam.Cislo3


theorem na_druhou (a : ℚ) : a ^ 2 = a * a := pow_two a

example (a b c d : ℕ) (a_je : a = b + d) (b_je : b = a * a) (c_je : c = b + d) (d_je : d = c * c) :
    b ^ d = d ^ b := by
  rw [←a_je] at c_je
  rw [c_je, ←b_je] at d_je
  rw [d_je]

example (a b c d : ℤ) (a_je : a = d ^ 4) (b_je : b = 1 / c) (c_je : c = a - b) (d_je : d = 4 * a) :
    (a + b) ^ 2 - c ^ 2 = b * d := by
  rw [c_je, d_je]
  ring

example (x : ℝ) : 50*x^2 - 126*x + 96 ≥ 0 := by
  have : 49*x^2 - 126*x + 81 ≥ 0
  · convert_to (7*x - 9) ^ 2 ≥ 0
    · ring
    exact pow_two_nonneg (7*x - 9)
  nlinarith

example (x y : ℝ) : 2 * x^3 * y^3 ≤ x^4 * y^2 + x^2 * y^4 := by
  have : 0 ≤ x^4 * y^2 + x^2 * y^4 - 2 * x^3 * y^3
  · convert_to 0 ≤ (x^2*y - x*y^2) ^ 2
    · ring
    exact pow_two_nonneg (x^2*y - x*y^2)
  linarith

example (x y z : ℝ) : 4*x^2 + 12*x*y - 4*x*z + 9*y^2 - 6*y*z + z^2 ≥ 0 := by
  convert_to (2*x + 3*y - z) ^ 2 ≥ 0
  · ring
  exact pow_two_nonneg (2*x + 3*y - z)

-- Barbora Vosáhlová dokázala:
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 1 / b ≤ a / b^2 + b / a^2 := by
  have : (a - b) ^ 2 * (a + b) ≥ 0
  · nlinarith
  have : a^3 + b^3 - a*b^2 - a^2*b ≥ 0
  · convert this
    ring
  have : a^3 + b^3 ≥ a*b^2 + a^2*b
  · linarith
  have : (a^3 + b^3) / (a^2 * b^2) ≥ (a*b^2 + a^2*b) / (a^2 * b^2)
  · have levy_citatel_nezap : 0 ≤ a^3 + b^3
    · nlinarith
    have jmenovatel_klad : 0 < a^2 * b^2
    · exact mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb)
    have samozr : a^2 * b^2 ≤ a^2 * b^2
    · rfl
    exact div_le_div levy_citatel_nezap this jmenovatel_klad samozr
  have : a^3 / (a^2 * b^2) + b^3 / (a^2 * b^2) ≥ (a * b^2) / (a^2 * b^2) + (a^2 * b) / (a^2 * b^2)
  · convert this
    · exact div_add_div_same (a^3) (b^3) (a^2 * b^2)
    ring
  convert this using 2 <;> field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring
