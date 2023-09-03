import mam.Cislo3

theorem na_druhou (a : ℚ) : a ^ 2 = a * a := sorry

example (a b c d : ℕ) (a_je : a = b + d) (b_je : b = a * a) (c_je : c = b + d) (d_je : d = c * c) :
  b ^ d = d ^ b := sorry

example (a b c d : ℤ) (a_je : a = d ^ 4) (b_je : b = 1 / c) (c_je : c = a - b) (d_je : d = 4 * a) :
  (a + b) ^ 2 - c ^ 2 = b * d := sorry

example (x : ℝ) : x^2 - 6*x + 10 ≥ 0 := sorry

example (x y : ℝ) : 2 * x^3 * y^3 ≤ x^4 * y^2 + x^2 * y^4 := sorry

example (x y z : ℝ) : 4*x^2 + 12*x*y - 4*x*z + 9*y^2 - 6*y*z + z^2 ≥ 0 := sorry

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / a + 1 / b ≤ a / b^2 + b / a^2 := sorry
