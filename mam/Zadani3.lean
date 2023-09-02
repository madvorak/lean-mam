import mam.Cislo3

theorem na_druhou (n : Nat) : n ^ 2 = n * n := sorry

example (a b c d : ℕ) (a_je : a = b + d) (b_je : b = a * a) (c_je : c = b + d) (d_je : d = c * c) :
  b ^ d = d ^ b := sorry

example {x : ℚ} : x^2 - 6*x + 10 ≥ 0 := sorry

example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a / b^2 + b / a^2 ≥ 1 / a + 1 / b := sorry
