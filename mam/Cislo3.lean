import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LibrarySearch


theorem dva_krat (n : ℕ) : 2 * n = n + n := two_mul n

theorem tri_krat (n : ℕ) : 3 * n = n + n + n := by
  convert_to 3 * n = 2 * n + n
  exact symm (dva_krat n)
  exact Nat.succ_mul 2 n

theorem tri_krat' (n : ℕ) : 3 * n = n + n + n := by ring

theorem soucet_na_druhou (x y : ℤ) : (x + y) ^ 2 = x^2 + 2*x*y + y^2 := by ring

theorem rozdil_na_treti (x y : ℚ) : (x - y) ^ 3 = x^3 - 3*x^2*y + 3*x*y^2 - y^3 := by ring

theorem rozdil_patych_mocnin (x y : ℝ) : x^5 - y^5 = (x - y) * (x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4) := by ring

example (n : ℕ) : 2 ^ (n+3) = 8 * 2^n := by ring

example (n : ℕ) (n_je_pet : n = 5) : n - 1 = 4 := by
  rw [n_je_pet]

example (n : ℕ) (n_je_pet : 5 = n) : n - 1 = 4 := by
  rw [symm n_je_pet]

example (n : ℕ) (n_je_pet : 5 = n) : n - 1 = 4 := by
  rw [←n_je_pet]

example (a b c : ℝ) (a_je_dva : a = 2) (b_je_tri : b = 3) (c_je_pet : c = 5) : a + b = c := by
  rw [a_je_dva, b_je_tri, c_je_pet]
  ring

example (a : ℝ) (a_je_dva : a = 2) (a_je_tri : a = 3) : False := by
  rw [a_je_dva] at a_je_tri
  simp at a_je_tri

example (x : ℝ) (xnn : x ≠ 0) : x^2 / x = x := by
  field_simp
  ring

theorem plus_prevracena (x : ℝ) (xnn : x ≠ 0) : x + 1/x = (x^2 + 1) / x := by
  field_simp
  ring

example (x y z : ℝ) (xnn : x ≠ 0) : x*y*z + 3*y*z*x - 2*z*x*y = y*x*z + x^2*z*y/x := by
  field_simp
  ring


example (x y z : ℝ) (xy : x ≤ y) (yz : y ≤ z) : x ≤ z := Trans.simple xy yz

example (x y z : ℝ) (xy : x < y) (yz : y < z) : x < z := Trans.simple xy yz

example (x y z : ℝ) (xy : x < y) (yz : y ≤ z) : x < z := instTransLtToLTLeToLE.proof_1 xy yz

example (x y z : ℝ) (xy : x ≤ y) (yz : y < z) : x < z := xy.trans_lt yz

example (a b c d : ℝ) (abcd : a + b + c ≤ 2 * d) (ab : a ≤ b) (ac : 2 * a ≤ c) : 2 * a ≤ d := by linarith

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
  have pomocne : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 81 ≥ 0
  · convert_to ((2*x - 3) ^ 2) ^ 2 ≥ 0
    · ring
    nlinarith
  linarith

example (x : ℝ) : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 100 ≥ 0 := by
  have pomocne : 16*x^4 - 96*x^3 + 216*x^2 - 216*x + 81 ≥ 0
  convert_to ((2*x - 3) ^ 2) ^ 2 ≥ 0
  ring
  nlinarith
  linarith

example (x : ℝ) (xpos : x > 0) : x + 1/x ≥ 2 := by
  have : (x - 1) ^ 2 ≥ 0
  · exact pow_two_nonneg (x - 1)
  have : x*x + 1 - 2*x ≥ 0
  · convert this
    ring
  have : x*x + 1 ≥ 2*x
  · exact le_of_sub_nonneg this
  have : (x*x + 1) / x ≥ 2*x / x
  -- pokud přejdeme na novější toolchain, půjde najít `div_le_div_right` misto `div_le_div`
  -- automaticky pomocí `library_search` což umožní zjednodušit důkaz
  -- možná bude potřeba zároveň obrátit strany nerovností
  · have levy_citatel_nezap : x*x + 1 ≥ 0
    · nlinarith
    have samozrejmost : x ≤ x
    · exact refl x
    exact div_le_div levy_citatel_nezap this xpos samozrejmost
  have : x*x/x + 1/x ≥ 2*x/x
  · convert this
    exact div_add_div_same (x*x) 1 x
  convert this
  · simp
  · convert_to 2 = 2 * (x / x)
    · exact IsAssociative.assoc 2 x x⁻¹
    convert_to (2 : ℝ) = 2 * 1
    · have : x ≠ 0
      · exact LT.lt.ne' xpos
      exact div_self this
    ring
