import mam.Cislo4
import Mathlib.Data.Real.Sqrt


lemma soucet_prvnich_n_lichych_sestupne (n : ℕ) : soucet (prvnich_n_lichych_sestupne n) = n * n := by
  induction n with
  | zero => decide
  | succ m ih =>
    convert_to 2 * m + 1 + soucet (prvnich_n_lichych_sestupne m) = m * m + 2 * m + 1
    · convert_to (m + 1) * (m + 1) = m * m + 2 * m + 1
      ring
    rw [ih]
    exact add_comm (2 * m + 1) (m * m)

lemma soucet_dvou_seznamu (x y : List ℕ) : soucet (x ++ y) = soucet x + soucet y := by
  induction x with
  | nil => simp
  | cons d l ih =>
    convert_to d + soucet (l ++ y) = d + soucet l + soucet y
    rw [ih]
    exact (add_assoc d (soucet l) (soucet y)).symm

lemma obrat_zachovava_soucet (x : List ℕ) : soucet (obrat x) = soucet x := by
  induction x with
  | nil => decide
  | cons d l ih =>
    convert_to soucet (obrat l ++ [d]) = soucet (d :: l)
    rw [soucet_dvou_seznamu, ih]
    convert_to soucet l + soucet [d] = soucet [d] + soucet l
    exact add_comm (soucet l) (soucet [d])

theorem soucet_prvnich_n_lichych (n : ℕ) : soucet (prvnich_n_lichych n) = n * n := by
  dsimp [prvnich_n_lichych]
  rw [obrat_zachovava_soucet]
  apply soucet_prvnich_n_lichych_sestupne


lemma dva_na_vs_na_druhou_aux (n : ℕ) : 2 ^ (n+5) > (n+5) ^ 2 := by
  induction n with
  | zero => decide
  | succ m ih =>
    convert_to 2 ^ (m+5) * 2 > (Nat.succ (m+5)) ^ 2
    have : (m+5) * (m+5) > 3 * (m+5)
    · nlinarith
    linarith

theorem dva_na_vs_na_druhou (n : ℕ) (aspon_pet : n ≥ 5) : 2^n > n^2 := by
  have minus5_plus5 : n = (n - 5) + 5
  · exact Nat.eq_add_of_sub_eq aspon_pet rfl
  rw [minus5_plus5]
  exact dva_na_vs_na_druhou_aux (n - 5)


lemma fibonacci_aux {x : ℝ} (predpoklad : x * x = x + 1) (m : ℕ) :
    x ^ (m+1) = x * fibonacci (m+1) + fibonacci m := by
  induction m with
  | zero => simp [fibonacci]
  | succ n ih =>
    convert_to x * x ^ (n+1) = x * (fibonacci n + fibonacci (n+1)) + fibonacci (n+1)
    · simp [fibonacci]
    rw [ih]
    convert_to (x * x) * fibonacci (n+1) + x * fibonacci n = x * (fibonacci n + fibonacci (n+1)) + fibonacci (n+1)
    · ring
    rw [predpoklad]
    ring

theorem binetuv_vzorec (n : ℕ) :
    fibonacci n = (1 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) := by
  cases n with
  | zero => simp [fibonacci]
  | succ m =>
    have odm5nd : Real.sqrt 5 * Real.sqrt 5 = 5
    · have pet_nz : 0 ≤ (5 : ℝ)
      · linarith
      exact Real.mul_self_sqrt pet_nz
    have odm5nn : Real.sqrt 5 ≠ 0
    · intro pro_spor
      have spor : Real.sqrt 5 * Real.sqrt 5 = 0 * Real.sqrt 5
      · exact congr_arg (· * Real.sqrt 5) pro_spor
      linarith
    rw [fibonacci_aux, fibonacci_aux]
    ring
    convert_to (fibonacci (m + 1) : ℝ) = (1 : ℝ) * (fibonacci (1 + m))
    · exact CommGroupWithZero.mul_inv_cancel (Real.sqrt 5) odm5nn
    convert_to (fibonacci (m + 1) : ℝ) = (fibonacci (m + 1) : ℝ)
    · ring
    rfl
    · have uprava : ((1 - Real.sqrt 5) / 2) * ((1 - Real.sqrt 5) / 2) =
                    (1 - 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5) / 2 / 2
      · ring
      rw [uprava, odm5nd]
      ring
    · have uprava : ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) =
                    (1 + 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5) / 2 / 2
      · ring
      rw [uprava, odm5nd]
      ring
