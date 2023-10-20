import mam.Cislo4
import Mathlib.Data.Real.Sqrt


lemma soucet_prvnich_n_lichych_sestupne (n : ℕ) : soucet (prvnich_n_lichych_sestupne n) = n * n := by
  induction' n with m ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_n_lichych_sestupne
  unfold soucet
  rw [ih, dva_krat]
  convert_to m + m + 1 + m * m = m * m + m + (m + 1)
  ring

lemma soucet_dvou_seznamu (x y : List ℕ) : soucet (x ++ y) = soucet x + soucet y := by
  induction' x with x₀ xs ih
  · simp
  convert_to x₀ + soucet (xs ++ y) = x₀ + soucet xs + soucet y
  rw [ih]
  ring

lemma obrat_zachovava_soucet (l : List ℕ) : soucet (obrat l) = soucet l := by
  induction' l with hlava zbytek indukcni
  · rfl
  unfold obrat
  rw [soucet_dvou_seznamu, indukcni]
  convert_to soucet zbytek + soucet [hlava] = soucet [hlava] + soucet zbytek
  ring

theorem soucet_prvnich_N_lichych (n : ℕ) : soucet (prvnich_n_lichych n) = n * n := by
  simp [prvnich_n_lichych]
  rw [obrat_zachovava_soucet]
  apply soucet_prvnich_n_lichych_sestupne


lemma dva_na_vs_na_druhou_aux (n : ℕ) : 2 ^ (n+5) > (n+5) ^ 2 := by
  induction' n with m ih
  · decide
  rw [Nat.succ_add, Nat.pow_succ]
  have : (m+5) * (m+5) > 3 * (m+5)
  · nlinarith
  linarith

theorem dva_na_vs_na_druhou (n : ℕ) (aspon_pet : n ≥ 5) : 2^n > n^2 := by
  have minus5_plus5 : n = n - 5 + 5
  · exact Nat.eq_add_of_sub_eq aspon_pet rfl
  rw [minus5_plus5]
  exact dva_na_vs_na_druhou_aux (n - 5)


lemma binetovo {x : ℝ} (predpoklad : x * x = x + 1) (m : ℕ) :
    x ^ (m+1) = x * fibonacci (m+1) + fibonacci m := by
  induction' m with n ih
  · simp [fibonacci]
  convert_to x * x ^ (n+1) = x * (fibonacci n + fibonacci (n+1)) + fibonacci (n+1)
  · simp [fibonacci]
  rw [ih]
  convert_to x * x * fibonacci (n+1) + x * fibonacci n = x * (fibonacci n + fibonacci (n+1)) + fibonacci (n+1)
  · ring
  rw [predpoklad]
  ring

theorem binetuv_vzorec (n : ℕ) :
    fibonacci n = (1 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) := by
  have odm5nd : Real.sqrt 5 * Real.sqrt 5 = (5 : ℝ)
  · have pet_nz : 0 ≤ (5 : ℝ)
    · linarith
    exact Real.mul_self_sqrt pet_nz
  have odm5nn : Real.sqrt 5 ≠ 0
  · intro pro_spor
    have spor : Real.sqrt 5 * Real.sqrt 5 = 0 * Real.sqrt 5
    · exact congrFun (congrArg HMul.hMul pro_spor) (Real.sqrt 5)
    linarith
  cases' n with m
  · simp [fibonacci]
  rw [binetovo, binetovo]
  ring
  convert_to (fibonacci (Nat.succ m)) = (1 : ℝ) * (fibonacci (1 + m))
  · sorry -- TODO fix after upgrade
  · sorry -- TODO fix after upgrade
  convert_to (fibonacci (Nat.succ m) : ℝ) = (fibonacci (m + 1) : ℝ)
  · sorry -- TODO fix after upgrade
  · sorry -- TODO fix after upgrade
  · ring
  have upravaM : ((1 - Real.sqrt 5) / 2) * ((1 - Real.sqrt 5) / 2) =
                  (1 - 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5) / 2 / 2
  · ring
  have upravaP : ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) =
                  (1 + 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5) / 2 / 2
  · ring
  sorry -- TODO fix after upgrade
