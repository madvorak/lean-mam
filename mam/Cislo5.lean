import mam.Cislo1
import mam.Cislo2
import mam.Cislo3
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch


lemma soucet_prvnich_n_lichych_sestupne (n : Nat) : soucet (prvnich_n_lichych_sestupne n) = n * n :=
by
  induction' n with m ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_n_lichych_sestupne
  unfold soucet
  rw [ih, dva_krat]
  rw [add_comm, add_assoc, add_assoc]

lemma soucet_dvou_seznamu (x y : List Nat) : soucet (x ++ y) = soucet x + soucet y :=
by
  induction' x with x₀ xs ih
  · simp
  convert_to x₀ + soucet (xs ++ y) = x₀ + soucet xs + soucet y
  rw [ih, add_assoc]

lemma obrat_zachovava_soucet (l : List Nat) : soucet (obrat l) = soucet l :=
by
  induction' l with hlava zbytek indukcni
  · rfl
  unfold obrat
  rw [soucet_dvou_seznamu, indukcni, add_comm]
  rfl

theorem soucet_prvnich_N_lichych (n : Nat) : soucet (prvnich_n_lichych n) = n * n :=
by
  simp [prvnich_n_lichych]
  rw [obrat_zachovava_soucet]
  apply soucet_prvnich_n_lichych_sestupne


lemma dva_na_vs_na_druhou_aux (n : Nat) : 2 ^ (n+5) > (n+5) ^ 2 :=
by
  induction' n with m ih
  · decide
  rw [Nat.succ_add, Nat.pow_succ]
  have : (m+5) * (m+5) > 3 * (m+5)
  · nlinarith
  linarith

theorem dva_na_vs_na_druhou (n : Nat) (aspon_pet : n ≥ 5) : 2^n > n^2 :=
by
  have minus5_plus5 : n = n - 5 + 5
  · exact Nat.eq_add_of_sub_eq aspon_pet rfl
  rw [minus5_plus5]
  exact dva_na_vs_na_druhou_aux (n - 5)


lemma binetuv_aux {x : ℝ} (predpoklad : x * x = x + 1) (m : Nat) :
  x ^ (m+1) = x * (fibonacci (m+1)) + fibonacci m :=
by
  induction' m with n ih
  · simp [fibonacci]
  rw [pow_succ, ih, fibonacci, Nat.succ_eq_add_one, mul_add, ←mul_assoc, predpoklad]
  ring
  simp
  ring -- TODO najit mnohem elementarnejsi dukaz !!!!!!

theorem binetuv_vzorec (n : Nat) :
  fibonacci n = (1 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) :=
by
  have odm5nd : Real.sqrt 5 * Real.sqrt 5 = (5 : ℝ)
  · have pet_nz : 0 ≤ (5 : ℝ)
    · linarith
    exact Real.mul_self_sqrt pet_nz
  have odm5nn : Real.sqrt 5 ≠ 0
  · intro pro_spor
    have spor : Real.sqrt 5 * Real.sqrt 5 = 0 * Real.sqrt 5
    · exact congrFun (congrArg HMul.hMul pro_spor) (Real.sqrt 5)
    linarith
  cases' n with m ih
  · simp [fibonacci]
  rw [binetuv_aux, binetuv_aux]
  ring
  convert_to (fibonacci (Nat.succ m)) = (1 : ℝ) * (fibonacci (1 + m))
  · exact CommGroupWithZero.mul_inv_cancel (Real.sqrt 5) odm5nn
  convert_to (fibonacci (Nat.succ m) : ℝ) = (fibonacci (m + 1) : ℝ)
  · ring
  rfl
  · have uprava : (1 - Real.sqrt 5) / 2 * ((1 - Real.sqrt 5) / 2) =
                  (1 - 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5) / 2 / 2
    · ring
    rw [uprava, odm5nd]
    ring
  · have uprava : (1 + Real.sqrt 5) / 2 * ((1 + Real.sqrt 5) / 2) =
                  (1 + 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5) / 2 / 2
    · ring
    rw [uprava, odm5nd]
    ring
