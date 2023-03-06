import mam.Cislo2
import mam.Cislo3
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch


lemma soucet_prvnich_n_lichych_sestupne (n : Nat) : soucet (prvnich_n_lichych_sestupne n) = n * n := by
  induction' n with m ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_n_lichych_sestupne
  unfold soucet
  rw [ih, dva_krat]
  rw [add_comm, add_assoc, add_assoc]

lemma soucet_dvou_seznamu (x y : List Nat) : soucet (x ++ y) = soucet x + soucet y := by
  induction' x with x₀ xs ih
  · simp
  convert_to x₀ + soucet (xs ++ y) = x₀ + soucet xs + soucet y
  rw [ih, add_assoc]

lemma obrat_zachovava_soucet (l : List Nat) : soucet (obrat l) = soucet l := by
  induction' l with hlava zbytek indukcni
  · rfl
  unfold obrat
  rw [soucet_dvou_seznamu, indukcni, add_comm]
  rfl

theorem soucet_prvnich_N_lichych (n : Nat) : soucet (prvnich_n_lichych n) = n * n := by
  simp [prvnich_n_lichych]
  rw [obrat_zachovava_soucet]
  apply soucet_prvnich_n_lichych_sestupne


lemma dva_na_vs_na_druhou_aux (n : Nat) : 2 ^ (n+5) > (n+5) ^ 2 := by
  induction' n with m ih
  · decide
  rw [Nat.succ_add, Nat.pow_succ]
  have : (m+5) * (m+5) > 3 * (m+5)
  · nlinarith
  linarith

theorem dva_na_vs_na_druhou (n : Nat) (aspon_pet : n ≥ 5) : 2^n > n^2 := by
  have minus5_plus5 : n = n - 5 + 5
  · exact Nat.eq_add_of_sub_eq aspon_pet rfl
  rw [minus5_plus5]
  exact dva_na_vs_na_druhou_aux (n - 5)
