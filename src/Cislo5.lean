import src.Cislo2
import src.Cislo3
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring


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
