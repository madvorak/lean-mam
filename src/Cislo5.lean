import src.Cislo2
import src.Cislo3
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring


lemma soucet_prvnich_N_lichych_sestupne (N : Nat) : soucet (prvnich_N_lichych_sestupne N) = N * N := by
  induction' N with n ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_N_lichych_sestupne
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

theorem soucet_prvnich_N_lichych (N : Nat) : soucet (prvnich_N_lichych N) = N * N := by
  simp [prvnich_N_lichych]
  rw [obrat_zachovava_soucet]
  apply soucet_prvnich_N_lichych_sestupne
