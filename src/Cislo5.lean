import src.Cislo2
import src.Cislo3
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring


theorem soucet_prvnich_N_lichych (N : Nat) : soucet (prvnich_N_lichych N) = N * N := by
  induction' N with n ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_N_lichych
  unfold soucet
  rw [ih, dva_krat]
  rw [add_comm, add_assoc, add_assoc]
