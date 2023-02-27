import src.Cislo2
import src.Cislo3
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Ring


def prvnich_n_lichych (n : Nat) : List Nat := List.map (fun a => 2 * a + 1) (List.range n)

#eval prvnich_n_lichych 6

theorem soucet_prvnich_n_lichych (n : Nat) : soucet (prvnich_n_lichych n) = n * n := by
  induction' n with m ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_n_lichych at *
  unfold List.range at *
  unfold List.range.loop
  sorry

def prvnich_N_lichych : Nat → List Nat
| 0   => []
| n+1 => (2 * n + 1) :: prvnich_N_lichych n

#eval prvnich_N_lichych 6

theorem soucet_prvnich_N_lichych (N : Nat) : soucet (prvnich_N_lichych N) = N * N := by
  induction' N with n ih
  · rfl
  rw [Nat.succ_mul, Nat.mul_succ]
  unfold prvnich_N_lichych
  unfold soucet
  rw [ih, dva_krat]
  rw [add_comm, add_assoc, add_assoc]
  