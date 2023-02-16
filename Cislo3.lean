import Cislo1
import Cislo2
--import Std.Data.List.Lemmas

theorem krat_dva (n : Nat) : n * 2 = n + n := by
  induction n
  rfl
  rw [Nat.mul_succ, Nat.mul_one]

 theorem fibo_odpovida {m n : Nat} (platny : n < m) : List.get? (fibo_list m) n = some (fibonacci n) := by
  induction n
  unfold fibonacci
  unfold fibo_list
  sorry
  sorry
