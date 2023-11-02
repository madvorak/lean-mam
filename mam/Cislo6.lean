import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch


def ciferny_soucet (a : Nat) : Nat :=
if a < 10
then a
else (a % 10) + ciferny_soucet (a / 10)
decreasing_by
  simp_wf
  have : a ≥ 10
  · apply le_of_not_lt
    assumption
  have : a / 10 * 10 ≤ a
  · exact Nat.div_mul_le_self a 10
  linarith

#eval ciferny_soucet 524
#eval ciferny_soucet 10200
#eval ciferny_soucet (10^50 - 1)
#eval ciferny_soucet 0


def ackermann : Nat → Nat → Nat
| 0  , n   => n+1
| m+1, 0   => ackermann m 1
| m+1, n+1 => ackermann m (ackermann (m+1) n)
termination_by ackermann m n => (m, n)

#eval ackermann 2 100
#eval ackermann 3 0
#eval ackermann 3 5
