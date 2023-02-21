import Cislo1
import Cislo2
import Std.Data.Rat.Basic
import Std.Data.Rat.Lemmas
import Std.Data.List.Lemmas
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic


theorem konjunkce_komutativni_v1 {P Q : Prop} (predpoklad : P ∧ Q) : Q ∧ P := by
  rcases predpoklad with ⟨p,q⟩
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_v2 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro predpoklad
  rcases predpoklad with ⟨p,q⟩
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_v3 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  rintro ⟨p,q⟩
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_v4 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro ⟨p,q⟩
  exact ⟨q,p⟩

theorem konjunkce_komutativni_v5 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro predpoklad
  exact And.symm predpoklad

theorem konjunkce_komutativni_v6 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  exact And.symm

theorem konjunkce_komutativni_v7 {P Q : Prop} : P ∧ Q → Q ∧ P :=
And.symm

theorem konjunkce_komutativni_obousmerne {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨p,q⟩
    exact ⟨q,p⟩
  · intro ⟨q,p⟩
    exact ⟨p,q⟩

theorem konjunkce_komutativni_obousmern {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro predpoklad
    exact konjunkce_komutativni_v1 predpoklad
  · intro predpoklad
    exact konjunkce_komutativni_v1 predpoklad

theorem konjunkce_komutativni_obousmer {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · apply konjunkce_komutativni_v7
  · apply konjunkce_komutativni_v7

theorem konjunkce_komutativni_rovnost {P Q : Prop} : (P ∧ Q) = (Q ∧ P) := by
  rw [konjunkce_komutativni_obousmer]


theorem krat_dva (n : Nat) : n * 2 = n + n := by
  rw [Nat.mul_succ, Nat.mul_one]

theorem krat_dva' : ∀ n : Nat, n * 2 = n + n := by
  intro x
  ring


theorem cislo_55_je_fibonacciho : ∃ n : Nat, fibonacci n = 55 := by
  use 10
  rfl


theorem tesne : ∀ n : Nat, ∃ m : Nat, ∀ k : Nat, (k ≤ n → k < m) ∧ (n < k → m ≤ k) := by
  intro n
  use n + 1
  intro k
  constructor
  · intro k_le_n
    rw [Nat.lt_succ]
    exact k_le_n
  · intro n_lt_k
    rw [Nat.succ_le]
    exact n_lt_k

theorem tesne' : ∀ n : Nat, ∃ m : Nat, ∀ k : Nat, (k ≤ n → k < m) ∧ (n < k → m ≤ k) :=
  fun n => ⟨n + 1, fun _ => ⟨Nat.lt_succ_of_le, Nat.succ_le.mpr⟩⟩


theorem racionalni_cisla_jsou_husta (x z : ℚ) : x < z → ∃ y : ℚ, x < y ∧ y < z := by
  intro mensi
  use (x + z) / 2
  constructor
  · convert_to x / 2 + x / 2 < x / 2 + z / 2
    · ring
    · rw [add_div]
    · apply add_lt_add_left
      exact div_lt_div_of_lt two_pos mensi
  · convert_to x / 2 + z / 2 < z / 2 + z / 2
    · rw [add_div]
    · ring
    · apply add_lt_add_right
      exact div_lt_div_of_lt two_pos mensi

theorem realna_cisla_jsou_husta : ∀ x z : ℝ, x < z → ∃ y : ℝ, x < y ∧ y < z := by
  intro x z mensi
  use (x + z) / 2
  constructor
  · convert_to x / 2 + x / 2 < x / 2 + z / 2
    · ring
    · rw [add_div]
    · apply add_lt_add_left
      exact div_lt_div_of_lt two_pos mensi
  · convert_to x / 2 + z / 2 < z / 2 + z / 2
    · rw [add_div]
    · ring
    · apply add_lt_add_right
      exact div_lt_div_of_lt two_pos mensi


theorem obrat_obrat {α : Type} (l : List α) : obrat_rychle (obrat_rychle l) = l := by
  sorry

theorem obrat_append {α : Type} (l₁ l₂ : List α) : obrat_rychle (l₁ ++ l₂) = obrat_rychle l₂ ++ obrat_rychle l₁ := by
  sorry

theorem prilep_obrat_dela_palindrom {α : Type} [DecidableEq α] (l : List α) : palindrom (l ++ obrat_rychle l) := by
  rw [palindrom, decide_eq_true_eq, obrat_append, obrat_obrat]
