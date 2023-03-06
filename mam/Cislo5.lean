import mam.Cislo2
import mam.Cislo3
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


lemma procmusimtohledokazovat {n : Nat} (hn : n ≥ 1) : 10^n ≥ 10 := by
  let m := n-1
  have hm : n = m+1
  · exact Nat.eq_add_of_sub_eq hn rfl
  rw [hm]
  ring
  have : 10 ^ (n-1) ≥ 1
  · exact Nat.one_le_pow' (n-1) 9
  exact le_mul_of_one_le_left' this

example {n : Nat} (hn : n ≥ 1) : 10^n ≥ 10^1 :=
pow_le_pow (by decide) hn

example (n : Nat) : 6 ∣ (10^n - 4) := by
  induction' n with m ih
  · decide  -- pro `n = 0` plati jakoby jen nahodou (to nam nevadi)
  by_cases je_m_nula : m = 0
  · rw [je_m_nula]
    decide
  /-push_neg at je_m_nula
  rw [←Nat.one_le_iff_ne_zero] at je_m_nula-/
  have pls : m ≥ 1
  · exact Nat.pos_of_ne_zero je_m_nula

  convert_to 6 ∣ (10^m - 4) * 10 + 36
  · convert_to 10^m * 10 - 4 = 10^m * 10 - 4 * 10 + 36
    · exact tsub_mul (10^m) 4 10  -- tohle `library_search` nenasel (nevim proc)
    have samozrejme : 10^m * 10 ≥ 4 * 10
    · have achjo : 10^m ≥ 10
      · exact procmusimtohledokazovat pls
      linarith
    have samozrejmejsi : 4 * 10 ≥ 36
    · decide
    convert_to 10^m * 10 - (4 * 10 - 36) = 10^m * 10 - 4 * 10 + 36
    exact tsub_tsub_assoc samozrejme samozrejmejsi
  have deli_leve : 6 ∣ (10^m - 4) * 10
  · exact Dvd.dvd.mul_right ih 10
  have deli_prave : 6 ∣ 36
  · decide
  exact dvd_add deli_leve deli_prave
