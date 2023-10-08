import mam.Cislo3


theorem aplikace_implikace_1 {P Q : Prop} (p : P) (pq : P → Q) : Q := by
  apply pq
  apply p

theorem aplikace_implikace_2 {P Q : Prop} (p : P) (pq : P → Q) : Q := by
  apply pq
  exact p

theorem aplikace_implikace_3 {P Q : Prop} (p : P) (pq : P → Q) : Q := by
  exact pq p

theorem aplikace_implikace_4 {P Q : Prop} (p : P) (pq : P → Q) : Q :=
pq p

theorem aplikace_implikaci_1 {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R := by
  apply qr
  apply pq
  exact p

theorem aplikace_implikaci_2 {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R := by
  apply qr
  exact pq p

theorem aplikace_implikaci_3 {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R :=
qr (pq p)

theorem aplikace_implikaci_4 {P Q R : Prop} (h₁ : P) (h₂ : P → Q) (h₃ : Q → R) : R :=
h₃ (h₂ h₁)

theorem skladani_implikaci_1 {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  intro p
  apply qr
  apply pq
  exact p

theorem skladani_implikaci_2 {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  intro p
  exact qr (pq p)

theorem skladani_implikaci_3 {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R := by
  exact fun p => qr (pq p)

theorem skladani_implikaci_4 {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R :=
fun p => qr (pq p)

theorem skladani_implikaci_5 {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R :=
qr ∘ pq

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  apply pqrst
  · exact p
  · apply pq
    exact p
  · apply qr
    apply pq
    exact p
  · apply rs
    apply qr
    apply pq
    exact p

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T :=
pqrst p (pq p) (qr (pq p)) (rs (qr (pq p)))

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  have q : Q
  · exact pq p
  have r : R
  · exact qr q
  apply pqrst
  · exact p
  · exact q
  · exact r
  · exact rs r

example {P Q R S T : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (pqrst : P → Q → R → S → T) : T := by
  have q : Q
  · exact pq p
  have r : R
  · exact qr q
  have s : S
  · exact rs r
  exact pqrst p q r s

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  apply stu
  · apply rs
    apply qr
    apply pq
    exact p
  · apply rt
    apply qr
    apply pq
    exact p

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  apply stu
  · apply rs
    exact qr (pq p)
  · apply rt
    exact qr (pq p)

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U :=
stu (rs (qr (pq p))) (rt (qr (pq p)))

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  have r : R
  · apply qr
    exact pq p
  apply stu
  · apply rs
    exact r
  · apply rt
    exact r

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U :=
let r := qr (pq p) ;
stu (rs r) (rt r)

example {P Q R S T U : Prop} (p : P) (pq : P → Q) (qr : Q → R) (rs : R → S) (rt : R → T) (stu : S → T → U) : U := by
  tauto

theorem konjunkce_komutativni_i1 {P Q : Prop} (predpoklad : P ∧ Q) : Q ∧ P := by
  cases' predpoklad with p q
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_i2 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro predpoklad
  rcases predpoklad with ⟨p,q⟩
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_i3 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  rintro ⟨p,q⟩
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_i4 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro ⟨p,q⟩
  exact ⟨q,p⟩

theorem konjunkce_komutativni_i5 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro predpoklad
  exact And.symm predpoklad

theorem konjunkce_komutativni_i6 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  exact And.symm

theorem konjunkce_komutativni_i7 {P Q : Prop} : P ∧ Q → Q ∧ P :=
And.symm

theorem konjunkce_komutativni_e1 {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨p,q⟩
    exact ⟨q,p⟩
  · intro ⟨q,p⟩
    exact ⟨p,q⟩

theorem konjunkce_komutativni_e2 {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro predpoklad
    exact konjunkce_komutativni_i1 predpoklad
  · intro predpoklad
    exact konjunkce_komutativni_i1 predpoklad

theorem konjunkce_komutativni_e3 {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  constructor
  · apply konjunkce_komutativni_i7
  · apply konjunkce_komutativni_i7

theorem konjunkce_komutativni_e4 {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  tauto

theorem konjunkce_komutativni_r {P Q : Prop} : (P ∧ Q) = (Q ∧ P) := by
  rw [konjunkce_komutativni_e3]


theorem blbina : 1 + 1 ≠ 3 := by ring

example : ¬ (1 + 1 = 3) := blbina

example : (1 + 1 = 3) → False := blbina

theorem nemozna_ekvivalence {P : Prop} : (P ↔ ¬ P) → False := by
  intro hyp
  by_cases p : P
  · have negace : ¬ P
    · rw [hyp] at p
      exact p
    exact negace p
  apply p
  rw [hyp]
  exact p


theorem krat_dva : ∀ n : ℕ, n * 2 = n + n := by
  intro x
  ring

theorem cislo_55_je_fibonacciho : ∃ n : ℕ, fibonacci n = 55 := by
  use 10
  rfl


theorem tesne : ∀ n : ℕ, ∃ m : ℕ, ∀ k : ℕ, (k ≤ n → k < m) ∧ (n < k → m ≤ k) := by
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

theorem tesne' (n : ℕ) : ∃ m : ℕ, ∀ k : ℕ, (k ≤ n → k < m) ∧ (n < k → m ≤ k) := by
  use n + 1
  intro k
  constructor
  · apply Nat.lt_succ_of_le
  · apply Nat.succ_le.mpr


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


theorem Cantorova_veta (T : Type) : ¬ (∃ f : T → Set T, Function.Surjective f) := by
  intro pro_spor
  cases' pro_spor with f surjektivni
  cases' surjektivni (fun x => x ∉ f x) with a sporne
  have paradox : (a ∈ f a) ↔ (a ∉ f a)
  · exact of_eq (congrArg (Membership.mem a) sporne)
  exact nemozna_ekvivalence paradox

theorem Cantoruv_dusledek (T : Type) : ¬ (∃ g : Set T → T, Function.Injective g) := by
  intro pro_spor
  cases' pro_spor with f prosta
  apply Cantorova_veta
  use Function.invFun f
  exact Function.invFun_surjective prosta
