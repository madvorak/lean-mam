import mam.Cislo3


-- ## Implikace

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

theorem aplikace_funkci {P Q R : Type} (a : P) (f : P → Q) (g : Q → R) : R :=
g (f a)

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

theorem skladani_funkci {P Q R : Type} (f : P → Q) (g : Q → R) : P → R :=
g ∘ f

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


-- ## Konjunkce

theorem konjunkce_komutativni_i1 {P Q : Prop} (predpoklad : P ∧ Q) : Q ∧ P := by
  obtain ⟨p,q⟩ := predpoklad
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_i2 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro predpoklad
  obtain ⟨p,q⟩ := predpoklad
  constructor
  · exact q
  · exact p

theorem konjunkce_komutativni_i3 {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro ⟨p,q⟩
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

theorem konjunkce_komutativni_i7 {P Q : Prop} : P ∧ Q → Q ∧ P := And.symm

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
  constructor <;> apply konjunkce_komutativni_i7

theorem konjunkce_komutativni_e5 {P Q : Prop} : P ∧ Q ↔ Q ∧ P := by
  tauto

theorem konjunkce_komutativni_e6 {P Q : Prop} : P ∧ Q ↔ Q ∧ P := And.comm

theorem konjunkce_komutativni_r {P Q : Prop} : (P ∧ Q) = (Q ∧ P) := by
  rw [konjunkce_komutativni_e3]


-- ## Disjunkce

theorem disjunkce_komutativni_i1 {P Q : Prop} (predpoklad : P ∨ Q) : Q ∨ P := by
  cases predpoklad with
  | inl p =>
    right
    exact p
  | inr q =>
    left
    exact q

theorem disjunkce_komutativni_i2 {P Q : Prop} (predpoklad : P ∨ Q) : Q ∨ P := by
  exact Or.symm predpoklad

theorem disjunkce_komutativni_i3 {P Q : Prop} : P ∨ Q → Q ∨ P := Or.symm

theorem disjunkce_komutativni_e1 {P Q : Prop} : P ∨ Q ↔ Q ∨ P := by
  constructor <;> apply disjunkce_komutativni_i3

theorem disjunkce_komutativni_e2 {P Q : Prop} : P ∨ Q ↔ Q ∨ P := by
  tauto

theorem disjunkce_komutativni_e3 {P Q : Prop} : P ∨ Q ↔ Q ∨ P := Or.comm


-- ## Negace

theorem blbina : 1 + 1 ≠ 3 := by norm_num

theorem blbina' : ¬ (1 + 1 = 3) := blbina

theorem blbina'' : (1 + 1 = 3) → False := blbina

theorem nemozna_ekvivalence {P : Prop} : (P ↔ ¬ P) → False := by
  intro hyp
  if p : P
  then
    have negace : ¬ P
    · rw [hyp] at p
      exact p
    exact negace p
  else
    apply p
    rw [hyp]
    exact p

theorem nemozna_ekvivalence' {P : Prop} : (P ↔ ¬ P) → False := by
  tauto

theorem nemozna_ekvivalence'' {P : Prop} : (P ↔ ¬ P) → False := iff_not_self


-- ## Kvantifikátory

theorem krat_tri : ∀ n : ℕ, n * 3 = n + n + n := by
  intro x
  ring

theorem cislo_55_je_fibonacciho : ∃ n : ℕ, fibonacci n = 55 := by
  use 10
  decide

theorem prir_tesne : ∀ n : ℕ, ∃ m : ℕ, ∀ k : ℕ, (k ≤ n → k < m) ∧ (n < k → m ≤ k) := by
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

theorem prir_tesne' (n : ℕ) : ∃ m : ℕ, ∀ k : ℕ, (k ≤ n → k < m) ∧ (n < k → m ≤ k) := by
  use n + 1
  intro k
  constructor
  · apply Nat.lt_succ_of_le
  · apply Nat.succ_le.mpr

theorem realna_cisla_jsou_husta (x z : ℝ) (mensi : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
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

theorem racionalni_cisla_jsou_husta : ∀ x z : ℚ, x < z → ∃ y : ℚ, x < y ∧ y < z := by
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

theorem cela_cisla_nejsou_husta : ¬ (∀ x z : ℤ, x < z → ∃ y : ℤ, x < y ∧ y < z) := by
  push_neg
  use 3, 4
  constructor
  · decide
  intro y hy
  exact hy

theorem deMorgan_existencni {α : Type} {R : α → Prop} (R_lze_splnit : ∃ a : α, R a) : ¬ (∀ a : α, ¬ R a) := by
  obtain ⟨a, splnen⟩ := R_lze_splnit
  intro pro_spor
  apply pro_spor
  exact splnen

theorem deMorgan_existencni' {α : Type} {R : α → Prop} (R_lze_splnit : ∃ a : α, R a) : ¬ (∀ a : α, ¬ R a) := by
  obtain ⟨a, splnen⟩ := R_lze_splnit
  push_neg
  use a
  exact splnen

theorem deMorgan_existencni'' {α : Type} {R : α → Prop} (R_lze_splnit : ∃ a : α, R a) : ¬ (∀ a : α, ¬ R a) := by
  tauto

theorem deMorgan_existencni''' {α : Type} {R : α → Prop} (R_lze_splnit : ∃ a : α, R a) : ¬ (∀ a : α, ¬ R a) :=
Exists.classicalRecOn R_lze_splnit


-- ## Množiny

example : { x : ℤ | x ≥ 100 } ⊆ { y : ℤ | y > 0 } := by
  intro a prvek
  rw [Set.mem_setOf_eq] at *
  linarith

example (M : Set ℝ) : ∀ a ∈ M, a ≤ |a| := by
  intro a _
  exact le_abs_self a


-- ## Vlastnosti funkcí

def Prosta {A B : Type} (f : A → B) : Prop := ∀ x y : A, x ≠ y → f x ≠ f y

def Surjektivni {A B : Type} (f : A → B) : Prop := ∀ z : B, ∃ x : A, f x = z

def Bijektivni {A B : Type} (f : A → B) : Prop := Prosta f ∧ Surjektivni f

theorem slozProsta {A B C : Type} {f : A → B} {g : B → C} (hf : Prosta f) (hg : Prosta g) :
    Prosta (g ∘ f) := by
  intro x y hxy
  apply hg
  apply hf
  exact hxy

theorem vetaCantor (T : Type) : ¬ (∃ f : T → Set T, Surjektivni f) := by
  intro pro_spor
  obtain ⟨f, surjektivni⟩ := pro_spor
  obtain ⟨a, sporne⟩ := surjektivni { x : T | x ∉ f x }
  have paradox : (a ∈ f a) ↔ (a ∉ f a)
  · exact of_eq (congr_arg (Membership.mem a) sporne)
  exact nemozna_ekvivalence paradox
