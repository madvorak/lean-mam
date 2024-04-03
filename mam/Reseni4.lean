import mam.Cislo4


example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro predpoklad
    obtain ⟨hp, hqr⟩ := predpoklad
    cases hqr with
    | inl hq =>
      left
      constructor
      · exact hp
      · exact hq
    | inr hr =>
      right
      constructor
      · exact hp
      · exact hr
  · intro predpoklad
    cases predpoklad with
    | inl hpq =>
      obtain ⟨hp, hq⟩ := hpq
      constructor
      · exact hp
      · left
        exact hq
    | inr hpr =>
      obtain ⟨hp, hr⟩ := hpr
      constructor
      · exact hp
      · right
        exact hr


example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x, ∀ y, ∀ z, ∀ b, ∃ a, R a b x y z) → (∀ z, ∀ y, ∃ x, ∀ w, ∃ v, R v w x y z) := by
  intro predpoklad
  obtain ⟨x, hx⟩ := predpoklad
  intro z
  intro y
  use x
  intro w
  obtain ⟨b, hb⟩ := hx y z w
  use b
  exact hb

example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x, ∀ y, ∀ z, ∀ b, ∃ a, R a b x y z) → (∀ z, ∀ y, ∃ x, ∀ w, ∃ v, R v w x y z) := by
  intro predpoklad
  obtain ⟨x, hx⟩ := predpoklad
  intro z
  intro y
  use x
  exact hx y z

example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x, ∀ y, ∀ z, ∀ b, ∃ a, R a b x y z) → (∀ z, ∀ y, ∃ x, ∀ w, ∃ v, R v w x y z) := by
  intro ⟨x, hx⟩ z y
  exact ⟨x, hx y z⟩

example (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    (∃ x, ∀ y, ∀ z, ∀ b, ∃ a, R a b x y z) → (∀ z, ∀ y, ∃ x, ∀ w, ∃ v, R v w x y z) :=
  fun ⟨x, hx⟩ z y => ⟨x, hx y z⟩


theorem slozSurjektivni {A B C : Type} {f : A → B} {g : B → C} (hf : Surjektivni f) (hg : Surjektivni g) :
    Surjektivni (g ∘ f) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [←hy, ←hx]
  rfl

theorem slozBijektivni {A B C : Type} {f : A → B} {g : B → C} (hf : Bijektivni f) (hg : Bijektivni g) :
    Bijektivni (g ∘ f) := by
  obtain ⟨prosta_f, surjektivni_f⟩ := hf
  obtain ⟨prosta_g, surjektivni_g⟩ := hg
  constructor
  · exact slozProsta prosta_f prosta_g
  · exact slozSurjektivni surjektivni_f surjektivni_g

theorem slozBijektivni' {A B C : Type} {f : A → B} {g : B → C} (hf : Bijektivni f) (hg : Bijektivni g) :
    Bijektivni (g ∘ f) :=
  ⟨slozProsta hf.left hg.left, slozSurjektivni hf.right hg.right⟩

theorem slozBijektivni'' {A B C : Type} {f : A → B} {g : B → C} (hf : Bijektivni f) (hg : Bijektivni g) :
    Bijektivni (g ∘ f) := by
  simp_all [Bijektivni, slozSurjektivni, slozProsta]


/-
Definujeme, kdy jsou typy (množiny) `A` a `B` stejně velké.
-/
def StejneVelke (A B : Type) : Prop := ∃ f : A → B, Bijektivni f

/-
Náš cíl je dokázat následující charakterizaci stejně velkých typů (množin).
Tuto větu (pojmenovaný `theorem`, který `A` a `B` dostane implicitní) najdete na konci souboru,
kde již budeme mít dostatek pomocných nástrojů k jejímu dokázání.
-/
example : ∀ A : Type, ∀ B : Type, (∃ f : A → B, Prosta f) ∧ (∃ g : B → A, Prosta g) → StejneVelke A B := by
  sorry -- Nedokazujte zde!

/-
Definujeme počet předchůdců určitého prvku `A` či `B`.
Obecná definice je zapsaná pro `a : A`:
`Generace f g a n` znamená, že `a` má přesně `n` předchůdců.
Pokud chceme charakterizovat prvek `b : B`, prohodíme funkce `f` a `g`:
`Generace g f b n` znamená, že `b` má přesně `n` předchůdců.
-/
inductive Generace : {A B : Type} → (A → B) → (B → A) → A → ℕ → Prop
-- Pokud neexistuje `b : B` takové že `g b = a` pak říkáme, že `a` má 0 předchůdců vzhledem k funkcím `f` a `g`.
| nula {A B : Type} {f : A → B} {g : B → A} {a : A} (sirot : ¬ ∃ b : B, g b = a) :
    Generace f g a 0
-- Pokud existuje `p : B` takové že `g p = a` pak říkáme, že `p` je rodič `a` vzhledem k funkcím `f` a `g`.
| nasl {A B : Type} {f : A → B} {g : B → A} {a : A} (p : B) (rodic : g p = a) {n : ℕ} (rodokmen : Generace g f p n) :
-- Pokud rodič `p` má `n` předchůdců, pak `a` má `n+1` předchůdců vzhledem k funkcím `f` a `g`.
    Generace f g a n.succ

variable {A B : Type} -- Implicitní typové proměnné (pro vše, co následuje) neposouvat výše!

/-
Definujeme prvek se sudým počtem předchůdců.
-/
def SudaGenerace (f : A → B) (g : B → A) (a : A) : Prop :=
  ∃ n : ℕ, Generace f g a (2*n)

/-
Definujeme prvek s lichým počtem předchůdců.
-/
def LichaGenerace (f : A → B) (g : B → A) (a : A) : Prop :=
  ∃ n : ℕ, Generace f g a (2*n + 1)

/-
Každý prvek s lichým počtem předchůdců má nějakého rodiče (a ten má sudý počet předchůdců).
-/
lemma LichaGenerace.existuje_rodic {f : A → B} {g : B → A} {a : A}
    (lichaGen : LichaGenerace f g a) :
    ∃ p : B, g p = a ∧ SudaGenerace g f p := by
  have ⟨n, hn⟩ := lichaGen
  cases hn with
  | nasl p hp hpg =>
    use p
    constructor
    · exact hp
    · use n
      exact hpg

/-
Pokud prvek má lichý počet předchůdců, jeho potomek má sudý počet předchůdců.
-/
lemma LichaGenerace.pristiSudaGenerace {f : A → B} {g : B → A} {a : A}
    (lichaGen : LichaGenerace f g a) :
    SudaGenerace g f (f a) := by
  have ⟨n, hn⟩ := lichaGen
  use n+1
  right
  · rfl
  convert hn

/-
Pokud prvek má sudý počet předchůdců, jeho potomek má lichý počet předchůdců.
-/
lemma SudaGenerace.pristiLichaGenerace {f : A → B} {g : B → A} {a : A}
    (sudaGen : SudaGenerace f g a) :
    LichaGenerace g f (f a) := by
  have ⟨n, hn⟩ := sudaGen
  use n
  right
  · rfl
  exact hn

/-
Pokud nesirotek má sudý počet předchůdců, jeho rodič má lichý počet předchůdců.
-/
lemma SudaGenerace.predchoziLichaGenerace {f : A → B} {g : B → A} {a : A}
    (sudaGen : SudaGenerace g f (f a)) (hf : Prosta f) :
    LichaGenerace f g a := by
  have ⟨n, hn⟩ := sudaGen
  cases n with
  | zero =>
    cases hn with
    | nula sirotek =>
      exfalso
      apply sirotek
      use a
  | succ k =>
    use k
    cases hn with
    | nasl p hpa hp =>
      have p_je_a : p = a
      · by_contra kdyby
        exact hf p a kdyby hpa
      rw [p_je_a] at hp
      exact hp

/-
Definujeme funkci `g⁻¹` pro jednoduchost pouze na prvcích liché generace.
Argument `a` je implicitní (stejně jako původní funkce `f` a `g` jsou implicitní argumenty).
Explicitním argumentem je důkaz, že `a` má lichý počet předchůdců vzhledem k funkcím `f` a `g`.
-/
noncomputable def inverze {f : A → B} {g : B → A} {a : A} (lichaGen : LichaGenerace f g a) : B :=
  lichaGen.existuje_rodic.choose

/-
Pro všechna `a` z liché generace platí `g (g⁻¹ a) = a`.
-/
lemma LichaGenerace.g_inverze {f : A → B} {g : B → A} {a : A} (lichaGen : LichaGenerace f g a) :
    g (inverze lichaGen) = a :=
  lichaGen.existuje_rodic.choose_spec.left

/-
Pro všechna `a` z liché generace je `g⁻¹ a` ze sudé generace.
-/
lemma LichaGenerace.sudaGen_inverze {f : A → B} {g : B → A} {a : A} (lichaGen : LichaGenerace f g a) :
    SudaGenerace g f (inverze lichaGen) :=
  lichaGen.existuje_rodic.choose_spec.right

/-
Funkce `g⁻¹` se tam, kde je definována, chová jako prostá funkce.
-/
lemma inverze_jakoProsta {f : A → B} {g : B → A} {x y : A} (hxy : x ≠ y)
    (hx : LichaGenerace f g x) (hy : LichaGenerace f g y) :
    inverze hx ≠ inverze hy := by
  intro rovnost
  have potom : g (inverze hx) = g (inverze hy)
  · exact congr_arg g rovnost
  rw [hx.g_inverze, hy.g_inverze] at potom
  exact hxy potom

/-
Konečně hlavní věta!
Pokud existuje prostá funkce `f : A → B` i prostá funkce `g : B → A`, pak jsou `A` a `B` stejně velké.
-/
theorem jsouStejneVelke : (∃ f : A → B, Prosta f) ∧ (∃ g : B → A, Prosta g) → StejneVelke A B := by
  intro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  classical
  let F : A → B := fun a => if ha : LichaGenerace f g a then inverze ha else f a
  use F
  constructor
  · intro x y hxy
    if hx : LichaGenerace f g x
    then
      if hy : LichaGenerace f g y
      then
        convert_to inverze hx ≠ inverze hy
        · exact dif_pos hx
        · exact dif_pos hy
        apply inverze_jakoProsta
        exact hxy
      else
        convert_to inverze hx ≠ f y
        · exact dif_pos hx
        · exact dif_neg hy
        have sudy : SudaGenerace g f (inverze hx)
        · exact hx.sudaGen_inverze
        have nesudy : ¬ SudaGenerace g f (f y)
        · intro necht
          apply hy
          apply necht.predchoziLichaGenerace
          exact hf
        intro kdyby
        rw [kdyby] at sudy
        exact nesudy sudy
    else
      if hy : LichaGenerace f g y
      then
        convert_to f x ≠ inverze hy
        · exact dif_neg hx
        · exact dif_pos hy
        have sudy : SudaGenerace g f (inverze hy)
        · exact hy.sudaGen_inverze
        have nesudy : ¬ SudaGenerace g f (f x)
        · intro necht
          apply hx
          apply necht.predchoziLichaGenerace
          exact hf
        intro kdyby
        rw [kdyby] at nesudy
        exact nesudy sudy
      else
        convert_to f x ≠ f y
        · exact dif_neg hx
        · exact dif_neg hy
        apply hf
        exact hxy
  · intro z
    if hz : SudaGenerace g f z
    then
      use g z
      have hgz : LichaGenerace f g (g z)
      · exact hz.pristiLichaGenerace
      convert_to inverze hgz = z
      · exact dif_pos hgz
      by_contra pro_spor
      exact hg (inverze hgz) z pro_spor hgz.g_inverze
    else
      by_contra vnejsi_spor
      apply hz
      use 0
      constructor
      intro vnitrni_spor
      apply vnejsi_spor
      obtain ⟨a, ha⟩ := vnitrni_spor
      use a
      convert ha
      have nlga : ¬ LichaGenerace f g a
      · intro hlga
        apply hz
        rw [←ha]
        exact hlga.pristiSudaGenerace
      exact dif_neg nlga
