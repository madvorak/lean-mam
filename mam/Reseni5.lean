import mam.Cislo5


def prvnich_n_krychli_sestupne : ℕ → List ℕ
| 0   => []
| n+1 => n^3 :: prvnich_n_krychli_sestupne n

def prvnich_n_krychli : ℕ → List ℕ :=
obrat ∘ prvnich_n_krychli_sestupne

lemma soucet_prvnich_n_krychli_sestupne (m : ℕ) :
    soucet (prvnich_n_krychli_sestupne m.succ) * 4 = (m ^ 2 * m.succ ^ 2) := by
  induction m with
  | zero => decide
  | succ n ih =>
    convert_to ((n+1) ^ 3 + soucet (prvnich_n_krychli_sestupne (n+1))) * 4 = (n+1) ^ 2 * (n+2) ^ 2
    convert_to (n+1) ^ 3 * 4 + soucet (prvnich_n_krychli_sestupne (n+1)) * 4 = (n+1) ^ 2 * (n+2) ^ 2
    · ring
    rw [ih]
    convert_to (n+1) ^ 3 * 4 + n ^ 2 * (n+1) ^ 2 = (n+1) ^ 2 * (n+2) ^ 2
    ring

theorem soucet_prvnich_n_krychli (n : ℕ) :
    soucet (prvnich_n_krychli n) = ((n-1) ^ 2 * n ^ 2) / 4 := by
  cases n with
  | zero => decide
  | succ m =>
    dsimp [prvnich_n_krychli]
    rw [obrat_zachovava_soucet]
    convert_to soucet (prvnich_n_krychli_sestupne m.succ) = m^2 * m.succ^2 / 4
    rw [←soucet_prvnich_n_krychli_sestupne m]
    simp


lemma obrat_pripoj {T : Type} (x : List T) (a : T) : obrat (x ++ [a]) = a :: obrat x := by
  induction x with
  | nil => rfl
  | cons d l ih => simp [obrat, ih]

theorem obrat_obrat {T : Type} (x : List T) : obrat (obrat x) = x := by
  induction x with
  | nil => rfl
  | cons d l ih => simp [obrat, ih, obrat_pripoj]
