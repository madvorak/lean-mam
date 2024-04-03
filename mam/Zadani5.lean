import mam.Cislo5


def prvnich_n_krychli_sestupne : ℕ → List ℕ
| 0   => []
| n+1 => n^3 :: prvnich_n_krychli_sestupne n

def prvnich_n_krychli : ℕ → List ℕ :=
obrat ∘ prvnich_n_krychli_sestupne

theorem soucet_prvnich_n_krychli (n : ℕ) :
    soucet (prvnich_n_krychli n) = ((n-1) ^ 2 * n ^ 2) / 4 := by
  sorry


theorem obrat_obrat {T : Type} (x : List T) : obrat (obrat x) = x := by
  sorry
