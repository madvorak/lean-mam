import mam.Cislo1


-- ## Vytvoření seznamu

def seznam123_a : List Nat := [1, 2, 3]
def seznam123_b : List Nat := 1 :: [2, 3]
def seznam123_c : List Nat := 1 :: (2 :: [3])
def seznam123_d : List Nat := 1 :: 2 :: [3]
def seznam123_e : List Nat := 1 :: 2 :: 3 :: []

#eval seznam123_a
#eval seznam123_b
#eval seznam123_c
#eval seznam123_d
#eval seznam123_e


def seznam12345_a : List Nat := 1 :: 2 :: 3 :: 4 :: 5 :: []
def seznam12345_b : List Nat := [1, 2, 3, 4, 5]
def seznam12345_c : List Nat := 1 :: [2, 3, 4] ++ [5]
def seznam12345_d : List Nat := [1, 2] ++ 3 :: [4, 5]
def seznam12345_e : List Nat := seznam123_a ++ [4, 5]

#eval seznam12345_a
#eval seznam12345_b
#eval seznam12345_c
#eval seznam12345_d
#eval seznam12345_e


def prvnich_n_lichych_sestupne : Nat → List Nat
| 0   => []
| n+1 => (2 * n + 1) :: (prvnich_n_lichych_sestupne n)

#eval prvnich_n_lichych_sestupne 6


-- ## Zpracování seznamu

def soucet : List Nat → Nat
| [ ]           => 0
| hlava :: telo => hlava + soucet telo

#eval soucet seznam123_a
#eval soucet seznam12345_a
#eval soucet (prvnich_n_lichych_sestupne 11)


def delka {T : Type} : List T → Nat
| [ ]       => 0
| _ :: telo => 1 + delka telo

#eval delka seznam123_a
#eval delka seznam12345_a
#eval delka ['a']
#eval delka ([] : List Float)
#eval delka (0 :: seznam123_a ++ seznam12345_a)
#eval delka (List.range 42)
#eval delka (prvnich_n_lichych_sestupne 1999)


def je_konstantni {T : Type} [DecidableEq T] : List T → Bool
| [ ]                      => true
| [ _ ]                    => true
| prvni :: druhy :: zbytek => (prvni = druhy) && je_konstantni (druhy :: zbytek)

#eval je_konstantni [5, 5, 5, 5]
#eval je_konstantni [5, 5, 3, 5]
#eval je_konstantni [1, 5, 5, 5]
#eval je_konstantni [5, 5, 5, 4]
#eval je_konstantni [5, 2, 5, 5]
#eval je_konstantni ['a', 'A']
#eval je_konstantni ['a', 'a']


def skalarni_soucin : List Float → List Float → Float
| [ ]    , _       => 0.0
| _      , [ ]     => 0.0
| a :: as, b :: bs => a*b + skalarni_soucin as bs

#eval skalarni_soucin [3, 0, 0.5, -2] [2, 8.7, 4, -1]
private def jedna_az (n : Nat) : List Float := (List.range n).map (fun a => Nat.toFloat (a+1))
#eval skalarni_soucin (jedna_az 5) (jedna_az 5)
#eval skalarni_soucin (jedna_az 5) (jedna_az 9)
#eval skalarni_soucin (jedna_az 5) (List.map (1 / ·) (jedna_az 5))
#eval skalarni_soucin (jedna_az 100) (List.map ((-1) ^ ·) (jedna_az 100))
#eval skalarni_soucin (jedna_az 6666) (List.map ((-1) ^ ·) (jedna_az 6666))


-- ## Přetvoření seznamu

def obrat {T : Type} : List T → List T
| [ ]           => []
| hlava :: telo => obrat telo ++ [hlava]

#eval obrat seznam123_a
#eval obrat seznam12345_a
#eval obrat (obrat seznam12345_a)
#eval seznam123_a ++ obrat seznam123_a
#eval obrat seznam12345_a ++ seznam12345_a
#eval skalarni_soucin (jedna_az 5) (obrat (jedna_az 5))
#eval skalarni_soucin (jedna_az 5) (obrat (List.map (1 / ·) (jedna_az 5)))

def prvnich_n_lichych : Nat → List Nat :=
obrat ∘ prvnich_n_lichych_sestupne

#eval prvnich_n_lichych 8
#eval soucet (prvnich_n_lichych 8)


def obrat_rychl {T : Type} (pripoj : List T) : List T → List T
| [ ]           => pripoj
| hlava :: telo => obrat_rychl (hlava :: pripoj) telo

def obrat_rychle {T : Type} (seznam : List T) : List T :=
obrat_rychl [] seznam

def obrat_rychla {T : Type} : List T → List T
| seznam => obrat_rychl [] seznam

#eval obrat        (seznam123_a ++ seznam12345_a)
#eval obrat_rychle (seznam123_a ++ seznam12345_a)
#eval obrat_rychla (seznam123_a ++ seznam12345_a)
#eval obrat        ([] : List Nat)
#eval obrat_rychle ([] : List Nat)
#eval obrat_rychla ([] : List Nat)
private def nah := [5, 2, 6, 0, 2, 8, 4, 1, 3, 6, 9, 1, 5, 5, 5, 4, 7, 0, 3, 4, 9, 8, 1, 6, 4, 5]
#eval obrat nah = obrat_rychle nah
#eval obrat_rychle (nah ++ nah) = obrat_rychla (nah ++ nah)
#eval obrat_rychla (obrat nah) = nah


-- ## Hrátky se seznamy

def je_palindrom {T : Type} [DecidableEq T] (seznam : List T) : Bool :=
seznam = obrat_rychle seznam

#eval je_palindrom [1]
#eval je_palindrom [1, 7]
#eval je_palindrom [1, 7, 1]
#eval je_palindrom [1, 7, 1, 1]
#eval je_palindrom [1, 7, 1, 1, 7]
#eval je_palindrom [1, 7, 1, 1, 7, 1]
#eval je_palindrom "".toList
#eval je_palindrom "oko".toList
#eval je_palindrom "okolo".toList
#eval je_palindrom "abba".toList
#eval je_palindrom "baba".toList
#eval je_palindrom "kobyla ma maly bok".toList
#eval je_palindrom "kobylamamalybok".toList
#eval je_palindrom "()()".toList
#eval je_palindrom "())(".toList
#eval je_palindrom (seznam12345_a ++ seznam12345_a)
#eval je_palindrom (seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (obrat seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (seznam12345_a ++ seznam12345_a ++ seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (seznam12345_a ++ seznam12345_a ++ obrat seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (seznam12345_a ++ obrat seznam12345_a ++ seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (obrat seznam12345_a ++ seznam12345_a ++ seznam12345_a ++ obrat seznam12345_a)
#eval je_palindrom (obrat seznam12345_a ++ seznam12345_a ++ obrat seznam12345_a ++ seznam12345_a)


def kte_mocniny_sestupne (k : Nat) : Nat → List Nat
| 0   => []
| n+1 => (n^k) :: (kte_mocniny_sestupne k n)

def kte_mocniny (k : Nat) (n : Nat) :=
obrat_rychle (kte_mocniny_sestupne k n)

#eval kte_mocniny 6 5


def rozdily_sousedu : List Nat → List Nat
| [ ]         => []
| [ _ ]       => []
| a :: b :: s => (b-a) :: rozdily_sousedu (b :: s)

#eval rozdily_sousedu [5, 5, 9, 19, 99, 100]
#eval rozdily_sousedu seznam12345_a
#eval rozdily_sousedu [42]
#eval rozdily_sousedu []

#eval kte_mocniny 2 11
#eval rozdily_sousedu (kte_mocniny 2 11)
#eval rozdily_sousedu (rozdily_sousedu (kte_mocniny 2 11))


def aplikuj_tolikrat {T : Type} (oper : T → T) (vstup : T) : Nat → T
| 0   => vstup
| n+1 => aplikuj_tolikrat oper (oper vstup) n

#eval aplikuj_tolikrat (· + 3) 10 6
#eval aplikuj_tolikrat (1 :: ·) [] 9

#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 0
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 1
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 2
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 3
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 4
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 5
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 6
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 7
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 8
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 8) 9

#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 2 11) 2
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 3 11) 3
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 4 11) 4
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 5 11) 5
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 6 11) 6
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 7 11) 7
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 8 11) 8
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 9 11) 9
#eval aplikuj_tolikrat rozdily_sousedu (kte_mocniny 10 11) 10
#eval faktorial 10

#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 3
#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 6
#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 9
#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 12
#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 15
#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 50
#eval aplikuj_tolikrat (1 + 1 / ·) 42.0 100
#eval aplikuj_tolikrat (1 + 1 / ·) (-100000.0) 100
