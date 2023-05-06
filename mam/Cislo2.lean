import mam.Cislo1


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

def rovnaji_se : Bool :=
seznam123_a = seznam123_b ∧ seznam123_b = seznam123_c ∧ seznam123_c = seznam123_d ∧ seznam123_d = seznam123_e
#eval rovnaji_se


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

def rovnaji_se_zase : Bool := seznam12345_a = seznam12345_b ∧ seznam12345_b = seznam12345_c ∧
  seznam12345_c = seznam12345_d ∧ seznam12345_d = seznam12345_e
#eval rovnaji_se_zase

def nerovnaji_se : Bool := seznam123_a = seznam12345_a
#eval nerovnaji_se


def prvnich_n_lichych_sestupne : Nat → List Nat
| 0   => []
| n+1 => (2 * n + 1) :: (prvnich_n_lichych_sestupne n)

#eval prvnich_n_lichych_sestupne 6


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


def obrat {T : Type} : List T → List T
| [ ]           => []
| hlava :: telo => obrat telo ++ [hlava]

#eval obrat seznam123_a
#eval obrat seznam12345_a
#eval obrat (obrat seznam12345_a)
#eval seznam123_a ++ obrat seznam123_a
#eval obrat seznam12345_a ++ seznam12345_a

def prvnich_n_lichych : Nat → List Nat :=
obrat ∘ prvnich_n_lichych_sestupne

#eval prvnich_n_lichych 8
#eval soucet (prvnich_n_lichych 8)


private def obrat_rychl {T : Type} (pripoj : List T) : List T → List T
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
private def nah := [5, 2, 6, 0, 2, 8, 4, 1, 2, 3, 6, 9, 1, 5, 5, 5, 4, 7, 0, 2, 3, 4, 9, 8, 1, 6, 4, 5]
#eval obrat nah = obrat_rychle nah
#eval obrat_rychle nah = obrat_rychla nah
#eval obrat_rychla (obrat nah) = nah


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


def skalarni_soucin : List Float → List Float → Float
| [ ]    , _       => 0.0
| _      , [ ]     => 0.0
| a :: as, b :: bs => a*b + skalarni_soucin as bs

#eval skalarni_soucin [3, 0, 0.5, -2] [2, 8.7, 4, -1]
private def jedna_az (n : Nat) : List Float := (List.map (fun a => Nat.toFloat (a+1)) (List.range n))
#eval skalarni_soucin (jedna_az 5) (jedna_az 5)
#eval skalarni_soucin (jedna_az 5) (jedna_az 9)
#eval skalarni_soucin (jedna_az 5) (obrat (jedna_az 5))
#eval skalarni_soucin (jedna_az 5) (List.map (1 / ·) (jedna_az 5))
#eval skalarni_soucin (jedna_az 5) (obrat (List.map (1 / ·) (jedna_az 5)))
#eval skalarni_soucin (jedna_az 100) (List.map ((-1) ^ ·) (jedna_az 100))
#eval skalarni_soucin (jedna_az 6666) (List.map ((-1) ^ ·) (jedna_az 6666))


private def fibo_gen (n : Nat) : List Nat → List Nat
| [ ]         => []
| [ _ ]       => []
| a :: b :: l => if n = 0
                 then a :: b :: l
                 else fibo_gen (n-1) ((a+b) :: a :: b :: l)

def fibo_list (n : Nat) : List Nat :=
obrat (fibo_gen (n-2) [1, 0])

#eval fibo_list 12

def seznam_pomeru : List Nat → List Float
| [ ]         => []
| [ _ ]       => []
| a :: b :: l => (Nat.toFloat a / Nat.toFloat b) :: seznam_pomeru (b :: l)

def fibo_pomery (n : Nat) : List Float :=
seznam_pomeru (fibo_list (n+1))

#eval fibo_pomery 25


def rozdily : List Nat → List Nat
| [ ]         => []
| [ _ ]       => []
| a :: b :: l => (b-a) :: rozdily (b :: l)

#eval rozdily [5, 5, 9, 19, 99, 100]
#eval rozdily seznam12345_a
#eval rozdily [42]
#eval rozdily []
#eval List.map (· ^ 2) (List.range 14)
#eval rozdily (List.map (· ^ 2) (List.range 14))
#eval rozdily (rozdily (List.map (· ^ 2) (List.range 14)))
#eval rozdily (rozdily (rozdily (List.map (· ^ 2) (List.range 14))))
#eval List.map (· ^ 3) (List.range 13)
#eval rozdily $ List.map (· ^ 3) (List.range 13)
#eval rozdily $ rozdily $ List.map (· ^ 3) (List.range 13)
#eval rozdily $ rozdily $ rozdily $ List.map (· ^ 3) (List.range 13)
#eval rozdily $ rozdily $ rozdily $ rozdily $ List.map (· ^ 3) (List.range 13)
#eval List.map (· ^ 4) (List.range 12)
#eval rozdily $ List.map (· ^ 4) (List.range 12)
#eval rozdily $ rozdily $ List.map (· ^ 4) (List.range 12)
#eval rozdily $ rozdily $ rozdily $ List.map (· ^ 4) (List.range 12)
#eval rozdily $ rozdily $ rozdily $ rozdily $ List.map (· ^ 4) (List.range 12)
#eval rozdily $ rozdily $ rozdily $ rozdily $ rozdily $ List.map (· ^ 4) (List.range 12)
#eval List.map (· ^ 5) (List.range 11)
#eval rozdily $ List.map (· ^ 5) (List.range 11)
#eval rozdily $ rozdily $ List.map (· ^ 5) (List.range 11)
#eval rozdily $ rozdily $ rozdily $ List.map (· ^ 5) (List.range 11)
#eval rozdily $ rozdily $ rozdily $ rozdily $ List.map (· ^ 5) (List.range 11)
#eval rozdily $ rozdily $ rozdily $ rozdily $ rozdily $ List.map (· ^ 5) (List.range 11)
#eval rozdily $ rozdily $ rozdily $ rozdily $ rozdily $ rozdily $ List.map (· ^ 5) (List.range 11)


def aplikuj_tolikrat {β : Type} (operace : β → β) (vstup : β) : Nat → β
| 0   => vstup
| n+1 => aplikuj_tolikrat operace (operace vstup) n

#eval aplikuj_tolikrat (· + 3) 10 5
#eval aplikuj_tolikrat (1 :: ·) [] 9
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 3
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 6
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 9
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 12
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 15
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 50
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) 42.0 100
#eval aplikuj_tolikrat (fun x => 1 + 1 / x) (-100000.0) 100
#eval aplikuj_tolikrat rozdily (List.map (· ^ 2) (List.range 10)) 2
#eval aplikuj_tolikrat rozdily (List.map (· ^ 3) (List.range 10)) 3
#eval aplikuj_tolikrat rozdily (List.map (· ^ 4) (List.range 10)) 4
#eval aplikuj_tolikrat rozdily (List.map (· ^ 5) (List.range 10)) 5
#eval aplikuj_tolikrat rozdily (List.map (· ^ 6) (List.range 10)) 6
#eval aplikuj_tolikrat rozdily (List.map (· ^ 7) (List.range 10)) 7
#eval aplikuj_tolikrat rozdily (List.map (· ^ 8) (List.range 10)) 8
#eval aplikuj_tolikrat rozdily (List.map (· ^ 9) (List.range 10)) 9
#eval faktorial 9
