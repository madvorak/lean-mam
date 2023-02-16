

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


def seznam12345_a : List Nat := [1, 2, 3, 4, 5]
def seznam12345_b : List Nat := seznam123_a ++ [4, 5]
def seznam12345_c : List Nat := 1 :: [2, 3, 4] ++ [5]
def seznam12345_d : List Nat := [1, 2] ++ 3 :: [4, 5]

#eval seznam12345_a
#eval seznam12345_b
#eval seznam12345_c
#eval seznam12345_d

def rovnaji_se_zase : Bool :=
seznam12345_a = seznam12345_b ∧ seznam12345_b = seznam12345_c ∧ seznam12345_c = seznam12345_d
#eval rovnaji_se_zase

def nerovnaji_se : Bool := seznam123_a = seznam12345_a
#eval nerovnaji_se


def soucet : List Int → Int
|        []       => 0
| (hlava :: telo) => hlava + soucet telo

#eval soucet [5, -4, -3, 1]
#eval soucet (List.map (fun (z : Nat) => z) seznam123_a)
#eval soucet (List.map (fun (z : Nat) => z) seznam12345_a)


def delka {α : Type} : List α → Nat
|    []       => 0
| (_ :: telo) => 1 + delka telo

#eval delka seznam123_a
#eval delka seznam12345_a
#eval delka ['a']
#eval delka ([] : List Float)
#eval delka (List.range 42)
#eval delka (0 :: seznam123_a ++ seznam12345_a)


def obrat {α : Type} : List α → List α
|        []       => []
| (hlava :: telo) => obrat telo ++ [hlava]

#eval obrat seznam123_a
#eval obrat seznam12345_a
#eval obrat (obrat seznam12345_a)
#eval seznam123_a ++ obrat seznam123_a
#eval obrat seznam12345_a ++ seznam12345_a


def je_konstantni {α : Type} [DecidableEq α] : List α → Bool
|  []                        => true
|  [_]                       => true
| (prvni :: druhy :: zbytek) => (prvni = druhy) && je_konstantni (druhy :: zbytek)

#eval je_konstantni [5, 5, 5, 5]
#eval je_konstantni [5, 5, 3, 5]
#eval je_konstantni [1, 5, 5, 5]
#eval je_konstantni [5, 5, 5, 4]
#eval je_konstantni ['a', 'A']
#eval je_konstantni ['a', 'a']
