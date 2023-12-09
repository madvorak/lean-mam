import mam.Cislo2


def nasobky_sedmi : Nat → List Nat
| 0   => [ ]
| n+1 => (7 * n) :: (nasobky_sedmi n)

#eval nasobky_sedmi 6


def soucin : List Int → Int
| [ ]           => 1
| hlava :: telo => hlava * soucin telo

#eval soucin [2, 3]
#eval soucin [-3, 15, -2]
#eval soucin [953812, -748513, 0, -982331, 198234]


def vynech_opakovani {T : Type} [DecidableEq T] : List T → List T
| [ ]         => [ ]
| [a]         => [a]
| a :: b :: z => if a = b
                 then vynech_opakovani (a :: z)
                 else a :: vynech_opakovani (b :: z)

#eval vynech_opakovani [1, 3, 3, 7]
#eval vynech_opakovani ['a', 'b', 'b', 'b', 'b', 'a', 'b', 'c', 'c', 'a']
#eval vynech_opakovani [7, 2, 2, 2, 2, 2]
#eval vynech_opakovani [4, 4, 4, 4, 5, 6]
#eval vynech_opakovani [0]
#eval vynech_opakovani [0, 0, 0]
#eval vynech_opakovani (List.range 8)
#eval vynech_opakovani ((List.range 8) ++ obrat (List.range 8))
#eval vynech_opakovani (List.map (· % 2) (List.range 20))
#eval vynech_opakovani (List.map (· / 2) (List.range 20))
#eval vynech_opakovani (List.map (· / 10) (List.range 20))
#eval vynech_opakovani (List.map je_ctverec (List.range 100))
#eval String.mk (vynech_opakovani "".toList)
#eval String.mk (vynech_opakovani "ahoj".toList)
#eval String.mk (vynech_opakovani "ahoooooooooooooooooooooooj".toList)
#eval String.mk (vynech_opakovani "       a           b            c      ".toList)


def prefixove_soucty_pom (pricist : Int) : List Int → List Int
| [ ]     => [ ]
| x :: xs => (pricist + x) :: prefixove_soucty_pom (pricist + x) xs

def prefixove_soucty : List Int → List Int :=
prefixove_soucty_pom 0

#eval prefixove_soucty [1, 2, 5, 0]
#eval prefixove_soucty [1, -5, 3, 2, 2, 2, 2]
#eval prefixove_soucty [0, 0, 10, -1, -2, -3, -4, -5, 0, 10, 0]

def postfixove_soucty : List Int → List Int :=
obrat_rychle ∘ prefixove_soucty ∘ obrat_rychle

#eval postfixove_soucty [1, 2, 5, 0]
#eval postfixove_soucty [1, -5, 3, 2, 2, 2, 2]
#eval postfixove_soucty [0, 0, 10, -1, -2, -3, -4, -5, 0, 10, 0]


def postfixove_soucty' : List Int → List Int
| [ ]     => [ ]
| x :: xs => match postfixove_soucty' xs with
             | [ ]     => [x]
             | z :: zs => (x+z) :: z :: zs

#eval postfixove_soucty' [1, 2, 5, 0]
#eval postfixove_soucty' [1, -5, 3, 2, 2, 2, 2]
#eval postfixove_soucty' [0, 0, 10, -1, -2, -3, -4, -5, 0, 10, 0]

def prefixove_soucty' : List Int → List Int :=
obrat_rychle ∘ postfixove_soucty ∘ obrat_rychle

#eval prefixove_soucty' [1, 2, 5, 0]
#eval prefixove_soucty' [1, -5, 3, 2, 2, 2, 2]
#eval prefixove_soucty' [0, 0, 10, -1, -2, -3, -4, -5, 0, 10, 0]
