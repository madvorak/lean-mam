import src.Cislo1
import src.Cislo2


def jekon {T : Type} [DecidableEq T] : List T → Bool
| [ ]                      => true
| [ _ ]                    => true
| prvni :: druhy :: zbytek => (prvni = druhy) && jekon zbytek

#eval jekon [5, 5, 5, 5]
#eval jekon [5, 5, 3, 5]
#eval jekon [1, 5, 5, 5]
#eval jekon [5, 5, 5, 4]
#eval jekon [5, 2, 5, 5]
#eval jekon ['a', 'A']
#eval jekon ['a', 'a']


def vynech_opakovani {T : Type} [DecidableEq T] : List T → List T := fun _ => [] -- TODO

#eval vynech_opakovani [1, 3, 3, 1]
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
