import mam.Cislo1


def povrch_kvadru (a b c : Nat) : Nat := 2 * (a * b + b * c + c * a)

#eval povrch_kvadru 2 3 4    /- `52` -/
#eval povrch_kvadru 6 6 6    /- `216` -/
#eval povrch_kvadru 14 0 7    /- `196` -/
#eval povrch_kvadru 999 1000 1001    /- `5999998` -/


def obsah_trojuhelniku (a b c : Float) : Float :=
let s := (a + b + c) / 2 ;
Float.sqrt (s * (s - a) * (s - b) * (s - c))

#eval obsah_trojuhelniku 12.7 15.8 19.4    /- `99.957071` -/
#eval obsah_trojuhelniku 3 4 5    /- `6` -/
#eval obsah_trojuhelniku 12 5 13    /- `30` -/
#eval obsah_trojuhelniku 1 1 1    /- `0.433013` -/
#eval obsah_trojuhelniku 1 1 0    /- `0` -/
#eval obsah_trojuhelniku 2 1 1    /- `0` -/
#eval obsah_trojuhelniku 500 999 500    /- `11166.366909` -/


def je_ctvrta_mocnina (a : Nat) : Bool := (Nat.sqrt (Nat.sqrt a)) ^ 4 = a

#eval je_ctvrta_mocnina 15
#eval je_ctvrta_mocnina 16
#eval je_ctvrta_mocnina 17
#eval je_ctvrta_mocnina 0
#eval je_ctvrta_mocnina 1
#eval je_ctvrta_mocnina 2
#eval je_ctvrta_mocnina 3
#eval je_ctvrta_mocnina 4
#eval je_ctvrta_mocnina 5
#eval List.filter je_ctvrta_mocnina (List.range 5000) /- `[0, 1, 16, 81, 256, 625, 1296, 2401, 4096]` -/


def reseni_kvadraticke_rovnice (a b c : Float) : List Float :=
let D := b * b - 4 * a * c ;
if D > 0.0
then let d := Float.sqrt D ;
     [(- b - d) / (2 * a), (- b + d) / (2 * a)]
else if D == 0.0
     then [(- b) / (2 * a)]
     else []

/- `x^2 = 2` -/
#eval reseni_kvadraticke_rovnice 1 0 (-2)
/- `[-1.414214, 1.414214]` -/

/- `x^2 = 9` -/
#eval reseni_kvadraticke_rovnice (-1) 0 9
/- `[3, -3]` -/

/- `x^2 = 1/2` -/
#eval reseni_kvadraticke_rovnice 2 0 (-1)
/- `[-0.707107, 0.707107]` -/

/- `25x^2 = 1` -/
#eval reseni_kvadraticke_rovnice (-25) 0 1
/- `[0.2, -0.2]` -/

/- `x^2 + 2x + 1 = 0` -/
#eval reseni_kvadraticke_rovnice 1 2 1
/- `[-1]` -/

/- `x^2 + x + 1 = 0` -/
#eval reseni_kvadraticke_rovnice 1 1 1
/- `[]` -/

/- `x^2 + -6x + 9 = 0` -/
#eval reseni_kvadraticke_rovnice 1 (-6) 9
/- `[3]` -/

/- `x^2 + -6x + 10 = 0` -/
#eval reseni_kvadraticke_rovnice 1 (-6) 10
/- `[]` -/

/- `x^2 - 14x + 49 = 0` -/
#eval reseni_kvadraticke_rovnice 1 (-14) 49
/- `[7]` -/

/- `x^2 - 14x + 50 = 0` -/
#eval reseni_kvadraticke_rovnice 1 (-14) 50
/- `[]` -/

/- `x^2 - 14x + 48 = 0` -/
#eval reseni_kvadraticke_rovnice 1 (-14) 48
/- `[6, 8]` -/

/- `x^2 - 29x - 28 = 0` -/
#eval reseni_kvadraticke_rovnice 1 (-29) 28
/- `[1, 28]` -/

/- `x^2 + 18x + 77 = 0` -/
#eval reseni_kvadraticke_rovnice 1 18 77
/- `[-11, -7]` -/

/- `77x^2 + 18x + 1 = 0` -/
#eval reseni_kvadraticke_rovnice 77 18 1
/- `[-0.142857, -0.0909091]` -/

/- `16x^2 + 40x + 25 = 0` -/
#eval reseni_kvadraticke_rovnice 16 40 25
/- `[-1.25]` -/

/- `25x^2 + 40x + 16 = 0` -/
#eval reseni_kvadraticke_rovnice 25 40 16
/- `[-0.8]` -/


partial def ciferace (a : Nat) : Nat :=
if a < 10
then a
else ciferace (ciferny_soucet a)

#eval ciferace 3
#eval ciferace 52
#eval ciferace 919
#eval ciferace 999
#eval ciferace 123456
#eval ciferace 100000000000000000000000000000000000000000000000000000001
#eval ciferace 9999999999999999999999999999999999999999999999999999999999999


private def maximum_pres_treti (g : Nat → Nat → Nat → Nat) (k m : Nat) : Nat → Nat
| 0   => 0
| n+1 => max (g k m n) (maximum_pres_treti g k m n)

private def maximum_pres_druhy (g : Nat → Nat → Nat → Nat) (k n : Nat) : Nat → Nat
| 0   => 0
| m+1 => max (maximum_pres_treti g k m n) (maximum_pres_druhy g k n m)

private def maximum_pres_prvni (g : Nat → Nat → Nat → Nat) (m n : Nat) : Nat → Nat
| 0   => 0
| k+1 => max (maximum_pres_druhy g k n m) (maximum_pres_prvni g m n k)

def maximum_z_krychle (g : Nat → Nat → Nat → Nat) (n : Nat) : Nat :=
maximum_pres_prvni g n n n

#eval maximum_z_krychle (fun x y z => x + y - z) 10    /- `18` -/
#eval maximum_z_krychle (fun x y z => x * (6-x) * y * (4-y) * z * (10-z)) 7    /- `900` -/


private def soucet_delitelu_pod (a : Nat) : Nat → Nat
| 0   => 0
| d+1 => (if a % d = 0 then d + a / d else 0) + (soucet_delitelu_pod a d)

private def soucet_delitelu (a : Nat) : Nat :=
soucet_delitelu_pod a (1 + Nat.sqrt a) - a - (if je_ctverec a then Nat.sqrt a else 0)

def je_prvocislo (a : Nat) : Bool :=
soucet_delitelu a = 1

def je_dokonale_cislo (a : Nat) : Bool :=
a > 0 && soucet_delitelu a = a

private def vypis_splnujici_do (podminka : Nat → Bool) (n : Nat) :=
List.filter podminka (List.range (n+1))

def seznam_prvocisel_do (n : Nat) :=
vypis_splnujici_do je_prvocislo n

#eval seznam_prvocisel_do 40
#eval seznam_prvocisel_do 100

def seznam_dokonalych_cisel_do (n : Nat) :=
vypis_splnujici_do je_dokonale_cislo n

#eval seznam_dokonalych_cisel_do 500
#eval seznam_dokonalych_cisel_do 10000
