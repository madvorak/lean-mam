import Std.Data.Nat.Basic


-- ## Deklarace funkce

def obvod_obdelnika (a b : Nat) : Nat := 2 * (a + b)

#eval obvod_obdelnika 3 2
#eval obvod_obdelnika 10 10


-- ## Podmínka

def parita (n : Nat) : String :=
if n % 2 = 0
then "sude"
else "liche"

#eval parita 4
#eval parita 5
#eval parita 0
#eval parita (99999999999 * 2 * 77777777777777777 + 1)
#eval parita (2 - 3)


def je_ctverec (a : Nat) : Bool := (Nat.sqrt a) ^ 2 = a

#eval je_ctverec 15
#eval je_ctverec 16
#eval je_ctverec 17
#eval je_ctverec 0
#eval je_ctverec 1
#eval je_ctverec 2
#eval je_ctverec 3
#eval je_ctverec 4
#eval je_ctverec 5


def dvojice_rostouci (x y : Int) : List Int :=
if x = y
then [x]
else if x < y
     then [x, y]
     else [y, x]

#eval dvojice_rostouci 4 6
#eval dvojice_rostouci 5 (-5)
#eval dvojice_rostouci 8 8


-- ## Rekurze

def faktorial : Nat → Nat
| 0   => 1
| n+1 => (n+1) * (faktorial n)

#eval faktorial 6
#eval faktorial 200
#eval faktorial 3000 / faktorial 2999


def fibonacci : Nat → Nat
| 0   => 0
| 1   => 1
| n+2 => fibonacci n + fibonacci (n+1)

#eval fibonacci 5
#eval fibonacci 10
#eval fibonacci 33


partial def ciferny_soucet (a : Nat) : Nat :=
if a < 10
then a
else (a % 10) + ciferny_soucet (a / 10)

#eval ciferny_soucet 524
#eval ciferny_soucet 10200
#eval ciferny_soucet (10^50 - 1)
#eval ciferny_soucet 0


private def suma_pres_radek (f : Nat → Nat → Float) (m : Nat) : Nat → Float
| 0   => 0.0
| n+1 => (f m n) + (suma_pres_radek f m n)

private def suma_pres_obdelnik (f : Nat → Nat → Float) (n : Nat) : Nat → Float
| 0   => 0.0
| m+1 => (suma_pres_radek f m n) + (suma_pres_obdelnik f n m)

def suma_pres_ctverec (f : Nat → Nat → Float) (n : Nat) : Float :=
suma_pres_obdelnik f n n

#eval suma_pres_ctverec (fun _ _ => 1.0) 7
#eval suma_pres_ctverec (fun _ k => Nat.toFloat k) 5
#eval suma_pres_ctverec (fun x y => Nat.toFloat (x * y)) 4
#eval suma_pres_ctverec (fun a b => 1.0 / (1.0 + Nat.toFloat a) / (1.0 + Nat.toFloat b)) 100
#eval suma_pres_ctverec (fun i j => (if i = j then 1.0 else 0.0)) 42


partial def ackermann : Nat → Nat → Nat
| 0  , n   => n+1
| m+1, 0   => ackermann m 1
| m+1, n+1 => ackermann m (ackermann (m+1) n)

#eval ackermann 2 100
#eval ackermann 3 0
#eval ackermann 3 5
