import LebFast.Heur
open LebesgueCover.Fast

/-- Reads lines `N eps ns(comma) rho_1 tx_1 ty_1 ... rho_k tx_k ty_k` (floats as IEEE bits in hex) and prints the
witnesses (body and IEEE bits of the body-frame point). -/
def hexToNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0
def natToHex (n : Nat) : String := (String.mk (Nat.toDigits 16 n)).pushn ' ' 0
def fl (s : String) : Float := Float.ofBits (hexToNat s).toUInt64

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut line ← stdin.getLine
  while line != "" do
    let ws := (line.trimAscii.toString.splitOn " ").filter (· != "")
    let N := ws[0]!.toNat!
    let eps := fl ws[1]!
    let ns := (ws[2]!.splitOn ",").map String.toNat!
    let bs := (ns.map mkFBody).toArray
    let mut pl : FPlace := #[(0.0, (0.0, 0.0))]
    for i in [0:ns.length] do
      pl := pl.push (fl ws[3 + 3 * i]!, (fl ws[4 + 3 * i]!, fl ws[5 + 3 * i]!))
    let (ib, Q) := witnessesF bs pl N eps
    let mut out := s!"{ib.size}"
    for j in [0:ib.size] do
      out := out ++ s!" {ib[j]!}:{natToHex Q[j]!.1.toBits.toNat}:{natToHex Q[j]!.2.toBits.toNat}"
    IO.println out
    line ← stdin.getLine
