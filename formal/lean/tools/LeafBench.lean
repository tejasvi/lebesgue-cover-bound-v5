import LebFast.Driver
open LebesgueCover.Fast

/-- Input: `NS 3,5,7`, `NU p/q`, `TAU p/q`, `V n l p/q p/q` lines, then `L lo_0 .. lo_{d-1} hi_0 .. hi_{d-1}` lines
(rationals `p/q`). Output per leaf: `ok bound secs`. -/
def parseRat (s : String) : Rat :=
  match s.splitOn "/" with
  | [a] => (a.toInt! : Rat)
  | [a, b] => mkRat a.toInt! b.toNat!
  | _ => 0

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut ns : List Nat := []
  let mut ν : Rat := 0
  let mut τ : Rat := 0
  let mut VT : Array (Nat × Nat × (Rat × Rat)) := #[]
  let mut nok := 0; let mut n := 0
  let t00 ← IO.monoMsNow
  let mut line ← stdin.getLine
  while line != "" do
    let ws := (line.trimAscii.toString.splitOn " ").filter (· != "")
    match ws with
    | "NS" :: r => ns := (r[0]!.splitOn ",").map String.toNat!
    | "NU" :: r => ν := parseRat r[0]!
    | "TAU" :: r => τ := parseRat r[0]!
    | "V" :: r => VT := VT.push (r[0]!.toNat!, r[1]!.toNat!, (parseRat r[2]!, parseRat r[3]!))
    | "L" :: r =>
      let d := r.length / 2
      let lo := (r.take d).toArray.map parseRat; let hi := (r.drop d).toArray.map parseRat
      let bs := (ns.map mkFBody).toArray
      let V : Nat → Nat → Rat × Rat := fun nn l =>
        match VT.find? (fun (a, b, _) => a == nn && b == l) with
        | some (_, _, v) => v
        | none => (0, 0)
      let t0 ← IO.monoNanosNow
      let (ok, b) := evalLeaf ns bs V ν τ lo hi
      let t1 ← IO.monoNanosNow
      n := n + 1; if ok then nok := nok + 1
      IO.println s!"{if ok then 1 else 0} {b} {(t1 - t0).toFloat / 1e9}"
    | _ => pure ()
    line ← stdin.getLine
  let t11 ← IO.monoMsNow
  IO.println s!"SUMMARY {n} ok {nok} secs {(t11 - t00).toFloat / 1000.0}"
