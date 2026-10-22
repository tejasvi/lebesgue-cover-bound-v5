import LebFast.Model
import LebFast.Exact

/-!
# Leaf evaluation: float proposal, exact check

The proposal (witness heuristic, fan centre, `β`, `σ`) is computed in floating point and converted to exact dyadic
rationals; the exact check `leafOKF` decides. Witness sets: `N = 256` first, then `N = 1024`.
-/

namespace LebesgueCover.Fast

/-- The exact value of a double (finite inputs). -/
def floatToRat (x : Float) : Rat :=
  let b : Nat := x.toBits.toNat
  let neg := b / 2 ^ 63 = 1
  let ex : Nat := (b / 2 ^ 52) % 2048
  let mant : Nat := b % 2 ^ 52
  let (m, e) : Nat × Int := if ex = 0 then (mant, -1074) else (mant + 2 ^ 52, Int.ofNat ex - 1075)
  let v : Rat := if e ≥ 0 then ((m * 2 ^ e.toNat : Nat) : Rat) else mkRat m (2 ^ (-e).toNat)
  if neg then -v else v

def ratToFloat (q : Rat) : Float := Float.ofInt q.num / q.den.toFloat

def dyUp40 (x : Float) : Rat := mkRat (Rat.ceil (floatToRat x * (2 ^ 40 : Nat))) (2 ^ 40)
def dyNear40 (x : Float) : Rat := mkRat (Rat.floor (floatToRat x * (2 ^ 40 : Nat) + 1 / 2)) (2 ^ 40)

/-- Exact data of a proposal. -/
def exactData (P : Proposal) : List (Nat × (Rat × Rat)) × (Rat × Rat) × (Nat → Rat) × (Nat → Rat) :=
  let W := (List.range P.ib.size).map fun j => (P.ib[j]!, (floatToRat P.Q[j]!.1, floatToRat P.Q[j]!.2))
  let z := (floatToRat P.z.1, floatToRat P.z.2)
  let betaA := P.beta.map dyNear40
  let sigmaA := P.sigma.map fun v => dyUp40 (v * (1.0 + 1e-6) + 1e-12)
  (W, z, fun i => betaA.getD i 0, fun a => sigmaA.getD a 0)

/-- Leaf evaluation: exact verdict and the float bound of the accepted (or last) proposal. -/
def evalLeaf (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat) :
    Bool × Float := Id.run do
  let k := ns.length
  let loF := lo.map ratToFloat; let hiF := hi.map ratToFloat
  let L := mkLeaf k loF hiF
  let pl := centrePlace L
  let mut last := -1.0
  for (N, eps) in [((256 : Nat), (1e-5 : Float)), (1024, 1e-6)] do
    match proposeAt bs L pl N eps with
    | none => pure ()
    | some P =>
      last := P.bound
      let (W, z, β, σ) := exactData P
      if leafOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) W z β σ then
        return (true, P.bound)
  return (false, last)

end LebesgueCover.Fast
