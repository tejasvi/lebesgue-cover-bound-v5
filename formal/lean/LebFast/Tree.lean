import LebFast.Driver

/-!
# Certificate trees (compiled walker)

A cell's tree is a DFS preorder code list: `a < d` splits coordinate `a` at the exact midpoint (lower half first),
`254` is a single-fan leaf, `252` a combination leaf whose fans are given in the side list by their shift sign
vectors and weights. Leaf data (witnesses, centres, `β`, `σ`) are recomputed by the float proposal code and checked
exactly by `leafOKF` / `combOKF`.
-/

namespace LebesgueCover.Fast

/-- One witness-set attempt for a single-fan leaf. -/
def tryProp (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat)
    (L : FLeaf) (pl : FPlace) (N : Nat) (eps : Float) : Bool :=
  match proposeAt bs L pl N eps with
  | none => false
  | some P =>
    let d := exactData P
    leafOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) d.1 d.2.1 d.2.2.1 d.2.2.2

/-- Single-fan leaf: witness sets `N = 256` then `N = 1024`. -/
def evalLeafB (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat) : Bool :=
  let L := mkLeaf ns.length (lo.map ratToFloat) (hi.map ratToFloat)
  let pl := centrePlace L
  tryProp ns bs V ν τ lo hi L pl 256 1e-5 || tryProp ns bs V ν τ lo hi L pl 1024 1e-6

/-- The placement `c + sv ∘ h` (box coordinates) for the heuristic. -/
def shiftPlace (L : FLeaf) (sv : List Int) : FPlace := Id.run do
  let d := L.c.size
  let p := (Array.range d).map fun a => L.c[a]! + (Float.ofInt (sv.getD a 0)) * L.h[a]!
  let mut pl : FPlace := #[(0.0, (0.0, 0.0))]
  for i in [1:L.k + 1] do
    let (si, tx, ty) := pIdx i
    pl := pl.push ((if i == 1 then 0.0 else 2.0 * Float.atan p[si]!), (p[tx]!, p[ty]!))
  return pl

/-- Combination leaf: one fan per shift sign vector (`N = 256` if the flag is set, else `N = 1024`), with the given
weights. -/
def evalCombB (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat)
    (fs : List (Bool × List Int × Rat)) : Bool :=
  let L := mkLeaf ns.length (lo.map ratToFloat) (hi.map ratToFloat)
  let props := fs.map fun (cheap, sv, lam) =>
    (proposeAt bs L (shiftPlace L sv) (if cheap then 256 else 1024) (if cheap then 1e-5 else 1e-6), lam)
  if props.all (fun (P, _) => P.isSome) then
    let fans := props.map fun (P, lam) =>
      let d := exactData (P.getD default)
      (d.1, d.2.1, d.2.2.1, d.2.2.2, lam)
    combOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) fans
  else false

/-- Walk a tree: returns the unread codes, side entries and delegated boxes, or `none` if a check fails. Code `250`
is a delegated subtree: its box must equal the next box of `subs` (that box is checked in another module). -/
def walk (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) :
    Nat → List Nat → List (List (Bool × List Int × Rat)) → List (Array Rat × Array Rat) → Array Rat → Array Rat →
      Option (List Nat × List (List (Bool × List Int × Rat)) × List (Array Rat × Array Rat))
  | 0, _, _, _, _, _ => none
  | _ + 1, [], _, _, _, _ => none
  | fuel + 1, c :: cs, sd, subs, lo, hi =>
    if c = 254 then (if evalLeafB ns bs V ν τ lo hi then some (cs, sd, subs) else none)
    else if c = 252 then
      match sd with
      | [] => none
      | f :: sd' => if evalCombB ns bs V ν τ lo hi f then some (cs, sd', subs) else none
    else if c = 250 then
      match subs with
      | [] => none
      | b :: subs' => if b.1 = lo ∧ b.2 = hi then some (cs, sd, subs') else none
    else if c < lo.size ∧ c < hi.size then
      let m := (lo[c]! + hi[c]!) / 2
      match walk ns bs V ν τ fuel cs sd subs lo (hi.set! c m) with
      | none => none
      | some (cs', sd', subs') => walk ns bs V ν τ fuel cs' sd' subs' (lo.set! c m) hi
    else none

/-- A cell passes if its tree is accepted and all codes, side entries and delegated boxes are used. -/
def checkCell (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi : Array Rat) (codes : List Nat)
    (sd : List (List (Bool × List Int × Rat))) : Bool :=
  let bs := (ns.map mkFBody).toArray
  match walk ns bs V ν τ codes.length codes sd [] lo hi with
  | some ([], [], []) => true
  | _ => false

/-! ## String-encoded data -/

/-- Codes: `'0'..'9'` → 0..9, `'a'..'z'` → 10..35 (split coordinates), `'L'` → 254, `'C'` → 252. -/
def decodeCodes (s : String) : List Nat :=
  s.toList.map fun ch =>
    if ch = 'L' then 254 else if ch = 'C' then 252 else if ch = 'X' then 250
    else if ch.isDigit then ch.toNat - '0'.toNat else ch.toNat - 'a'.toNat + 10

/-- `p/q` or `p` (decimal) as a rational. -/
def parseRatS (s : String) : Rat :=
  match s.splitOn "/" with
  | [a] => (a.toInt! : Rat)
  | [a, b] => mkRat a.toInt! b.toNat!
  | _ => 0

/-- Space-separated rationals. -/
def parseRatList (s : String) : Array Rat :=
  ((s.splitOn " ").filter (· ≠ "")).toArray.map parseRatS

/-- Side data: leaves separated by `|`, fans by `;`, a fan is `Ksigns:weight` with `K` = `a` (`N = 256`) or `b`
(`N = 1024`), signs in `-0+` (one per coordinate) and the weight a decimal numerator over `2^40`. -/
def decodeSide (s : String) : List (List (Bool × List Int × Rat)) :=
  if s = "" then [] else
  (s.splitOn "|").map fun leaf =>
    (leaf.splitOn ";").map fun fan =>
      match fan.splitOn ":" with
      | [sg, wt] =>
        let cs := sg.toList
        (cs.headD 'b' = 'a', cs.tail.map fun ch => if ch = '-' then (-1 : Int) else if ch = '+' then 1 else 0,
          mkRat wt.toInt! (2 ^ 40))
      | _ => (false, [], 0)

/-- A cell given by strings. -/
def checkCellStr (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (lo hi codes side : String) : Bool :=
  checkCell ns V ν τ (parseRatList lo) (parseRatList hi) (decodeCodes codes) (decodeSide side)

/-! ## The root grid and blocks of cells -/

/-- The split sequence of the root grid: `e` binary splits per coordinate, coordinates in order. -/
def gridSplits (d e : Nat) : List Nat := (List.range d).flatMap fun a => List.replicate e a

/-- The grid cells in DFS order (lower half first). -/
def gridCells : List Nat → Array Rat → Array Rat → List (Array Rat × Array Rat)
  | [], lo, hi => [(lo, hi)]
  | a :: rest, lo, hi =>
    let m := (lo[a]! + hi[a]!) / 2
    gridCells rest lo (hi.set! a m) ++ gridCells rest (lo.set! a m) hi

/-- Check consecutive cells, each with its tree read from the code stream. -/
def checkCells (ns : List Nat) (bs : Array FBody) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) :
    List (Array Rat × Array Rat) → List Nat → List (List (Bool × List Int × Rat)) → List (Array Rat × Array Rat) → Bool
  | [], [], [], [] => true
  | (lo, hi) :: cells, codes, sd, subs =>
    match walk ns bs V ν τ codes.length codes sd subs lo hi with
    | some (codes', sd', subs') => checkCells ns bs V ν τ cells codes' sd' subs'
    | none => false
  | _, _, _, _ => false

/-- A block of `count` grid cells starting at `start` (root box `rootLo, rootHi`), with string-encoded trees; `subs`
lists the boxes of the delegated subtrees as pairs of strings. -/
def checkBlockStr (ns : List Nat) (V : Nat → Nat → Rat × Rat) (ν τ : Rat) (rootLo rootHi : Array Rat) (d e start count : Nat)
    (codes side : String) (subs : List (String × String)) : Bool :=
  let bs := (ns.map mkFBody).toArray
  let cells := ((gridCells (gridSplits d e) rootLo rootHi).drop start).take count
  checkCells ns bs V ν τ cells (decodeCodes codes) (decodeSide side) (subs.map fun p => (parseRatList p.1, parseRatList p.2))

end LebesgueCover.Fast
