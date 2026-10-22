/-!
# The 11D root box (core Lean, shared by the certificate shards and the final theorem)
-/

namespace LebesgueCover.Fast

def ns11 : List Nat := [3, 5, 7, 9]
def tau11 : Rat := mkRat 4183 5000
def rl11 : Array Rat := #[mkRat (-1696575) 8388608, mkRat (-1696575) 8388608, mkRat (0) 1, mkRat (-3415393) 16777216, mkRat (-3415393) 16777216, mkRat (0) 1, mkRat (-3395327) 16777216, mkRat (-3395327) 16777216, mkRat (0) 1, mkRat (-1692535) 8388608, mkRat (-1692535) 8388608]
def rh11 : Array Rat := #[mkRat (1696575) 8388608, mkRat (1696575) 8388608, mkRat (333) 1024, mkRat (3415393) 16777216, mkRat (3415393) 16777216, mkRat (1973) 4096, mkRat (3395327) 16777216, mkRat (3395327) 16777216, mkRat (1491) 4096, mkRat (1692535) 8388608, mkRat (1692535) 8388608]

end LebesgueCover.Fast
