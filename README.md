# A lower bound of 0.8366 for Lebesgue's universal covering problem

Programs and certificates for the paper *A lower bound of 0.8366 for Lebesgue's universal covering problem*
by Tejasvi Singh Tomar (doi:10.5281/zenodo.23550397). The programs and certificates are archived at
doi:10.5281/zenodo.23550398.

## Theorem

Let `D` be the disk of diameter 1, let `B_n` be the regular Reuleaux `n`-gon of width 1, and let
`M(T_1, ..., T_m)` be the least area of the convex hull of congruent copies of `T_1, ..., T_m`. Then

    M(D, B_3, B_5) >= 0.8347,   M(D, B_3, B_5, B_7) >= 0.836   and   M(D, B_3, B_5, B_7, B_9) >= 0.8366.

Hence every convex set in the plane that contains a congruent copy of every set of diameter 1 has area at least
0.8366 (Lebesgue's universal covering problem). The previous lower bound was 0.83474, proved by J. Hatchett with
`D`, `B_3` and `B_5` (doi:10.5281/zenodo.22135010). The first inequality above is slightly weaker than that bound.
It is included as a smaller test of the method. The third inequality and the bound 0.8366 are also proved in Lean
(`formal/`, see below).

## Proof outline

1. **Reduction.** The disk is fixed at the origin and the Reuleaux triangle has rotation 0. A placement is a
   point of R^5 (bodies D, B_3, B_5), R^8 (with B_7) or R^11 (with B_7 and B_9). A reflection symmetry and the
   rotational symmetries of the bodies bound the rotations, and a corner estimate bounds the translations of
   every placement with hull area at most the target. This gives a root box.
2. **Box bound.** On a box of placements, finitely many points of the bodies (witnesses) move with their bodies.
   While they stay in angular order around a point of the disk, the area `F(p)` of the polygon they span is at
   most the hull area. `F` is a polynomial in the translations and in the sines and cosines of the angles, and it
   is bounded on the box by a second-order Taylor expansion, with a certified lower bound for the smallest
   eigenvalue of the Hessian and explicit bounds for the variation of the Hessian.
3. **Combination bound.** Where the hull changes its combinatorial type inside a box, the box bounds of several
   witness fans are combined with nonnegative weights that add up to 1, and their gradients are added before
   absolute values are taken. Only the certificate for `D, B_3, B_5, B_7, B_9` uses this step.
4. **Certificate.** A branch-and-bound tree over the root box. Every leaf is closed by the box bound, by the
   combination bound or by the corner estimate.

## Contents

| Path | Content |
|---|---|
| `checker/lbcheck.py` | the checker: ball arithmetic (Arb through python-flint, 80 bits); does not import the search; checks all three certificates |
| `checker/treecheck.py` | exact rational decoder of the trees, side files included (standard library and NumPy) |
| `search/lbsearch_v1.py`, `search/lbbnb_v1.py` | the search program that produced `cert5d_08347` (double precision; not part of the proof) |
| `search/lbsearch_v2.py`, `search/lbbnb_v2.py` | the search program that produced `cert8d_0836` (adds a cheaper first witness set) |
| `search/lbsearch_v4.py`, `search/lbbnb_v4.py` | the search program that produced `cert11d_08366` (adds the combination bound) |
| `search/area_bracket.py` | inner and outer polygon areas of the hull at one placement (numerical observations) |
| `certificates/cert5d_08347.tar.xz` | certificate of `M(D, B_3, B_5) >= 0.8347` (16 parts) |
| `certificates/cert8d_0836.tar.xz` | certificate of `M(D, B_3, B_5, B_7) >= 0.836` (24 parts) |
| `certificates/SHA256SUMS` | SHA-256 of the two archives |
| `certificates/cert11d_08366.sha256` | SHA-256 of the archive of the certificate of `M(D, B_3, B_5, B_7, B_9) >= 0.8366` (2,048 parts), which is too large for this repository and is archived only at doi:10.5281/zenodo.23550398 |
| `independent/` | second verifiers, decoders, minimization and negative tests, and the run of the second verifier on all leaves of the third certificate (see below) |
| `formal/` | the Lean 4 proof of `M(D, B_3, B_5, B_7, B_9) >= 0.8366` and of the bound 0.8366, with its own `README.md` and `SHA256SUMS` (see below) |

Each archive contains one directory with the files `partNNNN.json` (header) and `partNNNN.npy` (codes) of every
part and a file `SHA256SUMS` for them. The archive `cert11d_08366.tar.xz` (293,113,544 bytes) also contains the side
files `partNNNN_multi.npz`, the output of the first run of the checker on every part (`checklogs/`, `SUMMARY.txt`)
and copies of the checker and of the search program as they were used (`code/`, byte-identical to
`checker/lbcheck.py`, `search/lbsearch_v4.py` and `search/lbbnb_v4.py`).

The checker is included unmodified, so its docstrings still name the lemmas by the labels used while the proof was
written, call the program `lbcheck_v4.py`, and mention working notes and earlier versions of the program that are not
part of this release.
The labels correspond to the paper as follows: Lemma R is the symmetry lemma (Lemma 2.3), Lemma C the corner lemma
(Lemma 2.4), Lemma F the fan lemma and the fan bound (Lemmas 3.1 and 3.3), the run identity is Lemma 3.4, Lemma T the
Taylor bound (Lemma 3.5, with Lemmas 3.6 and 3.7), and Lemma K the combination bound (Lemma 3.8).

## Checking

Requirements for the checker: Python 3 (tested with 3.12), NumPy (tested with 2.5) and python-flint (tested with 0.9).

    cd certificates
    sha256sum -c SHA256SUMS
    tar -xJf cert5d_08347.tar.xz
    tar -xJf cert8d_0836.tar.xz
    (cd cert5d_08347 && sha256sum -c SHA256SUMS)
    (cd cert8d_0836 && sha256sum -c SHA256SUMS)
    python3 -I ../checker/lbcheck.py cert5d_08347 present
    python3 -I ../checker/lbcheck.py cert5d_08347 $(seq 0 15)
    python3 -I ../checker/lbcheck.py cert8d_0836 present
    python3 -I ../checker/lbcheck.py cert8d_0836 $(seq 0 23)
    python3 -I ../checker/treecheck.py cert5d_08347
    python3 -I ../checker/treecheck.py cert8d_0836

For the third certificate, download `cert11d_08366.tar.xz` from the archive into `certificates/`, then

    sha256sum -c cert11d_08366.sha256
    tar -xJf cert11d_08366.tar.xz
    (cd cert11d_08366 && sha256sum -c SHA256SUMS)
    python3 -I ../checker/lbcheck.py cert11d_08366 present
    seq 0 2047 | xargs -P 8 -I{} sh -c 'python3 -I ../checker/lbcheck.py cert11d_08366 {} > check11_{}.json'
    python3 -I ../checker/treecheck.py cert11d_08366

`present` prints `[true, ...]` when all parts exist and their headers agree. For every part the checker prints a
JSON line, and `treecheck.py` prints a JSON line with `"ok": true` when every leaf box verified by the checker
equals the exact leaf box, the leaves of every grid cell tile it, and every side file lists exactly the leaves with
code `253` of its part. A certificate is accepted when the checker prints a line for every part `0, ..., P-1`, every
line has `"ok": true` and `"fails": 0`, and `treecheck.py` prints `"ok": true`.

The parts can be checked separately and in parallel. `treecheck.py CERTDIR FIRST LAST` checks the parts
`FIRST, ..., LAST-1`, and `treecheck.py --combine OUTPUT...` adds up the outputs of such runs. On loaded servers the
longest part took about 2 minutes (`cert5d_08347`), 18 minutes (`cert8d_0836`) and 88 minutes (`cert11d_08366`, with
two processes per physical core) of wall-clock time per process. The sums of these times over all parts are about
3 minutes, 2.7 hours and 395 hours, respectively.

The checker regenerates the witnesses of each leaf with a floating-point heuristic, then verifies in ball
arithmetic: membership of the witnesses in their bodies, the angular order of the witnesses on the whole box, the
angle sum at the centre, and the Taylor bound. At a leaf with code `253` it verifies membership, angular order and
angle sum for every fan of the side file. It rejects the leaf if a fan of positive weight fails them, skips the fans
of weight 0 that fail them, and verifies that the combination of the Taylor bounds of the other fans, with the
weights of the side file, exceeds the target. It also verifies the root box against the corner estimate and the
tree structure. Only the inequalities verified in ball arithmetic enter the proof. For each part the checker reports
the smallest difference between an accepted leaf bound and the target. Because the checker accepts a leaf at the
first witness set that passes, this difference is computed from the accepted bounds; another witness set may give a
larger bound at the same leaf. With the
environment variable `LBCHECK_SELFTEST=1` the checker also compares, at every leaf with code `254`, the area `F`
computed from runs of consecutive witnesses on one body with the direct shoelace sum.

## Programs written separately from the checker (`independent/`)

The directory `independent/` holds programs written separately from the checker and the search. In their docstrings,
and in those of the checker and the search programs, "independent" means that a program shares no code with the
programs it checks. None of them imports either program, except the negative tests, which import
`checker/lbcheck.py` in order to test it. They need NumPy, SciPy (tested with 1.18), mpmath (tested with 1.4) and
python-flint.

| File | Purpose |
|---|---|
| `t1_tree.py CERTDIR LEAVES.npz` | exact decoder of the trees of the first two certificates; writes the leaf boxes |
| `v1_leafcheck.py LEAVES.npz TAU OUT.json IDX ...` | second verifier of leaves of the `D, B_3, B_5` certificate |
| `v8_leafcheck.py LEAVES.npz TAU OUT.json IDX ...` | the same for `D, B_3, B_5, B_7` (uses `gen8.py`) |
| `v2_validate.py`, `v8_validate.py` | comparison of the two verifiers with brute force on a few leaves |
| `h1_hull.py`, `gen8.py` | hull areas from the support functions (`D, B_3, B_5` and `D, B_3, B_5, B_7`) |
| `h2_minsearch.py`, `h8_minsearch.py` | hull areas at leaf centres and local minimization |
| `opt8_point.json` | the placement of `D, B_3, B_5, B_7` found by local minimization, in full precision (hull area 0.83649045598 by `gen8.area`), together with the values of `gen8.area` and `gen8.poly_bounds` at that placement |
| `gen11.py` | the same hull areas for `D, B_3, B_5, B_7, B_9` (imports `gen8.py`) |
| `c11_centres.py CERTDIR FIRST LAST OUT.jsonl` | hull areas at all leaf centres of the parts `FIRST, ..., LAST-1` of `cert11d_08366` |
| `p11_polish.py STARTS.json I0 I1 OUT.jsonl` | local minimization for `D, B_3, B_5, B_7, B_9` from the starts `I0, ..., I1-1` of a list (Nelder-Mead restarts, then Powell) |
| `p11_restarts.py X.json SEED NREST OUT.jsonl` | random restarts around a local minimum, each followed by the same minimization |
| `opt11_point.json` | the placement of `D, B_3, B_5, B_7, B_9` found by local minimization, in full precision (hull area 0.83729500640 by `gen11.area`), with `gen11.poly_bounds` and the polygon areas of `search/area_bracket.py` with 2^24 directions at that placement |
| `l1_lemmas.py` | numerical checks of the reduction lemmas |
| `n1_negative.py`, `n8_negative.py` | negative tests of the checker on the first two certificates |
| `n11_negative.py CERTDIR OUTDIR` | negative tests on the third certificate: modified copies of part 1618 (root, header, tree and side file); run `checker/lbcheck.py OUTDIR/T... 1618` on each |
| `t11_leaf_near_min.py CERTDIR X.json TAU` | runs the checker's leaf test on the leaf of the third certificate that contains the placement `X`, at the certificate's target and at `TAU` |
| `xstar_min11.json` | a placement of `D, B_3, B_5, B_7, B_9` near the numerical minimum |
| `m11_multistart.py NSTART SEED OUT.jsonl` | multistart Nelder-Mead for `D, B_3, B_5, B_7, B_9` from the placement of `opt8_point.json` extended by `B_9` and from random starts |
| `samples/` | leaf indices of the samples verified by the separate verifiers of the first two certificates (`strata_*.json` lists the strata), and `stage1_11d.npz` (the leaves of a sample of the third certificate, drawn by `v11/v11_sample.py` with seed 20261021 and verified before the full run) with the results `stage1_11d.jsonl` |
| `v11/` | the verifier and decoder for the third certificate, with its own `SHA256SUMS`: `v11_leafcheck.py` (leaf verifier), `gen11.py` (its hull geometry; not the same file as `independent/gen11.py`), `treedec11.py` (exact decoder with integer boxes), `v11_sample.py` (draws a sample), `v11_run.py` (runs the verifier on a sample), `box_run11.py` (runs it on all leaves of given parts) and the self-tests `test_*.py` |
| `full11/` | the run of the second verifier on all leaves of the third certificate (see the next section) |

The verifiers bound the area `F` of the witness polygon on a box without a Taylor remainder. They use neither the
Taylor bound (Lemma 3.5 of the paper) nor the combination bound (Lemma 3.8). The verifier in `v11/` also handles the
leaves with code `253`: it builds the fans of positive weight from the sign vectors and weights of the certificate,
verifies them on the leaf, and bounds their combined area in the same way, which uses only the inequality
`A >= sum_i kappa_i F_i` from the proof of Lemma 3.8. For fixed rotations,
`F` and the determinants that encode the angular order are affine in each translation coordinate, so their minima lie
at vertices of the box of translations, and their minima over the rotations are bounded from below in ball
arithmetic.

With `xstar_min11.json`, `t11_leaf_near_min.py` accepts the leaf at 0.8366 and rejects it at 0.8374.

Earlier versions of the verifier in `v11/`, with a looser fallback bound for the minima over the rotations, had failed
at some leaves of the sample in `samples/stage1_11d.npz`; the version in `v11/` verified all of them.

`box_run11.py CERTDIR PARTS OUTDIR WORKERS` expects the other files in a subdirectory `v11/` next to it, so copy
`box_run11.py` into `independent/` before running it. `PARTS` is a file with part numbers. Example:

    python3 -I independent/t1_tree.py certificates/cert5d_08347 leaves5.npz
    python3 -I independent/v1_leafcheck.py leaves5.npz 0.8347 v1.json $(cat independent/samples/sample_5d.txt independent/samples/tight_5d.txt)
    python3 -I independent/n1_negative.py certificates/cert5d_08347 leaves5.npz negative_work
    python3 -I independent/v11/v11_run.py independent/samples/stage1_11d.npz stage1_rerun.jsonl 8

## Run of the second verifier on all leaves of the third certificate (`independent/full11/`)

The second verifier verified all 16,193,402 leaves of `cert11d_08366`: a first pass with the verifier of `v11/`, and
two variants of it for the leaves that the first pass did not verify. The directory `full11/` has the layout of the
directory in which these runs were made, so that the accounting program `pass23/final11.py` runs unchanged. Apart from
`full11_pass1.sha256`, every file in it is a copy of a file of that directory.

| Pass | Program | Leaves verified |
|---|---|---|
| 1 | `v11_frozen_8b878f23/v11_leafcheck.py` (the files of `v11/`), bisection of a leaf to depth 4 | 16,191,196 |
| 2 | `v11bc_frozen_12dd7362/v11b_leafcheck.py`: pass 1, with each witness list also tried without the runs of witnesses on one body whose removal decreases the fan area at the point where the fan is built by less than 1e-5 or 1e-4, and bisection to depth 6 | 228 |
| 3 | `v11bc_frozen_12dd7362/v11c_leafcheck.py`: its own fans and weights; fans from the hull at the centre `c`, at the points `c + s * h` of the side file (leaves with code `253`) and at minimizers of the current combination, with witness lists filtered as in pass 2 (1e-5), each verified on the whole leaf; weights from a cutting-plane linear program (SciPy); the combined area bounded as in pass 1; bisection to depth 5 | 1,029 |
| 3d | `v11d_frozen_888b6867/v11c_leafcheck.py`: pass 3 with one fix: when the cutting-plane loop has converged to an optimum below the target, it adds a fan at the minimizer instead of stopping | 949 |

Pass 1 ran on all 2,048 parts with `box_run11.py`, spread over 43 servers. It took 3,959.7 CPU-hours (0.88 s per leaf)
and split 11,046 leaves. Of these, 8,840 then passed, and the other 2,206, which pass 1 did not verify, all failed at
depth 4. These leaves were decoded into
`pass23/fails_a.npz`, `fails_b.npz`, `fails_c1.npz` and `fails_c2.npz`, in the order in which the results of pass 1
came in, and run through the later passes with `pass23/run_pass.py`. Pass 2 ran on 367 leaves of `fails_a`, pass 3 on
the 1,042 leaves of `fails_a` that pass 2 had not verified (`pass23/logs_p2/pass3_a_idx.txt`), and pass 3d on the 13
leaves that pass 3 had not verified (`pass23/logs_p2/pass3d_a_idx.txt`) and on the leaves listed in `fails_b_idx.txt`,
`fails_c1_idx.txt` and `fails_c2_idx.txt`. In all passes together, 9,018 leaves passed only after a split (8,840 in pass 1,
136 in pass 2, 35 in pass 3 and 7 in pass 3d). The smallest margins (bound minus 0.8366) were 6.786542922579881e-09 in pass 1 (part 691) and
3.5679177660030045e-07 in the later passes (part 1715). The programs and their output call a combination of fans
"Lemma K"; they use only the inequality `A >= sum_i kappa_i F_i` and bound the combined area as above.

| File | Content |
|---|---|
| `v11_frozen_8b878f23/`, `v11bc_frozen_12dd7362/`, `v11d_frozen_888b6867/` | the programs of the passes, each with its own `SHA256SUMS`; the names end with the first hexadecimal digits of the SHA-256 of `v11_leafcheck.py`, of `v11c_leafcheck.py` and of the corrected `v11c_leafcheck.py` |
| `treedec11_all.json` | the output of the exact decoder `treedec11.py` on all parts (leaf counts per part and code, structural checks) |
| `pass23/fails_*.json`, `pass23/fails_*.npz` | the leaves that pass 1 did not verify, as `[part, pos, tag]`, and their exact boxes and side data, written by `v11_sample.py` with the list as targets and no random leaves (it also adds the 33 far leaves) |
| `pass23/fails_*_idx.txt` | the indices of these leaves in the `.npz` files |
| `pass23/run_pass.py PASS CODEDIR LEAVES.npz OUT.jsonl WORKERS [IDXFILE]` | runs pass 2 (`PASS` = 2) or pass 3 (`PASS` = 3) with the programs in `CODEDIR` on the leaves of `LEAVES.npz` or on those listed in `IDXFILE`; pass 3d is pass 3 with `CODEDIR` = `v11d_frozen_888b6867` |
| `pass23/results/pass*.jsonl` | the output of the later passes, one line per leaf; the `.meta` files hold the SHA-256 of the programs that were run |
| `pass23/final11.py` | the accounting program |
| `pass23/FINAL11.json` | its output: `"ALL 16193402 LEAVES VERIFIED"`, 0 unresolved leaves, 0 problems |
| `full11_pass1.sha256` | SHA-256 of `full11_pass1.tar.xz` (116,500,532 bytes), the output of pass 1, which is archived only at doi:10.5281/zenodo.23550398 |

The output of pass 1 has one directory per server, renamed `box01`, ..., `box43` for this release, with
`partNNNN.json` (leaf counts, SHA-256 of the input files and of the programs, the leaves not verified, the smallest
margin, CPU time) and `partNNNN_margins.npy` (the margin of each leaf in the order of the decoder, NaN for a leaf not
verified) for each part. `final11.py` checks that every part has a pass-1 result (the archive holds exactly one per part), that its input files have
the SHA-256 listed in the `SHA256SUMS` of the certificate, that the pass-1 programs have the SHA-256 of the files in
`v11_frozen_8b878f23/`, that the leaf counts equal those of `treedec11_all.json` and that every leaf has a result. It
then checks that every leaf that pass 1 did not verify was verified by a later pass. It matches each result to its leaf
in the `fails_*.npz` files by part and position, and it compares the SHA-256 in the `.meta` files with the programs in
the corresponding directory. The later passes read their leaves from the `fails_*.npz` files, which `v11_sample.py`
decoded from the certificate; `final11.py` does not decode the certificate again. To rerun it, extract `cert11d_08366`
into `certificates/` as above, download `full11_pass1.tar.xz` into `independent/full11/`, and run, from the top
directory of the repository,

    ln -s ../certificates/cert11d_08366 independent/cert11d_08366
    cd independent/full11
    sha256sum -c full11_pass1.sha256
    tar -xJf full11_pass1.tar.xz           # fleet11/results/box01, ..., box43, each with a file DONE
    python3 -I pass23/final11.py
    sha256sum pass23/FINAL11.json

`final11.py` reads only the file `SHA256SUMS` of the certificate. It rewrites `pass23/FINAL11.json`, which should then
be byte-identical to the file in this repository (SHA-256 `abf4552b8a9a77f6f9bb3c25d80b31f9d06592a4ab0193fbac34027b1643d00c`).

## Lean proof (`formal/`)

The third inequality and the bound 0.8366 are also proved in Lean 4 (toolchain `leanprover/lean4:v4.35.0-rc3`) with
Mathlib (tag `v4.35.0-rc3`). The directory `formal/` holds the Lean project (`formal/lean/`), its build scripts and the
generators of the certificate modules (`formal/tools/`), a README with the statements, the trust base and the build
steps, and a `SHA256SUMS` for these files. The final theorems, in namespace `L11` of the generated module
`L11/Root11Good.lean` (a copy is in `formal/final/`), include `hull5_ge` (`M(D, B_3, B_5, B_7, B_9) >= 0.8366`), `main5` (every universal cover has area at
least 0.8366) and `weak_main5` (the same for every convex set that contains a congruent copy of every convex set of
diameter 1). The statements are in `formal/lean/LebesgueCover/Defs.lean`. Their axioms are `propext`,
`Classical.choice`, `Quot.sound` and 75,061 auxiliary axioms of `native_decide`, one for each certificate module.

The Lean proof checks its own certificate, not the certificates in `certificates/`: a tree in which the rotations are
given by the half-angle coordinates `s = tan(rho/2)`, with 2,048 root cells and 9,239,121 leaves, whose leaves are closed
by one fan or a convex combination of fans, each bounded by an exact quadratic bound with an exact `LDL^T`
factorization instead of the Taylor bound (Section 4.6 of the paper). The
77,175 generated modules and their compiled `.olean` files (all but `AxL11.lean`, which prints the axioms) are too large
for this repository and are archived only at doi:10.5281/zenodo.23550398. Check both archives against this table, or
against the supplement's `SHA256SUMS`, before unpacking them:

| File | Bytes | SHA-256 |
|---|---|---|
| `l11_sources.tar.zst` | 133,521,541 | `acb85d373917295c26f77acd2b2144c2f47256fcc6d9418dface3ff78c00133a` |
| `l11_oleans.tar.zst` | 481,071,638 | `9a356edf6e801783658a296ebe9f52430212006e4ee700c3be5a1b285f12dbab` |

`formal/README.md` gives the commands to build the modules from the sources (about 940 hours of single-threaded
processes) and to load the shipped `.olean` files, which prints the statements and axioms of the final theorems without
a rebuild. Loading `.olean` files does not check their proofs in the kernel again.

## Certificate format

A certificate consists of `P` parts. The header `partNNNN.json` records `ns` (the numbers of corners of the
Reuleaux polygons), `tau` (the target), `lo` and `hi` (the corners of the root box), `split0` (the grid),
`nparts` and `part`, the parameters `N` and `eps` of the witness heuristic, and further search parameters and
statistics that the checker does not use. Coordinates are `(t1x, t1y, rho2, t2x, t2y, ..., rhok, tkx, tky)`. The
first Reuleaux polygon has rotation 0. The root box is cut into the grid cells, listed in the order of
`numpy.ndindex(*split0)`, and part `j` holds the cells `list(numpy.ndindex(*split0))[j::nparts]`. The array
`partNNNN.npy` (`uint8`) describes, for each of these cells in turn, a binary tree in depth-first preorder: a code
`a < dim` splits the current box at the midpoint of coordinate `a`, followed by the trees of the lower and the upper
half. The code `253` marks a leaf closed by the combination bound, `254` a leaf closed by the box bound of step 2 of
the outline, and `255` a leaf closed by the corner estimate. For the leaves with code `253`, the side file
`partNNNN_multi.npz` holds the arrays `pos` (the position of each such leaf in the code array, counted from 0),
`nstruct` (the number of fans of each leaf), and `shifts` and `lam` (one sign vector in `{-1, 0, 1}^dim` and one
weight per fan, with the fans of the leaves in the order of `pos`). The fan with sign vector `s` is built from the support points of the hull at the placement
`c + s * h`, where `c` is the centre of the leaf and `h` its vector of half-widths. No witnesses are stored.

## Search

    cd search
    python3 lbbnb_v1.py 3,5 0.8347 1e-6 PART 16 4,4,4,4,4 OUTDIR                          # cert5d_08347, PART = 0..15
    python3 lbbnb_v2.py 3,5,7 0.836 1e-6 PART 24 4,4,4,4,4,4,4,4 OUTDIR                   # cert8d_0836, PART = 0..23
    python3 lbbnb_v4.py 3,5,7,9 0.8366 1e-6 PART 2048 2,2,2,2,2,2,2,2,2,2,2 OUTDIR        # cert11d_08366, PART = 0..2047

Run the drivers from `search/` without `-I`, because they import the module next to them. The arguments are the
Reuleaux polygons, the target, the search margin, the part, the number of parts, the grid and the output directory.
The search closes a box when its floating-point bound reaches the target plus the margin. `lbsearch_v4.py` also needs
SciPy and highspy (tested with 1.15) for the linear program that chooses the weights of a combination. Rerunning each
version on some parts of its certificate reproduced those parts byte for byte: for `cert5d_08347` and `cert8d_0836` on
the machine where they were made, and for `cert11d_08366` part 1618 on another machine. With other floating-point
libraries the output may differ, but any output is checked in the same way.

## License

Apache License 2.0, see `LICENSE`.

## Citation

See `CITATION.cff`.
