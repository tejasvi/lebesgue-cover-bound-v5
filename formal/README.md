# Lean formalization of Λ ≥ 0.8366 for Lebesgue's universal covering problem

This directory contains a Lean 4 + Mathlib proof that every universal cover in the plane has area at least 0.8366,
through the bound M(D, B₃, B₅, B₇, B₉) ≥ 0.8366 on the least area of the convex hull of congruent copies of the disk
of diameter 1 and the regular Reuleaux triangle, pentagon, heptagon and nonagon of width 1.

## Statements and final theorems

The definitions and statements are in `lean/LebesgueCover/Defs.lean`: the plane `EuclideanSpace ℝ (Fin 2)` with
Lebesgue measure, the bodies `disk` and `reuleaux n`, universal covers (`IsUniversalCover`, every set of diameter at
most 1 has a congruent copy inside, reflections allowed), the Lebesgue constant `lebesgueConstant` (infimum of the areas
of universal covers), the weakest reading `IsWeakUniversalCover` (copies of every convex set of diameter exactly 1),
the hull infimum `hull5`, and the propositions `Hull5Statement`, `Main5Statement`, `WeakMain5Statement`,
`MainStatement` and `WeakMainStatement`.

The final theorems are in the generated module `L11/Root11Good.lean` (namespace `L11`; a copy is in
`final/Root11Good.lean`):

```lean
theorem hull5_ge : Hull5Statement             -- M(D, B₃, B₅, B₇, B₉) ≥ 0.8366
theorem main5 : Main5Statement                -- Λ ≥ 0.8366
theorem weak_main5 : WeakMain5Statement       -- the same for every weak universal cover
theorem main_836 : MainStatement              -- Λ ≥ 0.836
theorem weak_main_836 : WeakMainStatement
```

`#print axioms` gives, for each of the five, `propext`, `Classical.choice`, `Quot.sound` and 75,061 axioms named
`L11.<module>.ok._native.native_decide.ax_1_1`, one for each certificate module (2,048 cell modules `B<c>` and 73,013
subtree modules `S<c>_<k>`). There is no `sorry` and no other axiom.

## Trust base

Each `native_decide` auxiliary states `decide p = true` for the proposition `p` of one certificate module, a run of
the compiled leaf checker and tree walker on that module's data, and is justified by evaluating `p` with compiled code
instead of the kernel. `native_decide` therefore trusts the Lean compiler and runtime for these evaluations. Everything
else is checked by the kernel with the three standard axioms:

- the soundness of the compiled checker (`LebesgueCover/FastBridge.lean`) with respect to the reference leaf checker
  (`Checker.lean`, `Sound.lean`, `Quad.lean`, `Rot.lean`), and of the reference checker with respect to the geometric
  conclusion "every placement in the box has hull area > 0.8366" (`Fan.lean`, `FanLeaf.lean`);
- the tree, cell, block and grid lemmas: the 2,048 root cells cover the root box (`TreeSound.lean`);
- the table of Reuleaux vertices, from trigonometric enclosures evaluated in the kernel (`Trig/`, `VertTable.lean`);
- the far region, by a kernel-checked polygon and a corner bound (`Far.lean`, `Far11Data.lean`);
- the reduction of arbitrary isometries to placements in the root box: the plane as ℂ, the isometries of ℂ, the
  symmetries of the bodies, and half-angle rotation coordinates (`Reduce.lean`, `Main5.lean`);
- the diameters of the bodies and the passage from `Hull5Statement` to the two readings of Λ (`Diam.lean`).

The compiled checker proposes witnesses with floating-point heuristics (`LebFast/Heur.lean`). The soundness theorems
hold for arbitrary witnesses, so these heuristics are not part of the trust base. The branch-and-bound search that
produced the tree is not part of it either and is not needed to check the proof.

## Contents

- `lean/`: the Lake project (28 Lean files of the development, plus two optional tool programs; `lean-toolchain`,
  `lakefile.toml`, `lake-manifest.json`).
  `LebesgueCover/` is the Mathlib development listed above; `LebFast/` is the compiled checker in core Lean
  (`Heur`, `Model`, `Exact`, `Driver`, `Tree`, `VT`, and `Root11` with the root box). `tools/HeurTest.lean` and
  `tools/LeafBench.lean` are optional development programs, not part of the proof.
- `final/Root11Good.lean`: a copy of the module with the final theorems (also in `l11_sources.tar.zst`).
- `tools/`: `build_l11.sh` and `final_l11.sh` (build), `mkblocks3.py` and `mkroot11.py` (the generators of the
  `L11` modules; `mkroot11.py` reproduces `C*.lean` and `Root11Good.lean` exactly), `count_l11.py` (counts). The
  branch-and-bound search that produced the tree is not included; it is not needed to check the proof.
- Two archives distributed with this directory:
  - `l11_sources.tar.zst`: the 77,175 generated modules under `L11/` and their `SHA256SUMS_lean`:
    - `B<c>` (cell `c`, with its subtrees of more than a set size delegated) and `S<c>_<k>` (the delegated subtrees,
      at most 2,997 leaves, almost all at most 600): the certificate, checked by `native_decide`;
    - `G<c>`: per-cell glue (`block_good`);
    - `C<k>`: 64 chunks of 32 cells;
    - `Root11Good`: the root box and the final theorems;
    - `AxL11`: prints the axioms of the finals.
  - `l11_oleans.tar.zst`: the compiled `.olean` files of these modules (toolchain `v4.35.0-rc3`) and their
    `SHA256SUMS_olean`, for checking the final theorems without the roughly 940 hours of compiled evaluation
    (`native_decide`).

## Certificate

The root box has 11 coordinates: the translations of the four Reuleaux polygons relative to the disk and the
rotations of the pentagon, heptagon and nonagon relative to the triangle, in half-angle coordinates s = tan(ρ/2).
These coordinates and this root box differ from those of the certificate in the paper: the Lean proof checks a
separate tree, built for the leaf model formalized here. The root box is split into 2,048 cells by one bisection per
coordinate. Each cell carries a binary tree; a leaf is closed either
by one fan (a polygon of support points with a quadratic lower bound of its area on the leaf box) or by a convex
combination of several fans. In total: 9,239,121 leaves (3,639,774 single-fan and 5,599,347 combination leaves) and
18,476,194 nodes.

## Build

Requirements: `elan` with the toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib at tag `v4.35.0-rc3`
(commit c55e6e786f49), `zstd`.

```sh
cd lean
lake exe cache get                     # prebuilt Mathlib
lake build LebFast LebesgueCover       # the base development and the compiled checker libraries
mkdir -p blocks && zstd -dc /path/to/l11_sources.tar.zst | tar -xf - -C blocks
(cd blocks/L11 && sha256sum -c --quiet SHA256SUMS_lean)
bash ../tools/build_l11.sh 64          # certificate and glue modules
bash ../tools/final_l11.sh 32          # chunks, the final theorems, and their axioms
```

`build_l11.sh` compiles the `B` and `S` modules with the compiled checker libraries loaded through `--load-dynlib`
(about 0.37 s per leaf, about 940 hours of single-threaded processes in total, so a few thousand cores take about an
hour) and then the
`G` modules. `final_l11.sh` compiles the chunks and `Root11Good` (about 20 s and 10 GB for the root module) and writes
the axioms to `blocks/logs_final/axioms.txt`.

To inspect the final theorems from the shipped `.olean` files instead, unpack them after `lake build` and print the
axioms. This reads the declarations as compiled and does not re-run the kernel on them; checking them again needs a
kernel replay of the `.olean` files.

```sh
mkdir -p blocks/build && zstd -dc /path/to/l11_oleans.tar.zst | tar -xf - -C blocks/build
(cd blocks/build/L11 && sha256sum -c --quiet SHA256SUMS_olean)
LEAN_PATH=$(lake env printenv LEAN_PATH):$PWD/blocks/build lean blocks/L11/AxL11.lean
```

## Checks

`SHA256SUMS` lists every file of this directory; the two archives carry their own manifests. The modules were also re-checked separately: all 77,201 modules of
the closure were replayed in the kernel; a seeded 2% sample of the certificate modules, rebuilt with a second build of
the compiled checker from the same sources, is byte-identical to the original build; and the statements and axioms of
the five final theorems were confirmed.
