# Spectral extremes under exact cycle conditioning

Source and formal verification for the paper *Spectral extremes under
exact cycle conditioning*.

```
paper/main.tex      manuscript source
paper/main.pdf      compiled manuscript
lean/src/           542 Lean 4 modules
lean/lean-toolchain,
lean/lake-manifest.json,
lean/lakefile.toml  pinned compiler and dependency versions
verify.py           rebuilds every module from source and audits the kernel
```

## What is formalized

Over the literal finite permutation model: the conditional law given an
exact cycle count, the characteristic polynomial as the determinant of the
actual permutation matrix, the localization theorem, the ordinary-Ewens
random centering and joint limit, and the two-matching application. The
corresponding Lean statements are

```
exact_cycle_localization
actual_permutation_exact_cycle_localization
manuscript_actual_permutation_supremum_limit
actual_permutation_ordinary_random_centering
actual_permutation_ordinary_joint_limit
TwoMatchings.actual_two_matching_exact_component_localization
actual_permutation_conditioning_eventually_positive
```

all in `ConditionalSpectralExtremes`. The definitions they use are in
`lean/src/ManuscriptDefinitions.lean`, `PermutationProfile.lean` and
`ActualPermutationSpectrum.lean`; reading those four files is enough to
see what the statements assert.

Kernel checking establishes the formal statements. It does not establish
that they are equivalent to the prose of the paper, and it says nothing
about novelty.

## Rebuilding the manuscript

```
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Running the verification

Requires Python 3.10+, elan, and network access to fetch the locked
Mathlib. The compiler version is taken from `lean/lean-toolchain`, not
from the system default.

```
cd lean
lake exe cache get
cd ..
python verify.py --jobs 4
```

Each module is recompiled from source with

```
lean --trust=0 -Ddebug.skipKernelTC=false
```

so the kernel re-checks every declaration it adds; no cached build
products and no stored certificate are used. The script reports the
number of modules built, any module containing `sorry`, `axiom`,
`unsafe` or a similar escape, any unexpected compiler output, and the
axiom footprint of every declaration that prints one. It exits with
status 0 only if all modules build, no module produces unexpected
output, the seven statements above are present, and no declaration
depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. A full rebuild takes roughly an hour with four workers and
needs several GB of memory per worker; `--jobs` controls the parallelism.
A machine-readable record is written to `verification.json`.
If a long run is interrupted, `--resume` reuses the modules already
compiled into the build directory; the record then states how many
were reused, and the axiom audit covers only the rest.
