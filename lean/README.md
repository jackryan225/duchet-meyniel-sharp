# Lean files and how to rebuild them

## What is in this folder

- `OAI/Combinatorics/HadwigerScaled/` has the four new modules of this repository:
  `ScaledParameters.lean`, `ScaledTransfer.lean`, `ScaledExponential.lean` and `Main.lean`.
  `Main.lean` proves the five theorems listed in `../FIDELITY.md`.
- `../Challenge/Statement.lean` states the three main theorems in Mathlib terms. In the build it has the module name
  `ComparatorChallenge.HadwigerScaled`. `assemble.sh` copies it to that place.
- `Check/` has the three files that ran the checks: `Axioms.lean` (`#print axioms`), `ChallengeView.lean` and
  `SolutionView.lean` (full `pp.all` print of the definitions and statements in the two environments).
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: the project configuration that was built.
- `oai_files.txt` lists the 288 files of OpenAI's Lean library that the build needs. They are not copied into this
  repository. `OAI-SHA256SUMS` has their SHA-256 sums. `OURS-SHA256SUMS` has the sums of our 5 files.
- `assemble.sh` copies the 288 files from a checkout of openai/math and checks all 293 sums.
- `provenance.diff` shows how three of our modules and one theorem differ from the OpenAI files that they copy.
  It is documentation, not a patch to apply.

An earlier build of the same proofs gave the same results. After it, only comments changed: the header comments of
the four proof modules and of `../Challenge/Statement.lean` lost an outdated status note. `OURS-SHA256SUMS` lists the sums
of the files as published, and the build recorded below used exactly these files.

## Pinned versions

- Lean `leanprover/lean4:v4.34.1`.
- Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (see `lake-manifest.json`).
- OpenAI's library: github.com/openai/math at commit `3344da59991ed94f9ba711217b29c1d760badfa6`, folder `lean/`,
  Apache License 2.0.

## How to rebuild

You need `elan`, `git` and a machine with much memory. The build below ran on a machine with 128 GB of memory. We did not
measure the minimum.

    git clone https://github.com/openai/math openai-math
    git -C openai-math checkout 3344da59991ed94f9ba711217b29c1d760badfa6
    sh assemble.sh openai-math
    lake exe cache get
    ulimit -n 8192
    LEAN_NUM_THREADS=4 lake build OAI.Combinatorics.HadwigerScaled.Main ComparatorChallenge.HadwigerScaled

Expected result: `Build completed successfully` and exit code 0. The only warnings about `sorry` are the three in
`ComparatorChallenge/HadwigerScaled.lean`. That file states the theorems; it does not prove them.

Checks:

    lake env lean Check/Axioms.lean
    lake env lean Check/ChallengeView.lean > chal.txt
    lake env lean Check/SolutionView.lean > sol.txt
    cmp chal.txt sol.txt
    lake env leanchecker -v OAI.Combinatorics.HadwigerScaled OAI.Combinatorics.HadwigerCounterexample \
        OAI.Combinatorics.HadwigerMatching OAI.Combinatorics.ListHadwiger

Expected: each of the five theorems depends on `[propext, Classical.choice, Quot.sound]`; `cmp` prints nothing;
`leanchecker` replays 292 modules and exits with code 0.

## What was run, and the results (25 November 2026)

Build from an empty folder (08:20-08:33 UTC), with the files as published:

| Step | Result | Log |
|---|---|---|
| `sh assemble.sh <openai/math checkout at 3344da5>` | 288 + 5 SHA-256 sums OK, exit 0 | `../logs/p3-clean-1-assemble.txt` |
| `lake exe cache get && lake build OAI.Combinatorics.HadwigerScaled.Main ComparatorChallenge.HadwigerScaled` | 9216 jobs, exit 0; the only `sorry` warnings are the 3 in the statement file | `../logs/p3-clean-2-build.txt` |
| `lake env lean Check/Axioms.lean` | 5 of 5: propext, Classical.choice, Quot.sound | `../logs/p3-clean-3-axioms.txt` |
| `ChallengeView` and `SolutionView`, then `cmp` | identical (8,820 bytes) | `../logs/p3-clean-4-chal.txt`, `../logs/p3-clean-4-sol.txt` |
| `leanchecker -v` on the four module prefixes | 292 modules, exit 0 | `../logs/p3-clean-5-leanchecker.txt` |
| `lean4export` of the five theorems, then `lean4lean --import` | export OK (axioms exactly the three); 39,086 declarations checked, exit 0 | `../logs/p3-lean4lean.txt`, `../logs/p3-export-names.txt` |

The whole run is in `../logs/p3-clean.log`; its scripts are in `../logs/scripts/`. `../logs/README.md` says what was
changed in the copies of the logs (folder and host names only).
