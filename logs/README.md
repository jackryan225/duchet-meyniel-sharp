# Logs

These logs come from one build of the files of this repository, made on 25 November 2026 (08:20 to 08:33 UTC) from an
empty folder on a machine with 128 GB of memory. The 288 OpenAI files came from openai/math at commit
3344da59991ed94f9ba711217b29c1d760badfa6 and were checked with `lean/assemble.sh`.

| File | Content |
|---|---|
| `p3-clean.log` | the whole run, step by step, with exit codes |
| `p3-clean-1-assemble.txt` | output of `lean/assemble.sh` |
| `p3-clean-2-build.txt` | output of `lake exe cache get` and `lake build` |
| `p3-clean-3-axioms.txt` | `#print axioms` of the five theorems |
| `p3-clean-4-chal.txt`, `p3-clean-4-sol.txt` | full print (`pp.all`) of the definitions and the three statements, in the statement file and in the proof |
| `p3-clean-5-leanchecker.txt` | `leanchecker -v` replay of 292 modules |
| `p3-export-names.txt`, `p3-export-stderr.txt` | `lean4export` of the five theorems: theorem count, axioms, time and memory |
| `p3-lean4lean.txt` | `lean4lean --import` of that export |
| `scripts/p3-clean.sh`, `scripts/l4l.sh` | the scripts that ran these steps |

`p3-clean.log` also compares the statement print with the print of an earlier build of the same proofs (07:38 UTC, before
comment-only edits of the file headers). That earlier print is not included; the comparison says "identical".

In these copies, folders of the build machine are written as `$HOME/build/...` and its host name as `build-host`, and the
first comment lines of the two scripts were reworded. Nothing else was changed.
