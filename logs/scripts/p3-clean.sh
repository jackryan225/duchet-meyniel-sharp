#!/bin/sh
# Build from an empty folder of the files of this repository, then the checks (run in $HOME/build/p3-clean/release/lean).
# $HOME/build/p3-clean/oai-checkout/lean holds the 288 files of lean/oai_files.txt from openai/math at commit 3344da5.
ulimit -n 8192
export LEAN_NUM_THREADS=4
O=$HOME/build/results/p3; mkdir -p "$O"
s() { n=$1; shift; echo "--- STEP $n: $*"; sh -c "$*" > "$O/p3-clean-$n.txt" 2>&1; e=$?; tail -c 1500 "$O/p3-clean-$n.txt"; echo; echo "--- STEP $n: exit $e"; }
s 1-assemble 'sh assemble.sh $HOME/build/p3-clean/oai-checkout'
s 2-build 'lake exe cache get && lake build OAI.Combinatorics.HadwigerScaled.Main ComparatorChallenge.HadwigerScaled'
s 3-axioms 'lake env lean Check/Axioms.lean'
s 4-chal 'lake env lean Check/ChallengeView.lean'
s 4-sol 'lake env lean Check/SolutionView.lean'
cmp "$O/p3-clean-4-chal.txt" "$O/p3-clean-4-sol.txt" && echo "CMP chal sol: identical ($(wc -c < $O/p3-clean-4-chal.txt) bytes)"
cmp "$O/p3-clean-4-chal.txt" "$HOME/build/results/hw-sol.txt" && echo "CMP chal vs old hw-sol.txt (07:38Z build): identical"
s 5-leanchecker 'lake env leanchecker -v OAI.Combinatorics.HadwigerScaled OAI.Combinatorics.HadwigerCounterexample OAI.Combinatorics.HadwigerMatching OAI.Combinatorics.ListHadwiger'
echo "modules replayed: $(grep -c '^replaying' $O/p3-clean-5-leanchecker.txt)"
echo "axioms: $(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' $O/p3-clean-3-axioms.txt) standard of $(grep -c 'depends on axioms' $O/p3-clean-3-axioms.txt)"
grep -c "declaration uses 'sorry'\|declaration uses \`sorry\`" $O/p3-clean-2-build.txt | sed 's/^/sorry warnings in build: /'
grep "sorry" $O/p3-clean-2-build.txt | cut -c1-160
sh $HOME/build/scripts/l4l.sh p3 OAI.Combinatorics.HadwigerScaled.Main OAI.HadwigerCounterexample.exists_graphs_div OAI.HadwigerCounterexample.exists_graphs_beta OAI.HadwigerCounterexample.exists_small_hadwiger OAI.HadwigerCounterexample.not_linear_cm OAI.HadwigerCounterexample.not_hc_eps
