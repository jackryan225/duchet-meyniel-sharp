import Mathlib

/-! Mathlib-only statement of the three main theorems (comparator style). The four definitions are
copied verbatim from OpenAI's lean/ComparatorChallenges/HadwigerCounterexample.lean (github.com/openai/math,
commit 3344da59991ed94f9ba711217b29c1d760badfa6, Apache License 2.0). The proofs, under the same names,
are in lean/OAI/Combinatorics/HadwigerScaled/Main.lean. This file was built, and its statements were
compared with the proved ones (see FIDELITY.md and logs/). -/

namespace OAI

namespace HadwigerMatching

universe u
variable {V : Type u}

def IsTouchingMatching (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ G.IsClique (e : Set V)) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    ∃ v ∈ e, ∃ w ∈ f, G.Adj v w)

noncomputable def connectedMatchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), IsTouchingMatching G M ∧ M.card = n}

end HadwigerMatching

namespace LinearListHadwiger

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)

noncomputable def hadwigerNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | HasCliqueMinor G t}

end LinearListHadwiger

namespace HadwigerCounterexample

open HadwigerMatching LinearListHadwiger

/-- For every β > 0 there are arbitrarily large graphs with α ≤ 2,
connected-matching number < β·m and Hadwiger number < (1/3 + 2β)·m + 2/3. -/
theorem exists_small_hadwiger (β : ℚ) (hβ : 0 < β) (M : ℕ) : ∃ m : ℕ, M ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G : ℚ) < β * m ∧
      (hadwigerNumber G : ℚ) < (1/3 + 2*β) * m + 2/3 := by
  sorry

/-- Linear-CM (weak Füredi–Gyárfás–Simonyi) is false. -/
theorem not_linear_cm :
    ¬ ∃ c : ℚ, 0 < c ∧ ∃ M : ℕ, ∀ m ≥ M, ∀ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 → c * m ≤ (connectedMatchingNumber G : ℚ) := by
  sorry

/-- HC_ε is false: no ε > 0 with h(G) ≥ (1/3 + ε)|V| for all large α ≤ 2 graphs. -/
theorem not_hc_eps :
    ¬ ∃ ε : ℚ, 0 < ε ∧ ∃ M : ℕ, ∀ m ≥ M, ∀ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 → (1/3 + ε) * m ≤ (hadwigerNumber G : ℚ) := by
  sorry

end HadwigerCounterexample

end OAI
