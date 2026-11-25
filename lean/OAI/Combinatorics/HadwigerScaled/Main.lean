import OAI.Combinatorics.HadwigerScaled.ScaledParameters
import OAI.Combinatorics.HadwigerScaled.ScaledExponential
import OAI.Combinatorics.HadwigerCounterexample.Main

namespace OAI

/-!
# Connected matchings of size o(n) in graphs with independence number two

Same proof as OpenAI `exists_graphs` (HadwigerCounterexample/Main.lean), with
`exists_parameters_at (12*Q+1)` in place of `exists_parameters` and
`transfer_scales_div` in place of `transfer_scales`. The supersaturation input
`eventual_conflict_lower_bound` is used UNCHANGED: it already holds for every
`PreparationParameters` b satisfying `AnalyticParameters`, whatever b.L is.
-/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset
open scoped BigOperators Topology
open PreparationParameters HadwigerMatching LinearListHadwiger

theorem exists_graphs_div {Q : ℕ} (hQ : 0 < Q) (M : ℕ) : ∃ m:ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G:ℚ) < (m:ℚ)/Q := by
  classical
  obtain ⟨p,b,k,r,h,hg,hd,he⟩:= exists_parameters_at (12*(Q:ℝ)+1)
  have ht:=h.enter.first
  let B:=4*num (Comp p.g)
  let Y (n:ℕ):=k*n
  have hy := (trend_sizes atTop le_rfl ht.hM).1
  have hp : 0 < p.g := lt_of_lt_of_le (by norm_num) ht.hG
  have hs : ∀ᶠ n:ℕ in atTop, ∃ m:ℕ, max M 5 ≤ m ∧
      ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G:ℚ)<(m:ℚ)/Q := by
    filter_upwards [eventual_conflict_lower_bound h,ht.wrap,goodMixers p b.pins r (by linarith only [ht.hG])
      ht.hJ (by have hi:=h.profiles; omega) h.bigJ,hy.eventually
      (transfer_scales_div hp (show 0≤B from mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hQ),
      ((tendsto_ord hp).comp hy).eventually (eventually_ge_atTop (max M 5))] with n hn ht hl hq hN
    let N:=Y n
    obtain ⟨m,hm,he'⟩:=hl
    have hT:= hn m hm he'; have hV:2*num (Full p n)<(N:ℝ):=ht.1
    have hC : num (UnitType p n N)≤bp (B*N^ (2:ℕ)) := by
      rw [unit_size]; apply bp_le
      have hf : num (Full p n) ≤ N := by linarith only [hV,(Nat.cast_nonneg N : 0≤(N:ℝ))]
      unfold B
      calc _ ≤ num (Comp p.g)*4*(N:ℝ)*N := mul_le_mul_of_nonneg_left hf (by unfold num; positivity)
           _ = _ := by ring
    obtain ⟨x,hx,hX⟩:=hq (Orient p n N) (rawHoles m) (raw m N) (raw_law m hV) hC (by
      intro w hw hC hU
      apply hT w _ hU
      apply born w hw m
      rw [hd,he]; simpa only [N,Y,Nat.cast_mul,Nat.cast_ofNat] using hC)
    exact ⟨ord p.g N,hN,(rawHoles m).graph x,hx,hX⟩
  obtain ⟨n,hn⟩:=hs.exists; exact hn

/-- For every rational β > 0: arbitrarily large graphs with independence number at
most two and connected-matching number below β·|V|. -/
theorem exists_graphs_beta (β : ℚ) (hβ : 0 < β) (M : ℕ) : ∃ m : ℕ, M ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G : ℚ) < β * m := by
  let Q : ℕ := ⌈β⁻¹⌉₊
  have hQ : 0 < Q := Nat.ceil_pos.mpr (inv_pos.mpr hβ)
  obtain ⟨m,hm,G,ha,hc⟩ := exists_graphs_div hQ M
  refine ⟨m, le_trans (le_max_left _ _) hm, G, ha, lt_of_lt_of_le hc ?_⟩
  -- m/Q ≤ β m because 1/β ≤ Q
  have hQ' : β⁻¹ ≤ (Q:ℚ) := Nat.le_ceil _
  have hq : (0:ℚ) < Q := by exact_mod_cast hQ
  have hm0 : (0:ℚ) ≤ m := Nat.cast_nonneg _
  rw [div_le_iff₀ hq]
  have : 1 ≤ β * Q := by
    have := mul_le_mul_of_nonneg_left hQ' hβ.le
    rwa [mul_inv_cancel₀ hβ.ne'] at this
  nlinarith

/-- Corollary: h(G) < (1/3 + 2β)|V| + 2/3 (Duchet–Meyniel's n/3 is sharp for α ≤ 2). -/
theorem exists_small_hadwiger (β : ℚ) (hβ : 0 < β) (M : ℕ) : ∃ m : ℕ, M ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G : ℚ) < β * m ∧
      (hadwigerNumber G : ℚ) < (1/3 + 2*β) * m + 2/3 := by
  obtain ⟨m,hm,G,ha,hc⟩ := exists_graphs_beta β hβ (max M 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have : NeZero m := ⟨by omega⟩
  have hx := (full_matching_minor_proposition (Fin m) G).1
  rw [Fintype.card_fin] at hx
  refine ⟨m, le_trans (le_max_left _ _) hm, G, ha, hc, ?_⟩
  have hm0 : (0:ℚ) ≤ m := Nat.cast_nonneg _
  -- h ≤ (m + 4c + 2)/3 < (m + 4βm + 2)/3 ≤ (1/3+2β)m + 2/3
  calc (hadwigerNumber G : ℚ) ≤ ((m:ℚ) + 4*(connectedMatchingNumber G:ℚ) + 2)/3 := hx
    _ < ((m:ℚ) + 4*(β*m) + 2)/3 := by linarith
    _ ≤ (1/3 + 2*β) * m + 2/3 := by nlinarith

/-- Linear-CM (weak Füredi–Gyárfás–Simonyi) is false. -/
theorem not_linear_cm :
    ¬ ∃ c : ℚ, 0 < c ∧ ∃ M : ℕ, ∀ m ≥ M, ∀ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 → c * m ≤ (connectedMatchingNumber G : ℚ) := by
  rintro ⟨c, hc, M, hM⟩
  obtain ⟨m, hm, G, ha, hcm⟩ := exists_graphs_beta c hc M
  exact absurd (hM m hm G ha) (not_le.mpr hcm)

/-- HC_ε is false. -/
theorem not_hc_eps :
    ¬ ∃ ε : ℚ, 0 < ε ∧ ∃ M : ℕ, ∀ m ≥ M, ∀ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 → (1/3 + ε) * m ≤ (hadwigerNumber G : ℚ) := by
  rintro ⟨ε, hε, M, hM⟩
  obtain ⟨m, hm, G, ha, -, hh⟩ :=
    exists_small_hadwiger (ε/4) (by positivity) (max M ⌈(2:ℚ)/ε⌉₊)
  have h1 : M ≤ m := le_trans (le_max_left _ _) hm
  have h2 : (2:ℚ)/ε ≤ m := le_trans (Nat.le_ceil _)
    (by exact_mod_cast le_trans (le_max_right _ _) hm)
  have h3 : (2:ℚ) ≤ ε * m := by rwa [div_le_iff₀ hε, mul_comm] at h2
  have := hM m h1 G ha
  nlinarith

end HadwigerCounterexample

end

end OAI
