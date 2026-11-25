import OAI.Combinatorics.HadwigerScaled.ScaledTransfer
import OAI.Combinatorics.HadwigerCounterexample.ExponentialGraphTransfer

namespace OAI

/-! # Exponential graph transfer at threshold m/Q.

Generalizes OpenAI `transfer_scales` (ExponentialGraphTransfer.lean): marginal cap
`bp (12*Q+1)` instead of `bp 1000`, conclusion `cm < m/Q` instead of `m/100`.
Choice: k = (m+Q)/(2Q), so 2Qk ≤ m+Q and m-Q < 2Qk; with m ≥ 2Q this gives m ≤ 4Qk.
Exponent checks (y = g N, m = 2^(1000 y)):
  set term : m + m + (1 - (12Q+1)) k ≤ -m   ⇔ 12Qk ≥ 3m  ⇐ m ≤ 4Qk;
  pair term: m + 2000 y k - 4000 y k ≤ -m   ⇔ 1000 y k ≥ m ⇐ m ≤ 4Qk and y ≥ N ≥ Q.
-/

noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Real Filter

theorem transfer_scales_div {g : ℕ} (hg : 0 < g) {B : ℝ} (hB : 0 ≤ B) {Q : ℕ} (hQ : 0 < Q) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Type) [Fintype A] [Nonempty A]
      (H : Holes A) (μ : Wgt A), IsLaw μ →
      (Fintype.card (A × A) : ℝ) ≤ bp (B * (N:ℝ)^2) →
      (∀ w : Wgt (A × A), IsLaw w → pairCaps μ (bp (12*Q+1)) (bp (4000*g*N)) w →
        carried w H.unit → bp (-100*g*N) ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2)) →
      ∃ x : Fin (ord g N) → A,
        (H.graph x).indepNum ≤ 2 ∧
        (connectedMatchingNumber (H.graph x) : ℚ) < (ord g N : ℚ)/Q := by
  have hg' : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hh := bp_poly_dom_nat (a:=100*g) (by positivity) (B+1) 2
  filter_upwards [hh, eventually_ge_atTop (max 1 Q),
    (tendsto_ord hg).eventually (eventually_ge_atTop (2*Q+2))] with N hN hN' hord
  intro A _ _ H μ hμ hA hs
  let y : ℝ := g * (N:ℝ)
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN'
  have hNQ : Q ≤ N := le_trans (le_max_right _ _) hN'
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hy : 1 ≤ y := by unfold y; nlinarith
  have hyQ : (Q:ℝ) ≤ y := by
    have : (Q:ℝ) ≤ N := by exact_mod_cast hNQ
    unfold y; nlinarith
  let m := ord g N
  let L : ℕ := 2^(200*g*N)
  have hm : (m:ℝ) = bp (1000*y) := by rw [cast_ord]; unfold y; ring_nf
  have hl : (L:ℝ) = bp (200*y) := by
    have h := (bp_nat (200*g*N)).symm
    push_cast at h
    dsimp only [L]
    push_cast
    unfold y
    rwa [← mul_assoc]
  let z : ℝ := B*(N:ℝ)^2
  have hz : 0 ≤ z := by unfold z; positivity
  have hb : z + 1 < bp (100*y) := by
    have hh : (B+1)*(N:ℝ)^2 < bp (100*y) := by simpa only [y, mul_assoc] using hN
    unfold z
    nlinarith only [hh,hNr]
  let k := (m+Q)/(2*Q)
  have h2Q : 0 < 2*Q := by omega
  have hk1 : 2*Q*k ≤ m+Q := Nat.mul_div_le (m+Q) (2*Q)
  have hk2 : m + Q < 2*Q*k + 2*Q := by
    have h1 := Nat.div_add_mod (m+Q) (2*Q)
    have h2 := Nat.mod_lt (m+Q) h2Q
    change 2*Q*k + (m+Q) % (2*Q) = m+Q at h1
    omega
  refine transfer_div H hμ (bp_pos _) (bp_pos _) (bp_pos _) hs (L:=L) (k:=k) ?_ hQ hk1 ?_
  · have hi : log (Fintype.card (A × A) : ℝ) ≤ z * Real.log 2 := by
      rw [← log_bp]
      exact Real.log_le_log (by exact_mod_cast Fintype.card_pos) hA
    apply lt_of_le_of_lt hi
    calc z * log 2 < bp (100*y)*log 2 :=
           mul_lt_mul_of_pos_right (by linarith only [hb]) (Real.log_pos (by norm_num))
         _ = _ := by
           rw [hl,← mul_assoc (bp (200 * y)),← bp_add]
           unfold y; ring_nf
  · -- m ≥ 2Q+2, so m - Q < 2Qk gives m ≤ 4Qk
    have hmQ : 2*Q+2 ≤ m := hord
    have hk : (m:ℝ) ≤ 4*Q*k := by
      have hk' : m ≤ 4*Q*k := by nlinarith
      exact_mod_cast hk'
    have hm' : (2:ℝ) ≤ m := by
      have : 2 ≤ m := by omega
      exact_mod_cast this
    let a := (Fintype.card (A × A):ℝ)+1
    have ha : a ≤ bp (z+1) := by
      rw [bp_add,bp_one]
      have hx : 1 ≤ bp z := by simpa only [bp_zero] using bp_le hz
      change _ ≤ bp z at hA
      dsimp only [a]
      linarith only [hx,hA]
    have hal : a^L ≤ bp (m:ℝ) := calc
      a^L ≤ bp (z+1)^L := by
        have hp : 0 ≤ a := by dsimp [a]; positivity
        gcongr
      _ = bp ((z+1)*L) := (bp_mul_nat _ _).symm
      _ ≤ bp (m:ℝ) := bp_le (by
        rw [hm,hl]
        calc (z+1)*bp (200*y) ≤ bp (100*y)*bp (200*y) :=
               mul_le_mul_of_nonneg_right hb.le (bp_pos _).le
             _ ≤ bp (1000*y) := by rw [← bp_add]; apply bp_le; linarith only [hy])
    let d := bp (4000*(g:ℝ)*(N:ℝ))
    have ha1 : bp (m:ℝ) * ((2:ℝ)^m * (2/bp (12*Q+1))^k) ≤ bp (-(m:ℝ)) := by
      rw [← bp_nat, show 2/bp (12*Q+1) = bp (1-(12*Q+1)) by simp only [bp_sub,bp_one],
        ← bp_mul_nat, ← bp_add, ← bp_add]
      apply bp_le
      -- m + m + (1-(12Q+1)) k ≤ -m  ⇔  12 Q k ≥ 3 m
      nlinarith
    have ha2 : bp (m:ℝ) * ((m:ℝ)^(k+k) * (d⁻¹)^k) ≤ bp (-(m:ℝ)) := by
      have he : (m:ℝ)^(k+k) = bp ((1000*y)*(k+k:ℕ)) := by
        rw [hm,bp_mul_nat]
      rw [he, show d⁻¹ = bp (-(4000*y)) by simp only [bp_neg,d,y,mul_assoc],
        ← bp_mul_nat, ← bp_add, ← bp_add]
      apply bp_le
      push_cast
      -- need 1000 y k ≥ m: from m ≤ 4Qk and Q ≤ y
      have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
      have hx : (m:ℝ) ≤ 4*y*k := by nlinarith
      nlinarith
    have hx : bp (-(m:ℝ)) < 1/2 := by
      rw [show (1:ℝ)/2 = bp (-1) by simp only [one_div,bp_neg,bp_one]]
      exact bp_lt (by linarith only [hm'])
    change a^L * (2^m * (2/bp (12*Q+1))^k + (m:ℝ)^(k+k) * d⁻¹^k) < 1
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hal (by
      have h := bp_pos (12*(Q:ℝ)+1)
      have h' : 0 < d := bp_pos _
      positivity)) ?_
    linarith only [ha1,ha2,hx]

end HadwigerCounterexample

end

end OAI
