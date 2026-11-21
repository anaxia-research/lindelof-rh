import LiouvilleEnergyRH.Lindelof.Strip
import Mathlib.Analysis.Complex.Hadamard

/-!
# The Lindelöf hypothesis under the zero-free half-plane

If `ζ(s) ≠ 0` for `re s > 1/2`, then `ζ(1/2 + it) ≪_η (3 + |t|)^η` for every `η > 0`.

Fix `t₀` and put `g(s) = ζ(s) exp((s - c)^2)` with `c = 1/2 + i t₀`. On the strip
`1/4 ≤ re s ≤ u = 1/2 + 8e` the Gaussian factor is `≤ 2 exp(-(im s - t₀)^2)`, which absorbs the
polynomial growth of `ζ` away from height `t₀`. On `re s = 1/4` the unconditional bound gives
`‖g‖ ≤ 28 W`, and on `re s = u` the logarithmic control lemma gives `‖g‖ ≤ 4 D W^ε`, where
`W = 2 (3 + |t₀|)^2`. Hadamard's three-lines theorem at `s = c`, where `‖g(c)‖ = ‖ζ(c)‖`,
gives `‖ζ(c)‖ ≤ (28 W)^{1-θ} (4 D W^ε)^θ` with `1 - θ ≤ 32 e`.
-/

namespace LiouvilleEnergyRH.Lindelof

open Complex Set Metric Filter

/-- `(1 + |v|) e^{-v^2} ≤ 2`. -/
lemma gauss_le (v : ℝ) : (1 + |v|) * Real.exp (-v ^ 2) ≤ 2 := by
  have h1 : Real.exp (-v ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : |v| ≤ Real.exp (v ^ 2) := by
    have := Real.add_one_le_exp (v ^ 2)
    have : |v| ≤ v ^ 2 + 1 := by nlinarith [sq_abs v, abs_nonneg v]
    linarith
  have h3 : |v| * Real.exp (-v ^ 2) ≤ 1 := by
    have hp : 0 < Real.exp (-v ^ 2) := Real.exp_pos _
    calc |v| * Real.exp (-v ^ 2) ≤ Real.exp (v ^ 2) * Real.exp (-v ^ 2) :=
          mul_le_mul_of_nonneg_right h2 hp.le
      _ = 1 := by simp [← Real.exp_add]
  nlinarith

/-- The Gaussian factor on the strip. -/
lemma norm_gauss_le {t₀ : ℝ} {s : ℂ} (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 3 / 4) :
    ‖cexp ((s - (1 / 2 + (t₀ : ℂ) * I)) ^ 2)‖ ≤ 2 * Real.exp (-(s.im - t₀) ^ 2) := by
  rw [Complex.norm_exp]
  have hre : ((s - (1 / 2 + (t₀ : ℂ) * I)) ^ 2).re = (s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [hre, sub_eq_add_neg, Real.exp_add]
  have hq : (s.re - 1 / 2) ^ 2 ≤ 1 / 16 := by nlinarith
  have he : Real.exp ((s.re - 1 / 2) ^ 2) ≤ 2 := by
    calc Real.exp ((s.re - 1 / 2) ^ 2) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by have := Real.log_two_gt_d9; linarith)
      _ = 2 := Real.exp_log (by norm_num)
  exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le

/-- `ζ` on the strip `1/4 ≤ re s ≤ 3/4`, unconditionally. -/
lemma zeta_le_on_strip {s : ℂ} (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 3 / 4) :
    s ≠ 1 ∧ ‖riemannZeta s‖ ≤ 8 * (1 + |s.im|) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
  refine ⟨hs1, ?_⟩
  have hb := norm_riemannZeta_le_quarter h1 hs1
  have hd : 1 / 4 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    simp at this
    rw [abs_of_neg (by linarith)] at this
    linarith
  have hinv : 1 / ‖s - 1‖ ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hn : ‖s‖ ≤ 3 / 4 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 3 / 4 + |s.im| := by rw [abs_of_pos (by linarith)]; linarith
  nlinarith [abs_nonneg s.im]

lemma one_add_le (t t₀ : ℝ) : 1 + |t| ≤ (1 + |t₀|) * (1 + |t - t₀|) := by
  have : |t| ≤ |t₀| + |t - t₀| := by
    calc |t| = |t₀ + (t - t₀)| := by ring_nf
      _ ≤ |t₀| + |t - t₀| := abs_add_le _ _
  nlinarith [abs_nonneg t₀, abs_nonneg (t - t₀)]

lemma three_add_le (t t₀ : ℝ) : 3 + |t| ≤ (3 + |t₀|) * (1 + |t - t₀|) := by
  have : |t| ≤ |t₀| + |t - t₀| := by
    calc |t| = |t₀ + (t - t₀)| := by ring_nf
      _ ≤ |t₀| + |t - t₀| := abs_add_le _ _
  nlinarith [abs_nonneg t₀, abs_nonneg (t - t₀)]

set_option maxHeartbeats 1600000 in
/-- **The Lindelöf hypothesis.** If `ζ(s) ≠ 0` for `re s > 1/2`, then for every `η > 0` there is
`K` with `‖ζ(1/2 + it)‖ ≤ K (3 + |t|)^η` for all real `t`. -/
theorem lindelof (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ t : ℝ, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ K * (3 + |t|) ^ η := by
  set η' := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set e := min (η' / 192) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he192 : 192 * e ≤ η' := by have := min_le_left (η' / 192) (1 / 2000); linarith
  have he2 : e ≤ 1 / 2000 := min_le_right _ _
  set ε := η' / 6 with hε_def
  have hε : 0 < ε := by positivity
  have hε2 : 2 * ε ≤ 1 := by rw [hε_def]; linarith
  obtain ⟨D, hD, hDb⟩ := zeta_strip_bound hz he he' hε
  refine ⟨28 * max (4 * D) 1, fun t₀ => ?_⟩
  set u : ℝ := 1 / 2 + 8 * e with hu
  have hu1 : 1 / 2 < u := by linarith
  have hu2 : u ≤ 5 / 8 := by linarith
  set c : ℂ := 1 / 2 + (t₀ : ℂ) * I with hc
  set g : ℂ → ℂ := fun s => riemannZeta s * cexp ((s - c) ^ 2) with hg
  set W : ℝ := 2 * ((1 : ℕ) : ℝ) * (3 + |t₀|) ^ 2 with hW
  have hW1 : 1 ≤ W := by rw [hW]; push_cast; nlinarith [abs_nonneg t₀]
  have hW0 : 0 ≤ W := by linarith
  -- bound on the whole strip
  have hstrip : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖g s‖ ≤ 28 * W := by
    intro s h1 h2
    obtain ⟨_, hzb⟩ := zeta_le_on_strip h1 h2
    have hE := norm_gauss_le (t₀ := t₀) h1 h2
    have hG := gauss_le (s.im - t₀)
    have hO := one_add_le s.im t₀
    have hp : 0 ≤ Real.exp (-(s.im - t₀) ^ 2) := (Real.exp_pos _).le
    have hW' : 6 * (1 + |t₀|) ≤ W := by rw [hW]; push_cast; nlinarith [abs_nonneg t₀]
    simp only [hg, norm_mul]
    calc ‖riemannZeta s‖ * ‖cexp ((s - c) ^ 2)‖
        ≤ (8 * ((1 + |t₀|) * (1 + |s.im - t₀|))) * (2 * Real.exp (-(s.im - t₀) ^ 2)) := by
          gcongr
          exact hzb.trans (by nlinarith)
      _ = 16 * (1 + |t₀|) * ((1 + |s.im - t₀|) * Real.exp (-(s.im - t₀) ^ 2)) := by ring
      _ ≤ 16 * (1 + |t₀|) * 2 := by gcongr
      _ ≤ 28 * W := by nlinarith
  -- bound on the right line
  have hright : ∀ s ∈ re ⁻¹' {u}, ‖g s‖ ≤ 4 * D * W ^ ε := by
    intro s hs
    simp only [mem_preimage, mem_singleton_iff] at hs
    have hs' : s = (u : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [hs]
    have hzb := hDb u s.im le_rfl (by linarith)
    rw [← hs'] at hzb
    have hE := norm_gauss_le (t₀ := t₀) (s := s) (by rw [hs]; linarith) (by rw [hs]; linarith)
    set v := s.im - t₀
    have h3 := three_add_le s.im t₀
    have hbase : 2 * ((1 : ℕ) : ℝ) * (3 + |s.im|) ^ 2 ≤ W * (1 + |v|) ^ 2 := by
      rw [hW]; push_cast
      have h0 : 0 ≤ 3 + |s.im| := by positivity
      have := mul_le_mul h3 h3 h0 (by positivity)
      nlinarith
    have hpow : (2 * ((1 : ℕ) : ℝ) * (3 + |s.im|) ^ 2) ^ ε ≤ W ^ ε * (1 + |v|) := by
      calc (2 * ((1 : ℕ) : ℝ) * (3 + |s.im|) ^ 2) ^ ε ≤ (W * (1 + |v|) ^ 2) ^ ε :=
            Real.rpow_le_rpow (by positivity) hbase hε.le
        _ = W ^ ε * ((1 + |v|) ^ 2) ^ ε := Real.mul_rpow hW0 (by positivity)
        _ ≤ W ^ ε * (1 + |v|) := by
            gcongr
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            calc (1 + |v|) ^ ((2 : ℕ) * ε : ℝ) ≤ (1 + |v|) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v])
                    (by push_cast; linarith)
              _ = 1 + |v| := Real.rpow_one _
    have hG := gauss_le v
    have hWe : 0 ≤ W ^ ε := by positivity
    simp only [hg, norm_mul]
    calc ‖riemannZeta s‖ * ‖cexp ((s - c) ^ 2)‖
        ≤ (D * (W ^ ε * (1 + |v|))) * (2 * Real.exp (-v ^ 2)) := by
          gcongr
          exact hzb.trans (mul_le_mul_of_nonneg_left hpow hD)
      _ = 2 * D * W ^ ε * ((1 + |v|) * Real.exp (-v ^ 2)) := by ring
      _ ≤ 2 * D * W ^ ε * 2 := by gcongr
      _ = 4 * D * W ^ ε := by ring
  have hleft : ∀ s ∈ re ⁻¹' {(1 / 4 : ℝ)}, ‖g s‖ ≤ 28 * W := by
    intro s hs
    simp only [mem_preimage, mem_singleton_iff] at hs
    exact hstrip s (by rw [hs]) (by rw [hs]; norm_num)
  have hul : (1 / 4 : ℝ) < u := by linarith
  have hdiff : DifferentiableOn ℂ g (Complex.HadamardThreeLines.verticalClosedStrip (1 / 4) u) := by
    intro s hs
    have hre : s.re ≤ u := hs.2
    have hs1 : s ≠ 1 := by intro h; rw [h] at hre; simp at hre; linarith
    exact ((differentiableAt_riemannZeta hs1).mul
      ((differentiableAt_id.sub_const c).pow 2).cexp).differentiableWithinAt
  have hcl : closure (Complex.HadamardThreeLines.verticalStrip (1 / 4) u) ⊆
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 4) u :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage continuous_re)
  have hdc : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip (1 / 4) u) :=
    (hdiff.mono hcl).diffContOnCl
  have hbdd : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip (1 / 4) u) := by
    refine ⟨28 * W, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hstrip s hs.1 (by linarith [hs.2])
  have hcmem : c ∈ Complex.HadamardThreeLines.verticalClosedStrip (1 / 4) u := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage, mem_Icc, hc]
    simp; constructor <;> linarith
  have hmain := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hul hcmem
    hdc hbdd hleft hright
  have hgc : ‖g c‖ = ‖riemannZeta c‖ := by simp [hg]
  rw [hgc] at hmain
  have hcre : c.re = 1 / 2 := by simp [hc]
  rw [hcre] at hmain
  set θ : ℝ := (1 / 2 - 1 / 4) / (u - 1 / 4) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; apply div_nonneg <;> linarith
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
  have h1θ : 1 - θ ≤ 32 * e := by
    rw [hθ]
    have hden : 0 < u - 1 / 4 := by linarith
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hden]
    rw [hu]; nlinarith
  -- (28 W)^{1-θ} ≤ 28 W^{1-θ}
  have hA : (28 * W) ^ (1 - θ) ≤ 28 * W ^ (1 - θ) := by
    rw [Real.mul_rpow (by norm_num) hW0]
    gcongr
    calc (28 : ℝ) ^ (1 - θ) ≤ 28 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 28 := Real.rpow_one 28
  have hB : (4 * D * W ^ ε) ^ θ ≤ max (4 * D) 1 * W ^ ε := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have hm : (4 * D) ^ θ ≤ max (4 * D) 1 := by
      calc (4 * D) ^ θ ≤ (max (4 * D) 1) ^ θ :=
            Real.rpow_le_rpow (by positivity) (le_max_left _ _) hθ0
        _ ≤ (max (4 * D) 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) hθ1
        _ = max (4 * D) 1 := Real.rpow_one _
    have hw : (W ^ ε) ^ θ ≤ W ^ ε := by
      calc (W ^ ε) ^ θ ≤ (W ^ ε) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (Real.one_le_rpow hW1 hε.le) hθ1
        _ = W ^ ε := Real.rpow_one _
    exact mul_le_mul hm hw (by positivity) (by positivity)
  have hW3 : W ≤ (3 + |t₀|) ^ (3 : ℝ) := by
    rw [hW]; push_cast
    have : (3 + |t₀|) ^ (3 : ℝ) = (3 + |t₀|) ^ (3 : ℕ) := by norm_cast
    rw [this]
    nlinarith [abs_nonneg t₀, sq_nonneg (3 + |t₀|)]
  have hT1 : 1 ≤ 3 + |t₀| := by linarith [abs_nonneg t₀]
  have hWpow : W ^ (1 - θ) * W ^ ε ≤ (3 + |t₀|) ^ η := by
    rw [← Real.rpow_add (by linarith)]
    calc W ^ (1 - θ + ε) ≤ ((3 + |t₀|) ^ (3 : ℝ)) ^ (1 - θ + ε) :=
          Real.rpow_le_rpow hW0 hW3 (by linarith)
      _ = (3 + |t₀|) ^ (3 * (1 - θ + ε)) := by rw [← Real.rpow_mul (by linarith)]
      _ ≤ (3 + |t₀|) ^ η :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hε_def]; nlinarith)
  have hp1 : 0 ≤ (28 * W) ^ (1 - θ) := by positivity
  have hp2 : 0 ≤ W ^ (1 - θ) := by positivity
  have hp3 : 0 ≤ W ^ ε := by positivity
  calc ‖riemannZeta c‖ ≤ (28 * W) ^ (1 - θ) * (4 * D * W ^ ε) ^ θ := by
        exact hmain
    _ ≤ (28 * W ^ (1 - θ)) * (max (4 * D) 1 * W ^ ε) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 28 * max (4 * D) 1 * (W ^ (1 - θ) * W ^ ε) := by ring
    _ ≤ 28 * max (4 * D) 1 * (3 + |t₀|) ^ η := by gcongr

end LiouvilleEnergyRH.Lindelof
