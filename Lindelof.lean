import LiouvilleEnergyRH.Closure
import LiouvilleEnergyRH.Lindelof.Main
import AveragedChowla

/-!
# The Lindelöf hypothesis under Hypothesis H

Hypothesis H (no Dirichlet `L`-function vanishes in `re s > 1/2`) gives, for every `η > 0`,
`ζ(1/2 + it) ≪_η (3 + |t|)^η` (`lindelof_of_H`), and `ζ(σ + it) ≪ (3 + |t|)^η` uniformly on
`1/2 + δ ≤ σ ≤ 3/4` (`zeta_strip_of_H`). The only input from H is the zero-free half-plane of
`ζ`, `zeta_ne_zero_of_H`.
-/

namespace LiouvilleEnergyRH

/-- **The Lindelöf hypothesis.** Under Hypothesis H, `‖ζ(1/2 + it)‖ ≤ K (3 + |t|)^η`. -/
theorem lindelof_of_H (h : HypothesisH) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ t : ℝ, ‖riemannZeta (1 / 2 + (t : ℂ) * Complex.I)‖ ≤ K * (3 + |t|) ^ η :=
  Lindelof.lindelof (zeta_ne_zero_of_H h) hη

/-- Under Hypothesis H, `ζ` is bounded by `D (2 (3 + |t|)^2)^ε` on `1/2 + 8e ≤ σ ≤ 3/4`. -/
theorem zeta_strip_of_H (h : HypothesisH) {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ t : ℝ, 1 / 2 + 8 * e ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε :=
  Lindelof.zeta_strip_bound (zeta_ne_zero_of_H h) he he' hε

end LiouvilleEnergyRH
