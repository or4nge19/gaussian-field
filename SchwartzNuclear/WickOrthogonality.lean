/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick Monomial Orthogonality under Gaussian Measure

The Wick-ordered monomial `:x^n:_c` has zero mean under a centered
Gaussian of variance c, for n ≥ 1. This is the fundamental
orthogonality property that makes Wick ordering useful in QFT.

## Main results

- `wickMonomial_deriv` — d/dx :x^n:_c = n · :x^{n-1}:_c
- `stein_lemma` — E[x f(x)] = c E[f'(x)] under `gaussianReal 0 c.toNNReal`, for `f`
  differentiable with `f` and `f'` of polynomial growth
- `wickMonomial_mean_zero` — ∫ :x^n:_c dN(0,c) = 0 for n ≥ 1, `0 ≤ c`

## Existing infrastructure

- `wickMonomial` (HermiteWick.lean): the Wick monomial function
- `wick_eq_hermiteR` (HermiteWick.lean): :x^n:_c = c^{n/2} · He_n(x/√c)
- `probHermite` (auto1/Hermite/Basic.lean): Hermite polynomial H_n(x;c)
  with recurrence H_{n+1} = x·H_n - c·H_n'

## Proof strategy

The proof uses induction + Stein's lemma (Gaussian integration by parts):

For centered Gaussian μ with variance c:
  E[x · f(x)] = c · E[f'(x)]

Then:
- E[:x^0:] = 1
- E[:x^1:] = E[x] = 0 (centered)
- E[:x^{n+1}:] = E[x · :x^n:] - n·c · E[:x^{n-1}:]
                = c · E[d/dx :x^n:] - n·c · E[:x^{n-1}:]  (Stein)
                = c·n · E[:x^{n-1}:] - n·c · E[:x^{n-1}:]  (derivative)
                = 0  (induction)

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §I.3
- Glimm-Jaffe, *Quantum Physics*, §8.6
-/
module

public import SchwartzNuclear.HermiteWick
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

noncomputable section

open Real Polynomial MeasureTheory
open scoped NNReal ENNReal

/-! ## Helper: Wick polynomial representation

The Wick monomial `wickMonomial n c` is a polynomial in `x`. We represent it
as a `Polynomial ℝ` to leverage Mathlib's polynomial differentiability and
growth bounds. -/

/-- The Wick polynomial `:x^n:_c` as a formal polynomial. -/
private def wickPoly : ℕ → ℝ → ℝ[X]
  | 0, _ => 1
  | 1, _ => X
  | n + 2, c => X * wickPoly (n + 1) c - Polynomial.C ((n + 1 : ℝ) * c) * wickPoly n c

/-- The Wick monomial equals evaluation of the Wick polynomial. -/
private theorem wickMonomial_eq_eval (n : ℕ) (c x : ℝ) :
    wickMonomial n c x = (wickPoly n c).eval x := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [wickMonomial, wickPoly]
    | 1 => simp [wickMonomial, wickPoly]
    | k + 2 =>
      rw [wickMonomial_succ_succ]
      simp only [wickPoly, eval_sub, eval_mul, eval_X, eval_C]
      rw [ih (k + 1) (by omega), ih k (by omega)]

/-- The Wick monomial is differentiable (it's a polynomial). -/
private theorem wickMonomial_differentiable (n : ℕ) (c : ℝ) :
    Differentiable ℝ (wickMonomial n c) := by
  have : wickMonomial n c = fun x => (wickPoly n c).eval x := by
    ext x; exact wickMonomial_eq_eval n c x
  rw [this]; exact (wickPoly n c).differentiable

/-- The Wick monomial has polynomial growth (it's bounded by `C * (1 + |x|)^d`). -/
private theorem wickMonomial_growth (n : ℕ) (c : ℝ) :
    ∃ (C : ℝ) (d : ℕ), ∀ x : ℝ, |wickMonomial n c x| ≤ C * (1 + |x|) ^ d := by
  suffices h : ∀ (p : ℝ[X]), ∃ (C : ℝ) (d : ℕ), ∀ x : ℝ, |p.eval x| ≤ C * (1 + |x|) ^ d by
    obtain ⟨C, d, hb⟩ := h (wickPoly n c)
    exact ⟨C, d, fun x => by rw [wickMonomial_eq_eval]; exact hb x⟩
  intro p
  refine ⟨(∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) + 1, p.natDegree, fun x => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  have hone : (1 : ℝ) ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
  calc |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
        congr 1; ext i; rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * (1 + |x|) ^ p.natDegree := by
        apply Finset.sum_le_sum; intro i hi
        exact mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (abs_nonneg x) (le_add_of_nonneg_left one_pos.le) i).trans
            (pow_le_pow_right₀ hone (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
          (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * (1 + |x|) ^ p.natDegree := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        linarith [pow_nonneg (by linarith [abs_nonneg x] : (0 : ℝ) ≤ 1 + |x|) p.natDegree]

/-- `HasDerivAt` for `wickMonomial n c` at every point, for all `n` (including `n = 0`).
The derivative is `n * wickMonomial (n - 1) c x`. -/
private theorem wickMonomial_hasDerivAt_all (c : ℝ) (n : ℕ) :
    ∀ x : ℝ, HasDerivAt (wickMonomial n c) (↑n * wickMonomial (n - 1) c x) x := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => intro x; simp [wickMonomial]; exact hasDerivAt_const x 1
    | 1 => intro x; simp [wickMonomial]; exact hasDerivAt_id x
    | (k + 2) =>
      intro x
      have ih1 := ih (k + 1) (by omega) x
      have ih0 := ih k (by omega) x
      simp only [show (k + 1 : ℕ) - 1 = k from by omega] at ih1
      have hsub := ((hasDerivAt_id x).mul ih1).sub (ih0.const_mul ((↑k + 1 : ℝ) * c))
      have h_eq : (id * wickMonomial (k + 1) c - fun y => (↑k + 1) * c * wickMonomial k c y) =
        wickMonomial (k + 2) c := by ext y; simp [id, wickMonomial_succ_succ]
      rw [h_eq] at hsub
      refine hsub.congr_deriv ?_
      simp only [show k + 2 - 1 = k + 1 from by omega, id]
      cases k with
      | zero => simp [wickMonomial]; ring
      | succ j => rw [wickMonomial_succ_succ j c x]; push_cast; ring

/-! ## Gaussian moments and integrability of Wick monomials -/

namespace SteinLemma

open ProbabilityTheory

/-- All polynomial weights `(1 + |x|) ^ n` are integrable under a real Gaussian law
(`memLp_id_gaussianReal` and `(1 + |x|) ^ n ≤ 2 ^ (n - 1) (1 + |x| ^ n)`). -/
theorem integrable_one_add_abs_pow_gaussianReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n) (gaussianReal μ v) := by
  have hn : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal μ v) :=
    (memLp_id_gaussianReal' (μ := μ) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  refine (((integrable_const (1 : ℝ)).add hn).const_mul ((2 : ℝ) ^ (n - 1))).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h := add_pow_le (a := (1 : ℝ)) (b := |x|) zero_le_one (abs_nonneg x) n
  simpa [Real.norm_eq_abs] using h

/-- A measurable function of polynomial growth is integrable under a real Gaussian law. -/
theorem integrable_of_abs_le_gaussianReal {μ : ℝ} {v : ℝ≥0} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (gaussianReal μ v)) {C : ℝ} {n : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + |x|) ^ n) : Integrable f (gaussianReal μ v) :=
  ((integrable_one_add_abs_pow_gaussianReal μ v n).const_mul C).mono' hf
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

end SteinLemma

/-- Integrability of `wickMonomial n c` under every centered real Gaussian law: it is a
polynomial (`wickMonomial_growth`). -/
theorem wickMonomial_integrable (n : ℕ) (c : ℝ) (v : ℝ≥0) :
    Integrable (wickMonomial n c) (ProbabilityTheory.gaussianReal 0 v) := by
  obtain ⟨C, d, hbound⟩ := wickMonomial_growth n c
  exact SteinLemma.integrable_of_abs_le_gaussianReal
    (wickMonomial_differentiable n c).continuous.aestronglyMeasurable hbound

/-- Integrability of `x * wickMonomial n c x` under every centered real Gaussian law.
Follows from the recursion: `x * W_{n}(x) = W_{n+1}(x) + n*c*W_{n-1}(x)`. -/
theorem xmul_wickMonomial_integrable (n : ℕ) (c : ℝ) (v : ℝ≥0) :
    Integrable (fun x => x * wickMonomial n c x) (ProbabilityTheory.gaussianReal 0 v) := by
  cases n with
  | zero => simp [wickMonomial]; exact wickMonomial_integrable 1 c v
  | succ k =>
    have hfun : (fun x => x * wickMonomial (k + 1) c x) =
      (fun x => wickMonomial (k + 2) c x + (↑k + 1) * c * wickMonomial k c x) := by
      ext x; have := wickMonomial_succ_succ k c x; linarith
    rw [hfun]
    exact (wickMonomial_integrable (k + 2) c v).add
      ((wickMonomial_integrable k c v).const_mul _)

/-! ## Wick monomial derivative

d/dx :x^n:_c = n · :x^{n-1}:_c.

This is the analog of He_n'(x) = n · He_{n-1}(x) for Hermite polynomials. -/

/-- Derivative of the Wick monomial: d/dx :x^n:_c = n · :x^{n-1}:_c.

From `wick_eq_hermiteR`: :x^n:_c = √c^n · He_n(x/√c).
Differentiating: d/dx = √c^n · He_n'(x/√c) · 1/√c
                      = √c^{n-1} · n · He_{n-1}(x/√c)   [He_n' = n·He_{n-1}]
                      = n · :x^{n-1}:_c. -/
theorem wickMonomial_deriv (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    ∀ x, HasDerivAt (wickMonomial n c) (n * wickMonomial (n - 1) c x) x :=
  fun x => wickMonomial_hasDerivAt_all c n x

/-! ## Stein's lemma (Gaussian integration by parts)

For X ~ N(0, c): E[X · f(X)] = c · E[f'(X)], for `f` differentiable with `f` and `f'` of
polynomial growth.

This is the fundamental integration-by-parts formula for Gaussian measures. The proof is
integration by parts on `ℝ` against the density `g`, using `g' = -(x/c) g`; boundary terms
vanish because `f g`, `x f g` and `f' g` are integrable. Restaged from the one-dimensional
`stein_lemma_gaussianReal` (SpinGlass, `Common/Mathlib/Probability/Distributions/
GaussianIntegrationByParts.lean`; carrier `GibbsMeasure.Mathlib.Probability.Distributions.
Gaussian.IntegrationByParts`). Growth of `f'` is assumed: with only `f` of polynomial growth,
`f'` need not be integrable, its Bochner integral is then `0`, and the identity can fail. -/

namespace SteinLemma

open ProbabilityTheory

/-- The Gaussian density satisfies `g' = -((x - m) / v) g`. -/
theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v) (-(x - m) / v * gaussianPDFReal m v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h : HasDerivAt (fun x => -(x - m) ^ 2 / (2 * v)) (-(2 * (x - m)) / (2 * v)) x := by
    simpa using (((hasDerivAt_id x).sub_const m).pow 2).neg.div_const (2 * (v : ℝ))
  convert (h.exp.const_mul (√(2 * π * v))⁻¹) using 1
  · rfl
  · rw [gaussianPDFReal]
    field_simp

theorem integrable_gaussianPDFReal_mul {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal m v)) :
    Integrable fun x => gaussianPDFReal m v x * g x := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF m v) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hg
  simpa [toReal_gaussianPDF] using hg

/-- Stein's identity, integrability form: if `HasDerivAt f (f' x) x` everywhere and `f`, `x f`,
`f'` are `N(0, v)`-integrable, then `∫ x f(x) dN(0, v) = v ∫ f' dN(0, v)`. -/
theorem integral_mul_gaussianReal_of_integrable {v : ℝ≥0} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hfi : Integrable f (gaussianReal 0 v))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 v))
    (hf' : Integrable f' (gaussianReal 0 v)) :
    ∫ x, x * f x ∂gaussianReal 0 v = v * ∫ x, f' x ∂gaussianReal 0 v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f)
    (v := gaussianPDFReal 0 v) (u' := f') (v' := fun x => -(x - 0) / v * gaussianPDFReal 0 v x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal 0 hv x)
    (((integrable_gaussianPDFReal_mul hv hxf).const_mul (-(v : ℝ)⁻¹)).congr
      (ae_of_all _ fun x => by simp only [Pi.mul_apply]; ring))
    (((integrable_gaussianPDFReal_mul hv hf')).congr
      (ae_of_all _ fun x => by simp only [Pi.mul_apply]; ring))
    (((integrable_gaussianPDFReal_mul hv hfi)).congr
      (ae_of_all _ fun x => by simp only [Pi.mul_apply]; ring))
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h1 : ∫ x, f x * (-(x - 0) / v * gaussianPDFReal 0 v x) =
      -(v : ℝ)⁻¹ * ∫ x, gaussianPDFReal 0 v x * (x * f x) := by
    rw [← integral_const_mul]
    congr 1 with x
    ring
  have h2 : ∫ x, f' x * gaussianPDFReal 0 v x = ∫ x, gaussianPDFReal 0 v x * f' x := by
    congr 1 with x
    ring
  rw [h1, h2] at key
  calc ∫ x, gaussianPDFReal 0 v x * (x * f x)
      = -(v : ℝ) * (-(v : ℝ)⁻¹ * ∫ x, gaussianPDFReal 0 v x * (x * f x)) := by
        field_simp
    _ = v * ∫ x, gaussianPDFReal 0 v x * f' x := by rw [key]; ring

end SteinLemma

/-- **Stein's lemma**: E[x · f(x)] = c · E[f'(x)] under the centered Gaussian measure
N(0, c) (`ProbabilityTheory.gaussianReal 0 c.toNNReal`), for `f` differentiable with `f` and
`f'` of polynomial growth. -/
theorem stein_lemma (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf_growth : ∃ C n, ∀ x, |f x| ≤ C * (1 + |x|) ^ n)
    (hf'_growth : ∃ C n, ∀ x, |deriv f x| ≤ C * (1 + |x|) ^ n) :
    ∫ x, x * f x ∂(ProbabilityTheory.gaussianReal 0 c.toNNReal) =
      c * ∫ x, deriv f x ∂(ProbabilityTheory.gaussianReal 0 c.toNNReal) := by
  obtain ⟨C, n, hb⟩ := hf_growth
  obtain ⟨C', n', hb'⟩ := hf'_growth
  have hfm : AEStronglyMeasurable f (ProbabilityTheory.gaussianReal 0 c.toNNReal) :=
    hf.continuous.aestronglyMeasurable
  have hxb : ∀ x, |x * f x| ≤ C * (1 + |x|) ^ (n + 1) := fun x => by
    rw [abs_mul, pow_succ]
    have hx : |x| ≤ 1 + |x| := by linarith [abs_nonneg x]
    calc |x| * |f x| ≤ (1 + |x|) * (C * (1 + |x|) ^ n) :=
          mul_le_mul hx (hb x) (abs_nonneg _) (by positivity)
      _ = C * ((1 + |x|) ^ n * (1 + |x|)) := by ring
  have h := SteinLemma.integral_mul_gaussianReal_of_integrable (v := c.toNNReal)
    (fun x => (hf x).hasDerivAt) (SteinLemma.integrable_of_abs_le_gaussianReal hfm hb)
    (SteinLemma.integrable_of_abs_le_gaussianReal
      (measurable_id.mul hf.continuous.measurable).aestronglyMeasurable hxb)
    (SteinLemma.integrable_of_abs_le_gaussianReal
      (measurable_deriv f).aestronglyMeasurable hb')
  rwa [Real.coe_toNNReal c hc] at h

/-! ## Wick orthogonality -/

/-- **Wick monomial has zero mean under matching Gaussian.**

For n ≥ 1: ∫ :x^n:_c dN(0,c) = 0, under `ProbabilityTheory.gaussianReal 0 c.toNNReal`.

Proof by induction on n:
- Base (n=1): :x^1: = x, so ∫ x dμ = 0 (centered Gaussian).
- Step (n → n+1): Using the Wick recursion
    :x^{n+1}: = x · :x^n: - n·c · :x^{n-1}:
  and Stein's lemma E[x·f(x)] = c·E[f'(x)] (`stein_lemma`):
    E[:x^{n+1}:] = E[x · :x^n:] - n·c · E[:x^{n-1}:]
                 = c · E[d/dx :x^n:] - n·c · E[:x^{n-1}:]
                 = c · n · E[:x^{n-1}:] - n·c · E[:x^{n-1}:]
                 = 0.
-/
theorem wickMonomial_mean_zero (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x, wickMonomial n c x ∂(ProbabilityTheory.gaussianReal 0 c.toNNReal) = 0 := by
  -- Induction on n
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      -- n = 1: :x^1: = x, and ∫ x dμ = 0
      simp only [zero_add, wickMonomial_one]
      exact ProbabilityTheory.integral_id_gaussianReal
    | succ k =>
      -- n = k+2: use recursion + Stein + induction hypothesis
      -- Step 1: Unfold the recursion inside the integral
      simp_rw [wickMonomial_succ_succ k c]
      -- Step 2: Split the integral (requires integrability)
      rw [integral_sub (xmul_wickMonomial_integrable (k + 1) c _)
        ((wickMonomial_integrable k c _).const_mul _)]
      -- Step 3: Compute deriv (W_{k+1}) = (k+1) * W_k
      have hderiv : (fun x => deriv (wickMonomial (k + 1) c) x) =
        fun x => ↑(k + 1) * wickMonomial k c x := by
        ext x; exact (wickMonomial_hasDerivAt_all c (k + 1) x).deriv
      -- Step 4: Apply Stein's lemma to ∫ x * W_{k+1}(x) dμ
      have hgrowth' : ∃ (C : ℝ) (d : ℕ), ∀ x : ℝ,
          |deriv (wickMonomial (k + 1) c) x| ≤ C * (1 + |x|) ^ d := by
        obtain ⟨C, d, hb⟩ := wickMonomial_growth k c
        refine ⟨(k + 1) * C, d, fun x => ?_⟩
        rw [congrFun hderiv x, abs_mul, mul_assoc]
        exact mul_le_mul (by norm_cast) (hb x) (abs_nonneg _) (by positivity)
      have hstein := stein_lemma c hc (wickMonomial (k + 1) c)
        (wickMonomial_differentiable (k + 1) c) (wickMonomial_growth (k + 1) c) hgrowth'
      rw [hstein]
      simp_rw [hderiv]
      -- Step 5: Pull out constants and cancel
      rw [integral_const_mul, integral_const_mul]
      push_cast; ring

/-! ## Application: O(N) Wick ordering

For the O(N) model, the Wick monomial is wickMonomial_ON N c k t
where t = |φ|² = Σ (φⁱ)² has a chi-squared distribution with N
degrees of freedom under the product GFF.

The orthogonality generalizes:
  E[wickMonomial_ON N c k (|φ|²)] = 0 for k ≥ 1

This follows from the scalar case applied to each of the N
components + the chi-squared decomposition. Alternatively,
it follows from the Laguerre polynomial orthogonality under
the gamma distribution (since chi-squared = gamma(N/2, 2c)).

This is the key fact needed for the density transfer constant:
  E_GFF[V] = E_GFF[Σ_x :P(|φ(x)|²):_c] = 0
since each Wick-ordered monomial has zero mean. -/

end
