/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import StrictAffinoid.Reduction

public section

open Valued NormedField Filter Module IsStrictAffinoid

open scoped Topology

variable {σ : Type*} [Finite σ] {k : Type*} [NormedField k] [IsUltrametricDist k] [CompleteSpace k]
  [IsDiscreteValuationRing 𝒪[k]]

variable (k) in
instance : NontriviallyNormedField k := by
  refine NontriviallyNormedField.ofNormNeOne ?_
  by_contra! hk
  have hmax : IsLocalRing.maximalIdeal 𝒪[k] = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [Ideal.mem_bot]
      by_contra hx0
      have hx0' : (x : k) ≠ 0 := by
        intro hx0'
        exact hx0 (Subtype.ext hx0')
      have hxinv_mem : ((x : k)⁻¹) ∈ 𝒪[k] := by
        change ‖((x : k)⁻¹)‖ ≤ 1
        have hnorm : ‖((x : k)⁻¹)‖ = 1 := hk ((x : k)⁻¹) (inv_ne_zero hx0')
        simp [hnorm]
      have hxunit : IsUnit x := by
        refine ⟨{ val := x, inv := ⟨(x : k)⁻¹, hxinv_mem⟩, val_inv := ?_, inv_val := ?_ }, rfl⟩
        · ext
          simp [hx0']
        · ext
          simp [hx0']
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx hxunit
    · intro hx
      rw [Ideal.mem_bot] at hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      simp [hx]
  exact IsDiscreteValuationRing.not_a_field' hmax

omit [CompleteSpace k] in
theorem uniformizer_norm_lt_one (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) : ‖(ϖ : k)‖ < 1 := by
  rw [← Valued.mem_maximalIdeal_iff_norm_lt_one']
  simpa [hϖ.maximalIdeal_eq] using Ideal.subset_span (by simp)

omit [CompleteSpace k] in
theorem coeff_mem_span_uniformizer_pow_of_norm_le (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) (n : ℕ) :
    ∀ c : 𝒪[k], ‖(c : k)‖ ≤ ‖(ϖ : k)‖ ^ n → c ∈ (Ideal.span {ϖ}) ^ n := by
  have hϖ_ne : (ϖ : k) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  have hϖ_pos : 0 < ‖(ϖ : k)‖ := norm_pos_iff.mpr hϖ_ne
  have hϖ_lt : ‖(ϖ : k)‖ < 1 := uniformizer_norm_lt_one ϖ hϖ
  induction n with
  | zero =>
      intro c hc
      simp
  | succ n ih =>
      intro c hc
      have hc_lt : ‖(c : k)‖ < 1 :=
        lt_of_le_of_lt hc (pow_lt_one₀ (norm_nonneg _) hϖ_lt (Nat.succ_ne_zero n))
      have hc_max : c ∈ 𝓂[k] := (Valued.mem_maximalIdeal_iff_norm_lt_one' c).2 hc_lt
      have hc_span : c ∈ Ideal.span {ϖ} := by simpa [hϖ.maximalIdeal_eq] using hc_max
      rcases Ideal.mem_span_singleton'.1 hc_span with ⟨d, hd⟩
      have hd_norm_mul : ‖(d : k)‖ * ‖(ϖ : k)‖ = ‖(c : k)‖ := by
        rw [← norm_mul]
        exact congrArg norm (congrArg Subtype.val hd)
      have hmul_le : ‖(d : k)‖ * ‖(ϖ : k)‖ ≤ ‖(ϖ : k)‖ ^ n * ‖(ϖ : k)‖ := by
        calc _ = ‖(c : k)‖ := hd_norm_mul
          _ ≤ ‖(ϖ : k)‖ ^ (n + 1) := hc
          _ = ‖(ϖ : k)‖ ^ n * ‖(ϖ : k)‖ := by rw [pow_succ]
      have hd_le : ‖(d : k)‖ ≤ ‖(ϖ : k)‖ ^ n := le_of_mul_le_mul_right hmul_le hϖ_pos
      have hd_mem : d ∈ (Ideal.span {ϖ}) ^ n := ih d hd_le
      have hϖ_mem : ϖ ∈ Ideal.span {ϖ} := Ideal.subset_span (by simp)
      have hmul : d * ϖ ∈ (Ideal.span {ϖ}) ^ n * Ideal.span {ϖ} := Ideal.mul_mem_mul hd_mem hϖ_mem
      simpa [pow_succ, hd] using hmul

namespace TateAlgebra

theorem mem_span_uniformizer_pow_of_norm_le (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) (n : ℕ)
    {x : Integer k (TateAlgebra σ k)} (hx : ‖x.1‖ ≤ ‖(ϖ : k)‖ ^ n) :
    x ∈ (Ideal.span ({algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ} :
      Set (Integer k (TateAlgebra σ k)))) ^ n := by
  let xO := (integerEquiv σ k).symm x
  have hcoeff_mem (e : σ →₀ ℕ) : MvPowerSeries.coeff e xO.1 ∈ (Ideal.span {ϖ}) ^ n := by
    exact coeff_mem_span_uniformizer_pow_of_norm_le (k := k) (ϖ := ϖ) hϖ n
      (MvPowerSeries.coeff e xO.1) <| (TateAlgebra.coeff_norm_le x.1 e).trans hx
  have hpow_mem (e : σ →₀ ℕ) : MvPowerSeries.coeff e xO.1 ∈ Ideal.span {ϖ ^ n} := by
    simpa [Ideal.span_singleton_pow] using hcoeff_mem e
  have hpow_ne : ((ϖ : k) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have hcoeff_dvd (e : σ →₀ ℕ) : ∃ d : 𝒪[k], MvPowerSeries.coeff e xO.1 = d * ϖ ^ n := by
    rcases Ideal.mem_span_singleton'.1 (hpow_mem e) with ⟨d, hd⟩
    exact ⟨d, by simpa [mul_comm] using hd.symm⟩
  choose d hd using hcoeff_dvd
  have hcoeff_eq (e : σ →₀ ℕ) : MvPowerSeries.coeff e x.1.1 = (d e : k) * ((ϖ : k) ^ n) :=
    congrArg Subtype.val (hd e)
  let y : TateAlgebra σ k := x.1 * algebraMap k (TateAlgebra σ k) (((ϖ : k) ^ n)⁻¹)
  have hycoeff (e : σ →₀ ℕ) : ‖MvPowerSeries.coeff e y.1‖ ≤ 1 := by
    have hy_eq : y.1 = x.1.1 * MvPowerSeries.C (((ϖ : k) ^ n)⁻¹) := rfl
    rw [hy_eq, MvPowerSeries.coeff_mul_C, hcoeff_eq e, mul_assoc, mul_inv_cancel₀ hpow_ne, mul_one]
    exact (d e).2
  have hy : ‖y‖ ≤ 1 := norm_le_of_forall_coeff_le y (by positivity) hycoeff
  rw [Ideal.span_singleton_pow]
  refine Ideal.mem_span_singleton'.2 ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change y * (algebraMap k (TateAlgebra σ k)) ϖ.1 ^ n = x.1
  rw [← map_pow]
  calc
    _ = x.1 * (algebraMap k (TateAlgebra σ k) (((ϖ : k) ^ n)⁻¹) *
        algebraMap k (TateAlgebra σ k) ((ϖ : k) ^ n)) := by ring
    _ = x.1 := by rw [← map_mul, inv_mul_cancel₀ hpow_ne, map_one, mul_one]

omit [IsDiscreteValuationRing 𝒪[k]] in
theorem norm_le_of_mem_span_uniformizer_pow
    (ϖ : 𝒪[k]) (n : ℕ) {x : Integer k (TateAlgebra σ k)}
    (hx : x ∈ (Ideal.span ({algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ} :
      Set (Integer k (TateAlgebra σ k)))) ^ n) : ‖x.1‖ ≤ ‖(ϖ : k)‖ ^ n := by
  rw [Ideal.span_singleton_pow] at hx
  rcases Ideal.mem_span_singleton'.1 hx with ⟨y, rfl⟩
  calc
    _ ≤ ‖y‖ * ‖((algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ) ^ n)‖ := norm_mul_le _ _
    _ ≤ 1 * ‖((algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ) ^ n)‖ := by
          gcongr
          exact integer_norm_le y
    _ = ‖((algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ) ^ n)‖ := by ring
    _ = ‖(ϖ : k)‖ ^ n := by
      change ‖algebraMap k (TateAlgebra σ k) (ϖ : k) ^ n‖ = _
      rw [norm_pow, norm_algebraMap, norm_one, mul_one]

theorem topNil_eq_span_uniformizer (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) :
    topNil k (TateAlgebra σ k) = Ideal.span {algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ} := by
  let π : Integer k (TateAlgebra σ k) := algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ
  apply le_antisymm
  · intro x hx
    let xO := (integerEquiv σ k).symm x
    have hx_lt : ‖x.1‖ < 1 :=
      (mem_topologicalNilradical_iff_norm_lt_one' (k := k) (A := TateAlgebra σ k) x).1 hx
    have hcoeff_mem : ∀ e : σ →₀ ℕ, MvPowerSeries.coeff e xO.1 ∈ 𝓂[k] := by
      intro e
      rw [Valued.mem_maximalIdeal_iff_norm_lt_one']
      change ‖MvPowerSeries.coeff e x.1.1‖ < 1
      exact lt_of_le_of_lt (TateAlgebra.coeff_norm_le x.1 e) hx_lt
    have hcoeff_dvd : ∀ e : σ →₀ ℕ, ∃ d : 𝒪[k], MvPowerSeries.coeff e xO.1 = d * ϖ := by
      intro e
      have he : MvPowerSeries.coeff e xO.1 ∈ 𝓂[k] := hcoeff_mem e
      have he' : MvPowerSeries.coeff e xO.1 ∈ Ideal.span {ϖ} := by
        simpa [hϖ.maximalIdeal_eq] using he
      rcases Ideal.mem_span_singleton'.1 he' with ⟨d, hd⟩
      exact ⟨d, by simpa [mul_comm] using hd.symm⟩
    choose d hd using hcoeff_dvd
    have hcoeff_eq : ∀ e : σ →₀ ℕ, MvPowerSeries.coeff e x.1.1 = (d e : k) * (ϖ : k) := by
      intro e
      exact congrArg Subtype.val (hd e)
    have hϖ_ne : (ϖ : k) ≠ 0 := by exact_mod_cast hϖ.ne_zero
    let y0 : TateAlgebra σ k := x.1 * algebraMap k (TateAlgebra σ k) ((ϖ : k)⁻¹)
    have hycoeff : ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e y0.1‖ ≤ 1 := by
      intro e
      have hy0_eq : y0.1 = x.1.1 * MvPowerSeries.C ((ϖ : k)⁻¹) := by rfl
      rw [hy0_eq, MvPowerSeries.coeff_mul_C, hcoeff_eq e, mul_assoc, mul_inv_cancel₀ hϖ_ne, mul_one]
      exact (d e).2
    have hy0 : ‖y0‖ ≤ 1 := norm_le_of_forall_coeff_le y0 (by positivity) hycoeff
    let y : Integer k (TateAlgebra σ k) := ⟨y0, hy0⟩
    refine Ideal.mem_span_singleton'.2 ?_
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change _ * algebraMap k (TateAlgebra σ k) (ϖ : k) = x.1
    calc
      _ = x.1 * (algebraMap k (TateAlgebra σ k) ((ϖ : k)⁻¹) *
          algebraMap k (TateAlgebra σ k) (ϖ : k)) := by ring
      _ = x.1 := by rw [← map_mul, inv_mul_cancel₀ hϖ_ne, map_one, mul_one]
  · rw [Ideal.span_singleton_le_iff_mem, mem_topologicalNilradical_iff_norm_lt_one']
    change ‖(algebraMap k (TateAlgebra σ k) (ϖ : k) : TateAlgebra σ k)‖ < 1
    simpa using uniformizer_norm_lt_one ϖ hϖ

theorem isAdicComplete_span_uniformizer (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) :
    IsAdicComplete (Ideal.span ({algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ}))
      (Integer k (TateAlgebra σ k)) := by
  let π : Integer k (TateAlgebra σ k) := algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ
  let I : Ideal (Integer k (TateAlgebra σ k)) := Ideal.span {π}
  have hϖ_lt : ‖(ϖ : k)‖ < 1 := uniformizer_norm_lt_one ϖ hϖ
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · refine ⟨fun x hx ↦ ?_⟩
    by_cases hx0 : x = 0
    · exact hx0
    · have hx0' : x.1 ≠ 0 := by
        intro hx1
        apply hx0
        exact Subtype.ext hx1
      have hnorm_pos : 0 < ‖x.1‖ := norm_pos_iff.mpr hx0'
      have hpow0 : Tendsto (fun n : ℕ ↦ ‖(ϖ : k)‖ ^ n) atTop (𝓝 0) := by
        simpa [norm_pow] using Tendsto.norm (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ_lt)
      rcases Filter.eventually_atTop.1 (hpow0 (Iio_mem_nhds hnorm_pos)) with ⟨N, hN⟩
      have hxN : x ∈ I ^ N := by
        have hxN' := hx N
        rwa [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] at hxN'
      have hnorm_le : ‖x.1‖ ≤ ‖(ϖ : k)‖ ^ N :=
        norm_le_of_mem_span_uniformizer_pow (σ := σ) (k := k) ϖ N hxN
      exact (not_lt_of_ge hnorm_le) (hN N le_rfl) |>.elim
  · refine ⟨fun f hf ↦ ?_⟩
    have hnorm_sub : ∀ {m n : ℕ}, m ≤ n → ‖(f m - f n).1‖ ≤ ‖(ϖ : k)‖ ^ m := by
      intro m n hmn
      have hfmn := hf hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hfmn
      exact norm_le_of_mem_span_uniformizer_pow (σ := σ) (k := k) ϖ m hfmn
    have hcauchy : CauchySeq (fun n ↦ (f n).1) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hpow0 : Tendsto (fun n : ℕ ↦ ‖(ϖ : k)‖ ^ n) atTop (𝓝 0) := by
        simpa [norm_pow] using Tendsto.norm (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ_lt)
      rcases Filter.eventually_atTop.1 (hpow0 (Iio_mem_nhds hε)) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro m hm n hn
      wlog hmn : m ≤ n generalizing m n
      · have hnm : n ≤ m := le_of_not_ge hmn
        rw [dist_comm]
        exact this n hn m hm hnm
      calc
        dist (f m).1 (f n).1 = ‖(f m).1 - (f n).1‖ := by simp [dist_eq_norm]
        _ = ‖(f m - f n).1‖ := by rfl
        _ ≤ ‖(ϖ : k)‖ ^ m := hnorm_sub hmn
        _ < ε := hN m hm
    obtain ⟨L0, hL0⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hL0_mem : ‖L0‖ ≤ 1 := by
      let S : Set (TateAlgebra σ k) := {z | ‖z‖ ≤ 1}
      have hS_closed : IsClosed S := by
        dsimp [S]
        exact isClosed_le continuous_norm continuous_const
      have hS_mem : ∀ n, (f n).1 ∈ S := by
        intro n
        exact (f n).2
      exact hS_closed.mem_of_tendsto hL0 (Filter.Eventually.of_forall hS_mem)
    let L : Integer k (TateAlgebra σ k) := ⟨L0, hL0_mem⟩
    refine ⟨L, ?_⟩
    intro n
    have hdist_le : dist (f n).1 L0 ≤ ‖(ϖ : k)‖ ^ n := by
      let S : Set (TateAlgebra σ k) := {z | dist (f n).1 z ≤ ‖(ϖ : k)‖ ^ n}
      have hS_closed : IsClosed S :=
        isClosed_le (continuous_const.dist continuous_id) continuous_const
      have hS_mem : ∀ᶠ m in atTop, (f m).1 ∈ S := by
        refine Filter.eventually_atTop.2 ?_
        exact ⟨n, fun m hm ↦ by
          calc _ = ‖(f n).1 - (f m).1‖ := by simp [dist_eq_norm]
            _ = ‖(f n - f m).1‖ := by rfl
            _ ≤ ‖(ϖ : k)‖ ^ n := hnorm_sub hm⟩
      exact hS_closed.mem_of_tendsto hL0 hS_mem
    have hsub_mem : f n - L ∈ I ^ n := by
      exact mem_span_uniformizer_pow_of_norm_le (σ := σ) (k := k) ϖ hϖ n <| by
        simpa [L, dist_eq_norm] using hdist_le
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

variable (σ k) in
instance instIntegerIsNoetherianRing : IsNoetherianRing (Integer k (TateAlgebra σ k)) := by
  have : IsNoetherianRing (Integer k (TateAlgebra σ k) ⧸ topNil k (TateAlgebra σ k)) :=
    inferInstanceAs (IsNoetherianRing (Reduction k (TateAlgebra σ k)))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  refine isNoetherianRing_of_isAdicComplete_of_fg (topNil k (TateAlgebra σ k)) ?_ ?_
  · simpa [topNil_eq_span_uniformizer ϖ hϖ] using
      Submodule.fg_span_singleton (algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ)
  · simpa [topNil_eq_span_uniformizer ϖ hϖ] using isAdicComplete_span_uniformizer ϖ hϖ

end TateAlgebra

namespace IsStrictAffinoid

private instance {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    {A B : Type*} [NormedCommRing A] [NormedAlgebra k A]
    [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]
    [Algebra A B] [IsScalarTower k A B] [IsNoetherianRing (Integer k A)]
    [Module.Finite A B] : Module.Finite (Integer k A) (Integer k B) := by
  have : IsBoundedSMul A B := IsStrictAffinoid.isBoundedSMul k A B
  obtain ⟨n, y, hy⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨π, hπpos, hπlt⟩ := Valued.integer.exists_norm_lt_one k
  have hπposK : 0 < ‖(π : k)‖ := by simpa using hπpos
  have hπltK : ‖(π : k)‖ < 1 := by simpa using hπlt
  let L₀ : (Fin n → A) →ₗ[k] B := (Fintype.linearCombination A y).restrictScalars k
  have hL_bound (v : Fin n → A) : ‖L₀ v‖ ≤ (∑ i, ‖y i‖) * ‖v‖ := by
    calc _ ≤ ∑ i, ‖v i • y i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖v‖ * ‖y i‖ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        calc _ ≤ ‖v i‖ * ‖y i‖ := norm_smul_le _ _
          _ ≤ ‖v‖ * ‖y i‖ := by
            gcongr
            exact norm_le_pi_norm v i
      _ = ‖v‖ * (∑ i, ‖y i‖) := by rw [Finset.mul_sum]
      _ = (∑ i, ‖y i‖) * ‖v‖ := by ring
  let L : (Fin n → A) →L[k] B := L₀.mkContinuous (∑ i, ‖y i‖) hL_bound
  have hsurjA : Function.Surjective (Fintype.linearCombination A y) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := A) (v := y)).mp hy
  obtain ⟨C, hCpos, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le L hsurjA
  have hm_exists (i : Fin n) : ∃ m : ℕ, ‖(π : k)‖ ^ m * ‖y i‖ ≤ 1 := by
    by_cases hyi : y i = 0
    · exact ⟨0, by simp [hyi]⟩
    · have hypos : 0 < ‖y i‖ := norm_pos_iff.mpr hyi
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hypos) hπltK
      refine ⟨m, le_of_lt ?_⟩
      have hmul := mul_lt_mul_of_pos_right hm hypos
      simpa [inv_mul_cancel₀ hypos.ne'] using hmul
  choose m hm using hm_exists
  let M0 : ℕ := Finset.univ.sup m
  have hM0 (i : Fin n) : ‖(π : k)‖ ^ M0 * ‖y i‖ ≤ 1 :=
    have hpow : ‖(π : k)‖ ^ M0 ≤ ‖(π : k)‖ ^ m i :=
      pow_le_pow_of_le_one (norm_nonneg _) hπltK.le (Finset.le_sup (Finset.mem_univ i))
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hm i)
  obtain ⟨N0, hN0lt⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCpos) hπltK
  have hN0C : ‖(π : k)‖ ^ N0 * C ≤ 1 := by
    have hmul := mul_lt_mul_of_pos_right hN0lt hCpos
    exact le_of_lt (by simpa [inv_mul_cancel₀ hCpos.ne'] using hmul)
  let N : ℕ := M0 + N0
  let z : Fin n → Integer k B := fun i ↦
    Integer.mk k (((π : k) ^ M0) • y i) <| by
      calc _ = ‖(π : k)‖ ^ M0 * ‖y i‖ := by rw [norm_smul, norm_pow]
        _ ≤ 1 := hM0 i
  let M : Submodule (Integer k A) (Integer k B) :=
    Submodule.span (Integer k A) (Set.range z)
  let rB (q : ℕ) : Integer k B :=
    Integer.mk k (((π : k) ^ q) • (1 : B)) <| by
      calc _ = ‖(π : k)‖ ^ q * ‖(1 : B)‖ := by rw [norm_smul, norm_pow]
        _ = ‖(π : k)‖ ^ q := by simp
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hπltK.le
  have hmem (b : Integer k B) : rB N * b ∈ M := by
    obtain ⟨v, hv_eq, hv_norm⟩ := hC b.1
    have hv_norm' : ‖v‖ ≤ C := by
      calc ‖v‖ ≤ C * ‖b.1‖ := hv_norm
        _ ≤ C * 1 := by
          gcongr
          exact b.2
        _ = C := by ring
    let coeff : Fin n → Integer k A := fun i ↦
      Integer.mk k (((π : k) ^ N0) • v i) <| by
        calc
          ‖((π : k) ^ N0 • v i)‖ = ‖(π : k)‖ ^ N0 * ‖v i‖ := by
            rw [norm_smul, norm_pow]
          _ ≤ ‖(π : k)‖ ^ N0 * C := by
            gcongr
            exact (norm_le_pi_norm v i).trans hv_norm'
          _ ≤ 1 := hN0C
    have hb_repr : b.1 = ∑ i, v i • y i := by simpa [L, L₀] using hv_eq.symm
    let s : Integer k B := ∑ i, coeff i • z i
    have hs_val : s.1 = ∑ i, (((π : k) ^ N0) • v i) • (((π : k) ^ M0) • y i) := by
      change (Subalgebra.val (integerSubalgebra k B)) (∑ i, coeff i • z i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl <| fun _ _ ↦ (Algebra.smul_def _ _).symm
    have hreprB : (rB N * b).1 = ∑ i, (((π : k) ^ N0) • v i) • (((π : k) ^ M0) • y i) := by
      calc
        (rB N * b).1 = (rB N).1 * b.1 := rfl
        _ = ((π : k) ^ N) • b.1 := by
          simp [rB, Integer.mk, Algebra.smul_def]
        _ = ((π : k) ^ N) • (∑ i, v i • y i) := by rw [hb_repr]
        _ = ∑ i, ((π : k) ^ N) • (v i • y i) := by rw [Finset.smul_sum]
        _ = ∑ i, (((π : k) ^ N0) • v i) • (((π : k) ^ M0) • y i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hsplit : ((π : k) ^ N) • (v i • y i) =
              (((π : k) ^ N0) • v i) • (((π : k) ^ M0) • y i) := by
            dsimp [N]
            rw [pow_add, mul_smul]
            simp only [Algebra.smul_def, map_mul, map_pow]
            ring_nf
            simp [IsScalarTower.algebraMap_eq k A B, mul_left_comm, mul_comm]
          exact hsplit
    have hrepr : rB N * b = s := Subtype.ext (hreprB.trans hs_val.symm)
    rw [hrepr]
    exact Submodule.sum_mem M fun i hi ↦
      Submodule.smul_mem M (coeff i) (Submodule.subset_span ⟨i, rfl⟩)
  have : Module.Finite (Integer k A) M :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range z))
  let mulMap : Integer k B →ₗ[Integer k A] M :=
  { toFun := fun b ↦ ⟨rB N * b, hmem b⟩
    map_add' := by
      intro b c
      apply Subtype.ext
      simp only [mul_add, AddMemClass.mk_add_mk]
    map_smul' := by
      intro a b
      apply Subtype.ext
      simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] }
  have hmulMap_inj : Function.Injective mulMap := by
    intro b c hbc
    have hbcI : rB N * b = rB N * c := congrArg Subtype.val hbc
    have hbcB := congrArg (fun x : Integer k B ↦ x.1) hbcI
    have hscalar : ((π : k) ^ N) • b.1 = ((π : k) ^ N) • c.1 := by
      change (rB N).1 * b.1 = (rB N).1 * c.1 at hbcB
      simpa [rB, Integer.mk, Algebra.smul_def] using hbcB
    have hsub : ((π : k) ^ N) • (b.1 - c.1) = 0 := by rw [smul_sub, hscalar, sub_self]
    have hπN_ne : ((π : k) ^ N) ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp hπposK)
    exact Subtype.ext (sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left hπN_ne))
  exact Module.Finite.of_injective mulMap hmulMap_inj

variable {A B : Type*} [NormedCommRing A] [NormedAlgebra k A]
  [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]

instance instIntegerIsNoetherianRing : IsNoetherianRing (Integer k A) := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, -, hφsurj⟩
  algebraize [φ.toRingHom]
  have : Module.Finite (TateAlgebra σ k) A := AlgHom.Finite.of_surjective φ hφsurj
  exact IsNoetherianRing.of_finite (Integer k (TateAlgebra σ k)) (Integer k A)

instance [Algebra A B] [IsScalarTower k A B] [Module.Finite A B] :
    Module.Finite (Integer k A) (Integer k B) := inferInstance

theorem integerMap_finite_of_finite (f : A →ₐ[k] B)
    (hf : f.toRingHom.Finite) : (integerMap f).toRingHom.Finite := by
  algebraize [f.toRingHom]
  exact show Module.Finite (Integer k A) (Integer k B) from inferInstance

end IsStrictAffinoid
