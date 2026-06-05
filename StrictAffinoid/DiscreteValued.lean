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

open Valued NormedField IsStrictAffinoid

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
      rw [Subtype.ext_iff] at hx0
      have hxinv_mem : x.1⁻¹ ∈ 𝒪[k] := by
        change ‖x.1⁻¹‖ ≤ 1
        simp [hk x.1⁻¹ (inv_ne_zero hx0)]
      have hxunit : IsUnit x := ⟨⟨x, ⟨x.1⁻¹, hxinv_mem⟩,
        Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx hxunit
    · rintro rfl
      simp
  exact IsDiscreteValuationRing.not_a_field' hmax

omit [CompleteSpace k] in
theorem uniformizer_norm_lt_one (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) : ‖ϖ.1‖ < 1 := by
  rw [← Valued.mem_maximalIdeal_iff_norm_lt_one']
  simp [hϖ.maximalIdeal_eq]

omit [CompleteSpace k] in
theorem coeff_mem_span_uniformizer_pow_of_norm_le {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∀ {c : 𝒪[k]}, ‖c.val‖ ≤ ‖ϖ.val‖ ^ n → c ∈ (Ideal.span {ϖ}) ^ n := by
  have hϖ_pos : 0 < ‖ϖ.1‖ := norm_pos_iff.mpr (by exact_mod_cast hϖ.ne_zero)
  have hϖl : ‖ϖ.1‖ < 1 := uniformizer_norm_lt_one ϖ hϖ
  induction n with
  | zero => simp
  | succ n ih =>
      intro c hc
      have hc_lt : ‖c.1‖ < 1 :=
        lt_of_le_of_lt hc (pow_lt_one₀ (norm_nonneg _) hϖl (Nat.succ_ne_zero n))
      have hc_span : c ∈ Ideal.span {ϖ} := by
        simpa [hϖ.maximalIdeal_eq] using (Valued.mem_maximalIdeal_iff_norm_lt_one' c).2 hc_lt
      rcases Ideal.mem_span_singleton'.1 hc_span with ⟨d, hd⟩
      have hd_norm_mul : ‖(d : k)‖ * ‖ϖ.1‖ = ‖c.1‖ := by
        simpa [← norm_mul] using congrArg norm (congrArg Subtype.val hd)
      have hd_mem : d ∈ (Ideal.span {ϖ}) ^ n := ih <|
        le_of_mul_le_mul_right (by grw [hd_norm_mul, hc, pow_succ]) hϖ_pos
      simpa [pow_succ, hd] using Ideal.mul_mem_mul hd_mem (Ideal.mem_span_singleton_self ϖ)

namespace TateAlgebra

theorem mem_span_uniformizer_pow_of_norm_le {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (n : ℕ)
    {x : Integer k (TateAlgebra σ k)} (hx : ‖x.val‖ ≤ ‖ϖ.val‖ ^ n) :
    x ∈ (Ideal.span ({algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ} :
      Set (Integer k (TateAlgebra σ k)))) ^ n := by
  let xO := (integerEquiv σ k).symm x
  have hc (e : σ →₀ ℕ) : MvPowerSeries.coeff e xO.1 ∈ (Ideal.span {ϖ}) ^ n :=
    coeff_mem_span_uniformizer_pow_of_norm_le hϖ n <| (TateAlgebra.coeff_norm_le x.1 e).trans hx
  have hpow_ne : (ϖ.1 ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have hcoeff_dvd (e : σ →₀ ℕ) : ∃ d : 𝒪[k], MvPowerSeries.coeff e xO.1 = d * ϖ ^ n := by
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (by simpa [Ideal.span_singleton_pow] using hc e)
    exact ⟨d, by simp [hd]⟩
  choose d hd using hcoeff_dvd
  have hcoeff_eq (e : σ →₀ ℕ) : MvPowerSeries.coeff e x.1.1 = (d e : k) * (ϖ.1 ^ n) :=
    congrArg Subtype.val (hd e)
  let y : TateAlgebra σ k := x.1 * algebraMap k (TateAlgebra σ k) (ϖ.1 ^ n)⁻¹
  have hycoeff (e : σ →₀ ℕ) : ‖MvPowerSeries.coeff e y.1‖ ≤ 1 := by
    have hy_eq : y.1 = x.1.1 * MvPowerSeries.C (ϖ.1 ^ n)⁻¹ := rfl
    rw [hy_eq, MvPowerSeries.coeff_mul_C, hcoeff_eq e, mul_assoc, mul_inv_cancel₀ hpow_ne, mul_one]
    exact (d e).2
  rw [Ideal.span_singleton_pow]
  refine Ideal.mem_span_singleton'.2 ⟨⟨y, norm_le_of_forall_coeff_le y hycoeff⟩, Subtype.ext ?_⟩
  change y * (algebraMap k (TateAlgebra σ k)) ϖ.1 ^ n = x.1
  rw [← map_pow, mul_assoc, ← map_mul, inv_mul_cancel₀ hpow_ne, map_one, mul_one]

omit [IsDiscreteValuationRing 𝒪[k]] in
theorem norm_le_of_mem_span_uniformizer_pow (ϖ : 𝒪[k]) (n : ℕ) {x : Integer k (TateAlgebra σ k)}
    (hx : x ∈ (Ideal.span ({algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ} :
      Set (Integer k (TateAlgebra σ k)))) ^ n) : ‖x.1‖ ≤ ‖ϖ.1‖ ^ n := by
  rw [Ideal.span_singleton_pow] at hx
  rcases Ideal.mem_span_singleton'.1 hx with ⟨y, rfl⟩
  refine (norm_mul_le y.1 (((algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ) ^ n).1)).trans ?_
  change ‖y‖ * ‖algebraMap k (TateAlgebra σ k) ϖ.1 ^ n‖ ≤ ‖ϖ.1‖ ^ n
  rw [norm_pow, norm_algebraMap']
  simpa using mul_le_mul_of_nonneg_right y.norm_le (pow_nonneg (norm_nonneg _) n)

theorem topNil_eq_span_uniformizer (ϖ : 𝒪[k]) (hϖ : Irreducible ϖ) :
    topNil k (TateAlgebra σ k) = Ideal.span {algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ} := by
  apply le_antisymm
  · intro x hx
    let xO := (integerEquiv σ k).symm x
    have hc (e : σ →₀ ℕ) : MvPowerSeries.coeff e xO.1 ∈ 𝓂[k] := by
      rw [mem_topNil_iff' x] at hx
      rw [Valued.mem_maximalIdeal_iff_norm_lt_one']
      exact lt_of_le_of_lt (TateAlgebra.coeff_norm_le x.1 e) hx
    have hcoeff_dvd (e : σ →₀ ℕ) :
        ∃ d : 𝒪[k], MvPowerSeries.coeff e xO.1 = d * ϖ := by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (by simpa [hϖ.maximalIdeal_eq] using hc e)
      exact ⟨d, by simpa [mul_comm] using hd.symm⟩
    choose d hd using hcoeff_dvd
    have hcoeff_eq (e : σ →₀ ℕ) : MvPowerSeries.coeff e x.1.1 = (d e : k) * ϖ.1 :=
      congrArg Subtype.val (hd e)
    have hϖ_ne : ϖ.1 ≠ 0 := by exact_mod_cast hϖ.ne_zero
    let y0 : TateAlgebra σ k := x.1 * algebraMap k (TateAlgebra σ k) ϖ.1⁻¹
    have hycoeff (e : σ →₀ ℕ) : ‖MvPowerSeries.coeff e y0.1‖ ≤ 1 := by
      have hy0_eq : y0.1 = x.1.1 * MvPowerSeries.C (ϖ : k)⁻¹ := rfl
      rw [hy0_eq, MvPowerSeries.coeff_mul_C, hcoeff_eq e, mul_assoc, mul_inv_cancel₀ hϖ_ne, mul_one]
      exact (d e).2
    let y : Integer k (TateAlgebra σ k) := ⟨y0, norm_le_of_forall_coeff_le y0 hycoeff⟩
    refine Ideal.mem_span_singleton'.2 ⟨y, Subtype.ext ?_⟩
    change _ * algebraMap k (TateAlgebra σ k) ϖ.1 = x.1
    simp [y, y0, mul_assoc, ← map_mul, inv_mul_cancel₀ hϖ_ne]
  · rw [Ideal.span_singleton_le_iff_mem, mem_topNil_iff']
    change ‖algebraMap k (TateAlgebra σ k) ϖ.1‖ < 1
    simpa using uniformizer_norm_lt_one ϖ hϖ

theorem isAdicComplete_span_uniformizer {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) :
    IsAdicComplete (Ideal.span ({algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ}))
      (Integer k (TateAlgebra σ k)) := by
  have hpow0 : Filter.Tendsto (fun n : ℕ ↦ ‖ϖ.1‖ ^ n) Filter.atTop (𝓝 0) := by
    simpa [norm_pow] using Filter.Tendsto.norm
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (uniformizer_norm_lt_one ϖ hϖ))
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · refine ⟨fun x hx ↦ ?_⟩
    by_contra hx0
    have hnorm_pos : 0 < ‖x.1‖ := norm_pos_iff.mpr fun hx1 ↦ hx0 (Subtype.ext hx1)
    rcases Filter.eventually_atTop.1 (hpow0 (Iio_mem_nhds hnorm_pos)) with ⟨N, hN⟩
    exact not_lt_of_ge (norm_le_of_mem_span_uniformizer_pow ϖ N
      (by simpa [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hx N)) (hN N le_rfl)
  · refine ⟨fun f hf ↦ ?_⟩
    have hnorm_sub {m n : ℕ} (hmn : m ≤ n) : ‖(f m - f n).1‖ ≤ ‖ϖ.1‖ ^ m :=
      norm_le_of_mem_span_uniformizer_pow ϖ m <| by
        simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hf hmn
    have hcauchy : CauchySeq (fun n ↦ (f n).1) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      rcases Filter.eventually_atTop.1 (hpow0 (Iio_mem_nhds hε)) with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro m hm n hn
      wlog hmn : m ≤ n generalizing m n
      · simpa [dist_comm] using this n hn m hm (le_of_not_ge hmn)
      · simpa only [dist_eq_norm] using! (hnorm_sub hmn).trans_lt (hN m hm)
    obtain ⟨L0, hL0⟩ := cauchySeq_tendsto_of_complete hcauchy
    let L : Integer k (TateAlgebra σ k) := ⟨L0,
      (isClosed_le continuous_norm continuous_const).mem_of_tendsto hL0
        (Filter.Eventually.of_forall fun n ↦ (f n).2)⟩
    refine ⟨L, ?_⟩
    intro n
    have hdist_le : dist (f n).1 L0 ≤ ‖ϖ.1‖ ^ n :=
      (isClosed_le (continuous_const.dist continuous_id) continuous_const).mem_of_tendsto hL0 <|
        Filter.eventually_atTop.2 ⟨n, fun m hm ↦ by simpa only [dist_eq_norm] using! hnorm_sub hm⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact mem_span_uniformizer_pow_of_norm_le hϖ n (by simpa [L, dist_eq_norm] using hdist_le)

variable (σ k) in
instance instIntegerIsNoetherianRing : IsNoetherianRing (Integer k (TateAlgebra σ k)) := by
  have : IsNoetherianRing (Integer k (TateAlgebra σ k) ⧸ topNil k (TateAlgebra σ k)) :=
    inferInstanceAs (IsNoetherianRing (Reduction k (TateAlgebra σ k)))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  refine isNoetherianRing_of_isAdicComplete_of_fg (topNil k (TateAlgebra σ k)) ?_ ?_
  · simpa [topNil_eq_span_uniformizer ϖ hϖ] using!
      Submodule.fg_span_singleton (algebraMap 𝒪[k] (Integer k (TateAlgebra σ k)) ϖ)
  · simpa [topNil_eq_span_uniformizer ϖ hϖ] using isAdicComplete_span_uniformizer hϖ

end TateAlgebra

namespace IsStrictAffinoid

private instance (k : Type*) [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (A B : Type*) [NormedCommRing A] [NormedAlgebra k A]
    [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]
    [Algebra A B] [IsScalarTower k A B] [IsNoetherianRing (Integer k A)]
    [Module.Finite A B] : Module.Finite (Integer k A) (Integer k B) := by
  have : IsBoundedSMul A B := IsStrictAffinoid.isBoundedSMul k A B
  obtain ⟨n, y, hy⟩ := @Module.Finite.exists_fin A B _ _ _ _
  obtain ⟨π, hπpos, hπlt⟩ : ∃ π : 𝒪[k], _ ∧ ‖π.1‖ < 1 := Valued.integer.exists_norm_lt_one k
  let L₀ : (Fin n → A) →ₗ[k] B := (Fintype.linearCombination A y).restrictScalars k
  have hL_bound (v : Fin n → A) : ‖L₀ v‖ ≤ (∑ i, ‖y i‖) * ‖v‖ := by
    refine (norm_sum_le Finset.univ (fun i ↦ v i • y i)).trans ?_
    simpa [Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc] using Finset.sum_le_sum fun i _ ↦ by
      grw [norm_smul_le, mul_comm, mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)]
  let L : (Fin n → A) →L[k] B := L₀.mkContinuous (∑ i, ‖y i‖) hL_bound
  obtain ⟨C, hCpos, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le L <|
    (span_range_eq_top_iff_surjective_fintypeLinearCombination A y).mp hy
  have hm_exists (i : Fin n) : ∃ m : ℕ, ‖π.1‖ ^ m * ‖y i‖ ≤ 1 := by
    by_cases hyi : y i = 0
    · exact ⟨0, by simp [hyi]⟩
    · have hypos : 0 < ‖y i‖ := norm_pos_iff.mpr hyi
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hypos) hπlt
      refine ⟨m, le_of_lt ?_⟩
      simpa [inv_mul_cancel₀ hypos.ne'] using mul_lt_mul_of_pos_right hm hypos
  choose m hm using hm_exists
  let M0 : ℕ := Finset.univ.sup m
  have hM0 (i : Fin n) : ‖π.1‖ ^ M0 * ‖y i‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hπlt.le
      (Finset.le_sup (Finset.mem_univ i))) (norm_nonneg _)).trans (hm i)
  obtain ⟨N0, hN0lt⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCpos) hπlt
  have hN0C : ‖π.1‖ ^ N0 * C < 1 := by
    simpa [inv_mul_cancel₀ hCpos.ne'] using mul_lt_mul_of_pos_right hN0lt hCpos
  let N : ℕ := M0 + N0
  let z : Fin n → Integer k B := fun i ↦
    Integer.mk k ((π.1 ^ M0) • y i) <| by grw [norm_smul, norm_pow, hM0 i]
  let M : Submodule (Integer k A) (Integer k B) :=
    Submodule.span (Integer k A) (Set.range z)
  let rB (q : ℕ) : Integer k B :=
    Integer.mk k ((π.1 ^ q) • (1 : B)) <| by
      grw [norm_smul, norm_pow, pow_le_one₀ (norm_nonneg _) hπlt.le, norm_one, mul_one]
  have hmem (b : Integer k B) : rB N * b ∈ M := by
    obtain ⟨v, hv_eq, hv_norm⟩ := hC b.1
    have hv_norm' : ‖v‖ ≤ C := by
      grw [hv_norm, mul_le_mul_of_nonneg_left b.2 hCpos.le, mul_one]
    let coeff : Fin n → Integer k A := fun i ↦
      Integer.mk k ((π.1 ^ N0) • v i) <| by
        grw [norm_smul, norm_pow, ← hN0C, mul_le_mul_of_nonneg_left
          ((norm_le_pi_norm v i).trans hv_norm') (pow_nonneg (norm_nonneg _) N0)]
    let s : Integer k B := ∑ i, coeff i • z i
    have hs_val : s.1 = ∑ i, ((π.1 ^ N0) • v i) • ((π.1 ^ M0) • y i) := by
      change (Subalgebra.val (integerSubalgebra k B)) (∑ i, coeff i • z i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl <| fun _ _ ↦ (Algebra.smul_def _ _).symm
    have hreprB : (rB N * b).1 = ∑ i, ((π.1 ^ N0) • v i) • ((π.1 ^ M0) • y i) := by
      rw [show (rB N * b).1 = (π.1 ^ N) • b.1 by
        simp [rB, Integer.mk, Algebra.smul_def]]
      rw [show b.1 = ∑ i, v i • y i by simpa [L, L₀] using! hv_eq.symm, Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [pow_add, mul_smul]
      simp only [Algebra.smul_def, map_mul, map_pow]
      ring_nf
      simp [IsScalarTower.algebraMap_eq k A B, mul_left_comm, mul_comm]
    rw [show rB N * b = s from Subtype.ext (hreprB.trans hs_val.symm)]
    exact Submodule.sum_mem M fun i _ ↦
      Submodule.smul_mem M (coeff i) (Submodule.subset_span ⟨i, rfl⟩)
  have : Module.Finite (Integer k A) M :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range z))
  let mulMap : Integer k B →ₗ[Integer k A] M :=
  { toFun := fun b ↦ ⟨rB N * b, hmem b⟩
    map_add' := by
      intro b c
      exact Subtype.ext (by simp only [mul_add, AddMemClass.mk_add_mk])
    map_smul' := by
      intro a b
      exact Subtype.ext (by simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]) }
  have hmulMap_inj : Function.Injective mulMap := by
    intro b c hbc
    have hbcI : rB N * b = rB N * c := congrArg Subtype.val hbc
    have hbcB := congrArg (fun x : Integer k B ↦ x.1) hbcI
    have hscalar : (π.1 ^ N) • b.1 = (π.1 ^ N) • c.1 := by
      simpa [rB, Integer.mk, Algebra.smul_def] using hbcB
    have hsub : (π.1 ^ N) • (b.1 - c.1) = 0 := by rw [smul_sub, hscalar, sub_self]
    exact Subtype.ext <| sub_eq_zero.mp <|
      (smul_eq_zero.mp hsub).resolve_left (pow_ne_zero _ (norm_pos_iff.mp hπpos))
  exact Module.Finite.of_injective mulMap hmulMap_inj

variable (k) (A B : Type*) [NormedCommRing A] [NormedAlgebra k A]
  [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]

/-- Let `A` be a strict affinoid algebra over a discretely valued field, then `A°` is a Noetherian
ring. -/
instance : IsNoetherianRing (Integer k A) := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, -, hφsurj⟩
  algebraize [φ.toRingHom]
  have : Module.Finite (TateAlgebra σ k) A := AlgHom.Finite.of_surjective φ hφsurj
  exact IsNoetherianRing.of_finite (Integer k (TateAlgebra σ k)) (Integer k A)

/-- Let `A` be a strict affinoid algebra over a discretely valued field, and `B` be a finite
`A`-algebra, then `B°` is a finite `A°`-algebra. -/
instance [Algebra A B] [IsScalarTower k A B] [Module.Finite A B] :
    Module.Finite (Integer k A) (Integer k B) := inferInstance

variable {k A B} in
/-- If `f : A →ₐ[k] B` is a finite morphism between strict affinoid algebras over a
discrete valued field, then the induced morphism `f° : A° → B°` is finite. -/
theorem integerMap_finite_of_finite_of_discreteValued (f : A →ₐ[k] B) (hf : f.Finite) :
    (integerMap f).toRingHom.Finite := by
  algebraize [f.toRingHom]
  have : Module.Finite A B := RingHom.finite_algebraMap.mp hf
  exact show Module.Finite (Integer k A) (Integer k B) from inferInstance

theorem exists_surjective_integerMap_of_discreteValued :
    ∃ (σ : Type) (_ : Fintype σ) (φ : TateAlgebra σ k →ₐ[k] A) (_ : Function.Surjective φ),
    Function.Surjective (integerMap φ) := by
  rcases IsStrictAffinoid.exists_fin_contractive_presentation k A with ⟨n, φ₀, hφ₀contr, hφ₀surj⟩
  have : (integerMap φ₀).toRingHom.Finite :=
    integerMap_finite_of_finite_of_discreteValued φ₀ (AlgHom.Finite.of_surjective φ₀ hφ₀surj)
  algebraize [(integerMap φ₀).toRingHom]
  obtain ⟨m, y, hy⟩ :=
    @Module.Finite.exists_fin (Integer k (TateAlgebra (Fin n) k)) (Integer k A) _ _ _ _
  let ι := (Fin n) ⊕ (Fin m)
  let a : ι → Integer k A := fun
    | Sum.inl i => ⟨φ₀ (TateAlgebra.X i), (hφ₀contr _).trans (TateAlgebra.norm_X_le_one i)⟩
    | Sum.inr j => y j
  rcases exists_tateAlgHom_of_powerbounded a with ⟨φ, hφX⟩
  let eLeft : Fin n ↪ ι := ⟨Sum.inl, fun i j hij ↦ Sum.inl.inj hij⟩
  let ρ : TateAlgebra (Fin n) k →ₐ[k] TateAlgebra ι k := TateAlgebra.rename k eLeft
  have hφρ : φ.comp ρ = φ₀ := TateAlgebra.hom_ext fun i ↦ by simp [ρ, eLeft, a, hφX (Sum.inl i)]
  refine ⟨ι, inferInstance, φ, ?_, fun b ↦ ?_⟩
  · intro b
    rcases hφ₀surj b with ⟨x, hx⟩
    exact ⟨ρ x, by simpa [hx] using congrArg (fun ψ ↦ ψ x) hφρ⟩
  · rw [span_range_eq_top_iff_surjective_fintypeLinearCombination] at hy
    rcases hy b with ⟨c, hc⟩
    let XInt : Fin m → Integer k (TateAlgebra ι k) := fun j ↦
      ⟨TateAlgebra.X (Sum.inr j), TateAlgebra.norm_X_le_one (Sum.inr j)⟩
    let z : Integer k (TateAlgebra ι k) := ∑ j, (integerMap ρ (c j)) * XInt j
    refine ⟨z, ?_⟩
    have hcoeff_map (j : Fin m) : (integerMap φ) (integerMap ρ (c j)) = (integerMap φ₀) (c j) := by
      apply Subtype.ext
      change φ (ρ (c j).1) = φ₀ (c j).1
      simpa using congrArg (fun ψ : TateAlgebra (Fin n) k →ₐ[k] A ↦ ψ (c j).1) hφρ
    have hX_map (j : Fin m) : (integerMap φ) (XInt j) = y j := by
      apply Subtype.ext
      change φ (TateAlgebra.X (Sum.inr j)) = (y j).1
      simpa [a] using hφX (Sum.inr j)
    calc _ = ∑ j, (integerMap φ) ((integerMap ρ (c j)) * XInt j) := by simp [z]
      _ = ∑ j, (algebraMap (Integer k (TateAlgebra (Fin n) k)) (Integer k A) (c j)) * y j := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [map_mul, hcoeff_map j, hX_map j]
        rfl
      _ = b := by simpa [Fintype.linearCombination, Algebra.smul_def] using hc

end IsStrictAffinoid
