/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import StrictAffinoid.Weierstrass

public section

open Valued NormedField Filter TateAlgebra

open scoped Topology

variable {σ : Type*} (s : σ) {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {A B : Type*} [NormedCommRing A] [NormedAlgebra k A]
  [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]

omit [IsUltrametricDist k] [CompleteSpace k] in
lemma base_norm_eq_one_of_trivially_valued
    (htv : ¬ ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1) {x : k} (hx : x ≠ 0) : ‖x‖ = 1 :=
  of_not_not fun h ↦ htv ⟨x, hx, h⟩

omit [CompleteSpace k] in
lemma TateAlgebra.norm_eq_one_of_trivially_valued
    (htv : ¬ ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1) {F : TateAlgebra σ k} (hF : F ≠ 0) : ‖F‖ = 1 := by
  have hle : ‖F‖ ≤ 1 := by
    refine ciSup_le fun e ↦ ?_
    by_cases h : MvPowerSeries.coeff e F.1 = 0
    · simp [h]
    · exact le_of_eq (base_norm_eq_one_of_trivially_valued htv h)
  obtain ⟨e, he⟩ : ∃ e : σ →₀ ℕ, MvPowerSeries.coeff e F.1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hF
    ext e
    exact h e
  exact le_antisymm hle <| by
    grw [← TateAlgebra.coeff_norm_le F e, base_norm_eq_one_of_trivially_valued htv he]

lemma IsStrictAffinoid.norm_eq_one_of_trivially_valued
    (htv : ¬ ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1) {a : A} (ha : a ≠ 0) : ‖a‖ = 1 := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, hφ, hsurj⟩
  rcases hφ with ⟨C, hCpos, hφ⟩
  obtain ⟨x, rfl⟩ := hsurj a
  let Q (y : A) : Set ℝ := {r : ℝ | ∃ z : TateAlgebra σ k, φ z = y ∧ ‖z‖ = r}
  have hpn {y : A} (hy : y ≠ 0) {z : TateAlgebra σ k} (hz : φ z = y) : z ≠ 0 :=
    fun hz0 ↦ hy (by simp [hz0, ← hz])
  have hQ_eq_singleton {y : A} (hy : y ≠ 0) : Q y = {1} := by
    ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp [TateAlgebra.norm_eq_one_of_trivially_valued htv (hpn hy hz)]
    · rintro rfl
      obtain ⟨z, hz⟩ := hsurj y
      exact ⟨z, hz, TateAlgebra.norm_eq_one_of_trivially_valued htv (hpn hy hz)⟩
  have hxnpow_ne_zero (n : ℕ) : (φ x) ^ n ≠ 0 := by
    rw [← norm_pos_iff]
    simpa [IsStrictAffinoid.withSpectralNorm k] using pow_pos (norm_pos_iff.mpr ha) n
  have hnot_gt : ¬ 1 < ‖φ x‖ := by
    intro hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt
    obtain ⟨z, hz⟩ := hsurj ((φ x) ^ n)
    have : ‖φ x‖ ^ n ≤ C := by
      grw [← IsStrictAffinoid.withSpectralNorm k (φ x) n, ← hz, (hφ z).2,
        TateAlgebra.norm_eq_one_of_trivially_valued htv (hpn (hxnpow_ne_zero n) hz), mul_one]
    exact (not_lt_of_ge this) hn
  have hnot_lt : ¬ ‖φ x‖ < 1 := by
    intro hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < C⁻¹ by positivity) hlt
    obtain ⟨z, hz⟩ := hsurj ((φ x) ^ n)
    have hcn : 1 ≤ C * ‖φ x‖ ^ n := by
      simpa [hQ_eq_singleton (hxnpow_ne_zero n), Q, hz, withSpectralNorm k (φ x) n] using (hφ z).1
    have hlt1 : C * ‖φ x‖ ^ n < 1 := by
      simpa [mul_inv_cancel₀ hCpos.ne'] using mul_lt_mul_of_pos_left hn hCpos
    exact (not_lt_of_ge hcn) hlt1
  exact le_antisymm (le_of_not_gt hnot_gt) (le_of_not_gt hnot_lt)

section closed_ideals

namespace Ideal

lemma closure_denseSubtype {k A : Type*} [NontriviallyNormedField k] [SeminormedRing A]
    [NormedAlgebra k A] (I : Ideal A) : Dense {x : I.closure.restrictScalars k | x.1 ∈ I} := by
  rw [dense_iff_closure_eq]
  ext x
  constructor
  · simp
  · intro
    rw [closure_subtype]
    change x.1 ∈ closure (Subtype.val '' {x : I.closure.restrictScalars k | x.1 ∈ I})
    have himage : (Subtype.val '' {x : I.closure.restrictScalars k | x.1 ∈ I} : Set A) = I := by
      ext a
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · exact fun ha ↦ ⟨⟨a, subset_closure ha⟩, ha, rfl⟩
    simp [himage]

private lemma isClosed_of_isStrictAffinoid_of_nontriviallyNormed (k : Type*)
    [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    {A : Type*} [NormedCommRing A] [NormedAlgebra k A] [IsStrictAffinoid k A] (I : Ideal A) :
    IsClosed (I : Set A) := by
  have : IsNoetherianRing A := IsStrictAffinoid.isNoetherianRing k A
  rcases Submodule.fg_def.mp (IsNoetherian.noetherian I.closure) with ⟨S, hSfin, hspan⟩
  have : Fintype S := hSfin.fintype
  have hclosedClosure : IsClosed (I.closure : Set A) := by simp [Ideal.coe_closure]
  have : IsClosed (((I.closure.restrictScalars k : Submodule k A) : Set A)) := hclosedClosure
  let ψ : (S → A) →ₗ[A] A :=
    { toFun := fun v ↦ ∑ s, v s * (s : A)
      map_add' := by
        intro v w
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hψrange : LinearMap.range ψ = I.closure := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, rfl⟩
      simp [ψ, ← hspan, Ideal.sum_mem _ fun _ _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span _)]
    · classical
      rw [← hspan]
      exact Ideal.span_le.2 fun x hx ↦ ⟨fun t ↦ if t = ⟨x, hx⟩ then 1 else 0, by simp [ψ]⟩
  let φA : (S → A) →L[k] A :=
    { toLinearMap := ψ.restrictScalars k
      cont := continuous_finsetSum Finset.univ fun s _ ↦ (continuous_apply s).mul continuous_const }
  let φ : (S → A) →L[k] (I.closure.restrictScalars k) :=
    φA.codRestrict (I.closure.restrictScalars k) fun v ↦ by
      simpa [φA, hψrange] using show ψ v ∈ LinearMap.range ψ from ⟨v, rfl⟩
  have hφsurj : Function.Surjective φ := fun y ↦ by
    obtain ⟨v, hv⟩ : y.1 ∈ LinearMap.range ψ := by simp [hψrange]
    exact ⟨v, Subtype.ext hv⟩
  have hDdense : Dense {x : I.closure.restrictScalars k | x.1 ∈ I} := closure_denseSubtype I
  let r : ℝ := ((Fintype.card S : ℝ) + 1)⁻¹
  have hrpos : 0 < r := by positivity
  obtain ⟨c, hcpos, hcr⟩ := NormedField.exists_norm_lt k hrpos
  have hcardr_lt : (Fintype.card S : ℝ) * r < 1 := by
    simpa [r, div_eq_mul_inv] using (div_lt_one (by positivity)).2 (by linarith)
  have hcardc_lt : (Fintype.card S : ℝ) * ‖c‖ < 1 := lt_of_le_of_lt (by gcongr) hcardr_lt
  let g : S → I.closure.restrictScalars k :=
    fun s ↦ ⟨s, by simpa [← hspan] using Ideal.subset_span s.2⟩
  let W : Set (I.closure.restrictScalars k) := φ '' Metric.ball (0 : S → A) ‖c‖
  have hWopen : IsOpen W := (ContinuousLinearMap.isOpenMap φ hφsurj) _ Metric.isOpen_ball
  have hW0 : (0 : I.closure.restrictScalars k) ∈ W :=
    ⟨0, by simp [Metric.mem_ball, hcpos], by simp [φ]⟩
  have happrox (s : S) : ∃ y : I.closure.restrictScalars k, y.1 ∈ I ∧
      ∃ u : S → A, ‖u‖ < ‖c‖ ∧ φ u = g s - y := by
    let U : Set (I.closure.restrictScalars k) := {x | g s - x ∈ W}
    have hUopen : IsOpen U := hWopen.preimage (continuous_const.sub continuous_id)
    have hUnonempty : U.Nonempty := ⟨g s, by simp [U, hW0]⟩
    rcases hDdense.inter_open_nonempty U hUopen hUnonempty with ⟨y, ⟨u, hu, hu_eq⟩, hyI⟩
    exact ⟨y, hyI, u, by simpa [Metric.mem_ball] using hu, hu_eq⟩
  choose y hyI u hu_norm hu_eq using happrox
  let Tlin : (S → A) →ₗ[k] (S → A) :=
    { toFun := fun v s ↦ ∑ t, u s t * v t
      map_add' _ _ := by
        ext s
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' _ _ := by
        ext s
        simp [Pi.smul_apply, Finset.smul_sum] }
  have hTbound : ∀ v : S → A, ‖Tlin v‖ ≤ ((Fintype.card S : ℝ) * ‖c‖) * ‖v‖ := by
    intro v
    let C : ℝ := ((Fintype.card S : ℝ) * ‖c‖) * ‖v‖
    have hC : 0 ≤ C := by positivity
    have hbound' (s : S) : ‖Tlin v s‖₊ ≤ Real.toNNReal C := by
      simp only [Real.toNNReal_of_nonneg hC, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
      have hsum2 : (∑ t : S, ‖u s t * v t‖) ≤ ∑ _ : S, ‖c‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun _ _ ↦ ?_
        grw [norm_mul_le, norm_le_pi_norm, hu_norm, norm_le_pi_norm]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Tlin]
      grw [norm_sum_le, hsum2]
      simp [C, mul_assoc]
    rw [Pi.norm_def]
    change (Finset.univ.sup fun b ↦ ‖Tlin v b‖₊) ≤ C
    have hto : (↑(Real.toNNReal C) : ℝ) = C := by
      simp [Real.toNNReal_of_nonneg hC]
    rw [← hto]
    exact_mod_cast (Finset.sup_le_iff.mpr (fun s _ ↦ hbound' s))
  let T : ((S → A) →L[k] (S → A)) := Tlin.mkContinuous ((Fintype.card S : ℝ) * ‖c‖) hTbound
  have hTnorm : ‖T‖ ≤ (Fintype.card S : ℝ) * ‖c‖ :=
    LinearMap.mkContinuous_norm_le Tlin (by positivity) hTbound
  let U : ((S → A) →L[k] (S → A))ˣ := Units.oneSub T (lt_of_le_of_lt hTnorm hcardc_lt)
  let Sinv : ((S → A) →L[k] (S → A)) := ↑(U⁻¹)
  have hT_Alinear (a : A) (v : S → A) : T (a • v) = a • T v := by
    ext
    simp [T, Tlin, Finset.mul_sum, mul_left_comm]
  have hU_Alinear (a : A) (v : S → A) : (U : ((S → A) →L[k] (S → A))) (a • v) =
      a • (U : ((S → A) →L[k] (S → A))) v := by
    simp [U, hT_Alinear, sub_eq_add_neg]
  have hleft (v : S → A) : Sinv ((U : ((S → A) →L[k] (S → A))) v) = v := by
    rw [← ContinuousLinearMap.mul_apply]
    exact congrArg (fun F : (S → A) →L[k] (S → A) ↦ F v) (Units.inv_mul U)
  have hright (v : S → A) : (U : ((S → A) →L[k] (S → A))) (Sinv v) = v := by
    rw [← ContinuousLinearMap.mul_apply]
    exact congrArg (fun F : (S → A) →L[k] (S → A) ↦ F v) (Units.mul_inv U)
  have hU_inj : Function.Injective (U : ((S → A) →L[k] (S → A))) := fun v w hvw ↦ by
    simpa [hleft v, hleft w] using congrArg Sinv hvw
  have hSinv_Alinear (a : A) (v : S → A) : Sinv (a • v) = a • Sinv v := hU_inj <| by
    rw [hright (a • v), hU_Alinear a (Sinv v), hright v]
  let Slin : (S → A) →ₗ[A] (S → A) :=
    { toFun := Sinv
      map_add' := map_add Sinv
      map_smul' := hSinv_Alinear }
  have hSlin_mem {v : S → A} (hv : ∀ s, v s ∈ I) : ∀ s, Slin v s ∈ I := by
    intro s
    rw [← congrArg (fun w : S → A ↦ Slin w s) ((Pi.basisFun A S).sum_repr v)]
    simp only [Pi.basisFun_repr, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Ideal.sum_mem _ fun i _ ↦ ?_
    simpa [mul_comm] using Ideal.mul_mem_left I (Slin (Pi.basisFun A S i) s) (hv i)
  let G : S → A := fun s ↦ s
  let Y : S → A := fun s ↦ y s
  have hGY : (U : ((S → A) →L[k] (S → A))) G = Y := by
    ext s
    have hs : ∑ t, u s t * (t : A) = (s : A) - (y s : A) := by
      simpa [φ, φA, ψ, g] using congrArg Subtype.val (hu_eq s)
    have hs' : (s : A) - ∑ t, u s t * (t : A) = (y s : A) := by
      rw [hs]
      ring
    simpa [U, T, Tlin, G, Y] using hs'
  have hGmem : ∀ s, G s ∈ I := by
    have hSY : ∀ s, Slin Y s ∈ I := hSlin_mem hyI
    simpa [Slin, show Sinv Y = G by simpa [hGY] using hleft G] using hSY
  have hclosure_le : I.closure ≤ I := by
    grw [← hspan, ← Ideal.span_le.2 fun x hx ↦ hGmem ⟨x, hx⟩]
  simpa [le_antisymm hclosure_le subset_closure] using hclosedClosure

variable (k) in
include k in
theorem isClosed_of_isStrictAffinoid (I : Ideal A) : IsClosed (I : Set A) := by
  by_cases htv : ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField k := NontriviallyNormedField.ofNormNeOne htv
    exact isClosed_of_isStrictAffinoid_of_nontriviallyNormed k I
  · have : DiscreteTopology A := DiscreteTopology.of_forall_le_norm zero_lt_one fun a ha ↦ by
      simp [IsStrictAffinoid.norm_eq_one_of_trivially_valued htv ha]
    simp

end Ideal

end closed_ideals

omit [CompleteSpace k] in
lemma TateAlgebra.not_exist_injective_to_field {K : Type*} [NormedCommRing K] [NormedAlgebra k K]
    (n : ℕ) (hK : IsField K) (φ : TateAlgebra (Fin (n + 1)) k →ₐ[k] K) (hφfin : φ.Finite)
    (hφinj : Function.Injective φ) : False := by
  algebraize [φ.toRingHom]
  have : Algebra.IsIntegral (TateAlgebra (Fin (n + 1)) k) K :=
    (algebraMap_isIntegral_iff).mp (RingHom.IsIntegral.of_finite hφfin)
  let : Field (TateAlgebra (Fin (n + 1)) k) := (isField_of_isIntegral_of_isField hφinj hK).toField
  have hXne : (TateAlgebra.X 0 : TateAlgebra (Fin (n + 1)) k) ≠ 0 := by
    intro hX
    simpa [TateAlgebra.coe_X, MvPowerSeries.coeff_X] using
      congrArg (fun F ↦ MvPowerSeries.coeff (Finsupp.single 0 1) F.1) hX
  exact (IsUnit.ne_zero (a := 0) <| by
    simpa [TateAlgebra.constantCoeff_apply] using
      (isUnit_iff_ne_zero.mpr hXne).map TateAlgebra.constantCoeff) rfl

lemma TateAlgebra.module_finite_of_exist_finite_algHom_to_field {K : Type*} [NormedCommRing K]
    [NormedAlgebra k K] (hK : IsField K) (n : ℕ) (φ : TateAlgebra (Fin n) k →ₐ[k] K)
    (hφcontr : IsContractiveHom φ) (hφfin : φ.Finite) : Module.Finite k K := by
  induction n with
  | zero =>
      let θ : k →ₐ[k] K := φ.comp finZeroAlgEquiv.symm.toAlgHom
      have hθ : θ.toRingHom = algebraMap k K := RingHom.ext fun x ↦ θ.commutes x
      have : Algebra.IsIntegral k K := by
        rw [← algebraMap_isIntegral_iff, ← hθ]
        exact RingHom.IsIntegral.of_finite
          (RingHom.Finite.comp hφfin finZeroAlgEquiv.symm.toRingEquiv.finite)
      have : Algebra.FiniteType k K := by
        rw [← RingHom.finiteType_algebraMap, ← hθ]
        exact AlgHom.Finite.finiteType
          (RingHom.Finite.comp hφfin finZeroAlgEquiv.symm.toRingEquiv.finite)
      exact Algebra.IsIntegral.finite
  | succ n ih =>
      by_cases hφinj : Function.Injective φ
      · exact (TateAlgebra.not_exist_injective_to_field n hK φ hφfin hφinj).elim
      · rcases IsStrictAffinoid.noether_normalization_drop φ hφcontr hφfin hφinj with ⟨ψ, hψc, hψf⟩
        exact ih ψ hψc hψf

namespace IsStrictAffinoid

section finite_quotient

variable (k)

instance finiteDimensional_quotient_of_isMaximal (m : Ideal A) [m.IsMaximal] :
    FiniteDimensional k (A ⧸ m) := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  rcases IsStrictAffinoid.exists_fin_contractive_presentation k A with ⟨n, φ, hφcontr, hφsurj⟩
  let ψ : TateAlgebra (Fin n) k →ₐ[k] A ⧸ m := (Ideal.Quotient.mkₐ k m).comp φ
  have hψcontr : IsContractiveHom ψ := fun x ↦ (Ideal.Quotient.norm_mk_le m _).trans (hφcontr x)
  refine TateAlgebra.module_finite_of_exist_finite_algHom_to_field (Field.toIsField (A ⧸ m)) n ψ
    hψcontr <| AlgHom.Finite.of_surjective ψ fun y ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k m y
  exact Exists.imp (fun x hx ↦ by simp [ψ, hx]) (hφsurj a)

/-- Let `a` be an ideal of a strictly `k`-affinoid algebra `A` such that its radical `rad a` is a
  maximal ideal. Then `A / a` is of finite dimension over `k`. -/
instance finiteDimensional_quotient_of_radical_isMaximal (a : Ideal A) [a.radical.IsMaximal] :
    FiniteDimensional k (A ⧸ a) :=
  have : IsNoetherianRing A := IsStrictAffinoid.isNoetherianRing k A
  Module.Finite.quotient_of_quotient_radical_finite k a

end finite_quotient

section isContractiveHom

/-- Any `k`-algebra homomorphism between strict `k`-affinoid algebras is contractive. -/
lemma isContractiveHom (f : A →ₐ[k] B) : IsContractiveHom f := by
  by_cases htv : ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField k := NontriviallyNormedField.ofNormNeOne htv
    have : IsNoetherianRing B := IsStrictAffinoid.isNoetherianRing k B
    have hfcont : Continuous f.toLinearMap := by
      apply LinearMap.continuous_of_seq_closed_graph
      intro u x y hx hy
      have hux : Tendsto (fun n ↦ u n - x) atTop (𝓝 0) := by simpa using hx.sub_const x
      have huy : Tendsto (fun n ↦ f (u n - x)) atTop (𝓝 (y - f x)) := by
        simpa [map_sub] using Tendsto.sub hy tendsto_const_nhds
      let z : B := y - f x
      have hzpow (m : Ideal B) (hm : m.IsMaximal) (n : ℕ) : z ∈ m ^ n.succ := by
        have hradmax : (m ^ n.succ).radical.IsMaximal := by
          simp [Ideal.radical_pow m n.succ_ne_zero, hm.isPrime.radical, hm]
        let q : B →ₐ[k] B ⧸ m ^ n.succ := Ideal.Quotient.mkₐ k (m ^ n.succ)
        have hqz0 : q z = 0 := by
          by_contra hqz0
          let I : Ideal A := Ideal.comap f (m ^ n.succ)
          have : IsClosed ((m ^ n.succ : Ideal B) : Set B) :=
            Ideal.isClosed_of_isStrictAffinoid k (m ^ n.succ)
          have : IsClosed (I : Set A) := I.isClosed_of_isStrictAffinoid k
          let p : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
          have hIz (a : A) (ha : a ∈ I) : (q.comp f) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
          let F : A ⧸ I →ₐ[k] B ⧸ m ^ n.succ := Ideal.Quotient.liftₐ I (q.comp f) hIz
          have hker : RingHom.ker ((q.comp f)) = I := by
            ext a
            change ((Ideal.Quotient.mk (m ^ n.succ)) (f a) = 0) ↔ f a ∈ m ^ n.succ
            simp [Ideal.Quotient.eq_zero_iff_mem]
          have hF_inj : Function.Injective F := by
            simpa [F, Ideal.Quotient.liftₐ] using (Ideal.injective_lift_iff hIz).2 hker
          have : FiniteDimensional k (A ⧸ I) := FiniteDimensional.of_injective F.toLinearMap hF_inj
          let b := Module.Basis.ofVectorSpace k (B ⧸ m ^ n.succ)
          obtain ⟨i, hi⟩ : ∃ i, b.repr (q z) i ≠ 0 := by
            by_contra h
            push Not at h
            exact hqz0 <| b.repr.injective <| by
              ext j
              simpa using h j
          let l : (B ⧸ m ^ n.succ) →ₗ[k] k := b.coord i
          have hlcont : Continuous l := LinearMap.continuous_of_finiteDimensional l
          let g : A →ₗ[k] k := (l.comp F.toLinearMap).comp p.toLinearMap
          let h : B →ₗ[k] k := l.comp q.toLinearMap
          have hgcont : Continuous g :=
            (hlcont.comp F.toLinearMap.continuous_of_finiteDimensional).comp <|
              IsContractiveHom.continuous (fun a ↦ Ideal.Quotient.norm_mk_le I a)
          have hhcont : Continuous h := hlcont.comp <|
            IsContractiveHom.continuous (fun b ↦ Ideal.Quotient.norm_mk_le _ b)
          have ht0g : Tendsto (fun j ↦ g (u j - x)) atTop (𝓝 0) := by
            change Tendsto (g ∘ fun j ↦ u j - x) atTop (𝓝 0)
            simpa [g] using Tendsto.comp (Continuous.tendsto hgcont 0) hux
          have htz : Tendsto (fun j ↦ h (f (u j - x))) atTop (𝓝 (l (q z))) :=
            Tendsto.comp (Continuous.tendsto hhcont z) huy
          exact hi (tendsto_nhds_unique htz ht0g)
        exact Ideal.Quotient.eq_zero_iff_mem.1 hqz0
      let Ann : Ideal B :=
        { carrier := {b : B | b * z = 0}
          zero_mem' := by simp
          add_mem' := by
            intro a b ha hb
            change a * z = 0 at ha
            change b * z = 0 at hb
            simp [add_mul, ha, hb]
          smul_mem' := by
            intro a b hb
            simpa [mul_assoc] using congrArg (fun x ↦ a * x) hb }
      have hAnn_top : Ann = ⊤ := by
        by_contra hAnn
        obtain ⟨m, hm, hAnnm⟩ := Ideal.exists_le_maximal Ann hAnn
        have hzinf : z ∈ (⨅ i : ℕ, m ^ i : Ideal B) := by
          rw [Ideal.mem_iInf]
          intro i
          cases i with
          | zero => simp
          | succ n => exact hzpow m hm n
        have hzinf' : z ∈ (⨅ i : ℕ, m ^ i • (⊤ : Submodule B B) : Submodule B B) := by
          simpa [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hzinf
        obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff z).mp hzinf'
        have hr' : (r : B) * z = z := by simpa [smul_eq_mul] using hr
        have h1rz : (1 - (r : B)) ∈ Ann := by simp [Ann, sub_mul, hr']
        have h1rm : (1 - (r : B)) ∈ m := hAnnm h1rz
        have hnot : (1 - (r : B)) ∉ m := by
          intro hmem
          have h1 : (1 : B) ∈ m := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using m.add_mem hmem r.2
          exact (Ideal.ne_top_iff_one m).1 hm.ne_top h1
        exact hnot h1rm
      exact sub_eq_zero.mp <| by simpa [Ann] using (show (1 : B) ∈ Ann by simp [hAnn_top])
    let g : A →L[k] B := { toLinearMap := f.toLinearMap, cont := hfcont }
    have hg_bound (a : A) : ‖f a‖ ≤ ‖g‖ * ‖a‖ := g.le_opNorm a
    intro a
    by_cases ha0 : a = 0
    · simp [ha0]
    · by_contra hfa
      have hlt : ‖a‖ < ‖f a‖ := lt_of_not_ge hfa
      have hnorma_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      have hratio : 1 < ‖f a‖ / ‖a‖ := (one_lt_div hnorma_pos).2 hlt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖g‖ hratio
      have hboundn : ‖f a‖ ^ n ≤ ‖g‖ * ‖a‖ ^ n := by
        grw [← withSpectralNorm k, ← map_pow, hg_bound (a ^ n), withSpectralNorm k]
      have hmul : (‖f a‖ / ‖a‖) ^ n * ‖a‖ ^ n = ‖f a‖ ^ n := by
        rw [div_pow]
        field_simp [pow_ne_zero n hnorma_pos.ne']
      exact (not_lt_of_ge hboundn) (by
        simpa [hmul] using mul_lt_mul_of_pos_right hn (pow_pos hnorma_pos n))
  · intro a
    by_cases ha : a = 0
    · simp [ha]
    · refine (eq_or_ne (f a) 0).elim (fun hfa ↦ by simp [hfa]) (fun hfa ↦ ?_)
      rw [norm_eq_one_of_trivially_valued htv hfa, norm_eq_one_of_trivially_valued htv ha]

variable (k A B) in
theorem isBoundedSMul [Algebra A B] [IsScalarTower k A B] : IsBoundedSMul A B := by
  refine IsBoundedSMul.of_norm_smul_le <| fun a b ↦ ?_
  grw [Algebra.smul_def, norm_mul_le]
  gcongr
  exact isContractiveHom (IsScalarTower.toAlgHom k A B) a

end isContractiveHom

abbrev _root_.preImageNormSet {A B F : Type*} [SeminormedRing A] [SeminormedRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) (b : B) : Set ℝ :=
  {r : ℝ | ∃ a : A, f a = b ∧ ‖a‖ = r}

theorem _root_.bddBelow_preImageNormSet {A B F : Type*} [SeminormedRing A] [SeminormedRing B]
    [FunLike F A B] [RingHomClass F A B] (f : F) (b : B) : BddBelow (preImageNormSet f b) :=
  ⟨0, fun r ⟨a, _, hnorm⟩ ↦ by grw [← hnorm, norm_nonneg a]⟩

/-- Any surjective morphism between strict affinoid algebras is admissible. -/
theorem isAdmissibleHom_of_surjective {f : A →ₐ[k] B} (hf : Function.Surjective f) :
    IsAdmissibleHom f := by
  by_cases htv : ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField k := NontriviallyNormedField.ofNormNeOne htv
    let g : A →L[k] B := f.toLinearMap.mkContinuous 1 <|
      fun x ↦ by simpa using (IsStrictAffinoid.isContractiveHom f x)
    obtain ⟨C, -, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le g hf
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
    intro x
    constructor
    · obtain ⟨a, haeq, ha_bound⟩ := hC (f x)
      have hmem : ‖a‖ ∈ preImageNormSet f (f x) :=
        ⟨a, by simpa [g, LinearMap.mkContinuous_apply] using haeq, rfl⟩
      grw [csInf_le (bddBelow_preImageNormSet f (f x)) hmem, ha_bound,
        mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _)]
    · exact (IsStrictAffinoid.isContractiveHom f x).trans <| by
        nth_rw 1 [← one_mul ‖x‖]
        grw [mul_le_mul_of_nonneg_right (le_max_right C 1) (norm_nonneg x)]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hQbdd : BddBelow (preImageNormSet f (f x)) := bddBelow_preImageNormSet f (f x)
    constructor
    · by_cases hfx : f x = 0
      · grw [csInf_le hQbdd ⟨0, by simp [hfx], rfl⟩, norm_zero, hfx, norm_zero, mul_zero]
      · have hx_le_one : ‖x‖ ≤ 1 := by
          by_cases hx : x = 0
          · simp [hx]
          · exact (IsStrictAffinoid.norm_eq_one_of_trivially_valued htv hx).le
        grw [csInf_le hQbdd ⟨x, rfl, rfl⟩, IsStrictAffinoid.norm_eq_one_of_trivially_valued htv hfx]
        grw [mul_one, hx_le_one]
    · grw [IsStrictAffinoid.isContractiveHom f x, one_mul]

lemma _root_.TateAlgebra.hom_ext {σ : Type*} [Finite σ] {f g : TateAlgebra σ k →ₐ[k] A}
    (h : ∀ s : σ, f (TateAlgebra.X s) = g (TateAlgebra.X s)) : f = g := by
  have hpoly : f.comp MvPolynomial.toTate = g.comp MvPolynomial.toTate :=
    MvPolynomial.algHom_ext fun s ↦ by simp [MvPolynomial.toTate_X, h s]
  exact AlgHom.ext fun x ↦ congrArg (fun h ↦ h x) <| DenseRange.equalizer
    (MvPolynomial.toTate_denseRange σ k) (isContractiveHom f).continuous
      (isContractiveHom g).continuous <| congrArg (fun h : MvPolynomial σ k →ₐ[k] A ↦ ⇑h) hpoly

end IsStrictAffinoid
