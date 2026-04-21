/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import StrictAffinoid.Weierstrass

public section

open Valued NormedField Filter TateAlgebra

open scoped Topology

variable {σ : Type*} (s : σ) {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {A B : Type*} [NormedCommRing A] [NormedAlgebra k A]
  [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]

lemma continuous_of_contractive {C D : Type*} [NormedRing C] [NormedRing D]
    (g : C →+* D) (hg : IsContractiveHom g) : Continuous g := by
  have hLip : LipschitzWith 1 g := by
    intro x y
    simpa [edist_dist, dist_eq_norm] using ENNReal.ofReal_le_ofReal (hg (x - y))
  exact hLip.continuous

omit [IsUltrametricDist k] [CompleteSpace k] in
lemma base_norm_eq_one_of_trivially_valued
    (htv : ¬ ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1) {x : k} (hx : x ≠ 0) : ‖x‖ = 1 := by
  by_contra h
  exact htv ⟨x, hx, h⟩

omit [CompleteSpace k] in
lemma TateAlgebra.norm_eq_one_of_trivially_valued
    (htv : ¬ ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1) {F : TateAlgebra σ k} (hF : F ≠ 0) : ‖F‖ = 1 := by
  have hle : ‖F‖ ≤ 1 := by
    refine ciSup_le ?_
    intro e
    by_cases h : MvPowerSeries.coeff e F.1 = 0
    · simp [h]
    · exact le_of_eq (base_norm_eq_one_of_trivially_valued htv h)
  obtain ⟨e, he⟩ : ∃ e : σ →₀ ℕ, MvPowerSeries.coeff e F.1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hF
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro e
    exact h e
  have hge : 1 ≤ ‖F‖ := by
    have hcoeff :
        1 = ‖MvPowerSeries.coeff e F.1‖ :=
      (base_norm_eq_one_of_trivially_valued htv he).symm
    rw [hcoeff]
    exact TateAlgebra.coeff_norm_le F e
  exact le_antisymm hle hge

lemma IsStrictAffinoid.norm_eq_one_of_trivially_valued
    (htv : ¬ ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1) {a : A} (ha : a ≠ 0) : ‖a‖ = 1 := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, hφ, hsurj⟩
  rcases hφ with ⟨C, hCpos, hφ⟩
  obtain ⟨x, rfl⟩ := hsurj a
  have hx0 : x ≠ 0 := by
    intro hx0
    exact ha (by simp [hx0])
  let Q (y : A) : Set ℝ := {r : ℝ | ∃ z : TateAlgebra σ k, φ z = y ∧ ‖z‖ = r}
  have hQ_eq_singleton {y : A} (hy : y ≠ 0) : Q y = {1} := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨z, hz, rfl⟩
      have hz0 : z ≠ 0 := by
        intro hz0
        exact hy (by simpa [hz0] using hz.symm)
      simp [TateAlgebra.norm_eq_one_of_trivially_valued htv hz0]
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      obtain ⟨z, hz⟩ := hsurj y
      have hz0 : z ≠ 0 := by
        intro hz0
        exact hy (by simpa [hz0] using hz.symm)
      refine ⟨z, hz, ?_⟩
      simpa [hr] using
        (TateAlgebra.norm_eq_one_of_trivially_valued htv hz0)
  have hxnpow_ne_zero (n : ℕ) : (φ x) ^ n ≠ 0 := by
    intro hzero
    have hnorm0 : ‖(φ x) ^ n‖ = 0 := by simp [hzero]
    have hnormpos : 0 < ‖(φ x) ^ n‖ := by
      rw [IsStrictAffinoid.withSpectralNorm k n (φ x)]
      exact pow_pos (norm_pos_iff.mpr ha) _
    exact hnormpos.ne' hnorm0
  have hnot_gt : ¬ 1 < ‖φ x‖ := by
    intro hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt
    obtain ⟨z, hz⟩ := hsurj ((φ x) ^ n)
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hxnpow_ne_zero n (by simpa [hz0] using hz.symm)
    have hz1 : ‖z‖ = 1 :=
      TateAlgebra.norm_eq_one_of_trivially_valued htv hz0
    have hpow :
        ‖(φ x) ^ n‖ = ‖φ x‖ ^ n := by
      simpa using IsStrictAffinoid.withSpectralNorm k n (φ x)
    have hbound : ‖(φ x) ^ n‖ ≤ C := by
      have h1 : ‖(φ x) ^ n‖ = ‖φ z‖ := by simp [hz]
      have h2 : ‖φ z‖ ≤ C * ‖z‖ := (hφ z).2
      have h3 : C * ‖z‖ = C := by simp [hz1]
      exact h1.trans_le (h2.trans_eq h3)
    have : ‖φ x‖ ^ n ≤ C := by simpa [hpow] using hbound
    exact (not_lt_of_ge this) hn
  have hnot_lt : ¬ ‖φ x‖ < 1 := by
    intro hlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < C⁻¹ by positivity) hlt
    obtain ⟨z, hz⟩ := hsurj ((φ x) ^ n)
    have hφz1 := (hφ z).1
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hxnpow_ne_zero n (by simpa [hz0] using hz.symm)
    have hz1 : ‖z‖ = 1 :=
      TateAlgebra.norm_eq_one_of_trivially_valued htv hz0
    have hQ : sInf (Q ((φ x) ^ n)) = 1 := by
      simp [hQ_eq_singleton (hxnpow_ne_zero n)]
    have hpow : ‖(φ x) ^ n‖ = ‖φ x‖ ^ n := IsStrictAffinoid.withSpectralNorm k n (φ x)
    have hsInf_le : sInf (Q ((φ x) ^ n)) ≤ C * ‖φ x‖ ^ n := by simpa [Q, hz, hpow] using hφz1
    have : 1 ≤ C * ‖φ x‖ ^ n := by simpa [hQ] using hsInf_le
    have hlt1 : C * ‖φ x‖ ^ n < 1 := by
      have hmul : C * ‖φ x‖ ^ n < C * C⁻¹ := mul_lt_mul_of_pos_left hn hCpos
      simpa [mul_inv_cancel₀ hCpos.ne'] using hmul
    exact (not_lt_of_ge this) hlt1
  have hle : ‖φ x‖ ≤ 1 := le_of_not_gt hnot_gt
  have hge : 1 ≤ ‖φ x‖ := le_of_not_gt hnot_lt
  exact le_antisymm hle hge

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
      · intro ha
        refine ⟨⟨a, ?_⟩, ha, rfl⟩
        exact subset_closure ha
    rw [himage]
    exact x.2

private lemma isClosed_of_isStrictAffinoid_of_nontriviallyNormed (k : Type*)
    [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    {A : Type*} [NormedCommRing A] [NormedAlgebra k A] [IsStrictAffinoid k A] (I : Ideal A) :
    IsClosed (I : Set A) := by
  letI : IsNoetherianRing A := IsStrictAffinoid.isNoetherianRing k A
  have hI_fg : I.closure.FG := IsNoetherian.noetherian I.closure
  rcases Submodule.fg_def.mp hI_fg with ⟨S, hSfin, hspan⟩
  letI : Fintype S := hSfin.fintype
  have hclosedClosure : IsClosed (I.closure : Set A) := by
    simp [Ideal.coe_closure]
  letI : IsClosed (((I.closure.restrictScalars k : Submodule k A) : Set A)) := by
    exact hclosedClosure
  letI : CompleteSpace (I.closure.restrictScalars k) := by
    let s : Set A := ((I.closure.restrictScalars k : Submodule k A) : Set A)
    infer_instance
  let ψ : (S → A) →ₗ[A] A :=
    { toFun := fun v => ∑ s, v s * (s : A)
      map_add' := by
        intro v w
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hψrange : LinearMap.range ψ = I.closure := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rcases hx with ⟨v, rfl⟩
      rw [← hspan]
      change ∑ s ∈ Finset.univ, v s * (s : A) ∈ Ideal.span S
      exact Ideal.sum_mem _ fun s hs => Ideal.mul_mem_left _ _ (Ideal.subset_span s.2)
    · classical
      rw [← hspan]
      refine Ideal.span_le.2 ?_
      intro x hx
      refine ⟨fun t => if t = ⟨x, hx⟩ then 1 else 0, ?_⟩
      simp [ψ]
  let φA : (S → A) →L[k] A :=
    { toLinearMap := ψ.restrictScalars k
      cont := by
        have hcont (s : S) : Continuous fun v : S → A => v s * (s : A) :=
          (continuous_apply s).mul continuous_const
        simpa using continuous_finset_sum (Finset.univ) (fun s _ => hcont s) }
  let φ : (S → A) →L[k] (I.closure.restrictScalars k) :=
    φA.codRestrict (I.closure.restrictScalars k) (by
      intro v
      show φA v ∈ I.closure
      rw [← hψrange]
      exact ⟨v, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : A) ∈ LinearMap.range ψ := by
      rw [hψrange]
      exact y.2
    rcases hy with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    ext
    exact hv
  have hDdense : Dense {x : I.closure.restrictScalars k | x.1 ∈ I} :=
    closure_denseSubtype I
  let r : ℝ := ((Fintype.card S : ℝ) + 1)⁻¹
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨c, hcpos, hcr⟩ := NormedField.exists_norm_lt k hrpos
  have hcardr_lt : (Fintype.card S : ℝ) * r < 1 := by
    have hden : 0 < (Fintype.card S : ℝ) + 1 := by positivity
    have hlt : (Fintype.card S : ℝ) < (Fintype.card S : ℝ) + 1 := by linarith
    simpa [r, div_eq_mul_inv] using (div_lt_one hden).2 hlt
  have hcardc_lt : (Fintype.card S : ℝ) * ‖c‖ < 1 := by
    have hcard_nonneg : 0 ≤ (Fintype.card S : ℝ) := by positivity
    have hle : (Fintype.card S : ℝ) * ‖c‖ ≤ (Fintype.card S : ℝ) * r := by
      gcongr
    exact lt_of_le_of_lt hle hcardr_lt
  let g : S → I.closure.restrictScalars k := fun s => ⟨s, by
    rw [← hspan]
    exact Ideal.subset_span s.2⟩
  have hφopen : IsOpenMap φ :=
    let hcodom : CompleteSpace (I.closure.restrictScalars k) := inferInstance
    @ContinuousLinearMap.isOpenMap k k _ _ (RingHom.id k) (S → A) _ _
      (I.closure.restrictScalars k) _ _ φ (RingHom.id k)
        inferInstance inferInstance inferInstance hcodom inferInstance hφsurj
  let W : Set (I.closure.restrictScalars k) := φ '' Metric.ball (0 : S → A) ‖c‖
  have hWopen : IsOpen W := hφopen _ Metric.isOpen_ball
  have hW0 : (0 : I.closure.restrictScalars k) ∈ W := by
    refine ⟨0, ?_, by simp [φ]⟩
    simp [Metric.mem_ball, hcpos]
  have happrox (s : S) :
      ∃ y : I.closure.restrictScalars k, y.1 ∈ I ∧
        ∃ u : S → A, ‖u‖ < ‖c‖ ∧ φ u = g s - y := by
    let U : Set (I.closure.restrictScalars k) := {x | g s - x ∈ W}
    have hUopen : IsOpen U := hWopen.preimage (continuous_const.sub continuous_id)
    have hUnonempty : U.Nonempty := ⟨g s, by simp [U, hW0]⟩
    rcases hDdense.inter_open_nonempty U hUopen hUnonempty with ⟨y, hy⟩
    rcases hy.1 with ⟨u, hu, hu_eq⟩
    exact ⟨y, hy.2, u, by simpa [Metric.mem_ball] using hu, hu_eq⟩
  choose y hyI u hu_norm hu_eq using happrox
  let Tlin : (S → A) →ₗ[k] (S → A) :=
    { toFun := fun v s => ∑ t, u s t * v t
      map_add' := by
        intro v w
        ext s
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        ext s
        have hsum :
            ∑ t, u s t * (a • v) t = ∑ t, a • (u s t * v t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simp
        have hsmul :
            ∑ t, a • (u s t * v t) =
              ((RingHom.id k) a • fun s : S => ∑ t, u s t * v t) s := by
          simp [Pi.smul_apply, Finset.smul_sum]
        exact hsum.trans hsmul }
  have hTbound : ∀ v : S → A, ‖Tlin v‖ ≤ ((Fintype.card S : ℝ) * ‖c‖) * ‖v‖ := by
    intro v
    let C : ℝ := ((Fintype.card S : ℝ) * ‖c‖) * ‖v‖
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hbound' : ∀ s ∈ Finset.univ, ‖Tlin v s‖₊ ≤ Real.toNNReal C := by
      intro s hs
      have hsreal : ‖Tlin v s‖ ≤ C := by
        have hsum1 : ‖∑ t, u s t * v t‖ ≤ ∑ t, ‖u s t * v t‖ := norm_sum_le _ _
        have hsum2 : (∑ t : S, ‖u s t * v t‖) ≤ ∑ t : S, ‖c‖ * ‖v‖ := by
          refine Finset.sum_le_sum ?_
          intro t ht
          have hmul1 : ‖u s t * v t‖ ≤ ‖u s t‖ * ‖v t‖ := norm_mul_le _ _
          have hmul2 : ‖u s t‖ * ‖v t‖ ≤ ‖c‖ * ‖v‖ := by
            gcongr
            · exact le_of_lt <| lt_of_le_of_lt (norm_le_pi_norm (u s) t) (hu_norm s)
            · exact norm_le_pi_norm v t
          exact le_trans hmul1 hmul2
        have hsum3 : (∑ t : S, ‖c‖ * ‖v‖) = C := by simp [C, mul_assoc]
        exact (le_trans hsum1 hsum2).trans_eq hsum3
      exact (NNReal.coe_le_coe).mp (by simpa [Real.toNNReal_of_nonneg hC] using hsreal)
    rw [Pi.norm_def]
    have hsup : ↑(Finset.univ.sup fun b => ‖Tlin v b‖₊) ≤ ↑(Real.toNNReal C) := by
      exact_mod_cast (Finset.sup_le_iff.mpr hbound')
    change ↑(Finset.univ.sup fun b => ‖Tlin v b‖₊) ≤ C
    have hto : (↑(Real.toNNReal C) : ℝ) = C := by
      simp [Real.toNNReal_of_nonneg hC]
    rw [← hto]
    exact hsup
  let T : ((S → A) →L[k] (S → A)) :=
    Tlin.mkContinuous ((Fintype.card S : ℝ) * ‖c‖) hTbound
  have hTnorm : ‖T‖ ≤ (Fintype.card S : ℝ) * ‖c‖ := by
    exact LinearMap.mkContinuous_norm_le Tlin (by positivity) hTbound
  let U : ((S → A) →L[k] (S → A))ˣ := Units.oneSub T (lt_of_le_of_lt hTnorm hcardc_lt)
  let Sinv : ((S → A) →L[k] (S → A)) := ↑(U⁻¹)
  have hT_Alinear (a : A) (v : S → A) : T (a • v) = a • T v := by
    ext s
    change ∑ t, u s t * (a * v t) = a * ∑ t, u s t * v t
    have hsum : ∑ t, u s t * (a * v t) = ∑ t, a * (u s t * v t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    rw [hsum, Finset.mul_sum]
  have hU_Alinear (a : A) (v : S → A) : (U : ((S → A) →L[k] (S → A))) (a • v) =
      a • (U : ((S → A) →L[k] (S → A))) v := by
    simp [U, hT_Alinear, sub_eq_add_neg]
  have hleft (v : S → A) : Sinv ((U : ((S → A) →L[k] (S → A))) v) = v := by
    change ((↑(U⁻¹) : ((S → A) →L[k] (S → A))) (((U : ((S → A) →L[k] (S → A))) v))) = v
    rw [← ContinuousLinearMap.mul_apply]
    exact congrArg (fun F : (S → A) →L[k] (S → A) => F v) (Units.inv_mul U)
  have hright (v : S → A) : (U : ((S → A) →L[k] (S → A))) (Sinv v) = v := by
    change ((U : ((S → A) →L[k] (S → A))) (((↑(U⁻¹) : ((S → A) →L[k] (S → A))) v))) = v
    rw [← ContinuousLinearMap.mul_apply]
    exact congrArg (fun F : (S → A) →L[k] (S → A) => F v) (Units.mul_inv U)
  have hU_inj : Function.Injective (U : ((S → A) →L[k] (S → A))) := by
    intro v w hvw
    have h := congrArg Sinv hvw
    simpa [hleft v, hleft w] using h
  have hSinv_Alinear (a : A) (v : S → A) : Sinv (a • v) = a • Sinv v := by
    apply hU_inj
    have h1 : (U : ((S → A) →L[k] (S → A))) (Sinv (a • v)) = a • v := hright (a • v)
    have h2 : a • v = a • (U : ((S → A) →L[k] (S → A))) (Sinv v) := by rw [hright v]
    have h3 : a • (U : ((S → A) →L[k] (S → A))) (Sinv v) =
        (U : ((S → A) →L[k] (S → A))) (a • Sinv v) := by
      symm
      exact hU_Alinear a (Sinv v)
    exact h1.trans (h2.trans h3)
  let Slin : (S → A) →ₗ[A] (S → A) :=
    { toFun := Sinv
      map_add' := by
        intro v w
        exact map_add Sinv v w
      map_smul' := hSinv_Alinear }
  have hSlin_mem {v : S → A} (hv : ∀ s, v s ∈ I) : ∀ s, Slin v s ∈ I := by
    intro s
    have hrepr : Slin v s = ∑ i, v i * Slin (Pi.basisFun A S i) s := by
      have h := congrArg (fun w : S → A => Slin w s) ((Pi.basisFun A S).sum_repr v)
      simpa using h.symm
    rw [hrepr]
    refine Ideal.sum_mem _ ?_
    intro i hi
    simpa [mul_comm] using Ideal.mul_mem_left I (Slin (Pi.basisFun A S i) s) (hv i)
  let G : S → A := fun s => s
  let Y : S → A := fun s => y s
  have hGY : (U : ((S → A) →L[k] (S → A))) G = Y := by
    ext s
    have hs : ∑ t, u s t * (t : A) = (s : A) - (y s : A) := by
      simpa [φ, φA, ψ, g] using congrArg Subtype.val (hu_eq s)
    have hs' : (s : A) - ∑ t, u s t * (t : A) = (y s : A) := by
      rw [hs]
      ring
    simpa [U, T, Tlin, G, Y] using hs'
  have hSinvY_eq_G : Sinv Y = G := by
    simpa [hGY] using hleft G
  have hGmem : ∀ s, G s ∈ I := by
    have hYmem : ∀ s, Y s ∈ I := by
      intro s
      simpa [Y] using hyI s
    have hSY : ∀ s, Slin Y s ∈ I := hSlin_mem hYmem
    intro s
    simpa [Slin, hSinvY_eq_G] using hSY s
  have hclosure_le : I.closure ≤ I := by
    rw [← hspan]
    refine Ideal.span_le.2 ?_
    intro x hx
    exact hGmem ⟨x, hx⟩
  have hI_le_closure : I ≤ I.closure := by
    intro x hx
    change x ∈ closure (I : Set A)
    exact subset_closure hx
  have hclosure_eq : I.closure = I := le_antisymm hclosure_le hI_le_closure
  simpa [hclosure_eq] using hclosedClosure

variable (k) in
include k in
theorem isClosed_of_isStrictAffinoid (I : Ideal A) : IsClosed (I : Set A) := by
  by_cases htv : ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField k := NontriviallyNormedField.ofNormNeOne htv
    exact isClosed_of_isStrictAffinoid_of_nontriviallyNormed k I
  · have : DiscreteTopology A := by
      refine DiscreteTopology.of_forall_le_norm zero_lt_one ?_
      intro a ha
      simp [IsStrictAffinoid.norm_eq_one_of_trivially_valued htv ha]
    simp

end Ideal

end closed_ideals

namespace IsStrictAffinoid

section finite_quotient

omit [CompleteSpace k] in
lemma _root_.TateAlgebra.not_exist_injective_to_field {K : Type*} [NormedCommRing K] [NormedAlgebra k K]
    (n : ℕ) (hK : IsField K) (φ : TateAlgebra (Fin (n + 1)) k →ₐ[k] K) (hφfin : φ.Finite)
    (hφinj : Function.Injective φ) : False := by
  algebraize [φ.toRingHom]
  have : Algebra.IsIntegral (TateAlgebra (Fin (n + 1)) k) K :=
    (algebraMap_isIntegral_iff).mp (RingHom.IsIntegral.of_finite hφfin)
  letI : Field (TateAlgebra (Fin (n + 1)) k) := (isField_of_isIntegral_of_isField hφinj hK).toField
  have hXne : (TateAlgebra.X 0 : TateAlgebra (Fin (n + 1)) k) ≠ 0 := by
    intro hX
    have hcoeff := congrArg (fun F : TateAlgebra (Fin (n + 1)) k =>
      MvPowerSeries.coeff (Finsupp.single 0 1) ((F : TateAlgebra (Fin (n + 1)) k) :
        MvPowerSeries (Fin (n + 1)) k)) hX
    simp [TateAlgebra.coe_X, MvPowerSeries.coeff_X] at hcoeff
  have hXu : IsUnit (TateAlgebra.X 0 : TateAlgebra (Fin (n + 1)) k) := isUnit_iff_ne_zero.mpr hXne
  have h0u : IsUnit (0 : k) := by
    have hmap := hXu.map (TateAlgebra.constantCoeff)
    simp [TateAlgebra.constantCoeff_apply] at hmap
  exact (IsUnit.ne_zero h0u) rfl

lemma _root_.TateAlgebra.module_finite_of_exist_finite_algHom_to_field {K : Type*} [NormedCommRing K]
    [NormedAlgebra k K] (hK : IsField K) (n : ℕ) (φ : TateAlgebra (Fin n) k →ₐ[k] K)
    (hφcontr : IsContractiveHom φ.toRingHom) (hφfin : φ.Finite) : Module.Finite k K := by
  induction n with
  | zero =>
      let θ : k →ₐ[k] K := φ.comp finZeroAlgEquiv.symm.toAlgHom
      have hθ : θ.toRingHom = algebraMap k K := by
        ext x
        exact θ.commutes x
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

variable (k)

instance finiteDimensional_quotient_of_isMaximal (m : Ideal A) [m.IsMaximal] :
    FiniteDimensional k (A ⧸ m) := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  rcases IsStrictAffinoid.exists_fin_contractve_presentation k A with ⟨n, φ, hφcontr, hφsurj⟩
  let ψ : TateAlgebra (Fin n) k →ₐ[k] A ⧸ m := (Ideal.Quotient.mkₐ k m).comp φ
  have hψcontr : IsContractiveHom ψ.toRingHom := by
    intro x
    exact le_trans (Ideal.Quotient.norm_mk_le m _) (hφcontr x)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k m y
    obtain ⟨x, rfl⟩ := hφsurj a
    exact ⟨x, rfl⟩
  exact TateAlgebra.module_finite_of_exist_finite_algHom_to_field (Field.toIsField (A ⧸ m)) n ψ
    hψcontr (AlgHom.Finite.of_surjective ψ hψsurj)

/-- Let `a` be an ideal of a strictly `k`-affinoid algebra `A` such that its radical `rad a` is a
  maximal ideal. Then `A / a` is of finite dimension over `k`. -/
instance finiteDimensional_quotient_of_radical_isMaximal (a : Ideal A) [a.radical.IsMaximal] :
    FiniteDimensional k (A ⧸ a) := by
  let R := A ⧸ a
  letI : IsNoetherianRing A := IsStrictAffinoid.isNoetherianRing k A
  let e := DoubleQuot.quotQuotEquivQuotOfLEₐ k (show a ≤ a.radical from Ideal.le_radical)
  have hnil : Ideal.map (Ideal.Quotient.mk a) a.radical = nilradical R := by
    rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by simp)]
    simp [R, nilradical]
  have hnilmax : (nilradical R).IsMaximal := by
    rw [← hnil]
    refine Ideal.Quotient.maximal_of_isField _ ?_
    letI : Field (A ⧸ a.radical) := Ideal.Quotient.field a.radical
    exact MulEquiv.isField (Field.toIsField (A ⧸ a.radical)) e.toMulEquiv
  letI : Ring.KrullDimLE 0 R := Ring.KrullDimLE.of_isMaximal_nilradical R
  letI : IsArtinianRing R := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  letI : IsLocalRing R := IsLocalRing.of_isMaximal_nilradical R
  have hjac : Ring.jacobson R = nilradical R := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, Ring.KrullDimLE.nilradical_eq_maximalIdeal]
  haveI : Module.Finite k (R ⧸ Ring.jacobson R) :=
    Module.Finite.equiv <| AlgEquiv.toLinearEquiv <| AlgEquiv.trans
      (e.symm.trans (Ideal.quotientEquivAlgOfEq k hnil)) (Ideal.quotientEquivAlgOfEq k hjac).symm
  letI : Module.Finite k R := IsSemiprimaryRing.finite_of_isArtinian k R R
  exact Module.Basis.finiteDimensional_of_finite (IsNoetherian.finsetBasis k R)

end finite_quotient

section isContractiveHom

lemma isContractiveHom (f : A →ₐ[k] B) : IsContractiveHom f.toRingHom := by
  by_cases htv : ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField k := NontriviallyNormedField.ofNormNeOne htv
    have : IsNoetherianRing B := IsStrictAffinoid.isNoetherianRing k B
    have hfcont : Continuous f.toLinearMap := by
      apply LinearMap.continuous_of_seq_closed_graph
      intro u x y hx hy
      have hux' : Tendsto (fun n => u n - x) atTop (𝓝 (x - x)) := by
        exact Tendsto.sub hx tendsto_const_nhds
      have hux : Tendsto (fun n => u n - x) atTop (𝓝 0) := by
        simpa using hux'
      have huy : Tendsto (fun n => f (u n - x)) atTop (𝓝 (y - f x)) := by
        simpa [map_sub] using
          Tendsto.sub hy (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
      let z : B := y - f x
      have hzpow : ∀ (m : Ideal B) (_ : m.IsMaximal) (n : ℕ), z ∈ m ^ n.succ := by
        intro m hm n
        have hradmax : (m ^ n.succ).radical.IsMaximal := by
          rw [Ideal.radical_pow m n.succ_ne_zero, Ideal.IsPrime.radical hm.isPrime]
          exact hm
        let q : B →ₐ[k] B ⧸ m ^ n.succ := Ideal.Quotient.mkₐ k (m ^ n.succ)
        have hqz0 : q z = 0 := by
          by_contra hqz0
          let I : Ideal A := Ideal.comap f.toRingHom (m ^ n.succ)
          haveI : IsClosed ((m ^ n.succ : Ideal B) : Set B) :=
            Ideal.isClosed_of_isStrictAffinoid k (m ^ n.succ)
          haveI : IsClosed (I : Set A) := I.isClosed_of_isStrictAffinoid k
          let p : A →ₐ[k] A ⧸ I := Ideal.Quotient.mkₐ k I
          have hIzeroAlg : ∀ a ∈ I, (q.comp f) a = 0 := by
            intro a ha
            exact Ideal.Quotient.eq_zero_iff_mem.2 ha
          let F : A ⧸ I →ₐ[k] B ⧸ m ^ n.succ := Ideal.Quotient.liftₐ I (q.comp f) hIzeroAlg
          have hIzeroRing : ∀ a ∈ I, ((q.comp f).toRingHom) a = 0 := by
            intro a ha
            exact hIzeroAlg a ha
          have hker : RingHom.ker ((q.comp f).toRingHom) = I := by
            ext a
            change ((Ideal.Quotient.mk (m ^ n.succ)) (f a) = 0) ↔ f a ∈ m ^ n.succ
            simp [Ideal.Quotient.eq_zero_iff_mem]
          have hFinj :
              Function.Injective (Ideal.Quotient.lift I ((q.comp f).toRingHom) hIzeroRing) :=
            (Ideal.injective_lift_iff hIzeroRing).2 hker
          have hF_inj : Function.Injective F := by
            simpa [F, Ideal.Quotient.liftₐ] using hFinj
          haveI : FiniteDimensional k (A ⧸ I) := FiniteDimensional.of_injective F.toLinearMap hF_inj
          let b := Module.Basis.ofVectorSpace k (B ⧸ m ^ n.succ)
          obtain ⟨i, hi⟩ : ∃ i, b.repr (q z) i ≠ 0 := by
            by_contra h
            push Not at h
            apply hqz0
            apply b.repr.injective
            ext j
            simpa using h j
          let l : (B ⧸ m ^ n.succ) →ₗ[k] k := b.coord i
          have hlqz : l (q z) ≠ 0 := by
            simpa [l] using hi
          have hpcont : Continuous p.toLinearMap := by
            exact continuous_of_contractive p.toRingHom (fun a => Ideal.Quotient.norm_mk_le I a)
          have hqcont : Continuous q.toLinearMap := by
            exact continuous_of_contractive q.toRingHom
              (fun b => Ideal.Quotient.norm_mk_le (m ^ n.succ) b)
          have hFcont : Continuous F.toLinearMap :=
            LinearMap.continuous_of_finiteDimensional F.toLinearMap
          have hlcont : Continuous l := LinearMap.continuous_of_finiteDimensional l
          have hFp : F.comp p = q.comp f := Ideal.Quotient.liftₐ_comp I (q.comp f) hIzeroAlg
          let g : A →ₗ[k] k := (l.comp F.toLinearMap).comp p.toLinearMap
          let h : B →ₗ[k] k := l.comp q.toLinearMap
          have hgcont : Continuous g := (hlcont.comp hFcont).comp hpcont
          have hhcont : Continuous h := hlcont.comp hqcont
          have hgf : ∀ a : A, g a = h (f a) := by
            intro a
            have hFpa : F (p a) = q (f a) := by
              exact congrArg (fun φ : A →ₐ[k] B ⧸ m ^ n.succ => φ a) hFp
            exact congrArg l hFpa
          have ht0g : Tendsto (fun j => g (u j - x)) atTop (𝓝 0) := by
            change Tendsto (⇑g ∘ fun j => u j - x) atTop (𝓝 0)
            have hg0 : g 0 = 0 := by simp [g]
            simpa [hg0] using Tendsto.comp (Continuous.tendsto hgcont 0) hux
          have ht0 : Tendsto (fun j => h (f (u j - x))) atTop (𝓝 0) := by
            simpa [hgf] using ht0g
          have htz' : Tendsto (fun j => h (f (u j - x))) atTop (𝓝 (h z)) := by
            change Tendsto (⇑h ∘ fun j => f (u j - x)) atTop (𝓝 (h z))
            exact Tendsto.comp (Continuous.tendsto hhcont z) huy
          have htz : Tendsto (fun j => h (f (u j - x))) atTop (𝓝 (l (q z))) := by
            simpa [h] using htz'
          exact hlqz (tendsto_nhds_unique htz ht0)
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
            change a * b * z = 0
            rw [mul_assoc, hb, mul_zero] }
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
        have hr' : (r : B) * z = z := by
          simpa [smul_eq_mul] using hr
        have h1rz : (1 - (r : B)) ∈ Ann := by
          change (1 - (r : B)) * z = 0
          rw [sub_mul, one_mul, hr', sub_self]
        have h1rm : (1 - (r : B)) ∈ m := hAnnm h1rz
        have hnot : (1 - (r : B)) ∉ m := by
          intro hmem
          have h1 : (1 : B) ∈ m := by
            have hs : (1 - (r : B)) + r ∈ m := m.add_mem hmem r.2
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs
          exact (Ideal.ne_top_iff_one m).1 hm.ne_top h1
        exact hnot h1rm
      have hz0 : z = 0 := by
        have h1ann : (1 : B) ∈ Ann := by
          simp [hAnn_top]
        have h1ann' : (1 : B) * z = 0 := h1ann
        simpa [one_mul] using h1ann'
      have : y - f x = 0 := by simpa [z] using hz0
      exact sub_eq_zero.mp this
    let g : A →L[k] B := { toLinearMap := f.toLinearMap, cont := hfcont }
    have hg_bound (a : A) : ‖f a‖ ≤ ‖g‖ * ‖a‖ := by
      simpa [g] using g.le_opNorm a
    intro a
    by_cases ha0 : a = 0
    · simp [ha0]
    · by_contra hfa
      have hlt : ‖a‖ < ‖f a‖ := lt_of_not_ge hfa
      have hnorma_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      have hratio : 1 < ‖f a‖ / ‖a‖ := by
        simpa using (one_lt_div hnorma_pos).2 hlt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖g‖ hratio
      have hpowB : ‖(f a) ^ n‖ = ‖f a‖ ^ n := by
        simpa using IsStrictAffinoid.withSpectralNorm k n (f a)
      have hpowA : ‖a ^ n‖ = ‖a‖ ^ n := by
        simpa using IsStrictAffinoid.withSpectralNorm k n a
      have hboundn : ‖f a‖ ^ n ≤ ‖g‖ * ‖a‖ ^ n := by
        have h1 : ‖f a‖ ^ n = ‖(f a) ^ n‖ := hpowB.symm
        have h2 : ‖(f a) ^ n‖ = ‖f (a ^ n)‖ := by simp
        have h3 : ‖f (a ^ n)‖ ≤ ‖g‖ * ‖a ^ n‖ := hg_bound (a ^ n)
        have h4 : ‖g‖ * ‖a ^ n‖ = ‖g‖ * ‖a‖ ^ n := by rw [hpowA]
        exact h1.trans_le (h2.trans_le (h3.trans_eq h4))
      have hapos_pow : 0 < ‖a‖ ^ n := pow_pos hnorma_pos _
      have hmul : (‖f a‖ / ‖a‖) ^ n * ‖a‖ ^ n = ‖f a‖ ^ n := by
        rw [div_pow]
        field_simp [pow_ne_zero n hnorma_pos.ne']
      have hcontr : ‖g‖ * ‖a‖ ^ n < ‖f a‖ ^ n := by
        have hm := mul_lt_mul_of_pos_right hn hapos_pow
        simpa [hmul] using hm
      exact (not_lt_of_ge hboundn) hcontr
  · intro a
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hfa : f a = 0
      · simp [hfa]
      · change ‖f a‖ ≤ ‖a‖
        rw [IsStrictAffinoid.norm_eq_one_of_trivially_valued htv hfa,
          IsStrictAffinoid.norm_eq_one_of_trivially_valued htv ha]

variable (k A B) in
theorem isBoundedSMul [Algebra A B] [IsScalarTower k A B] : IsBoundedSMul A B := by
  refine IsBoundedSMul.of_norm_smul_le <| fun a b ↦ ?_
  calc _ = ‖algebraMap A B a * b‖ := by rw [Algebra.smul_def]
    _ ≤ ‖algebraMap A B a‖ * ‖b‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * ‖b‖ := by
      gcongr
      exact isContractiveHom (IsScalarTower.toAlgHom k A B) a

end isContractiveHom

section NontriviallyNormedField

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {A B : Type*} [NormedCommRing A] [NormedAlgebra k A]
  [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]

/-- A surjective morphism between strict affinoid algebras is admissible. -/
theorem admissible_of_surjective (f : A →ₐ[k] B)
    (hf : Function.Surjective f) : IsAdmissibleHom f.toRingHom := by
  let g : A →L[k] B := f.toLinearMap.mkContinuous 1 <|
    fun x => by simpa using (IsStrictAffinoid.isContractiveHom f x)
  obtain ⟨C, hCpos, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le g hf
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro x
  constructor
  · change sInf {r : ℝ | ∃ a : A, f.toRingHom a = f.toRingHom x ∧ ‖a‖ = r} ≤ max C 1 * ‖f x‖
    let Q : Set ℝ := {r : ℝ | ∃ a : A, f.toRingHom a = f.toRingHom x ∧ ‖a‖ = r}
    have hQbdd : BddBelow Q := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨a, -, rfl⟩
      exact norm_nonneg _
    obtain ⟨a, haeq, ha_bound⟩ := hC (f x)
    have hmem : ‖a‖ ∈ Q := by
      refine ⟨a, ?_, rfl⟩
      simpa [g, LinearMap.mkContinuous_apply] using haeq
    exact (csInf_le hQbdd hmem).trans <| ha_bound.trans <| by
      gcongr
      exact le_max_left C 1
  · change ‖f x‖ ≤ max C 1 * ‖x‖
    calc
      ‖f x‖ ≤ 1 * ‖x‖ := by
        simpa using (IsStrictAffinoid.isContractiveHom f x)
      _ ≤ max C 1 * ‖x‖ := by
        gcongr
        exact le_max_right C 1

end NontriviallyNormedField

lemma _root_.TateAlgebra.hom_ext {σ : Type*} [Finite σ] {f g : TateAlgebra σ k →ₐ[k] A}
    (h : ∀ s : σ, f (TateAlgebra.X s) = g (TateAlgebra.X s)) : f = g := by
  have hpoly : f.comp MvPolynomial.toTate = g.comp MvPolynomial.toTate := by
    apply MvPolynomial.algHom_ext
    intro s
    simpa [MvPolynomial.toTate_X] using h s
  have hfcont : Continuous f := by
    have hf := IsStrictAffinoid.isContractiveHom f
    have hLip : LipschitzWith 1 f := by
      intro x y
      simpa [edist_dist, dist_eq_norm, ENNReal.coe_one, one_mul, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using (ENNReal.ofReal_le_ofReal (hf (x - y)))
    exact hLip.continuous
  have hgcont : Continuous g := by
    have hg := IsStrictAffinoid.isContractiveHom g
    have hLip : LipschitzWith 1 g := by
      intro x y
      simpa [edist_dist, dist_eq_norm, ENNReal.coe_one, one_mul, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc] using (ENNReal.ofReal_le_ofReal (hg (x - y)))
    exact hLip.continuous
  have hpoly_fun : (fun p : MvPolynomial σ k => f p.toTate) =
      fun p : MvPolynomial σ k => g p.toTate := by
    exact congrArg (fun h : MvPolynomial σ k →ₐ[k] A => ⇑h) hpoly
  have hfg_fun :
      (f : TateAlgebra σ k → A) = g := by
    exact DenseRange.equalizer (MvPolynomial.toTate_denseRange σ k) hfcont hgcont hpoly_fun
  exact AlgHom.ext fun x => by simpa using congrArg (fun h : TateAlgebra σ k → A => h x) hfg_fun

end IsStrictAffinoid
