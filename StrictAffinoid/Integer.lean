/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuedField
public import StrictAffinoid.Contractive

@[expose] public section

open Valued NormedField Filter TateAlgebra

open scoped Topology

variable {σ : Type*} (s : σ) {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {A B : Type*} [NormedCommRing A] [NormedAlgebra k A]
  [IsStrictAffinoid k A] [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B]

instance : IsLocalRing 𝒪[k] := ValuationRing.isLocalRing _

namespace IsStrictAffinoid

section integer

variable (k A B)

/-- The subalgebra `A° := { a | ρ(a) ≤ 1 }`. -/
def integerSubalgebra : Subalgebra 𝒪[k] A where
  carrier := {a : A | ‖a‖ ≤ 1}
  mul_mem' {a} {b} ha hb :=
    (norm_mul_le a b).trans (by simpa using mul_le_mul ha hb (norm_nonneg _) zero_le_one)
  add_mem' {a} {b} ha hb :=
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  algebraMap_mem' r := by
    apply (norm_algebraMap A r.1).trans_le
    simp only [norm_one, mul_one]
    exact r.2

variable {k A} in
@[simp]
lemma mem_integerSubalgebra_iff (a : A) : a ∈ integerSubalgebra k A ↔ ‖a‖ ≤ 1 := Iff.rfl

/-- The ring of integers `A°` of a strict affinoid algebra `A`, consisting of power-bounded
elements which is defined as elements `a ∈ A` satisfying `ρ(a) ≤ 1`. -/
def Integer : Type _ := integerSubalgebra k A

variable {A} in
/-- Constructor for an element in the ring of integers `A°`. -/
def Integer.mk (a : A) (ha : ‖a‖ ≤ 1) : Integer k A := ⟨a, ha⟩

deriving noncomputable instance NormedCommRing, IsUltrametricDist for Integer

section inst

noncomputable instance : Algebra 𝒪[k] (Integer k A) :=
  inferInstanceAs (Algebra 𝒪[k] (integerSubalgebra k A))

noncomputable instance : Algebra (Integer k A) A :=
  inferInstanceAs (Algebra (integerSubalgebra k A) A)

instance : IsScalarTower 𝒪[k] (Integer k A) A :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower 𝒪[k] k A := IsScalarTower.of_algebraMap_eq' rfl

end inst

section simp

variable {k A}

lemma integer_norm_le (a : Integer k A) : ‖a‖ ≤ 1 := a.2

@[simp]
lemma integer_zero_val : (0 : Integer k A).val = 0 := rfl

@[simp]
lemma integer_one_val : (1 : Integer k A).val = 1 := rfl

@[simp]
lemma integer_add_val (F G : Integer k A) : (F + G).val = F.val + G.val := rfl

@[simp]
lemma integer_mul_val (F G : Integer k A) : (F * G).val = F.val * G.val := rfl

@[simp]
lemma integer_pow_val (F : Integer k A) (n : ℕ) : (F ^ n).val = F.val ^ n := rfl

@[simp]
lemma integer_neg_val (F : Integer k A) : (- F).val = - F.val := rfl

@[simp]
lemma integer_sub_val (F G : Integer k A) : (F - G).val = F.val - G.val := rfl

@[simp]
lemma integer_algebraMap_val (r : 𝒪[k]) :
    (algebraMap 𝒪[k] (Integer k A) r).val = algebraMap 𝒪[k] A r := rfl

end simp

variable {k A B} in
/-- The induced morphism `f° : A° → B°` on rings of integers for a contractive morphism. -/
noncomputable def integerMap (f : A →ₐ[k] B) : Integer k A →ₐ[𝒪[k]] Integer k B :=
  ((f.restrictScalars 𝒪[k]).comp (integerSubalgebra k A).val).codRestrict
    (integerSubalgebra k B) <| fun a ↦ ((isContractiveHom f) a).trans a.2

section inst

noncomputable instance integer_algebra [Algebra A B] [IsScalarTower k A B] :
    Algebra (Integer k A) (Integer k B) :=
  (integerMap (IsScalarTower.toAlgHom k A B)).toRingHom.toAlgebra

instance integer_isBoundedSMul [Algebra A B] [IsScalarTower k A B] :
    IsBoundedSMul (Integer k A) (Integer k B) := by
  refine IsBoundedSMul.of_norm_smul_le <| fun a b ↦ ?_
  calc _ ≤ ‖algebraMap (Integer k A) (Integer k B) a‖ * ‖b‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * ‖b‖ := by
      gcongr
      exact isContractiveHom (IsScalarTower.toAlgHom k A B) a.1

end inst

end integer

lemma norm_finset_sum_le_of_forall_le {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
    {ι : Type*} {s : Finset ι} {f : ι → A} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, i ∈ s → ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simpa using hC
  · intro a s ha ih h
    simpa [Finset.sum_insert ha] using (IsUltrametricDist.norm_add_le_max _ _).trans <|
      max_le (h a (by simp)) (ih (fun b hb ↦ h b (by simp [hb])))

lemma norm_prod_pow_le_one {σ : Type*} (a : σ → Integer k A) (d : σ →₀ ℕ) :
    ‖d.prod (fun s e ↦ ((a s).1 ^ e))‖ ≤ 1 := by
  classical
  unfold Finsupp.prod
  refine Finset.induction_on d.support ?_ ?_
  · simp
  · intro s t hs ih
    have hs' : ‖((a s).1 ^ d s)‖ ≤ 1 := by
      rw [IsStrictAffinoid.withSpectralNorm k (d s) (a s).1]
      exact pow_le_one₀ (norm_nonneg _) (a s).2
    have hprod :
        ‖∏ x ∈ insert s t, (a x).1 ^ d x‖ =
          ‖((a s).1 ^ d s) * ∏ x ∈ t, (a x).1 ^ d x‖ := by
      rw [Finset.prod_insert hs]
    have hmul :
        ‖((a s).1 ^ d s) * ∏ x ∈ t, (a x).1 ^ d x‖ ≤
          ‖((a s).1 ^ d s)‖ * ‖∏ x ∈ t, (a x).1 ^ d x‖ := norm_mul_le _ _
    have hle : ‖((a s).1 ^ d s)‖ * ‖∏ x ∈ t, (a x).1 ^ d x‖ ≤ 1 * 1 := by
      gcongr
    have hone : (1 : ℝ) * 1 = 1 := by ring
    exact hprod.trans_le (hmul.trans (hle.trans_eq hone))

lemma eval_monomial_norm_le {σ : Type*} (a : σ → Integer k A)
    (d : σ →₀ ℕ) (c : k) :
    ‖(MvPolynomial.aeval fun s ↦ (a s).1) (MvPolynomial.monomial d c)‖ ≤ ‖c‖ := by
  have halg : ‖algebraMap k A c‖ ≤ ‖c‖ := by
    rw [norm_algebraMap A c, norm_one, mul_one]
  have hmono :
      ‖(MvPolynomial.aeval fun s ↦ (a s).1) (MvPolynomial.monomial d c)‖ =
        ‖algebraMap k A c * d.prod (fun s e ↦ ((a s).1 ^ e))‖ := by
    rw [MvPolynomial.aeval_monomial]
  have hmul :
      ‖algebraMap k A c * d.prod (fun s e ↦ ((a s).1 ^ e))‖ ≤
        ‖algebraMap k A c‖ * ‖d.prod (fun s e ↦ ((a s).1 ^ e))‖ := norm_mul_le _ _
  have hle : ‖algebraMap k A c‖ * ‖d.prod (fun s e ↦ ((a s).1 ^ e))‖ ≤ ‖c‖ * 1 :=
    mul_le_mul halg (norm_prod_pow_le_one a d) (norm_nonneg _) (norm_nonneg _)
  exact hmono.trans_le (hmul.trans (hle.trans_eq (by rw [mul_one])))

lemma eval_poly_norm_le {σ : Type*} (a : σ → IsStrictAffinoid.Integer k A) (p : MvPolynomial σ k) :
    ‖(MvPolynomial.aeval fun s ↦ (a s).1) p‖ ≤ ‖p.toTate‖ := by
  let ε : MvPolynomial σ k →ₐ[k] A := MvPolynomial.aeval fun s ↦ (a s).1
  have hsum :
      ε p = ∑ d ∈ p.support, ε (MvPolynomial.monomial d (MvPolynomial.coeff d p)) := by
    have hsum0 :
        ε p = ε (∑ d ∈ p.support, MvPolynomial.monomial d (MvPolynomial.coeff d p)) :=
      congrArg ε (MvPolynomial.as_sum p)
    have hsum1 :
        ε (∑ d ∈ p.support, MvPolynomial.monomial d (MvPolynomial.coeff d p)) =
          ∑ d ∈ p.support, ε (MvPolynomial.monomial d (MvPolynomial.coeff d p)) := by
      simp only [map_sum]
    exact hsum0.trans hsum1
  rw [hsum]
  refine norm_finset_sum_le_of_forall_le (norm_nonneg _) ?_
  intro d hd
  have hmono :
      ‖ε (MvPolynomial.monomial d (MvPolynomial.coeff d p))‖ ≤
        ‖MvPolynomial.coeff d p‖ := eval_monomial_norm_le a d (MvPolynomial.coeff d p)
  have hcoeff : ‖MvPolynomial.coeff d p‖ ≤ ‖p.toTate‖ := by
    have hbound :
        BddAbove (Set.range fun e : σ →₀ ℕ ↦
          ‖MvPowerSeries.coeff e p.toMvPowerSeries‖) := by
      refine ⟨max 0 (∑ e ∈ p.support, ‖MvPolynomial.coeff e p‖), ?_⟩
      rintro y ⟨e, rfl⟩
      by_cases he : e ∈ p.support
      · exact le_trans
          (by
            simpa [MvPolynomial.coeff_coe] using
              (Finset.single_le_sum (fun x hx ↦ norm_nonneg (MvPolynomial.coeff x p)) he :
                ‖MvPolynomial.coeff e p‖ ≤ ∑ x ∈ p.support, ‖MvPolynomial.coeff x p‖))
          (le_max_right _ _)
      · have hzero : MvPolynomial.coeff e p = 0 := MvPolynomial.notMem_support_iff.mp he
        simp [MvPolynomial.coeff_coe, hzero]
    rw [TateAlgebra.norm_def, gaussNorm, MvPolynomial.toTate_coe p]
    simpa [MvPolynomial.coeff_coe] using
      (le_ciSup hbound d : ‖MvPowerSeries.coeff d p.toMvPowerSeries‖ ≤
        ⨆ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e p.toMvPowerSeries‖)
  exact le_trans hmono hcoeff

lemma exists_tateAlgHom_of_powerbounded
    {σ : Type*} (a : σ → IsStrictAffinoid.Integer k A) :
    ∃ φ : TateAlgebra σ k →ₐ[k] A, ∀ s : σ, φ (TateAlgebra.X s) = (a s).1 := by
  let polyMetric : PseudoMetricSpace (MvPolynomial σ k) :=
    PseudoMetricSpace.induced MvPolynomial.toTate inferInstance
  let : UniformSpace (MvPolynomial σ k) := polyMetric.toUniformSpace
  let polyEval : MvPolynomial σ k →ₐ[k] A := MvPolynomial.aeval fun s ↦ (a s).1
  have hPolyToTate : IsUniformInducing (MvPolynomial.toTate (σ := σ) (R := k)) := by
    rw [isUniformInducing_iff_uniformSpace]
    rfl
  have hPolyEvalLip : LipschitzWith 1 polyEval := by
    refine LipschitzWith.mk_one ?_
    intro p q
    have hdist :
        dist (polyEval p) (polyEval q) = ‖polyEval (p - q)‖ := by
      simp [dist_eq_norm]
    have hle : ‖polyEval (p - q)‖ ≤ ‖(p - q).toTate‖ := eval_poly_norm_le a (p - q)
    have htate : ‖(p - q).toTate‖ = dist p q := by
      rw [show dist p q = dist p.toTate q.toTate by rfl, dist_eq_norm, map_sub]
    exact hdist.trans_le (hle.trans_eq htate)
  let φRing : TateAlgebra σ k →+* A :=
    IsDenseInducing.extendRingHom hPolyToTate
      (MvPolynomial.toTate_denseRange σ k) hPolyEvalLip.uniformContinuous
  have hφRing_poly (p : MvPolynomial σ k) :
      φRing p.toTate = polyEval p := by
    exact IsDenseInducing.extend_eq
      (hPolyToTate.isDenseInducing (MvPolynomial.toTate_denseRange σ k))
        hPolyEvalLip.uniformContinuous.continuous p
  let φ : TateAlgebra σ k →ₐ[k] A :=
    { toRingHom := φRing
      commutes' := by
        intro r
        simpa [polyEval, MvPolynomial.toTate] using hφRing_poly (MvPolynomial.C r) }
  refine ⟨φ, ?_⟩
  intro s
  simpa [φ, polyEval, MvPolynomial.toTate_X] using hφRing_poly (MvPolynomial.X s)

end IsStrictAffinoid

namespace TateAlgebra

open IsStrictAffinoid

variable (σ : Type*) [Finite σ] (k : Type*) [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

/-- The canonical ring equivalence between the Tate algebra over the valuation ring `𝒪[k]`
and the ring of integers of the Tate algebra over the field `k`. -/
noncomputable def integerEquiv : TateAlgebra σ 𝒪[k] ≃+* Integer k (TateAlgebra σ k) where
  __ :=
    let f : TateAlgebra σ 𝒪[k] →+* TateAlgebra σ k :=
      (MvPowerSeries.map 𝒪[k].subtype).restrict _ _ (fun _ h ↦ h)
    f.codRestrict _ <| fun x ↦ by
      simpa [norm_def, gaussNorm] using ciSup_le (fun e ↦ ((MvPowerSeries.coeff e) x.1).2)
  invFun x :=
    ⟨fun e ↦ ⟨MvPowerSeries.coeff e x.1.1, (TateAlgebra.coeff_norm_le x.1 e).trans x.2⟩, x.1.2⟩
  left_inv _ := rfl

end TateAlgebra
