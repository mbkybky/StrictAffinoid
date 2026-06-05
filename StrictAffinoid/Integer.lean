/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuedField
public import StrictAffinoid.Contractive

@[expose] public section

open Valued NormedField Filter

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
  add_mem' {a} {b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  algebraMap_mem' r := (norm_algebraMap' A r.1).trans_le r.2

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

lemma Integer.norm_eq {a : Integer k A} : ‖a‖ = ‖a.val‖ := rfl

lemma Integer.norm_le {a : Integer k A} : ‖a‖ ≤ 1 := a.2

lemma Integer.algebraMap_eq_val {a : Integer k A} : algebraMap (Integer k A) A a = a.val := rfl

@[simp]
lemma Integer.zero_val : (0 : Integer k A).val = 0 := rfl

@[simp]
lemma Integer.one_val : (1 : Integer k A).val = 1 := rfl

@[simp]
lemma Integer.add_val (F G : Integer k A) : (F + G).val = F.val + G.val := rfl

@[simp]
lemma Integer.mul_val (F G : Integer k A) : (F * G).val = F.val * G.val := rfl

@[simp]
lemma Integer.pow_val (F : Integer k A) (n : ℕ) : (F ^ n).val = F.val ^ n := rfl

@[simp]
lemma Integer.neg_val (F : Integer k A) : (- F).val = - F.val := rfl

@[simp]
lemma Integer.sub_val (F G : Integer k A) : (F - G).val = F.val - G.val := rfl

@[simp]
lemma Integer.algebraMap_val (r : 𝒪[k]) :
    (algebraMap 𝒪[k] (Integer k A) r).val = algebraMap 𝒪[k] A r := rfl

end simp

section integerMap

variable {k A B}

/-- The induced morphism `f° : A° → B°` on rings of integers for a contractive morphism. -/
noncomputable def integerMap (f : A →ₐ[k] B) : Integer k A →ₐ[𝒪[k]] Integer k B :=
  ((f.restrictScalars 𝒪[k]).comp (integerSubalgebra k A).val).codRestrict
    (integerSubalgebra k B) <| fun a ↦ ((isContractiveHom f) a).trans a.2

lemma integerMap_val (f : A →ₐ[k] B) (a : Integer k A) : (integerMap f a).val = f a.val := rfl

end integerMap

section inst

noncomputable instance Integer.algebra [Algebra A B] [IsScalarTower k A B] :
    Algebra (Integer k A) (Integer k B) :=
  (integerMap (IsScalarTower.toAlgHom k A B)).toRingHom.toAlgebra

instance Integer.isBoundedSMul [Algebra A B] [IsScalarTower k A B] :
    IsBoundedSMul (Integer k A) (Integer k B) := by
  refine IsBoundedSMul.of_norm_smul_le <| fun a b ↦ (norm_mul_le _ b).trans ?_
  gcongr
  exact isContractiveHom (IsScalarTower.toAlgHom k A B) a.1

end inst

end integer

lemma norm_finset_sum_le_of_forall_le {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
    {ι : Type*} {s : Finset ι} {f : ι → A} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, i ∈ s → ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

lemma norm_prod_pow_le_one {σ : Type*} (a : σ → Integer k A) (d : σ →₀ ℕ) :
    ‖d.prod (fun s e ↦ ((a s).1 ^ e))‖ ≤ 1 :=
  (Finset.norm_prod_le d.support fun s ↦ (a s).1 ^ d s).trans <|
    Finset.prod_le_one (fun s _ ↦ norm_nonneg _) fun s _ ↦ by
      grw [IsStrictAffinoid.withSpectralNorm k, pow_le_one₀ (norm_nonneg _) (a s).2]

lemma eval_monomial_norm_le {σ : Type*} (a : σ → Integer k A) (d : σ →₀ ℕ) (c : k) :
    ‖(MvPolynomial.aeval fun s ↦ (a s).1) (MvPolynomial.monomial d c)‖ ≤ ‖c‖ := by
  grw [MvPolynomial.aeval_monomial, norm_mul_le, norm_algebraMap', norm_prod_pow_le_one, mul_one]

lemma eval_poly_norm_le {σ : Type*} (a : σ → IsStrictAffinoid.Integer k A) (p : MvPolynomial σ k) :
    ‖(MvPolynomial.aeval fun s ↦ (a s).1) p‖ ≤ ‖p.toTate‖ := by
  let ε : MvPolynomial σ k →ₐ[k] A := MvPolynomial.aeval fun s ↦ (a s).1
  rw [show ε p = ∑ d ∈ p.support, ε (MvPolynomial.monomial d (MvPolynomial.coeff d p)) by
    simp only [map_sum, congrArg ε (MvPolynomial.as_sum p)]]
  refine norm_finset_sum_le_of_forall_le (norm_nonneg _) fun d _ ↦ ?_
  grw [eval_monomial_norm_le a d (MvPolynomial.coeff d p),
    show ‖MvPolynomial.coeff d p‖ ≤ ‖p.toTate‖ by
      simpa [MvPolynomial.coeff_coe, MvPolynomial.toTate_coe] using p.toTate.coeff_norm_le d]

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
  have hPolyEvalLip : LipschitzWith 1 polyEval := LipschitzWith.mk_one fun p q ↦ by
    simpa [polyEval, map_sub, dist_eq_norm, show dist p q = dist p.toTate q.toTate by rfl] using
      eval_poly_norm_le a (p - q)
  let φRing : TateAlgebra σ k →+* A :=
    IsDenseInducing.extendRingHom hPolyToTate
      (MvPolynomial.toTate_denseRange σ k) hPolyEvalLip.uniformContinuous
  have hφ (p : MvPolynomial σ k) : φRing p.toTate = polyEval p :=
    IsDenseInducing.extend_eq
      (hPolyToTate.isDenseInducing (MvPolynomial.toTate_denseRange σ k))
        hPolyEvalLip.uniformContinuous.continuous p
  let φ : TateAlgebra σ k →ₐ[k] A :=
    { toRingHom := φRing
      commutes' r := by simpa [polyEval, MvPolynomial.toTate] using hφ (MvPolynomial.C r) }
  exact ⟨φ, fun s ↦ by simpa [φ, polyEval, MvPolynomial.toTate_X] using hφ (MvPolynomial.X s)⟩

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
