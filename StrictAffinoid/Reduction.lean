/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import StrictAffinoid.Integer

public section

open Valued NormedField Filter IsStrictAffinoid

open scoped Topology

variable {k : Type*} [NormedField k] [IsUltrametricDist k] [CompleteSpace k]
  {A : Type*} [NormedCommRing A] [NormedAlgebra k A] [IsStrictAffinoid k A]

omit [CompleteSpace k] in
theorem Valued.mem_maximalIdeal_iff_norm_lt_one (x : 𝒪[k]) : x ∈ 𝓂[k] ↔ ‖x‖ < 1 :=
  (IsLocalRing.mem_maximalIdeal x).trans Valuation.Integer.not_isUnit_iff_valuation_lt_one

omit [CompleteSpace k] in
theorem Valued.mem_maximalIdeal_iff_norm_lt_one' (x : 𝒪[k]) : x ∈ 𝓂[k] ↔ ‖x.val‖ < 1 :=
  mem_maximalIdeal_iff_norm_lt_one x

namespace IsStrictAffinoid

noncomputable instance : IsLinearTopology (Integer k A) (Integer k A) := by
  let J : ℝ → Ideal (Integer k A) := fun ε ↦
    if hε : 0 < ε then
      { carrier := {x | ‖x‖ < ε}
        zero_mem' := by simpa using hε
        add_mem' := by
          intro x y hx hy
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
        smul_mem' := by
          intro a b hb
          refine lt_of_le_of_lt
            (calc
              ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
              _ ≤ 1 * ‖b‖ := by gcongr; exact a.2
              _ = ‖b‖ := by ring)
            hb }
    else ⊥
  refine IsLinearTopology.mk_of_hasBasis' (Integer k A) (p := fun ε : ℝ ↦ 0 < ε) (s := J) ?_ ?_
  · exact Metric.nhds_basis_ball.congr (fun ε ↦ Iff.rfl) (fun ε hε ↦ by
      ext x
      simp [J, hε, Metric.ball, dist_eq_norm])
  · intro I r m
    exact I.smul_mem r

variable (k A) in
/-- `A°°`, the set of elements with spectral norm `< 1`. -/
noncomputable def topNil : Ideal (Integer k A) := topologicalNilradical (Integer k A)

theorem mem_topologicalNilradical_iff_norm_lt_one (a : Integer k A) :
    a ∈ topNil k A ↔ ‖a‖ < 1 := by
  constructor
  · intro ha
    obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
    have hn' : ‖(a.1 ^ n : A)‖ < 1 := by simpa [Metric.ball, dist_eq_norm] using hn
    have hpow : ‖a‖ ^ n < 1 := by simpa [IsStrictAffinoid.withSpectralNorm k n a.1] using hn'
    by_contra h
    exact (not_lt_of_ge (one_le_pow₀ (le_of_not_gt h))) hpow
  · exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one

theorem mem_topologicalNilradical_iff_norm_lt_one' (a : Integer k A) :
    a ∈ topNil k A ↔ ‖a.val‖ < 1 :=
  mem_topologicalNilradical_iff_norm_lt_one a

variable (k A)

theorem topNil_isRadical : (topNil k A).IsRadical := by
  refine (Ideal.isRadical_iff_pow_one_lt 2 Nat.one_lt_two).mpr (fun a ha ↦ ?_)
  rw [mem_topologicalNilradical_iff_norm_lt_one] at ha ⊢
  have ha' : ‖a.1 ^ 2‖ < 1 := ha
  have hpow : ‖a.1‖ ^ 2 < 1 := by simpa [IsStrictAffinoid.withSpectralNorm k 2 a.1] using ha'
  by_contra hlt
  exact (not_lt_of_ge (one_le_pow₀ (le_of_not_gt hlt))) hpow

@[expose] public section

/-- $\widetilde{A} := A^{\circ} / A^{\circ\circ}$ is the reduction of the
strict affinoid algebra $A$. -/
def Reduction : Type _ := Integer k A ⧸ topNil k A

section inst

deriving noncomputable instance CommRing for Reduction

noncomputable instance : Algebra (Integer k A) (Reduction k A) :=
  inferInstanceAs (Algebra (Integer k A) (Integer k A ⧸ topNil k A))

instance : (topNil k A).LiesOver 𝓂[k] := by
  constructor
  ext x
  change x ∈ 𝓂[k] ↔ algebraMap 𝒪[k] (Integer k A) x ∈ topNil k A
  rw [Valued.mem_maximalIdeal_iff_norm_lt_one',
    IsStrictAffinoid.mem_topologicalNilradical_iff_norm_lt_one]
  rw [show ‖algebraMap 𝒪[k] (Integer k A) x‖ = ‖(algebraMap k A x : A)‖ by rfl]
  rw [norm_algebraMap A (x : k), norm_one, mul_one]

noncomputable instance : Algebra 𝓀[k] (Reduction k A) :=
  Ideal.Quotient.algebraOfLiesOver (topNil k A) 𝓂[k]

instance : IsReduced (Reduction k A) :=
  (Ideal.isRadical_iff_quotient_reduced (topNil k A)).1 (topNil_isRadical k A)

end inst

/-- The canonical reduction map from $A^{\circ}$ to the reduction $\widetilde{A}$. -/
noncomputable abbrev reductionMap : Integer k A →+* Reduction k A :=
  Ideal.Quotient.mk (topNil k A)

end

end IsStrictAffinoid

@[expose] public section

namespace AlgHom

variable {B : Type*} [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B] {f : A →ₐ[k] B}

/-- $\widetide{f} : \widetilde{A} → \widetilde{B}$ is the reduction of $f$. -/
noncomputable def reduction : Reduction k A →+* Reduction k B :=
  Ideal.quotientMap (topNil k B) (IsStrictAffinoid.integerMap f).toRingHom <| by
    intro a ha
    simp only [mem_topologicalNilradical_iff_norm_lt_one, Ideal.mem_comap] at ha ⊢
    exact lt_of_le_of_lt ((isContractiveHom f) a.1) ha

theorem reduction_ker_isRadical : (RingHom.ker f.reduction).IsRadical :=
  Ideal.IsRadical.comap f.reduction Ideal.isRadical_bot

end AlgHom

namespace TateAlgebra

variable (σ : Type*) [Finite σ] (k : Type*) [NormedField k] [IsUltrametricDist k] [CompleteSpace k]

noncomputable abbrev mvPolynomialToReduction :
    MvPolynomial σ 𝒪[k] →+* Reduction k (TateAlgebra σ k) :=
  (reductionMap k (TateAlgebra σ k)).comp <| (integerEquiv σ k).toRingHom.comp <|
    @MvPolynomial.toTate σ 𝒪[k] _ _

private theorem norm_integerEquiv_toTate_lt_one_iff (p : MvPolynomial σ 𝒪[k]) :
    ‖((integerEquiv σ k) (MvPolynomial.toTate p)).1‖ < 1 ↔
      ∀ m : σ →₀ ℕ, ‖↑(MvPolynomial.coeff m p)‖ < 1 := by
  let F : TateAlgebra σ k := ((integerEquiv σ k) p.toTate).1
  have hcoeff (m : σ →₀ ℕ) : ‖MvPowerSeries.coeff m F.1‖ = ‖↑(MvPolynomial.coeff m p)‖ := by
    change ‖MvPowerSeries.coeff m p.toTate.1‖ = _
    simp [MvPolynomial.toTate_coe]
  constructor
  · intro h m
    calc _ = ‖MvPowerSeries.coeff m F.1‖ := by rw [hcoeff]
      _ ≤ ‖F‖ := TateAlgebra.coeff_norm_le F m
      _ < 1 := h
  · intro h
    by_cases hF : F = 0
    · simp [F, hF]
    · obtain ⟨m, hm⟩ := TateAlgebra.exists_coeff_norm_eq_norm F hF
      calc ‖F‖ = ‖MvPowerSeries.coeff m F.1‖ := hm.symm
        _ = ‖MvPolynomial.coeff m p‖ := hcoeff m
        _ < 1 := h m

theorem mvPolynomialToReduction_surjective : Function.Surjective (mvPolynomialToReduction σ k) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  let F : TateAlgebra σ 𝒪[k] := (integerEquiv σ k).symm x
  rcases Metric.mem_closure_iff.mp (MvPolynomial.toTate_denseRange σ 𝒪[k] F) 1 zero_lt_one with
    ⟨G, hG, hdist⟩
  rcases hG with ⟨p, rfl⟩
  refine ⟨p, ?_⟩
  rw [mvPolynomialToReduction, reductionMap]
  apply Ideal.Quotient.eq.2
  have hx : x = (integerEquiv σ k) F := by simp [F]
  have hdist' : dist (MvPolynomial.toTate p : TateAlgebra σ 𝒪[k]) F < 1 := by
    simpa [dist_comm] using hdist
  simpa [mem_topologicalNilradical_iff_norm_lt_one, hx, dist_eq_norm] using hdist'

theorem mvPolynomialToReduction_ker :
    RingHom.ker (mvPolynomialToReduction σ k) = 𝓂[k].map MvPolynomial.C := by
  ext p
  change ((Ideal.Quotient.mk (topNil k (TateAlgebra σ k))) ((integerEquiv σ k) p.toTate) = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [mem_topologicalNilradical_iff_norm_lt_one, MvPolynomial.mem_map_C_iff]
  simp_rw [Valued.mem_maximalIdeal_iff_norm_lt_one]
  exact norm_integerEquiv_toTate_lt_one_iff σ k p

noncomputable def reductionEquiv : MvPolynomial σ 𝓀[k] ≃+* Reduction k (TateAlgebra σ k) :=
  (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) 𝓂[k]).toRingEquiv.trans <|
    (Ideal.quotEquivOfEq (mvPolynomialToReduction_ker σ k).symm).trans <|
      (mvPolynomialToReduction σ k).quotientKerEquivOfSurjective
        (mvPolynomialToReduction_surjective σ k)

instance : IsNoetherianRing (Reduction k (TateAlgebra σ k)) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial σ 𝓀[k]) (reductionEquiv σ k)

end TateAlgebra

namespace Ideal

variable (k)

/-- `I° := I \cap A°`. -/
noncomputable def integer (I : Ideal A) : Ideal (Integer k A) :=
  Ideal.comap (algebraMap ((Integer k A)) A) I

/-- The reduction of an ideal `\widetide{I}` is the image of `I°` in the
reduction `\widetilde{A}`. -/
noncomputable def reduction (I : Ideal A) : Ideal (Reduction k A) :=
  Ideal.map (reductionMap k A) (I.integer k)

end Ideal
