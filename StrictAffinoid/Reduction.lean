/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import StrictAffinoid.Integer

@[expose] public section

open Valued NormedField IsStrictAffinoid

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
          exact lt_of_le_of_lt (by simpa using norm_mul_le_of_le (a₂ := b.1) a.2 le_rfl) hb }
    else ⊥
  refine IsLinearTopology.mk_of_hasBasis' (Integer k A) (p := fun ε : ℝ ↦ 0 < ε) (s := J)
    (Metric.nhds_basis_ball.congr (fun _ ↦ Iff.rfl) (fun ε hε ↦ ?_)) (fun I r m ↦ I.smul_mem r)
  ext
  simp [J, hε, Metric.ball, dist_eq_norm]

variable (k A) in
/-- `A°°`, the set of elements with spectral norm `< 1`. -/
@[no_expose]
noncomputable def topNil : Ideal (Integer k A) := topologicalNilradical (Integer k A)

theorem mem_topNil_iff (a : Integer k A) :
    a ∈ topNil k A ↔ ‖a‖ < 1 := by
  constructor
  · intro ha
    obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
    have hn' : ‖a.1 ^ n‖ < 1 := by simpa [Metric.ball, dist_eq_norm] using! hn
    have hpow : ‖a‖ ^ n < 1 := by simpa [IsStrictAffinoid.withSpectralNorm k] using! hn'
    exact lt_of_not_ge fun h ↦ hpow.not_ge (one_le_pow₀ h)
  · exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one

theorem mem_topNil_iff' (a : Integer k A) :
    a ∈ topNil k A ↔ ‖a.val‖ < 1 :=
  mem_topNil_iff a

variable (k A)

theorem topNil_isRadical : (topNil k A).IsRadical := by
  refine (Ideal.isRadical_iff_pow_one_lt 2 Nat.one_lt_two).mpr (fun a ha ↦ ?_)
  rw [mem_topNil_iff'] at ha ⊢
  have hpow : ‖a.1‖ ^ 2 < 1 := by simpa [IsStrictAffinoid.withSpectralNorm k] using ha
  exact lt_of_not_ge fun hlt ↦ hpow.not_ge (one_le_pow₀ hlt)

variable {k A} in
lemma integer_isUnit_one_sub_of_norm_lt_one (x : Integer k A) (hx : ‖x‖ < 1) : IsUnit (1 - x) := by
  have hxA : ‖x.1‖ < 1 := hx
  rcases isUnit_one_sub_of_norm_lt_one hxA with ⟨u, hu⟩
  have hv_le : ‖u⁻¹.1‖ ≤ 1 := by
    refine le_of_not_gt fun hv_gt ↦ ?_
    have hx_mul_lt : ‖x.1‖ * ‖u⁻¹.1‖ < ‖u⁻¹.1‖ := by
      simpa using mul_lt_mul_of_pos_right hxA (zero_lt_one.trans hv_gt)
    have hv_eq : u⁻¹.1 = 1 + x.1 * u⁻¹.1 := by
      simpa [sub_eq_iff_eq_add, sub_mul, hu] using Units.val_inv u
    have hle : ‖u⁻¹.1‖ ≤ max 1 (‖x.1‖ * ‖u⁻¹.1‖) := (congrArg norm hv_eq).trans_le <|
      (IsUltrametricDist.norm_add_le_max 1 _).trans (max_le_max (by simp) (norm_mul_le _ _))
    exact hle.not_gt (max_lt hv_gt hx_mul_lt)
  exact ⟨⟨1 - x, ⟨u⁻¹.1, hv_le⟩, Subtype.ext (by simp [hu]), Subtype.ext (by simp [hu])⟩, rfl⟩

theorem topNil_le_jacobson : topNil k A ≤ (⊥ : Ideal (Integer k A)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hx_lt : ‖x‖ < 1 := (mem_topNil_iff x).1 hx
  have hxy_lt : ‖x * y‖ < 1 := (norm_mul_le x y).trans_lt <|
    (mul_le_mul_of_nonneg_left y.2 (norm_nonneg x)).trans_lt <| by
      simpa using mul_lt_mul_of_pos_right hx_lt zero_lt_one
  simpa [sub_eq_add_neg, add_comm, mul_comm] using
    integer_isUnit_one_sub_of_norm_lt_one (- (x * y)) (by simpa using hxy_lt)

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
  rw [Valued.mem_maximalIdeal_iff_norm_lt_one', mem_topNil_iff]
  rw [show ‖algebraMap 𝒪[k] (Integer k A) x‖ = ‖(algebraMap k A x : A)‖ by rfl, norm_algebraMap' A]

noncomputable instance : Algebra 𝓀[k] (Reduction k A) :=
  Ideal.Quotient.algebraOfLiesOver (topNil k A) 𝓂[k]

instance : IsReduced (Reduction k A) :=
  (Ideal.isRadical_iff_quotient_reduced (topNil k A)).1 (topNil_isRadical k A)

end inst

/-- The canonical reduction map from $A^{\circ}$ to the reduction $\widetilde{A}$. -/
noncomputable abbrev reductionMap : Integer k A →+* Reduction k A := Ideal.Quotient.mk (topNil k A)

end IsStrictAffinoid

namespace AlgHom

variable {B : Type*} [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B] {f : A →ₐ[k] B}

/-- $\widetide{f} : \widetilde{A} → \widetilde{B}$ is the reduction of $f$. -/
noncomputable def reduction : Reduction k A →+* Reduction k B :=
  Ideal.quotientMap (topNil k B) (IsStrictAffinoid.integerMap f).toRingHom <| by
    intro a ha
    simp only [mem_topNil_iff, Ideal.mem_comap] at ha ⊢
    exact lt_of_le_of_lt ((isContractiveHom f) a.1) ha

theorem reduction_ker_isRadical : (RingHom.ker f.reduction).IsRadical :=
  Ideal.isRadical_bot.comap f.reduction

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
    simp [← hcoeff, (TateAlgebra.coeff_norm_le F m).trans_lt h]
  · intro h
    obtain ⟨m, hm⟩ := TateAlgebra.exists_coeff_norm_eq_norm F
    exact hm ▸ (hcoeff m).symm ▸ h m

theorem mvPolynomialToReduction_surjective : Function.Surjective (mvPolynomialToReduction σ k) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  let F : TateAlgebra σ 𝒪[k] := (integerEquiv σ k).symm x
  obtain ⟨-, ⟨p, rfl⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (MvPolynomial.toTate_denseRange σ 𝒪[k] F) 1 zero_lt_one
  refine ⟨p, ?_⟩
  rw [mvPolynomialToReduction, reductionMap]
  apply Ideal.Quotient.eq.2
  simpa [mem_topNil_iff, F, dist_eq_norm] using!
    (show dist p.toTate F < 1 by simpa [dist_comm] using hdist)

theorem mvPolynomialToReduction_ker :
    RingHom.ker (mvPolynomialToReduction σ k) = 𝓂[k].map MvPolynomial.C := by
  ext p
  change ((Ideal.Quotient.mk (topNil k (TateAlgebra σ k))) ((integerEquiv σ k) p.toTate) = 0) ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_topNil_iff]
  simp_rw [MvPolynomial.mem_map_C_iff, Valued.mem_maximalIdeal_iff_norm_lt_one]
  exact norm_integerEquiv_toTate_lt_one_iff σ k p

noncomputable def reductionEquiv : MvPolynomial σ 𝓀[k] ≃+* Reduction k (TateAlgebra σ k) :=
  (MvPolynomial.quotientEquivQuotientMvPolynomial 𝓂[k]).toRingEquiv.trans <|
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
  Ideal.comap (algebraMap (Integer k A) A) I

lemma integer_mem_iff (a : Integer k A) {I : Ideal A} : a ∈ I.integer k ↔ a.1 ∈ I := Iff.rfl

/-- The reduction of an ideal `\widetide{I}` is the image of `I°` in the
reduction `\widetilde{A}`. -/
noncomputable abbrev reduction (I : Ideal A) : Ideal (Reduction k A) :=
  Ideal.map (reductionMap k A) (I.integer k)

lemma reduction_mem_iff (z : Reduction k A) {I : Ideal A} :
    z ∈ I.reduction k ↔ ∃ (a : Integer k A) (_ : a ∈ I.integer k), reductionMap k A a = z := by
  apply (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).trans
  simp only [exists_prop]
  rfl

end Ideal

section ker

variable {B : Type*} [NormedCommRing B] [NormedAlgebra k B] [IsStrictAffinoid k B] {f : A →ₐ[k] B}

lemma exists_topNil_lift_pow_of_image_topNil (hf : IsAdmissibleHom f) {a : Integer k A}
    (ha : (integerMap f) a ∈ topNil k B) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : Integer k A, b ∈ topNil k A ∧
      (integerMap f) b = (integerMap f) (a ^ n) := by
  have ha_lt : ‖f a.1‖ < 1 := by
    simpa [mem_topNil_iff] using! ha
  rcases hf with ⟨C, hCpos, hC⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hCpos) ha_lt
  let n : ℕ := m + 1
  have hpow_lt : ‖f a.1‖ ^ (m + 1) < C⁻¹ := by
    grw [pow_succ, mul_le_mul_of_nonneg_left ha_lt.le (pow_nonneg (norm_nonneg _) m)]
    simp [hm]
  have hlt : sInf (preImageNormSet f (f (a.1 ^ n))) < 1 := by
    apply lt_of_le_of_lt (hC (a.1 ^ n)).1
    simpa [map_pow, IsStrictAffinoid.withSpectralNorm k, mul_inv_cancel₀ hCpos.ne'] using
      mul_lt_mul_of_pos_left hpow_lt hCpos
  obtain ⟨_, ⟨x, hx, hxnorm⟩, hrlt⟩ :=
    (csInf_lt_iff (bddBelow_preImageNormSet f (f (a.1 ^ n))) ⟨_, _, rfl, rfl⟩).1 hlt
  exact ⟨n, Nat.succ_pos m, ⟨x, le_of_lt (hxnorm.trans_lt hrlt)⟩,
    mem_topNil_iff _ |>.2 (hxnorm.trans_lt hrlt), Subtype.ext hx⟩

lemma map_integerMap_ker_le_reduction_ker :
    Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) ≤ RingHom.ker f.reduction := by
  intro z hz
  rcases Ideal.Quotient.mk_surjective z with ⟨a, rfl⟩
  change _ ∈ Ideal.map (Ideal.Quotient.mk (topNil k A)) (RingHom.ker (integerMap f)) at hz
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hz
  rcases hz with ⟨c, hc, hqeq⟩
  rw [← hqeq]
  exact congrArg (Ideal.Quotient.mk (topNil k B)) hc

lemma reduction_mem_map_integerMap_ker_of_sub_topNil {f : A →ₐ[k] B} {a b : Integer k A}
    (hb : b ∈ topNil k A) (hEq : integerMap f b = integerMap f a) :
    reductionMap k A a ∈ Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) := by
  change _ ∈ Ideal.map (Ideal.Quotient.mk (topNil k A)) (RingHom.ker (integerMap f))
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  exact ⟨a - b, RingHom.mem_ker.2 (by simp [map_sub, hEq]),
    Ideal.Quotient.eq.2 (by simp [(topNil k A).neg_mem hb])⟩

lemma reduction_ker_le_map_integerMap_ker_of_topNil_lift {f : A →ₐ[k] B}
    (htop : ∀ b ∈ topNil k B, ∃ a : topNil k A, (integerMap f) a = b) :
    RingHom.ker f.reduction ≤ Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) := by
  intro z hz
  rcases Ideal.Quotient.mk_surjective z with ⟨a, rfl⟩
  change Ideal.Quotient.mk (topNil k B) ((integerMap f) a) = 0 at hz
  rcases htop ((integerMap f) a) (Ideal.Quotient.eq_zero_iff_mem.1 hz) with ⟨b, hbEq⟩
  exact reduction_mem_map_integerMap_ker_of_sub_topNil b.2 hbEq

/-- The kernel of the reduction map is the radical of the reduction of the kernel of `f°`. -/
theorem reduction_ker_eq_radical_map_integerMap_ker {f : A →ₐ[k] B}
    (hf : IsAdmissibleHom f) : RingHom.ker f.reduction =
      (Ideal.map (reductionMap k A) (RingHom.ker (integerMap f))).radical := by
  ext z
  constructor
  · intro hz
    rcases Ideal.Quotient.mk_surjective z with ⟨a, rfl⟩
    obtain ⟨n, -, b, hb, hEq⟩ :=
      exists_topNil_lift_pow_of_image_topNil hf (Ideal.Quotient.eq_zero_iff_mem.1 hz)
    exact Ideal.mem_radical_iff.2 ⟨n, reduction_mem_map_integerMap_ker_of_sub_topNil hb hEq⟩
  · intro hz
    exact (f.reduction_ker_isRadical.radical_le_iff).2 map_integerMap_ker_le_reduction_ker hz

end ker
