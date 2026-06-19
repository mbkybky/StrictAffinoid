/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import StrictAffinoid.Cartesian
public import StrictAffinoid.Reduction

public section

open Valued NormedField IsStrictAffinoid

open scoped Topology BigOperators

section IsDistinguishedEpi

variable {k : Type*} [NormedField k] {A B C : Type*} [SeminormedRing A] [NormedAlgebra k A]
  [SeminormedRing B] [NormedAlgebra k B] [SeminormedRing C] [NormedAlgebra k C]

/-- `f : A →ₐ[k] B` is distinguished if for any `b ∈ B`, there exists `a ∈ A` such that
  `f a = b` and `‖a‖ = ‖b‖`. -/
def IsDistinguishedEpi (f : A →ₐ[k] B) : Prop := ∀ b : B, ∃ (a : A) (_ : f a = b), ‖a‖ = ‖b‖

lemma IsDistinguishedEpi.surjective {f : A →ₐ[k] B} (hf : IsDistinguishedEpi f) :
    Function.Surjective f := by
  intro b
  rcases hf b with ⟨a, ha, -⟩
  exact ⟨a, ha⟩

lemma IsDistinguishedEpi.comp {f : A →ₐ[k] B} {g : B →ₐ[k] C} (hf : IsDistinguishedEpi f)
    (hg : IsDistinguishedEpi g) : IsDistinguishedEpi (g.comp f) := by
  intro c
  rcases hg c with ⟨b, rfl, hb⟩
  rcases hf b with ⟨a, rfl, ha⟩
  exact ⟨a, rfl, ha.trans hb⟩

lemma IsDistinguishedEpi.id : IsDistinguishedEpi (AlgHom.id k A) := fun a ↦ ⟨a, rfl, rfl⟩

end IsDistinguishedEpi

/-- A strict affinoid algebra is distinguished if it admits a distinguished epimorphism from a Tate
algebra. -/
class IsDistinguished (k : Type*) [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (A : Type*) [SeminormedRing A] [NormedAlgebra k A] : Prop extends IsStrictAffinoid k A where
  exist_distinguishedEpi (k A) :
    ∃ (σ : Type) (_ : Fintype σ) (φ : TateAlgebra σ k →ₐ[k] A), IsDistinguishedEpi φ

attribute [instance 100] IsDistinguished.toIsStrictAffinoid

variable (σ : Type*) [Finite σ] {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {A B C : Type*} [NormedCommRing A] [NormedAlgebra k A] [NormedCommRing B] [NormedAlgebra k B]
  [NormedCommRing C] [NormedAlgebra k C]

namespace IsDistinguished

open Module

variable [IsDistinguished k A]

include k

theorem _root_.IsDistinguishedEpi.isDistinguished [IsStrictAffinoid k B]
    {f : A →ₐ[k] B} (hf : IsDistinguishedEpi f) : IsDistinguished k B where
  exist_distinguishedEpi := by
    rcases IsDistinguished.exist_distinguishedEpi k A with ⟨τ, hτ, φ, hφ⟩
    exact ⟨τ, hτ, f.comp φ, hφ.comp hf⟩

instance : IsDistinguished k (TateAlgebra σ k) where
  exist_distinguishedEpi := by
    let τ : Type := Shrink.{0} σ
    let e : σ ≃ τ := equivShrink.{0} σ
    refine ⟨τ, Fintype.ofFinite τ, TateAlgebra.rename k e.symm.toEmbedding, fun F ↦ ?_⟩
    refine ⟨TateAlgebra.rename k e.toEmbedding F, ?_, TateAlgebra.rename_norm_eq e F⟩
    simp [TateAlgebra.rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id]

variable (k) in
/-- `ρ(A) ⊆ |k|` if `A` is a distinguished strict affinoid algebra. -/
theorem value_group_subset (a : A) : ∃ x : k, ‖x‖ = ‖a‖ := by
  rcases IsDistinguished.exist_distinguishedEpi k A with ⟨τ, _, φ, hφ⟩
  rcases hφ a with ⟨F, rfl, hF⟩
  simp [← hF, F.value_group_subset]

variable (k) in
/-- Let `A` be a distinguished `k`-affinoid algebra, then any ideal of `A` is strictly closed. -/
theorem ideal_isStrictlyClosed (I : Ideal A) : I.IsStrictlyClosed := by
  rcases IsDistinguished.exist_distinguishedEpi k A with ⟨σ, _, φ, hφ⟩
  intro a
  rcases Ideal.Quotient.mk_surjective a with ⟨x, rfl⟩
  rcases hφ x with ⟨t₀, ht₀, -⟩
  let J : Ideal (TateAlgebra σ k) := Ideal.comap φ I
  rcases TateAlgebra.ideal_isStrictlyClosed σ k J (Ideal.Quotient.mk J t₀) with ⟨t, ht, htnorm⟩
  have ha : (Ideal.Quotient.mk I) (φ t) = (Ideal.Quotient.mk I) x := by
    simpa [Ideal.Quotient.eq, ← ht₀, J, map_sub] using Ideal.Quotient.eq.1 ht
  refine ⟨φ t, ha, le_antisymm ?_ ?_⟩
  · refine le_of_not_gt fun hlt ↦ ?_
    obtain ⟨a₁, ha₁, ha₁lt⟩ := QuotientAddGroup.norm_lt_iff.1 hlt
    rcases hφ a₁ with ⟨t₁, ht₁, ht₁norm⟩
    have ht₁q : Ideal.Quotient.mk J t₁ = Ideal.Quotient.mk J t₀ := by
      rw [Ideal.Quotient.eq, Ideal.mem_comap]
      simpa [map_sub, ht₁, ht₀] using Ideal.Quotient.eq.1 ha₁
    have ht_le_t₁ : ‖t‖ ≤ ‖t₁‖ := by
      simpa [htnorm, ht₁q] using Ideal.Quotient.norm_mk_le J t₁
    exact not_lt_of_ge ((isContractiveHom φ t).trans (ht_le_t₁.trans_eq ht₁norm)) ha₁lt
  · grw [← ha, Ideal.Quotient.norm_mk_le I (φ t)]

variable (k) in
/-- Let `A` be a distinguished `k`-affinoid algebra, then any ideal of `A` is boundedly
generated. -/
theorem ideal_isBoundedlyGenerated (I : Ideal A) : IsBoundedlyGenerated A I := by
  rcases IsDistinguished.exist_distinguishedEpi k A with ⟨τ, hτ, φ, hφ⟩
  let J : Ideal (TateAlgebra τ k) := Ideal.comap φ I
  rcases TateAlgebra.ideal_isBoundedlyGenerated τ k J with ⟨σ, hσ, e, he⟩
  refine ⟨σ, hσ, fun i ↦ ⟨φ (e i).1, (e i).2⟩, ⟨?_, ?_⟩⟩
  · intro i
    grw [Submodule.coe_norm, isContractiveHom φ (e i).1, ← Submodule.coe_norm, he.norm_le_one i]
  · intro m
    rcases hφ m.1 with ⟨t, ht, htnorm⟩
    rcases he.boundedly_generate ⟨t, by simp [J, ht, m.2]⟩ with ⟨b, hb, hbnorm⟩
    refine ⟨fun i ↦ φ (b i), ?_, ?_⟩
    · apply Subtype.ext
      have hbval : t = ∑ i, b i • e i := congrArg Subtype.val hb
      simp [← ht, hbval, map_sum, map_mul]
    · intro i
      grw [Submodule.coe_norm, isContractiveHom φ (b i), hbnorm i, Submodule.coe_norm, htnorm]

variable (k) in
theorem ideal_integer_fg (I : Ideal A) : (I.integer k).FG := by
  rcases ideal_isBoundedlyGenerated k I with ⟨τ, hτ, E, hE⟩
  let Eint : τ → Integer k A := fun i ↦ ⟨(E i).1, hE.norm_le_one i⟩
  have hEspan : Ideal.span (Set.range Eint) = I.integer k := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨i, rfl⟩
      exact (E i).2
    · intro q hq
      rcases hE.boundedly_generate (⟨q.1, hq⟩ : I) with ⟨a, ha, hanorm⟩
      let aI : τ → Integer k A := fun i ↦ ⟨a i, (hanorm i).trans q.2⟩
      have hqint : q = ∑ i, aI i * Eint i := by
        apply Subtype.ext
        have hqval : q.1 = ∑ i, a i * (E i).1 := by
          simpa using congrArg Subtype.val ha
        have hsum_val : (∑ i, aI i * Eint i).1 = ∑ i, a i * (E i).1 := by
          simpa [← Integer.algebraMap_eq_val] using by rfl
        exact hqval.trans hsum_val.symm
      rw [hqint]
      apply Ideal.sum_mem
      intro i _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  rw [← hEspan]
  exact Submodule.fg_span (Set.finite_range Eint)

theorem exists_lift_norm_eq_residue_norm {f : A →ₐ[k] B} (hf : Function.Surjective f) (b : B) :
    ∃ (a : A) (_ : f a = b), ‖a‖ = sInf (preImageNormSet f b) := by
  rcases IsDistinguished.exist_distinguishedEpi k A with ⟨σ, hσ, φ, hφ⟩
  let g : TateAlgebra σ k →ₐ[k] B := f.comp φ
  have hg : Function.Surjective g := hf.comp hφ.surjective
  let e : (TateAlgebra σ k ⧸ RingHom.ker g) ≃ₐ[k] B := Ideal.quotientKerAlgEquivOfSurjective hg
  let x : TateAlgebra σ k ⧸ RingHom.ker g := e.symm b
  obtain ⟨t, ht, htnormq⟩ := TateAlgebra.ideal_isStrictlyClosed σ k (RingHom.ker g) x
  have hgb : g t = b := by simpa [e, x] using congrArg e ht
  have htnorm : ‖t‖ = sInf (preImageNormSet g b) := by
    apply le_antisymm
    · refine le_csInf ⟨‖t‖, ⟨t, hgb, rfl⟩⟩ fun r ⟨t', ht'b, ht'norm⟩ ↦ ?_
      have hmk' : (Ideal.Quotient.mk (RingHom.ker g)) t' = x := by
        apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
        simpa [e, x] using ht'b
      rw [htnormq, ← ht'norm]
      simpa [hmk'] using Ideal.Quotient.norm_mk_le (RingHom.ker g) t'
    · exact csInf_le (bddBelow_preImageNormSet g b) ⟨t, hgb, rfl⟩
  have hab : f (φ t) = b := hgb
  have hSf_a : ‖φ t‖ ∈ preImageNormSet f b := ⟨φ t, hab, rfl⟩
  refine ⟨φ t, hab, le_antisymm ?_ ?_⟩
  · grw [IsStrictAffinoid.isContractiveHom φ t, htnorm]
    refine le_csInf ⟨‖φ t‖, hSf_a⟩ ?_
    intro r ⟨a', ha'b, ha'⟩
    rcases hφ a' with ⟨t', ht'a', ht'⟩
    grw [csInf_le (bddBelow_preImageNormSet g b) ⟨t', by simp [g, ht'a', ha'b], rfl⟩, ht', ha']
  · exact csInf_le (bddBelow_preImageNormSet f b) hSf_a

end IsDistinguished

namespace IsStrictAffinoid

variable [IsStrictAffinoid k A] [IsStrictAffinoid k B] [IsStrictAffinoid k C]

lemma isDistinguishedEpi_of_comp {f : A →ₐ[k] B} {g : B →ₐ[k] C}
    (hfg : IsDistinguishedEpi (g.comp f)) : IsDistinguishedEpi g := by
  intro c
  rcases hfg c with ⟨a, ha, hnorm⟩
  refine ⟨f a, ha, le_antisymm ((isContractiveHom f a).trans_eq hnorm) ?_⟩
  simpa [← ha] using isContractiveHom g (f a)

/-- `f° : A° → B°` is surjective if `f` is a distinguished epimorphism. -/
theorem integerMap_surjective_of_isDistinguishedEpi {f : A →ₐ[k] B} (hf : IsDistinguishedEpi f) :
    Function.Surjective (integerMap f) := by
  intro b
  rcases hf b.1 with ⟨a, ha, hnorm⟩
  exact ⟨⟨a, by simpa [hnorm] using by exact b.2⟩, Subtype.ext ha⟩

/-- $\widetilde{f} : \widetilde{A} \to \widetilde{B}$ is surjective if
$f$ is a distinguished epimorphism. -/
theorem reduction_surjective_of_isDistinguishedEpi {f : A →ₐ[k] B} (hf : IsDistinguishedEpi f) :
    Function.Surjective f.reduction :=
  Ideal.quotientMap_surjective (integerMap_surjective_of_isDistinguishedEpi hf)

/-- `f` is a distinguished epimorphism if `f° : A° → B°` is surjective and `ρ(A) ⊆ |k|`. -/
theorem isDistinguishedEpi_of_integerMap_surjective {f : A →ₐ[k] B}
    (hf : Function.Surjective (integerMap f))
    (hvg : ∀ b : B, ∃ c : k, ‖c‖ = ‖b‖) : IsDistinguishedEpi f := by
  intro b
  by_cases hb0 : b = 0
  · exact ⟨0, by simp [hb0], by simp [hb0]⟩
  · rcases hvg b with ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hc0
      exact hb0 (norm_eq_zero.mp (by simpa [hc0] using hc.symm))
    have hb_norm_ne : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    let bI : Integer k B := ⟨c⁻¹ • b, by
      have hbI_norm : ‖c⁻¹ • b‖ = 1 := by
        rw [norm_smul, norm_inv, hc, inv_mul_cancel₀]
        exact hb_norm_ne
      exact le_of_eq hbI_norm⟩
    rcases hf bI with ⟨aI, haI⟩
    have haI' : f aI.1 = c⁻¹ • b := congrArg Subtype.val haI
    have haI_norm : ‖aI.1‖ = 1 := by
      refine le_antisymm aI.2 ?_
      have hbI_norm : ‖c⁻¹ • b‖ = 1 := by rw [norm_smul, norm_inv, hc, inv_mul_cancel₀ hb_norm_ne]
      grw [← hbI_norm, ← haI', isContractiveHom f aI.1]
    refine ⟨c • aI.1, ?_, ?_⟩
    · grw [map_smul, haI']
      simp [hc0]
    · grw [norm_smul, hc, haI_norm, mul_one]

end IsStrictAffinoid

/--
Let $\mathscr{A}$ be a distinguished $k$-affinoid algebra, $\mathscr{B}$ be a strict $k$-affinoid
algebra, $f : \mathscr{A} \to \mathscr{B}$ be a surjective $k$-algebra homomorphism.
Then the following are equivalent:
1. $f$ is distinguished.
2. $f(\mathscr{A}^{\circ\circ}) = \mathscr{B}^{\circ\circ}$.
3. The ideal $\widetilde{\ker(f^\circ)} \subset \widetilde{\mathscr{A}}$ is radical.
4. $\ker(\widetilde{f}) = \widetilde{\ker(f^\circ)}$.
-/
theorem IsStrictAffinoid.isDistinguishedEpi_tfae [IsDistinguished k A] [IsStrictAffinoid k B]
    {f : A →ₐ[k] B} (hf : Function.Surjective f) : List.TFAE
    [ IsDistinguishedEpi f,
      ∀ b ∈ topNil k B, ∃ a : topNil k A, (integerMap f) a = b,
      (Ideal.map (reductionMap k A) (RingHom.ker (integerMap f))).IsRadical,
      RingHom.ker f.reduction = Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) ] := by
  tfae_have 1 → 2 := by
    intro hdist b hb
    have hb_lt : ‖b.1‖ < 1 := (mem_topNil_iff b).1 hb
    rcases hdist b.1 with ⟨a, ha, hnorm⟩
    let aI : Integer k A := ⟨a, (hnorm.trans_lt hb_lt).le⟩
    exact ⟨⟨aI, (mem_topNil_iff aI).2 (hnorm.trans_lt hb_lt)⟩, Subtype.ext ha⟩
  tfae_have 2 → 3 := by
    rw [← Ideal.radical_eq_iff]
    intro htop
    apply le_antisymm
    · rw [← reduction_ker_eq_radical_map_integerMap_ker (isAdmissibleHom_of_surjective hf)]
      exact reduction_ker_le_map_integerMap_ker_of_topNil_lift htop
    · exact Ideal.le_radical
  tfae_have 3 → 4 := by
    simp [reduction_ker_eq_radical_map_integerMap_ker (isAdmissibleHom_of_surjective hf),
      Ideal.radical_eq_iff]
  tfae_have 4 → 1 := by
    intro hred b
    by_cases hb0 : b = 0
    · exact ⟨0, by simp [hb0], by simp [hb0]⟩
    · obtain ⟨a, ha, hamin⟩ := IsDistinguished.exists_lift_norm_eq_residue_norm hf b
      rcases IsDistinguished.value_group_subset k a with ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hb0
        apply norm_eq_zero.mp
        have ha_norm0 : ‖a‖ = 0 := by simpa [hc0] using hc.symm
        have hf_norm0 : ‖f a‖ = 0 :=
          le_antisymm ((isContractiveHom f a).trans_eq ha_norm0) (norm_nonneg _)
        simpa [ha] using hf_norm0
      have ha0 : a ≠ 0 := by
        intro ha0
        exact hb0 (by simpa [ha0] using ha.symm)
      let aI : Integer k A := ⟨c⁻¹ • a, by
        have haI_norm : ‖c⁻¹ • a‖ = 1 := by
          rw [norm_smul, norm_inv, hc, inv_mul_cancel₀]
          exact norm_ne_zero_iff.mpr ha0
        exact le_of_eq haI_norm⟩
      have haI_not_mem :
          reductionMap k A aI ∉ Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) := by
        intro hmem
        obtain ⟨cI, hcI, hqeq⟩ :=
          (Ideal.mem_map_iff_of_surjective (reductionMap k A) Ideal.Quotient.mk_surjective).1 hmem
        let y : Integer k A := aI - cI
        have hy_top : y ∈ topNil k A := (Ideal.Quotient.eq).1 hqeq.symm
        have hcI0 : (integerMap f) cI = 0 := by simpa [RingHom.mem_ker] using hcI
        have hcI0' : f cI.1 = 0 := congrArg Subtype.val hcI0
        have hy_eq : f y.1 = c⁻¹ • b := by simp [y, aI, ha, hcI0']
        have hy_lt : ‖y.1‖ < 1 :=
          (mem_topNil_iff y).1 hy_top
        let a' : A := c • y.1
        have ha'_eq : f a' = b := by simp [a', hy_eq, hc0]
        have ha'_lt : ‖a'‖ < ‖a‖ := by
          simpa [a', norm_smul] using
            (mul_lt_mul_of_pos_left hy_lt (norm_pos_iff.mpr hc0)).trans_le (by simp [hc])
        have hSa' : ‖a'‖ ∈ preImageNormSet f b := ⟨a', ha'_eq, rfl⟩
        have : ¬ sInf (preImageNormSet f b) ≤ ‖a'‖ := by
          rw [← hamin]
          exact (not_le_of_gt ha'_lt)
        exact this (csInf_le (bddBelow_preImageNormSet f b) hSa')
      have hred_ne : f.reduction (reductionMap k A aI) ≠ 0 := by
        intro hz
        exact haI_not_mem <| by
          rw [← hred]
          simpa [RingHom.mem_ker] using hz
      have hnt : (integerMap f) aI ∉ topNil k B := by
        intro hbI_top
        exact hred_ne (Ideal.Quotient.eq_zero_iff_mem.2 hbI_top)
      have hbI_norm : ‖(integerMap f) aI‖ = 1 := by
        apply le_antisymm
        · exact (integerMap f aI).norm_le
        · exact le_of_not_gt <| fun hlt ↦
            hnt ((mem_topNil_iff ((integerMap f) aI)).2 hlt)
      have hbI_eq_norm : ‖(integerMap f) aI‖ = ‖c‖⁻¹ * ‖b‖ := by
        simp [Integer.norm_eq, integerMap_val, aI, ha, norm_smul, norm_inv]
      have hb_eq_c : ‖b‖ = ‖c‖ := by
        calc _ = ‖c‖ * (‖c‖⁻¹ * ‖b‖) := by field_simp [norm_ne_zero_iff.mpr hc0]
          _ = _ := by simp [← hbI_eq_norm, hbI_norm]
      exact ⟨a, ha, hc.symm.trans hb_eq_c.symm⟩
  tfae_finish
