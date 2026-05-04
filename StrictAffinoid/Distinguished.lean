/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import StrictAffinoid.StrictlyClosed

public section

open Valued NormedField TateAlgebra

open scoped Topology

section IsDistinguishedEpi

variable {k : Type*} [NormedField k] {A B C : Type*} [SeminormedRing A] [NormedAlgebra k A]
  [SeminormedRing B] [NormedAlgebra k B] [SeminormedRing C] [NormedAlgebra k C]

/-- `f : A →ₐ[k] B` is distinguished if for any `b ∈ B`, there exists `a ∈ A` such that
  `f a = b` and `‖a‖ = ‖b‖`. -/
def IsDistinguishedEpi (f : A →ₐ[k] B) : Prop := ∀ b : B, ∃ a : A, f a = b ∧ ‖a‖ = ‖b‖

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
  exact ⟨a, by simp, by simp [ha, hb]⟩

lemma IsDistinguishedEpi.id : IsDistinguishedEpi (AlgHom.id k A) := fun a ↦ ⟨a, rfl, rfl⟩

lemma isAdmissibleHom_of_isDistinguishedEpi_of_isContractiveHom {k : Type*} [NormedField k]
    {A B : Type*} [SeminormedRing A] [NormedAlgebra k A] [SeminormedRing B] [NormedAlgebra k B]
    {f : A →ₐ[k] B} (hfd : IsDistinguishedEpi f) (hfc : IsContractiveHom f.toRingHom) :
    IsAdmissibleHom f.toRingHom := by
  refine ⟨1, Real.zero_lt_one, ?_⟩
  intro a
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, one_mul]
  rcases hfd (f a) with ⟨b, hb, hn⟩
  exact ⟨(csInf_le (bddBelow_preImageNormSet f (f a)) ⟨b, hb, rfl⟩).trans_eq hn, hfc a⟩

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

variable [IsDistinguished k A]

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
  by_cases hzero : F = 0
  · refine ⟨0, ?_⟩
    simp [hzero] at hF ⊢
  · rcases TateAlgebra.exists_coeff_norm_eq_norm F hzero with ⟨e, he⟩
    refine ⟨MvPowerSeries.coeff e F.1, ?_⟩
    simpa [hF] using he

theorem exists_lift_norm_eq_residue_norm {f : A →ₐ[k] B} (hf : Function.Surjective f) (b : B) :
    ∃ a : A, f a = b ∧ ‖a‖ = sInf {r : ℝ | ∃ a' : A, f a' = b ∧ ‖a'‖ = r} := by
  rcases IsDistinguished.exist_distinguishedEpi k A with ⟨τ, hτ, φ, hφ⟩
  have : Fintype τ := hτ
  let g : TateAlgebra τ k →ₐ[k] B := f.comp φ
  have hg : Function.Surjective g := hf.comp hφ.surjective
  let e : (TateAlgebra τ k ⧸ RingHom.ker g) ≃ₐ[k] B := Ideal.quotientKerAlgEquivOfSurjective hg
  let x : TateAlgebra τ k ⧸ RingHom.ker g := e.symm b
  obtain ⟨t, ht, htnormq⟩ := TateAlgebra.exists_norm_eq_residue_norm (I := RingHom.ker g) x
  have hgb : g t = b := by simpa [e, x] using congrArg e ht
  have htnorm : ‖t‖ = sInf (preImageNormSet g b) := by
    apply le_antisymm
    · refine le_csInf ⟨‖t‖, ⟨t, hgb, rfl⟩⟩ ?_
      rintro r ⟨t', ht'b, ht'norm⟩
      have hmk' : (Ideal.Quotient.mk (RingHom.ker g)) t' = x := by
        apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
        simpa [e, x] using ht'b
      calc
        ‖t‖ = ‖x‖ := htnormq
        _ ≤ ‖t'‖ := by simpa [hmk'] using Ideal.Quotient.norm_mk_le (RingHom.ker g) t'
        _ = r := ht'norm
    · exact csInf_le (bddBelow_preImageNormSet g b) ⟨t, hgb, rfl⟩
  let a : A := φ t
  have hab : f a = b := hgb
  have hSf_a : ‖a‖ ∈ preImageNormSet f b := ⟨a, hab, rfl⟩
  refine ⟨a, hab, le_antisymm ?_ ?_⟩
  · have ha_le_t : ‖a‖ ≤ ‖t‖ := IsStrictAffinoid.isContractiveHom φ t
    refine ha_le_t.trans ?_
    rw [htnorm]
    refine le_csInf ⟨‖a‖, hSf_a⟩ ?_
    rintro r ⟨a', ha'b, ha'norm⟩
    rcases hφ a' with ⟨t', ht'a', ht'norm⟩
    have ht'Sg : ‖t'‖ ∈ preImageNormSet g b := by
      refine ⟨t', ?_, rfl⟩
      simp [g, ht'a', ha'b]
    calc _ ≤ ‖t'‖ := csInf_le (bddBelow_preImageNormSet g b) ht'Sg
      _ = ‖a'‖ := ht'norm
      _ = r := ha'norm
  · exact csInf_le (bddBelow_preImageNormSet f b) hSf_a

end IsDistinguished

namespace IsStrictAffinoid

variable [IsStrictAffinoid k A] [IsStrictAffinoid k B] [IsStrictAffinoid k C]

lemma isDistinguishedEpi_of_comp {f : A →ₐ[k] B} {g : B →ₐ[k] C}
    (hfg : IsDistinguishedEpi (g.comp f)) : IsDistinguishedEpi g := by
  intro c
  rcases hfg c with ⟨a, ha, hnorm⟩
  refine ⟨f a, ha, le_antisymm ((IsStrictAffinoid.isContractiveHom f a).trans_eq hnorm) ?_⟩
  simpa [← ha] using IsStrictAffinoid.isContractiveHom g (f a)

lemma isAdmissibleHom_of_isDistinguishedEpi {f : A →ₐ[k] B} (hf : IsDistinguishedEpi f) :
    IsAdmissibleHom f.toRingHom :=
  isAdmissibleHom_of_isDistinguishedEpi_of_isContractiveHom hf (isContractiveHom f)

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
  · refine ⟨0, ?_, ?_⟩
    · simp [hb0]
    · simp [hb0]
  · rcases hvg b with ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hb0
      apply norm_eq_zero.mp
      rw [← hc, hc0]
      simp
    have hb_norm_ne : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    let bI : Integer k B := ⟨c⁻¹ • b, by
      have hbI_norm : ‖c⁻¹ • b‖ = 1 := by
        rw [norm_smul, norm_inv, hc, inv_mul_cancel₀]
        exact hb_norm_ne
      exact le_of_eq hbI_norm⟩
    rcases hf bI with ⟨aI, haI⟩
    have haI' : f aI.1 = c⁻¹ • b := congrArg Subtype.val haI
    have haI_norm : ‖aI.1‖ = 1 := by
      have hle1 : ‖aI.1‖ ≤ 1 := aI.2
      have hge1 : 1 ≤ ‖aI.1‖ := by
        have hbI_norm : ‖c⁻¹ • b‖ = 1 := by
          rw [norm_smul, norm_inv, hc, inv_mul_cancel₀]
          exact hb_norm_ne
        calc _ = ‖c⁻¹ • b‖ := hbI_norm.symm
          _ = ‖f aI.1‖ := by rw [haI']
          _ ≤ ‖aI.1‖ := isContractiveHom f aI.1
      exact le_antisymm hle1 hge1
    refine ⟨c • aI.1, ?_, ?_⟩
    · calc
        f (c • aI.1) = c • f aI.1 := by simp
        _ = c • (c⁻¹ • b) := by rw [haI']
        _ = b := by simp [hc0]
    · calc
        ‖c • aI.1‖ = ‖c‖ * ‖aI.1‖ := by rw [norm_smul]
        _ = ‖c‖ := by simp [haI_norm]
        _ = ‖b‖ := hc

private lemma exists_topNil_lift_pow_of_image_topNil {f : A →ₐ[k] B} (hf : Function.Surjective f)
    {a : Integer k A} (ha : (integerMap f) a ∈ topNil k B) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : Integer k A, b ∈ topNil k A ∧
      (integerMap f) b = (integerMap f) (a ^ n) := by
  have ha_lt : ‖f a.1‖ < 1 := by
    simpa [mem_topologicalNilradical_iff_norm_lt_one] using ha
  by_cases htv : ∃ x : k, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let : NontriviallyNormedField k := NontriviallyNormedField.ofNormNeOne htv
    rcases admissible_of_surjective f hf with ⟨C, hCpos, hC⟩
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < C⁻¹ by positivity) ha_lt
    let n : ℕ := m + 1
    have hn_pos : 0 < n := Nat.succ_pos m
    have hpow_lt : ‖f a.1‖ ^ n < C⁻¹ := by
      calc _ = ‖f a.1‖ ^ m * ‖f a.1‖ := by simp [n, pow_succ]
        _ ≤ ‖f a.1‖ ^ m * 1 := by
          have hmul : ‖f a.1‖ ^ m * ‖f a.1‖ ≤ ‖f a.1‖ ^ m * 1 := by gcongr
          simpa using hmul
        _ = ‖f a.1‖ ^ m := by ring
        _ < C⁻¹ := hm
    have hCpow_lt : C * ‖f a.1‖ ^ n < 1 := by
      have hmul := mul_lt_mul_of_pos_left hpow_lt hCpos
      simpa [mul_inv_cancel₀ hCpos.ne'] using hmul
    have hQne : (preImageNormSet f (f (a.1 ^ n))).Nonempty := ⟨‖a.1 ^ n‖, a.1 ^ n, rfl, rfl⟩
    have hfnorm : ‖f (a.1 ^ n)‖ = ‖f a.1‖ ^ n := by
      rw [map_pow, IsStrictAffinoid.withSpectralNorm k n (f a.1)]
    have hlt : sInf (preImageNormSet f (f (a.1 ^ n))) < 1 := by
      have htarget_lt : C * ‖f (a.1 ^ n)‖ < 1 := by
        simpa [map_pow, IsStrictAffinoid.withSpectralNorm k n (f a.1)] using hCpow_lt
      exact lt_of_le_of_lt (hC (a.1 ^ n)).1 htarget_lt
    obtain ⟨r, hrQ, hrlt⟩ := (csInf_lt_iff (bddBelow_preImageNormSet f (f (a.1 ^ n))) hQne).1 hlt
    rcases hrQ with ⟨x, hx, hxnorm⟩
    let b : Integer k A := ⟨x, le_of_lt (hxnorm.trans_lt hrlt)⟩
    refine ⟨n, hn_pos, b, ?_, ?_⟩
    · rw [mem_topologicalNilradical_iff_norm_lt_one]
      exact hxnorm.trans_lt hrlt
    · exact Subtype.ext hx
  · have hzero : f a.1 = 0 := by
      by_contra hne
      have hone : ‖f a.1‖ = 1 := IsStrictAffinoid.norm_eq_one_of_trivially_valued htv hne
      exact (not_lt_of_ge hone.ge) ha_lt
    refine ⟨1, Nat.one_pos, 0, ?_, ?_⟩
    · exact (topNil k A).zero_mem
    · simpa using (Subtype.ext hzero).symm

theorem isDistinguishedEpi_tfae [IsDistinguished k A] {f : A →ₐ[k] B}
    (hf : Function.Surjective f) : List.TFAE
    [ IsDistinguishedEpi f,
      ∀ b ∈ topNil k B, ∃ a : topNil k A, (integerMap f) a = b,
      (topNil k A ⊔ RingHom.ker (integerMap f)).IsRadical,
      RingHom.ker f.reduction = Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) ] := by
  tfae_have 1 → 2 := by
    intro hdist b hb
    have hb_lt : ‖b.1‖ < 1 := (mem_topologicalNilradical_iff_norm_lt_one b).1 hb
    rcases hdist b.1 with ⟨a, ha, hnorm⟩
    have ha_le : ‖a‖ ≤ 1 := le_of_lt (hnorm.trans_lt hb_lt)
    let aI : Integer k A := ⟨a, ha_le⟩
    have ha_top : aI ∈ topNil k A := by
      rw [mem_topologicalNilradical_iff_norm_lt_one]
      exact hnorm.trans_lt hb_lt
    refine ⟨⟨aI, ha_top⟩, ?_⟩
    exact Subtype.ext ha
  tfae_have 2 → 3 := by
    intro htop
    let J : Ideal (Integer k A) := topNil k A ⊔ RingHom.ker (integerMap f)
    rw [Ideal.isRadical_iff_pow_one_lt 2 Nat.one_lt_two]
    intro a ha
    have hJmap : ∀ {x : Integer k A}, x ∈ J → (integerMap f) x ∈ topNil k B := by
      intro x hx
      rw [Submodule.mem_sup] at hx
      rcases hx with ⟨y, hy, c, hc, rfl⟩
      have hy' : (integerMap f) y ∈ topNil k B := by
        rw [mem_topologicalNilradical_iff_norm_lt_one] at hy ⊢
        exact lt_of_le_of_lt (isContractiveHom f y.1) hy
      have hc' : (integerMap f) c = 0 := by simpa [RingHom.mem_ker] using hc
      simpa [map_add, hc'] using hy'
    have himage_sq : (integerMap f) (a ^ 2) ∈ topNil k B := hJmap ha
    have himage : (integerMap f) a ∈ topNil k B := by
      have hrad := topNil_isRadical k B
      rw [Ideal.isRadical_iff_pow_one_lt 2 Nat.one_lt_two] at hrad
      apply hrad
      simpa [map_pow] using himage_sq
    rcases htop ((integerMap f) a) himage with ⟨b, hbEq⟩
    have hk : a - b ∈ RingHom.ker (integerMap f) := by
      rw [RingHom.mem_ker]
      apply Subtype.ext
      simp [map_sub, hbEq]
    have hsum : (b : Integer k A) + (a - b) = a := by abel
    exact hsum ▸ Submodule.add_mem_sup b.2 hk
  tfae_have 3 → 4 := by
    intro hJrad
    let J : Ideal (Integer k A) := topNil k A ⊔ RingHom.ker (integerMap f)
    ext z
    constructor
    · intro hz
      rcases Ideal.Quotient.mk_surjective z with ⟨a, rfl⟩
      rw [RingHom.mem_ker] at hz
      change Ideal.Quotient.mk (topNil k B) ((integerMap f) a) = 0 at hz
      rw [Ideal.Quotient.eq_zero_iff_mem] at hz
      change _ ∈ Ideal.map (Ideal.Quotient.mk (topNil k A)) (RingHom.ker (integerMap f))
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
      rcases exists_topNil_lift_pow_of_image_topNil hf hz with ⟨n, hn_pos, b, hb, hEq⟩
      have hk : a ^ n - b ∈ RingHom.ker (integerMap f) := by
        rw [RingHom.mem_ker]
        apply Subtype.ext
        simp [map_sub, hEq]
      have hpow_mem : a ^ n ∈ J := by
        have hsum : b + (a ^ n - b) = a ^ n := by abel
        exact hsum ▸ Submodule.add_mem_sup hb hk
      have ha_rad : a ∈ J.radical := (Ideal.mem_radical_iff).2 ⟨n, hpow_mem⟩
      have hrad_eq : J.radical = J := (Ideal.radical_eq_iff).2 hJrad
      have haJ : a ∈ J := by simpa [hrad_eq] using ha_rad
      rw [Submodule.mem_sup] at haJ
      rcases haJ with ⟨y, hy, c, hc, hdecomp⟩
      refine ⟨c, hc, ?_⟩
      rw [Ideal.Quotient.eq]
      have hca : c - a = -y := by
        rw [← hdecomp]
        abel
      simpa [hca] using (topNil k A).neg_mem hy
    · intro hz
      rcases Ideal.Quotient.mk_surjective z with ⟨a, rfl⟩
      change _ ∈ Ideal.map (Ideal.Quotient.mk (topNil k A)) (RingHom.ker (integerMap f)) at hz
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hz
      rcases hz with ⟨c, hc, hqeq⟩
      rw [RingHom.mem_ker]
      change Ideal.Quotient.mk (topNil k B) ((integerMap f) a) = 0
      have hc0 : (integerMap f) c = 0 := by simpa [RingHom.mem_ker] using hc
      have hleft : f.reduction (Ideal.Quotient.mk (topNil k A) c) = 0 := by
        change Ideal.Quotient.mk (topNil k B) ((integerMap f) c) = 0
        simp [hc0]
      simpa [hleft] using congrArg f.reduction hqeq.symm
  tfae_have 4 → 1 := by
    intro hred b
    by_cases hb0 : b = 0
    · exact ⟨0, by simp [hb0], by simp [hb0]⟩
    · obtain ⟨a, ha, hamin⟩ := IsDistinguished.exists_lift_norm_eq_residue_norm hf b
      rcases IsDistinguished.value_group_subset (k := k) (A := A) a with ⟨c, hc⟩
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
        apply hb0
        simpa [ha0] using ha.symm
      let aI : Integer k A := ⟨c⁻¹ • a, by
        have haI_norm : ‖c⁻¹ • a‖ = 1 := by
          rw [norm_smul, norm_inv, hc, inv_mul_cancel₀]
          exact norm_ne_zero_iff.mpr ha0
        exact le_of_eq haI_norm⟩
      have haI_eq : f aI.1 = c⁻¹ • b := by
        calc _ = c⁻¹ • f a := by simp [aI]
          _ = c⁻¹ • b := by rw [ha]
      have haI_not_mem :
          reductionMap k A aI ∉ Ideal.map (reductionMap k A) (RingHom.ker (integerMap f)) := by
        intro hmem
        obtain ⟨cI, hcI, hqeq⟩ :=
          (Ideal.mem_map_iff_of_surjective (reductionMap k A) Ideal.Quotient.mk_surjective).1 hmem
        let y : Integer k A := aI - cI
        have hy_top : y ∈ topNil k A := (Ideal.Quotient.eq).1 hqeq.symm
        have hcI0 : (integerMap f) cI = 0 := by simpa [RingHom.mem_ker] using hcI
        have hcI0' : f cI.1 = 0 := congrArg Subtype.val hcI0
        have hy_eq : f y.1 = c⁻¹ • b := by
          calc _ = f aI.1 - f cI.1 := by simp [y]
            _ = c⁻¹ • b := by simp [haI_eq, hcI0']
        have hy_lt : ‖y.1‖ < 1 :=
          (mem_topologicalNilradical_iff_norm_lt_one (k := k) (A := A) y).1 hy_top
        let a' : A := c • y.1
        have ha'_eq : f a' = b := by
          calc _ = c • f y.1 := by simp [a']
            _ = c • (c⁻¹ • b) := by rw [hy_eq]
            _ = b := by simp [hc0]
        have ha'_lt : ‖a'‖ < ‖a‖ := by
          calc _ = ‖c‖ * ‖y.1‖ := by rw [show a' = c • y.1 by rfl, norm_smul]
            _ < ‖c‖ * 1 := mul_lt_mul_of_pos_left hy_lt (norm_pos_iff.mpr hc0)
            _ = ‖a‖ := by simp [hc]
        have hSa' : ‖a'‖ ∈ preImageNormSet f b := ⟨a', ha'_eq, rfl⟩
        have : ¬ sInf (preImageNormSet f b) ≤ ‖a'‖ := by
          rw [← hamin]
          exact (not_le_of_gt ha'_lt)
        exact this (csInf_le (bddBelow_preImageNormSet f b) hSa')
      have hred_ne : f.reduction (reductionMap k A aI) ≠ 0 := by
        intro hz
        have hker : reductionMap k A aI ∈ RingHom.ker f.reduction := by
          simpa [RingHom.mem_ker] using hz
        exact haI_not_mem (by simpa [hred] using hker)
      have hbI_not_top : (integerMap f) aI ∉ topNil k B := by
        intro hbI_top
        apply hred_ne
        exact Ideal.Quotient.eq_zero_iff_mem.2 hbI_top
      have hbI_norm : ‖(integerMap f) aI‖ = 1 := by
        apply le_antisymm
        · exact (integerMap f aI).2
        · exact le_of_not_gt <| by
            intro hlt
            exact hbI_not_top <|
              (mem_topologicalNilradical_iff_norm_lt_one ((integerMap f) aI)).2 hlt
      have hbI_eq_norm : ‖(integerMap f) aI‖ = ‖c‖⁻¹ * ‖b‖ := by
        change ‖f aI.1‖ = ‖c‖⁻¹ * ‖b‖
        rw [haI_eq, norm_smul, norm_inv]
      have hb_eq_c : ‖b‖ = ‖c‖ := by
        calc _ = ‖c‖ * (‖c‖⁻¹ * ‖b‖) := by field_simp [norm_ne_zero_iff.mpr hc0]
          _ = ‖c‖ * ‖(integerMap f) aI‖ := by rw [hbI_eq_norm]
          _ = ‖c‖ := by simp [hbI_norm]
      exact ⟨a, ha, hc.symm.trans hb_eq_c.symm⟩
  tfae_finish

end IsStrictAffinoid
