/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Nilpotent

public section

namespace Ideal

theorem fg_of_fg_map_of_fg_inf_ker_of_surjective {R S : Type*} [CommRing R]
    [CommRing S] {f : R →+* S} {I : Ideal R} (hmap : (I.map f).FG) (hk : (I ⊓ (RingHom.ker f)).FG)
    (hf : Function.Surjective f) : I.FG := by
  algebraize [f]
  have h : Submodule.map (Module.compHom.toLinearMap f) I = (I.map f).restrictScalars R := by
    ext
    have : RingHomSurjective f := ⟨hf⟩
    simp [Ideal.map_eq_submodule_map]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Module.compHom.toLinearMap f) ?_ hk
  simpa [h] using Submodule.FG.restrictScalars_of_surjective hmap hf

lemma fg_of_quotient_map_fg {R : Type*} [CommRing R] {I J : Ideal R}
    (hmap : (Ideal.map (Ideal.Quotient.mk J) I).FG) (hJ : J.FG) (hJI : J ≤ I) : I.FG :=
  Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective hmap (by simpa [inf_eq_right.mpr hJI] using hJ)
    Quotient.mk_surjective

end Ideal

namespace Module.Finite

lemma quotient_of_quotient_isNilpotent_finite (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] [IsNoetherianRing A] {I : Ideal A} (hI : IsNilpotent I)
    [Module.Finite R (A ⧸ I)] : Module.Finite R A := by
  refine Ideal.IsNilpotent.induction_on I hI
    (P := fun {A} [CommRing A] (I : Ideal A) ↦
      ∀ [Algebra R A] [IsNoetherianRing A] [Module.Finite R (A ⧸ I)], Module.Finite R A) ?_ ?_
  · intro A _ I hsq _ _ fin
    let T : Submodule A I := ⊤
    have hsmul : I • T = ⊥ := by
      ext x
      constructor
      · intro hx
        rw [Submodule.mem_smul_top_iff] at hx
        have hx0 : x.1 ∈ (⊥ : Ideal A) := by
          rw [← hsq]
          simpa only [show I • I = I * I by rfl, pow_two] using hx
        exact Subtype.ext hx0
      · intro hx
        simp only [Submodule.mem_bot] at hx
        simp [hx]
    have : Module.Finite R (I ⧸ I • T) := Module.Finite.trans (A ⧸ I) (I ⧸ I • T)
    have : Module.Finite R (Submodule.restrictScalars R I) :=
      Module.Finite.equiv ((Submodule.quotEquivOfEqBot (I • T) hsmul).restrictScalars R)
    have : Module.Finite R (A ⧸ Submodule.restrictScalars R I) := fin
    exact Module.Finite.of_submodule_quotient (Submodule.restrictScalars R I)
  · intro S _ I J hIJ hI _ _ _ _
    have : Module.Finite R ((S ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J) :=
      Module.Finite.equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ R hIJ).symm.toLinearEquiv
    exact hI

lemma quotient_of_quotient_radical_finite (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] [IsNoetherianRing A] (I : Ideal A)
    [Module.Finite R (A ⧸ I.radical)] : Module.Finite R (A ⧸ I) := by
  let S : Type _ := A ⧸ I
  have hm : Ideal.map (Ideal.Quotient.mk I) I.radical = nilradical S := by
    rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by simp [Ideal.mk_ker])]
    simp [Ideal.map_quotient_self, nilradical]
  let e : (S ⧸ nilradical S) ≃ₐ[R] A ⧸ I.radical :=
    (Ideal.quotientEquivAlgOfEq R hm.symm).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ R I.le_radical)
  have : Module.Finite R (S ⧸ nilradical S) := Module.Finite.equiv e.symm.toLinearEquiv
  exact quotient_of_quotient_isNilpotent_finite R (IsNoetherianRing.isNilpotent_nilradical S)

end Module.Finite
