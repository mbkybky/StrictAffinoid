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

lemma fg_of_quotient_map_fg {R : Type*} [CommRing R] {I J : Ideal R}
    (hmap : (Ideal.map (Ideal.Quotient.mk J) I).FG) (hJ : J.FG) (hJI : J ≤ I) : I.FG :=
  fg_of_fg_map_of_fg_inf_ker_of_surjective hmap (by simp [inf_eq_right.mpr hJI, hJ])
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
    have hsmul : I • (⊤ : Submodule A I) = ⊥ := by
      ext x
      simp [Submodule.mem_smul_top_iff, ← pow_two, hsq]
    have : Module.Finite R (I ⧸ I • (⊤ : Submodule A I)) := Module.Finite.trans (A ⧸ I) (I ⧸ I • ⊤)
    have : Module.Finite R (Submodule.restrictScalars R I) := Module.Finite.equiv
      ((Submodule.quotEquivOfEqBot (I • (⊤ : Submodule A I)) hsmul).restrictScalars R)
    have : Module.Finite R (A ⧸ Submodule.restrictScalars R I) := fin
    exact Module.Finite.of_submodule_quotient (Submodule.restrictScalars R I)
  · intro S _ I J hIJ hI _ _ _ _
    have : Module.Finite R ((S ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J) :=
      Module.Finite.equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ R hIJ).symm.toLinearEquiv
    exact hI

lemma quotient_of_quotient_radical_finite (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] [IsNoetherianRing A] (I : Ideal A)
    [Module.Finite R (A ⧸ I.radical)] : Module.Finite R (A ⧸ I) := by
  have hm : Ideal.map (Ideal.Quotient.mk I) I.radical = nilradical (A ⧸ I) := by
    rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by simp)]
    simp [nilradical]
  let e : ((A ⧸ I) ⧸ nilradical (A ⧸ I)) ≃ₐ[R] A ⧸ I.radical :=
    (Ideal.quotientEquivAlgOfEq R hm.symm).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ R I.le_radical)
  have : Module.Finite R ((A ⧸ I) ⧸ nilradical (A ⧸ I)) := Module.Finite.equiv e.symm.toLinearEquiv
  exact quotient_of_quotient_isNilpotent_finite R (IsNoetherianRing.isNilpotent_nilradical (A ⧸ I))

end Module.Finite
