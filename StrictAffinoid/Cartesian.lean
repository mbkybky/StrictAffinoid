/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StrictAffinoid.Weierstrass

@[expose] public section

open Module LocalizedModule

open scoped BigOperators Pointwise nonZeroDivisors

namespace Submodule

variable {α R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

theorem smul_pointwise_eq_self_of_isUnit [SMul α R] [IsScalarTower α R M] {N : Submodule R M}
    {u : α} (hu : IsUnit u) : u • N = N := by
  ext x
  rw [N.mem_smul_pointwise_iff_exists]
  rcases hu with ⟨u, rfl⟩
  refine ⟨?_, fun hx ↦ ⟨u.inv • x, N.smul_of_tower_mem u.inv hx, by simp [← mul_smul]⟩⟩
  rintro ⟨m, hm, rfl⟩
  exact N.smul_of_tower_mem u hm

theorem mul_smul_pointwise_eq_of_isUnit [SMul α R] [IsScalarTower α R M] {N : Submodule R M}
    {u : α} (hu : IsUnit u) (v : α) : (u * v) • N = v • N := by
  rw [mul_smul, (v • N).smul_pointwise_eq_self_of_isUnit hu]

end Submodule

theorem Module.smul_top_eq_smul_top_of_field_smul {k A M : Type*}
    [Field k] [CommSemiring A] [Algebra k A] [AddCommMonoid M] [Module A M]
    {c : k} (hc : c ≠ 0) (ω : A) :
    (c • ω) • (⊤ : Submodule A M) = ω • (⊤ : Submodule A M) := by
  rw [Algebra.smul_def, Submodule.mul_smul_pointwise_eq_of_isUnit
    (IsUnit.map (algebraMap k A) (isUnit_iff_ne_zero.mpr hc))]

theorem IsLocalizedModule.mk'_eq_localization_smul
    {R M M' : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
    {p : Submonoid R} [Algebra R S] [IsLocalization p S]
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M']
    [Module S M'] [IsScalarTower R S M']
    (f : M →ₗ[R] M') [IsLocalizedModule p f] (m : M) (s : p) :
    IsLocalizedModule.mk' f m s = (IsLocalization.mk' S (1 : R) s) • f m := by
  rw [IsLocalizedModule.mk'_eq_iff]
  change f m = (s : R) • ((IsLocalization.mk' S (1 : R) s) • f m)
  rw [← smul_assoc, Algebra.smul_def]
  simp [mul_comm]

section Cartesian

variable {A : Type*} [SeminormedRing A] {M : Type*} [SeminormedAddCommGroup M] [Module A M]

namespace Module

variable (A) {σ : Type*} [Fintype σ] (e : σ → M)

/-- Let $ M $ be a seminormed $ A $-module. Then $ e_1, \dots, e_n \in M $ form a pseudo-cartesian
generator if for any $ m \in M $, there exist $ a_i \in A $ such that
$ m = \sum\limits_i a_i e_i $ and $ \|a_i\| \|e_i\| \le \|m\| $ for all $ i $. -/
structure IsPseudoCartesianGenerator : Prop where
  exists_norm_le (m : M) : ∃ a : σ → A, m = ∑ i, a i • e i ∧ ∀ i : σ, ‖a i‖ * ‖e i‖ ≤ ‖m‖

/-- Let $ M $ be a seminormed $ A $-module, Then $ e_1, \dots, e_n \in M $ form a cartesian
generator if for any $ m \in M $ and any expression
$ m = \sum\limits_i a_i e_i $, we have $ \|a_i\| \|e_i\| \le \|m\| $ for all $ i $. -/
structure IsCartesianGenerator : Prop extends IsPseudoCartesianGenerator A e where
  norm_le (m : M) (a : σ → A) (_ : m = ∑ i, a i • e i) (i : σ) : ‖a i‖ * ‖e i‖ ≤ ‖m‖

/-- Let $ M $ be a seminormed $ R $-module, $ e_1, \dots, e_n \in M^\circ $. If for any $ a \in M $,
there exist $ a_i \in A $ such that $ a = \sum\limits_{i = 1}^n a_i • e_i $ and
$ \|a_i\| \le \|a\| $, then we say that $ e_1, \dots, e_n $ boundedly generate $ M $. -/
structure IsBoundedGenerator : Prop where
  norm_le_one (i : σ) : ‖e i‖ ≤ 1
  boundedly_generate (m : M) : ∃ a : σ → A, m = ∑ i, a i • e i ∧ ∀ i : σ, ‖a i‖ ≤ ‖m‖

/-- A seminormed module is called a pseudo-cartesian module if it admits a pseudo-cartesian
generating system. -/
class IsPseudoCartesian
    (A M : Type*) [SeminormedRing A] [SeminormedAddCommGroup M] [Module A M] : Prop where
  out (A M) : ∃ (σ : Type) (_ : Fintype σ) (e : σ → M), IsPseudoCartesianGenerator A e

/-- A seminormed module is called a cartesian module if it admits a cartesian generating system. -/
class IsCartesian
    (A M : Type*) [SeminormedRing A] [SeminormedAddCommGroup M] [Module A M] : Prop where
  out (A M) : ∃ (σ : Type) (_ : Fintype σ) (e : σ → M), IsCartesianGenerator A e

/-- A seminormed module is called a boundedly generated module if it admits a boundedly generating
system. -/
class IsBoundedlyGenerated
    (A M : Type*) [SeminormedRing A] [SeminormedAddCommGroup M] [Module A M] : Prop where
  out (A M) : ∃ (σ : Type) (_ : Fintype σ) (e : σ → M), IsBoundedGenerator A e

variable (M)

instance [NormOneClass A] : IsCartesian A A where
  out :=
    ⟨PUnit, inferInstance, fun _ ↦ 1, ⟨⟨fun m ↦ ⟨fun _ ↦ m, by simp⟩⟩, fun m a hm i ↦ by simp [hm]⟩⟩

instance [IsCartesian A M] : IsPseudoCartesian A M where
  out := by
    rcases IsCartesian.out A M with ⟨σ, hσ, e, he⟩
    exact ⟨σ, hσ, e, he.toIsPseudoCartesianGenerator⟩

scoped instance IsPseudoCartesian.module_finite [IsPseudoCartesian A M] :
    Module.Finite A M := by
  rcases IsPseudoCartesian.out A M with ⟨σ, hσ, e, he⟩
  refine Module.Finite.of_fg_top ?_
  rw [Submodule.fg_def]
  refine ⟨Set.range e, Set.finite_range e, ?_⟩
  rw [eq_top_iff]
  intro m _
  rcases he.exists_norm_le m with ⟨a, hm, -⟩
  rw [hm]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable {A M}

theorem IsPseudoCartesian.of_linearEquiv
    {M₂ : Type*} [SeminormedAddCommGroup M₂] [Module A M₂]
    (e : M ≃ₗ[A] M₂) (he : ∀ x : M, ‖e x‖ = ‖x‖)
    [IsPseudoCartesian A M₂] : IsPseudoCartesian A M := by
  rcases IsPseudoCartesian.out A M₂ with ⟨σ, hσ, g, hg⟩
  refine ⟨σ, hσ, fun i ↦ e.symm (g i), ⟨?_⟩⟩
  intro m
  rcases hg.exists_norm_le (e m) with ⟨a, ha_repr, ha_norm⟩
  refine ⟨a, e.injective (by simp [ha_repr]), fun i ↦ ?_⟩
  simp [← he m, (he (e.symm (g i))).symm, ha_norm i]

theorem IsCartesian.of_linearEquiv
    {M₂ : Type*} [SeminormedAddCommGroup M₂] [Module A M₂]
    (e : M ≃ₗ[A] M₂) (he : ∀ x : M, ‖e x‖ = ‖x‖)
    [IsCartesian A M₂] : IsCartesian A M := by
  rcases IsCartesian.out A M₂ with ⟨σ, hσ, g, hg⟩
  have hsymm_norm (x : M₂) : ‖e.symm x‖ = ‖x‖ := by simpa using (he (e.symm x)).symm
  refine ⟨σ, hσ, fun i ↦ e.symm (g i), ⟨⟨?_⟩, ?_⟩⟩
  · intro m
    rcases hg.exists_norm_le (e m) with ⟨a, ha_repr, ha_norm⟩
    refine ⟨a, e.injective (by simp [ha_repr]), fun i ↦ ?_⟩
    grw [hsymm_norm (g i), ← he m, ha_norm i]
  · intro m a hm i
    have hm₂ : e m = ∑ j : σ, a j • g j := by simp [hm]
    grw [hsymm_norm (g i), ← he m, hg.norm_le (e m) a hm₂]

theorem IsPseudoCartesian.extendScalars_of_isometric_algebra
    {B R : Type*} [SeminormedCommRing B] [SeminormedRing R] [Algebra B R]
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    (hnorm : ∀ b : B, ‖algebraMap B R b‖ = ‖b‖)
    [IsPseudoCartesian B M] : IsPseudoCartesian R M := by
  rcases IsPseudoCartesian.out B M with ⟨σ, hσ, e, he⟩
  refine ⟨σ, hσ, e, ⟨?_⟩⟩
  intro m
  rcases he.exists_norm_le m with ⟨a, hm, ha⟩
  exact ⟨fun i ↦ algebraMap B R (a i), by simp [hm], fun i ↦ by grw [hnorm, ha i]⟩

theorem IsPseudoCartesian.of_ringEquiv
    {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    {M : Type*} [NormedAddCommGroup M] [Module S M]
    (e : R ≃+* S) (he : ∀ x : R, ‖e x‖ = ‖x‖)
    [@IsPseudoCartesian R M _ _ (Module.compHom M e.toRingHom)] :
    IsPseudoCartesian S M := by
  let : Module R M := Module.compHom M e.toRingHom
  rcases IsPseudoCartesian.out R M with ⟨σ, hσ, g, hg⟩
  refine ⟨σ, hσ, g, ⟨?_⟩⟩
  intro m
  rcases hg.exists_norm_le m with ⟨a, ha_repr, ha_norm⟩
  refine ⟨fun i ↦ e (a i), ?_, ?_⟩
  · simpa [Module.compHom] using! ha_repr
  · exact fun i ↦ by simp [he, ha_norm i]

theorem IsCartesian.of_ringEquiv
    {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    {M : Type*} [NormedAddCommGroup M] [Module S M]
    (e : R ≃+* S) (he : ∀ x : R, ‖e x‖ = ‖x‖) [IsCartesian S M] :
    let : Module R M := Module.compHom M e.toRingHom
    IsCartesian R M := by
  let : Module R M := Module.compHom M e.toRingHom
  have he_symm (y : S) : ‖e.symm y‖ = ‖y‖ := by simpa using (he (e.symm y)).symm
  rcases IsCartesian.out S M with ⟨σ, hσ, g, hg⟩
  refine ⟨σ, hσ, g, ⟨⟨?_⟩, ?_⟩⟩
  · intro m
    rcases hg.exists_norm_le m with ⟨b, hb_repr, hb_norm⟩
    refine ⟨fun i ↦ e.symm (b i), ?_, ?_⟩
    · change m = ∑ i : σ, e (e.symm (b i)) • g i
      simpa using hb_repr
    · intro i
      simp [he_symm, hb_norm i]
  · intro m a hm i
    have hmS : m = ∑ j : σ, e (a j) • g j := by simpa [Module.compHom] using! hm
    simpa [he] using hg.norm_le m (fun j ↦ e (a j)) hmS i

theorem IsBoundedSMul.of_ringEquiv
    {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    {M : Type*} [NormedAddCommGroup M] [Module S M] [IsBoundedSMul S M]
    (e : R ≃+* S) (he : ∀ x : R, ‖e x‖ = ‖x‖) :
    let : Module R M := Module.compHom M e.toRingHom
    IsBoundedSMul R M := by
  let : Module R M := Module.compHom M e.toRingHom
  refine ⟨?_, ?_⟩
  · intro c x y
    rw [show dist c 0  = dist (e c) 0 by simp [dist_eq_norm, he c]]
    exact dist_smul_pair (e c) x y
  · intro c d x
    have hdist : dist (e c) (e d) = dist c d := by simp [dist_eq_norm, ← map_sub, he (c - d)]
    rw [← hdist]
    exact dist_pair_smul (e c) (e d) x

theorem IsPseudoCartesian.of_isometry
    {V : Type*} [SeminormedAddCommGroup V] [Module A V]
    (L : M →ₗ[A] V) (hL : Function.Injective L)
    (hNorm : ∀ x : M, ‖L x‖ = ‖x‖) (N : Submodule A M) [IsPseudoCartesian A (N.map L)] :
    IsPseudoCartesian A N :=
  IsPseudoCartesian.of_linearEquiv (Submodule.equivMapOfInjective L hL N) (fun x ↦ hNorm x)

theorem IsPseudoCartesian.submoduleOf {N K : Submodule A M} (hNK : N ≤ K)
    [IsPseudoCartesian A N] : IsPseudoCartesian A (N.submoduleOf K) :=
  IsPseudoCartesian.of_linearEquiv (N.submoduleOfEquivOfLe hNK) (fun _ ↦ rfl)

theorem IsPseudoCartesian.of_submoduleOf {N K : Submodule A M} (hKN : K ≤ N)
    [IsPseudoCartesian A (K.submoduleOf N)] : IsPseudoCartesian A K :=
  IsPseudoCartesian.of_linearEquiv (K.submoduleOfEquivOfLe hKN).symm (fun _ ↦ rfl)

/-- If $ e_1, \dots, e_n $ boundedly generate $ M $, then it form a pseudo-cartesian generator. -/
theorem IsBoundedGenerator.isPseudoCartesianGenerator (h : IsBoundedGenerator A e) :
    IsPseudoCartesianGenerator A e where
  exists_norm_le m := by
    rcases h.boundedly_generate m with ⟨a, hm, ha⟩
    refine ⟨a, hm, fun i ↦ ?_⟩
    grw [ha i, h.norm_le_one i]
    simp

/-- Let `k` be a normed field, `A` a normed algebra over `k`, and `M` a normed `A`-module.
If `‖M‖ ⊆ |k|`, then `M` is a boundedly generated `A`-module. -/
theorem IsPseudoCartesian.isBoundedlyGenerated_of_value_group_subset (k A M : Type*)
    [NormedField k] [SeminormedRing A] [NormedAlgebra k A] [NormedAddCommGroup M] [Module k M]
    [IsBoundedSMul k M] [Module A M] [IsScalarTower k A M] [IsPseudoCartesian A M]
    (h : ∀ m : M, ∃ x : k, ‖x‖ = ‖m‖) : IsBoundedlyGenerated A M := by
  rcases IsPseudoCartesian.out A M with ⟨σ, hσ, e, he⟩
  choose c hc using fun i : σ ↦ h (e i)
  let e' : Option σ → M := fun
    | none => 0
    | some i => (c i)⁻¹ • e i
  refine ⟨Option σ, inferInstance, e', ⟨?_, ?_⟩⟩
  · rintro (_ | i)
    · simp [e']
    · by_cases hci : c i = 0
      · have hei_norm : ‖e i‖ = 0 := by rw [← hc i, hci, norm_zero]
        simp [e', hci, norm_eq_zero.mp hei_norm]
      · have h := norm_smul_le ((c i)⁻¹) (e i)
        grw [norm_inv, ← hc i] at h
        simpa [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hci)] using h
  · intro m
    rcases he.exists_norm_le m with ⟨a, hm, ha⟩
    let b : Option σ → A := fun
      | none => 0
      | some i => c i • a i
    refine ⟨b, ?_, ?_⟩
    · have hterm (i : σ) : (c i • a i : A) • ((c i)⁻¹ • e i) = a i • e i := by
        by_cases hci : c i = 0
        · have hei_norm : ‖e i‖ = 0 := by rw [← hc i, hci, norm_zero]
          simp [norm_eq_zero.mp hei_norm]
        · rw [smul_assoc, smul_comm (a i) ((c i)⁻¹) (e i), smul_smul, mul_inv_cancel₀ hci, one_smul]
      have hsum : (∑ j : Option σ, b j • e' j) = ∑ i, a i • e i := by simp [b, e', hterm]
      exact hm.trans hsum.symm
    · rintro (_ | i)
      · simp [b, norm_nonneg m]
      · grw [norm_smul_le, hc i, mul_comm, ha i]

variable {A : Type*} [NormedRing A] {M : Type*} [NormedAddCommGroup M] [Module A M]
  {σ : Type*} [Fintype σ] {e : σ → M}

theorem IsCartesianGenerator.linearIndependent_of_ne_zero (h : IsCartesianGenerator A e)
    (hne : ∀ i, e i ≠ 0) : LinearIndependent A e := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  let a : σ → A := fun j ↦ if j ∈ s then g j else 0
  have hsum : (∑ j, a j • e j) = 0 := by simp [a, hg]
  have hle : ‖a i‖ * ‖e i‖ ≤ 0 := by simpa using h.norm_le 0 a hsum.symm i
  have hprod : ‖a i‖ * ‖e i‖ = 0 :=
    le_antisymm hle (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa [a, hi] using (mul_eq_zero.mp hprod).resolve_right (norm_pos_iff.mpr (hne i)).ne'

variable (A M) in
theorem IsCartesian.exists_non_zero_cartesianGenerator [IsCartesian A M] :
    ∃ (σ : Type) (_ : Fintype σ) (e : σ → M) (_ : ∀ i, e i ≠ 0), IsCartesianGenerator A e := by
  classical
  rcases IsCartesian.out A M with ⟨σ, hσ, e, he⟩
  refine ⟨{i : σ // e i ≠ 0}, inferInstance, fun i ↦ e i, fun ⟨_, hi⟩ ↦ hi, ⟨?_⟩, ?_⟩
  · intro m
    rcases he.exists_norm_le m with ⟨a, hm, ha⟩
    refine ⟨fun i : {i : σ // e i ≠ 0} ↦ a i, ?_, ?_⟩
    · rw [hm]
      have hfilter : ∑ i with e i ≠ 0, a i • e i = ∑ i : σ, a i • e i :=
        Finset.sum_filter_of_ne fun i _ hterm hi ↦ hterm (by simp [hi])
      exact hfilter.symm.trans <| Finset.sum_subtype (Finset.univ.filter (fun i : σ ↦ e i ≠ 0))
        (fun i ↦ by simp) (fun i : σ ↦ a i • e i)
    · exact fun i ↦ ha i
  · intro m a hm i
    let b : σ → A := fun j ↦ if h : e j ≠ 0 then a ⟨j, h⟩ else 0
    have hsum : m = ∑ j : σ, b j • e j := by
      have hfilter : ∑ j with e j ≠ 0, b j • e j = ∑ j : σ, b j • e j :=
        Finset.sum_filter_of_ne fun j _ hterm hj ↦ hterm (by simp [hj])
      have hsubtype : ∑ j with e j ≠ 0, b j • e j = ∑ j : {j : σ // e j ≠ 0}, a j • e j := by
        trans ∑ j : {j : σ // e j ≠ 0}, b j • e j
        · exact Finset.sum_subtype (Finset.univ.filter (fun j : σ ↦ e j ≠ 0))
            (fun _ ↦ by simp) (fun j : σ ↦ b j • e j)
        · refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp [b, j.2]
      rw [hm, ← hsubtype, hfilter]
    simpa [b, i.2] using he.norm_le m b hsum i

/-- The elements of a cartesian generator that are nonzero form a basis. -/
noncomputable def IsCartesianGenerator.nonzeroBasis
    (h : IsCartesianGenerator A e) (hne : ∀ i, e i ≠ 0) : Module.Basis σ A M := by
  refine Module.Basis.mk (linearIndependent_of_ne_zero h hne) ?_
  intro m _
  rcases h.exists_norm_le m with ⟨a, rfl, -⟩
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem Matrix.cramer_mulVec_eq_det_smul {k s : Type*} [Field k] [Fintype s] [DecidableEq s]
    (A : Matrix s s k) (hdet : A.det ≠ 0) (c : s → k) :
    A.cramer (A.mulVec c) = A.det • c := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hunit
  rw [← Matrix.det_smul_inv_mulVec_eq_cramer A (A.mulVec c) hunit, Matrix.inv_mulVec_eq_vec rfl]

open IsPseudoCartesian in
/-- Let `k` be a normed field and `M` a cartesian `k`-vector space. If the norm of `M` is
non-archimedean, then any linear subspace of `M` is cartesian. -/
instance _root_.Submodule.IsCartesian.of_normedField {k M : Type*} [NormedField k]
    [NormedAddCommGroup M] [IsUltrametricDist M] [Module k M]
    [IsBoundedSMul k M] [IsCartesian k M] (N : Submodule k M) : IsCartesian k N := by
  classical
  rcases IsCartesian.exists_non_zero_cartesianGenerator k M with ⟨σ, hσ, e, hne, he⟩
  let B : Module.Basis σ k M := he.nonzeroBasis hne
  have hB_pos (i : σ) : 0 < ‖B i‖ := norm_pos_iff.mpr (B.ne_zero i)
  let row : σ → Module.Dual k N := fun i ↦ (B.coord i).comp N.subtype
  have hcoord_le (x : N) (i : σ) : ‖row i x‖ * ‖B i‖ ≤ ‖x‖ := by
    have hxsum : (x : M) = ∑ i : σ, row i x • B i := by simp [row, Module.Basis.coord_apply]
    simp only [IsCartesianGenerator.nonzeroBasis, Basis.coe_mk, B] at hxsum ⊢
    exact he.norm_le (x : M) (fun i : σ ↦ row i x) hxsum i
  have hambient_upper (x : N) (C : ℝ) (hC : 0 ≤ C)
      (hcoords : ∀ i : σ, ‖row i x‖ * ‖B i‖ ≤ C) : ‖x‖ ≤ C := by
    have hxsum : (x : M) = ∑ i : σ, row i x • B i := by simp [row, Module.Basis.coord_apply]
    change ‖(x : M)‖ ≤ C
    grw [hxsum, IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC]
    exact fun i _ ↦ by grw [norm_smul_le, hcoords]
  have hrow_span : Submodule.span k (Set.range row) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rcases LinearMap.exists_extend f with ⟨g, hg⟩
    have hf_decomp : f = ∑ i : σ, g (B i) • row i := by
      rw [← hg]
      ext x
      have hx : (x : M) = ∑ i : σ, (B.repr (x : M)) i • B i := by simp
      change g (x : M) = (∑ i : σ, g (B i) • row i) x
      rw [hx, map_sum]
      simp [row, Module.Basis.coord_apply, map_smul, smul_eq_mul, mul_comm]
    rw [hf_decomp]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rcases exists_linearIndependent k (Set.range row) with ⟨s, hss, hs_span, hs_li⟩
  have hs_top : Submodule.span k s = ⊤ := by rwa [hrow_span] at hs_span
  have : Fintype s := ((Set.finite_range row).subset hss).fintype
  let ψ : Module.Basis s k (Module.Dual k N) := by
    refine Module.Basis.mk hs_li ?_
    intro f _
    rw [show Set.range (Subtype.val : s → Module.Dual k N) = s by
      ext f
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hf
        exact ⟨⟨f, hf⟩, rfl⟩]
    simp [hs_top]
  let idx : s → σ := fun j ↦ Classical.choose (hss j.2)
  have hidx (j : s) : row (idx j) = ψ j := by simpa [idx, ψ] using (hss j.2).choose_spec
  let mat : (s → σ) → Matrix s s k := fun p i j ↦ ψ.equivFun (row (p j)) i
  have hmat_idx : mat idx = 1 := by
    ext i j
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [mat, hidx]
    · simp [mat, hidx, hij]
  let Candidate := {p : s → σ // (mat p).det ≠ 0}
  have : Nonempty Candidate := ⟨⟨idx, by simp [hmat_idx]⟩⟩
  let weight : Candidate → ℝ := fun p ↦ ‖(mat p.1).det‖ * ∏ j : s, ‖B (p.1 j)‖
  obtain ⟨pmax, -, hpmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  have hpmax_le (q : Candidate) : weight q ≤ weight pmax := hpmax q (by simp)
  let p : s → σ := pmax.1
  have hdetp : (mat p).det ≠ 0 := pmax.2
  have hcols' : LinearIndependent k (fun j : s ↦ ψ.equivFun (row (p j))) := by
    simpa [mat, p, Matrix.col] using! Matrix.linearIndependent_cols_of_det_ne_zero hdetp
  have hker : (ψ.equivFun.symm : (s → k) →ₗ[k] Module.Dual k N).ker = ⊥ :=
    LinearEquiv.ker ψ.equivFun.symm
  have hli_phi : LinearIndependent k (fun j : s ↦ row (p j)) := by
    have hmap := hcols'.map' (ψ.equivFun.symm : (s → k) →ₗ[k] Module.Dual k N) hker
    convert hmap using 1
    ext j
    simp [Function.comp, Module.Basis.equivFun_apply]
  have hspan_phi : Submodule.span k (Set.range (fun j : s ↦ row (p j))) = ⊤ :=
    hli_phi.span_eq_top_of_card_eq_finrank' ((Module.finrank_eq_card_basis ψ).symm)
  let φBasis : Module.Basis s k (Module.Dual k N) :=
    Module.Basis.mk hli_phi <| fun f _ ↦ by simp [hspan_phi]
  have hφ_apply (j : s) : φBasis j = row (p j) := by simp [φBasis]
  let bN := Module.finBasis k N
  let evalE : N ≃ₗ[k] Module.Dual k (Module.Dual k N) :=
    bN.toDualEquiv.trans bN.dualBasis.toDualEquiv
  have heval (x : N) (f : Module.Dual k N) : evalE x f = f x := by
    change (bN.dualBasis.toDualEquiv (bN.toDualEquiv x)) f = f x
    rw [Module.Basis.toDualEquiv_apply, Module.Basis.toDualEquiv_apply]
    have h := LinearMap.congr_fun (Module.Basis.toDual_toDual bN) x
    exact LinearMap.congr_fun h f
  let uBasis : Module.Basis s k N := φBasis.dualBasis.map evalE.symm
  have hcoeff (f : Module.Dual k N) (j : s) : φBasis.equivFun f j = f (uBasis j) := by
    simpa [uBasis] using heval (uBasis j) f
  have hcoord_u (i j : s) : row (p i) (uBasis j) = if i = j then 1 else 0 := by
    rw [← heval (uBasis j) (row (p i))]
    simpa [uBasis, hφ_apply, eq_comm] using Module.Basis.dualBasis_apply_self φBasis j i
  have hdet_update (k0 : σ) (j : s) :
      (mat (Function.update p j k0)).det = (mat p).det * row k0 (uBasis j) := by
    let A := mat p
    let c : s → k := φBasis.equivFun (row k0)
    have hb : ψ.equivFun (row k0) = A.mulVec c := by
      ext i
      rw [show row k0 = φBasis.equivFun.symm c by simp [c], Module.Basis.equivFun_symm_apply]
      trans ∑ l : s, c l * ψ.equivFun (row (p l)) i
      · simp [hφ_apply]
      · refine Finset.sum_congr rfl ?_
        intro l _
        simp [A, mat, mul_comm]
    have hmat_update : mat (Function.update p j k0) = A.updateCol j (ψ.equivFun (row k0)) := by
      ext i l
      by_cases hlj : l = j
      · subst hlj
        simp [A, mat]
      · simp [A, mat, Function.update, hlj]
    rw [hmat_update]
    trans A.cramer (ψ.equivFun (row k0)) j
    · rw [Matrix.cramer_apply]
    trans (A.det • c) j
    · rw [hb, Matrix.cramer_mulVec_eq_det_smul A hdetp c]
    · change A.det * c j = A.det * row k0 (uBasis j)
      rw [show c j = row k0 (uBasis j) by simpa [c] using hcoeff (row k0) j]
  have hcoeff_bound (k0 : σ) (j : s) : ‖row k0 (uBasis j)‖ * ‖B k0‖ ≤ ‖B (p j)‖ := by
    let c := row k0 (uBasis j)
    by_cases hc : c = 0
    · simp [c, hc, norm_nonneg]
    let qfun : s → σ := Function.update p j k0
    have hdetq : (mat qfun).det ≠ 0 := by
      rw [hdet_update k0 j]
      exact mul_ne_zero hdetp hc
    let qCand : Candidate := ⟨qfun, hdetq⟩
    let E : ℝ := ∏ l ∈ (Finset.univ.erase j), ‖B (p l)‖
    have hEpos : 0 < E := Finset.prod_pos fun l _ ↦ hB_pos (p l)
    have hDpos : 0 < ‖(mat p).det‖ := norm_pos_iff.mpr hdetp
    have hprod_q : (∏ l : s, ‖B (qfun l)‖) = ‖B k0‖ * E := by
      have hupdate :
          (∏ l : s, Function.update (fun l : s ↦ ‖B (p l)‖) j ‖B k0‖ l) = ‖B k0‖ * E := by
        simpa [E, Finset.sdiff_singleton_eq_erase] using
          Finset.prod_update_of_mem (by simp) (fun l : s ↦ ‖B (p l)‖) ‖B k0‖
      trans ∏ l : s, Function.update (fun l : s ↦ ‖B (p l)‖) j ‖B k0‖ l
      · refine Finset.prod_congr rfl fun l _ ↦ ?_
        by_cases hlj : l = j
        · subst hlj
          simp [qfun]
        · simp [qfun, Function.update, hlj]
      · exact hupdate
    have hprod_p : (∏ l : s, ‖B (p l)‖) = ‖B (p j)‖ * E :=
      (Finset.mul_prod_erase Finset.univ (fun l : s ↦ ‖B (p l)‖)
        (Finset.mem_univ j)).symm
    have hmain : (‖(mat p).det‖ * E) * (‖c‖ * ‖B k0‖) ≤
        (‖(mat p).det‖ * E) * ‖B (p j)‖ := by
      have hmaxq := hpmax_le qCand
      dsimp [weight, qCand, qfun, p] at hmaxq
      rw [hprod_q, hprod_p, hdet_update k0 j, norm_mul] at hmaxq
      nlinarith [hmaxq]
    exact (mul_le_mul_iff_of_pos_left (mul_pos hDpos hEpos)).mp hmain
  have hu_norm (j : s) : ‖uBasis j‖ = ‖B (p j)‖ := by
    refine le_antisymm ?_ ?_
    · exact hambient_upper (uBasis j) ‖B (p j)‖ (norm_nonneg _) fun i ↦ hcoeff_bound i j
    · have hpivot : row (p j) (uBasis j) = 1 := by simpa using hcoord_u j j
      simpa [hpivot] using hcoord_le (uBasis j) (p j)
  let γ := Fin (Fintype.card s)
  let finEquiv : s ≃ γ := Fintype.equivFin s
  let uFinBasis : Module.Basis γ k N := uBasis.reindex finEquiv
  have huFin_norm (j : γ) : ‖uFinBasis j‖ = ‖B (p (finEquiv.symm j))‖ := by
    simpa [uFinBasis, finEquiv] using hu_norm (finEquiv.symm j)
  have hcoord_uFin (i j : γ) :
      row (p (finEquiv.symm i)) (uFinBasis j) = if i = j then 1 else 0 := by
    simpa [uFinBasis, finEquiv] using hcoord_u (finEquiv.symm i) (finEquiv.symm j)
  refine ⟨γ, inferInstance, uFinBasis, ⟨⟨?_⟩, ?_⟩⟩
  · intro m
    refine ⟨fun j ↦ (uFinBasis.repr m) j, ?_, ?_⟩
    · exact (uFinBasis.sum_repr m).symm
    · intro j
      have hrow : row (p (finEquiv.symm j)) m = (uFinBasis.repr m) j := by
        have hm_sum : m = ∑ l : γ, (uFinBasis.repr m) l • uFinBasis l := by simp
        rw [hm_sum, map_sum]
        trans ∑ l : γ, (uFinBasis.repr m) l *
            row (p (finEquiv.symm j)) (uFinBasis l)
        · refine Finset.sum_congr rfl fun l _ ↦ ?_
          simp [map_smul, smul_eq_mul]
        · rw [Finset.sum_eq_single j]
          · simp [hcoord_uFin]
          · intro l _ hlj
            have hne : j ≠ l := fun h ↦ hlj h.symm
            simp [hcoord_uFin, hne]
          · exact fun hj ↦ (hj (Finset.mem_univ j)).elim
      simpa [hrow, huFin_norm j] using hcoord_le m (p (finEquiv.symm j))
  · intro m a hm j
    have hrow : row (p (finEquiv.symm j)) m = a j := by
      rw [hm, map_sum]
      trans ∑ l : γ, a l * row (p (finEquiv.symm j)) (uFinBasis l)
      · refine Finset.sum_congr rfl fun l _ ↦ ?_
        simp [map_smul, smul_eq_mul]
      · rw [Finset.sum_eq_single j]
        · simp [hcoord_uFin]
        · intro l _ hlj
          have hne : j ≠ l := fun h ↦ hlj h.symm
          simp [hcoord_uFin, hne]
        · exact fun hj ↦ (hj (Finset.mem_univ j)).elim
    simpa [hrow, huFin_norm j] using hcoord_le m (p (finEquiv.symm j))

end Module

namespace Submodule

/-- A submodule `N` of a seminormed module `M` is strictly closed if  for every `x : M ⧸ N`,
there exists a lift `m : M` with `‖m‖ = ‖x‖`. -/
def IsStrictlyClosed (N : Submodule A M) : Prop :=
  ∀ x : M ⧸ N, ∃ m : M, N.mkQ m = x ∧ ‖m‖ = ‖x‖

variable (M) in
theorem top_isStrictlyClosed : (⊤ : Submodule A M).IsStrictlyClosed :=
  fun x ↦ ⟨0, Subsingleton.elim _ _, by simp [Subsingleton.elim x 0]⟩

theorem IsStrictlyClosed.isClosed {M : Type*} [NormedAddCommGroup M] [Module A M]
    {N : Submodule A M} (hN : N.IsStrictlyClosed) : IsClosed (N : Set M) := by
  refine isClosed_of_closure_subset ?_
  intro x hx
  have hxnorm : ‖N.mkQ x‖ = 0 := QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure.2 hx
  rcases hN (N.mkQ x) with ⟨m, hm, hnorm⟩
  have hm0 : m = 0 := by rw [← norm_eq_zero, hnorm, hxnorm]
  exact (Submodule.Quotient.mk_eq_zero N).1 (by simpa [hm0] using hm.symm)

theorem IsStrictlyClosed.submoduleOf {N K : Submodule A M} (hNK : N ≤ K)
    (hN : N.IsStrictlyClosed) : (N.submoduleOf K).IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  rcases hN (N.mkQ (m : M)) with ⟨r, hrq, hrnorm⟩
  have hr_mem : r ∈ K := by
    have hdiff : r - (m : M) ∈ N := by rwa [← Submodule.Quotient.eq]
    simpa [sub_eq_add_neg, add_assoc] using K.add_mem (hNK hdiff) m.2
  let rK : K := ⟨r, hr_mem⟩
  have hrK_q : (N.submoduleOf K).mkQ rK = (N.submoduleOf K).mkQ m := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    simp only [Submodule.submoduleOf, mem_comap, subtype_apply, AddSubgroupClass.coe_sub]
    rwa [← Submodule.Quotient.eq]
  refine ⟨rK, hrK_q, le_antisymm ?_ ?_⟩
  · change ‖r‖ ≤ ‖(N.submoduleOf K).mkQ m‖
    rw [hrnorm]
    refine QuotientAddGroup.le_norm_iff.2 ?_
    intro y hy
    have hyE : N.mkQ (y : M) = N.mkQ (m : M) := by
      simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hymem : y - m ∈ N.submoduleOf K := by rwa [← Submodule.Quotient.eq]
      exact hymem
    rw [← hyE]
    exact Submodule.Quotient.norm_mk_le N (y : M)
  · change ‖(N.submoduleOf K).mkQ m‖ ≤ ‖rK‖
    rw [← hrK_q]
    exact Submodule.Quotient.norm_mk_le (N.submoduleOf K) rK

theorem IsStrictlyClosed.of_contracting_quotient_projection {N : Submodule A M}
    (Q : M →ₗ[A] M) (hmem : ∀ x, x - Q x ∈ N) (hkill : ∀ x ∈ N, Q x = 0)
    (hcontr : ∀ x, ‖Q x‖ ≤ ‖x‖) : N.IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  have hqm : N.mkQ (Q m) = N.mkQ m := by
    simpa [Submodule.mkQ_apply, Submodule.Quotient.eq, neg_sub] using N.neg_mem (hmem m)
  refine ⟨Q m, hqm, le_antisymm ?_ ?_⟩
  · refine QuotientAddGroup.le_norm_iff.2 ?_
    intro y hy
    have hdiff : y - m ∈ N := by rwa [← Submodule.Quotient.eq]
    have hQeq : Q y = Q m := by simpa [sub_eq_zero] using hkill (y - m) hdiff
    grw [← hQeq, hcontr y]
  · change ‖N.mkQ m‖ ≤ ‖Q m‖
    rw [← hqm]
    exact Submodule.Quotient.norm_mk_le N (Q m)

theorem isUltrametricDistQuotientOfIsStrictlyClosed
    {A M : Type*} [SeminormedRing A] [SeminormedAddCommGroup M] [IsUltrametricDist M]
    [Module A M] (N : Submodule A M) (hN : N.IsStrictlyClosed) : IsUltrametricDist (M ⧸ N) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ?_
  intro x y
  rcases hN x with ⟨mx, hmx, hmxnorm⟩
  rcases hN y with ⟨my, hmy, hmynorm⟩
  rw [← hmxnorm, ← hmynorm, ← hmx, ← hmy, ← map_add]
  exact (Submodule.Quotient.norm_mk_le N (mx + my)).trans
    (IsUltrametricDist.norm_add_le_max mx my)

theorem isBoundedSMulQuotientOfIsStrictlyClosed
    {A M : Type*} [SeminormedRing A] [SeminormedAddCommGroup M] [Module A M]
    [IsBoundedSMul A M] (N : Submodule A M) (hN : N.IsStrictlyClosed) :
    IsBoundedSMul A (M ⧸ N) := by
  refine IsBoundedSMul.of_norm_smul_le ?_
  intro a x
  rcases hN x with ⟨m, hm, hmnorm⟩
  rw [← hmnorm, ← hm, ← map_smul]
  exact (Submodule.Quotient.norm_mk_le N (a • m)).trans (norm_smul_le a m)

theorem smul_top_submoduleOf_le_of_smul_le
    {R X : Type*} [CommSemiring R] [AddCommMonoid X] [Module R X] {N K : Submodule R X} {ω : R}
    (hωNK : ω • N ≤ K) : ω • (⊤ : Submodule R N) ≤ K.submoduleOf N := by
  intro x hx
  rw [Submodule.mem_smul_pointwise_iff_exists] at hx
  rcases hx with ⟨y, -, hy⟩
  exact hωNK ⟨(y : X), y.2, congrArg Subtype.val hy⟩

theorem restrictScalars_smul_top_eq_of_smul_eq
    {B R S X : Type*} [CommSemiring B] [CommSemiring R] [CommSemiring S] [Algebra B R] [Algebra B S]
    [AddCommMonoid X] [Module B X] [Module R X] [Module S X]
    [IsScalarTower B R X] [IsScalarTower B S X]
    (a : R) (b : S) (hsmul : ∀ x : X, b • x = a • x) :
    ((a • (⊤ : Submodule R X)).restrictScalars B) =
      ((b • (⊤ : Submodule S X)).restrictScalars B) := by
  ext x
  constructor <;> intro hx
  · change x ∈ a • (⊤ : Submodule R X) at hx
    change x ∈ b • (⊤ : Submodule S X)
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    rcases hx with ⟨y, -, hxy⟩
    exact ⟨y, Submodule.mem_top, by rw [hsmul y, hxy]⟩
  · change x ∈ b • (⊤ : Submodule S X) at hx
    change x ∈ a • (⊤ : Submodule R X)
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    rcases hx with ⟨y, -, hxy⟩
    exact ⟨y, Submodule.mem_top, by rw [← hsmul y, hxy]⟩

theorem IsStrictlyClosed.trans [IsUltrametricDist M] {N K : Submodule A M}
    (hN_in_K : (N.submoduleOf K).IsStrictlyClosed) (hK : K.IsStrictlyClosed)
    (hNK : N ≤ K) : N.IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  rcases hK (K.mkQ m) with ⟨r, hrq, hrnorm⟩
  have hmr_mem : m - r ∈ K := by
    have hrm : r - m ∈ K := by rwa [← Submodule.Quotient.eq]
    simpa [neg_sub] using K.neg_mem hrm
  let d : K := ⟨m - r, hmr_mem⟩
  rcases hN_in_K ((N.submoduleOf K).mkQ d) with ⟨s, hsq, hsnorm⟩
  let z : M := r + (s : M)
  have hzq : N.mkQ z = N.mkQ m := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hsd : (s : K) - d ∈ N.submoduleOf K := by rwa [← Submodule.Quotient.eq]
    have hmain : r + (s : M) - m = (s : M) - (m - r) := by abel
    simpa [z, hmain] using! hsd
  refine ⟨z, hzq, le_antisymm ?_ ?_⟩
  · refine (QuotientAddGroup.le_norm_iff).2 ?_
    intro y hy
    have hyN : y - m ∈ N := by rwa [← Submodule.Quotient.eq]
    have hyKq : K.mkQ y = K.mkQ m := by
      simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hNK hyN
    have hr_le_y : ‖r‖ ≤ ‖y‖ := by
      rw [hrnorm, ← hyKq]
      exact Submodule.Quotient.norm_mk_le K y
    have hyr_mem : y - r ∈ K := by
      have hym : y - m ∈ K := hNK hyN
      simpa [sub_eq_add_neg, add_assoc] using K.add_mem hym hmr_mem
    let t : K := ⟨y - r, hyr_mem⟩
    have htq : (N.submoduleOf K).mkQ t = (N.submoduleOf K).mkQ s := by
      simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
      change (y - r) - (s : M) ∈ N
      have hyz : y - z ∈ N := by
        rw [← Submodule.Quotient.eq]
        exact hy.trans hzq.symm
      have hmain : (y - r) - (s : M) = y - z := by
        simp [z, sub_eq_add_neg, add_comm, add_assoc]
      simpa [hmain] using hyz
    have hs_le_t : ‖s‖ ≤ ‖t‖ := by
      rw [hsnorm, ← htq.trans hsq]
      exact Submodule.Quotient.norm_mk_le (N.submoduleOf K) t
    have ht_le_y : ‖t‖ ≤ ‖y‖ := by
      change ‖y - r‖ ≤ ‖y‖
      grw [← max_eq_left hr_le_y]
      simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max y (-r)
    have hs_le_y : ‖(s : M)‖ ≤ ‖y‖ := hs_le_t.trans ht_le_y
    have hz_le := IsUltrametricDist.norm_add_le_max r (s : M)
    grw [hr_le_y, hs_le_y] at hz_le
    simpa [z] using hz_le
  · change ‖N.mkQ m‖ ≤ ‖z‖
    rw [← hzq]
    exact Submodule.Quotient.norm_mk_le N z

theorem IsStrictlyClosed.of_quotient {N K : Submodule A M} (hNK : N ≤ K)
    (hN : N.IsStrictlyClosed)
    (hKbar : (K.map N.mkQ).IsStrictlyClosed) : K.IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  let Kbar : Submodule A (M ⧸ N) := K.map N.mkQ
  rcases hKbar (Kbar.mkQ (N.mkQ m)) with ⟨q, hqK, hqnorm⟩
  rcases hN q with ⟨r, hrq, hrnorm⟩
  have hrKq : K.mkQ r = K.mkQ m := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hqmem : q - N.mkQ m ∈ Kbar := by rwa [← Submodule.Quotient.eq]
    rcases hqmem with ⟨k, hk, hkq⟩
    have hrm_q : N.mkQ (r - m) = N.mkQ k := by
      simpa [map_sub, hrq] using hkq.symm
    have hdiff : (r - m) - k ∈ N := by rwa [← Submodule.Quotient.eq]
    simpa [sub_eq_add_neg, add_assoc] using K.add_mem (hNK hdiff) hk
  refine ⟨r, hrKq, ?_⟩
  change ‖r‖ = ‖K.mkQ m‖
  rw [← hrKq]
  refine le_antisymm ?_ (Submodule.Quotient.norm_mk_le K r)
  rw [hrnorm, hqnorm, ← hqK]
  refine (QuotientAddGroup.le_norm_iff).2 ?_
  intro y hy
  have hyr : y - r ∈ K := by rwa [← Submodule.Quotient.eq]
  have hq_y : Kbar.mkQ (N.mkQ y) = Kbar.mkQ q := by
    simpa [Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrq] using ⟨y - r, hyr, rfl⟩
  grw [← hq_y, Submodule.mkQ_apply, Quotient.norm_mk_le, Submodule.mkQ_apply, Quotient.norm_mk_le]

theorem IsStrictlyClosed.of_linearEquiv
    {M₂ : Type*} [SeminormedAddCommGroup M₂] [Module A M₂]
    (e : M ≃ₗ[A] M₂) (he : ∀ x : M, ‖e x‖ = ‖x‖) {N : Submodule A M}
    (h : (N.map e.toLinearMap).IsStrictlyClosed) : N.IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  let N₂ : Submodule A M₂ := N.map e.toLinearMap
  rcases h (N₂.mkQ (e m)) with ⟨r₂, hr₂q, hr₂norm⟩
  have hrq : N.mkQ (e.symm r₂) = N.mkQ m := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem₂ : r₂ - e m ∈ N₂ := by rwa [← Submodule.Quotient.eq]
    rcases hmem₂ with ⟨n, hn, hn_eq⟩
    have hdiff : e.symm r₂ - m = n := e.injective (by simp [← hn_eq])
    simpa [hdiff] using hn
  refine ⟨e.symm r₂, hrq, ?_⟩
  change ‖e.symm r₂‖ = ‖N.mkQ m‖
  refine le_antisymm ?_ ?_
  · have hquot_le : ‖N₂.mkQ (e m)‖ ≤ ‖N.mkQ m‖ := by
      refine (QuotientAddGroup.le_norm_iff).2 ?_
      intro y hy
      have hy₂ : N₂.mkQ (e y) = N₂.mkQ (e m) := by
        simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
        have hymem : y - m ∈ N := by rwa [← Submodule.Quotient.eq]
        exact ⟨y - m, hymem, by simp⟩
      grw [← hy₂, ← he y]
      exact Submodule.Quotient.norm_mk_le N₂ (e y)
    grw [← he, LinearEquiv.apply_symm_apply, hr₂norm, hquot_le]
  · simpa [← hrq] using Submodule.Quotient.norm_mk_le N (e.symm r₂)

theorem restrictScalars_quotient_norm
    {B R : Type*} [SeminormedCommRing B] [SeminormedRing R] [Algebra B R]
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    (N : Submodule R M) (m : M) : ‖(N.restrictScalars B).mkQ m‖ = ‖N.mkQ m‖ := by
  refine le_antisymm ?_ ?_
  · refine QuotientAddGroup.le_norm_iff.2 ?_
    intro y hy
    have hyB : (N.restrictScalars B).mkQ y = (N.restrictScalars B).mkQ m := hy
    rw [← hyB]
    exact Submodule.Quotient.norm_mk_le (N.restrictScalars B) y
  · refine QuotientAddGroup.le_norm_iff.2 ?_
    intro y hy
    have hyR : N.mkQ y = N.mkQ m := hy
    rw [← hyR]
    exact Submodule.Quotient.norm_mk_le N y

theorem Quotient.restrictScalarsEquiv_norm
    {B R : Type*} [SeminormedCommRing B] [SeminormedRing R] [Algebra B R]
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    (N : Submodule R M) (x : M ⧸ N.restrictScalars B) :
    ‖Submodule.Quotient.restrictScalarsEquiv B N x‖ = ‖x‖ := by
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  change ‖Submodule.Quotient.restrictScalarsEquiv B N ((N.restrictScalars B).mkQ m)‖ =
    ‖(N.restrictScalars B).mkQ m‖
  simpa [Submodule.Quotient.restrictScalarsEquiv_mk B N m] using
    (Submodule.restrictScalars_quotient_norm N m).symm

theorem Quotient.restrictScalarsEquiv_symm_norm
    {B R : Type*} [SeminormedCommRing B] [SeminormedRing R] [Algebra B R]
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    (N : Submodule R M) (x : M ⧸ N) :
    ‖(Submodule.Quotient.restrictScalarsEquiv B N).symm x‖ = ‖x‖ := by
  simpa using (Submodule.Quotient.restrictScalarsEquiv_norm N
    ((Submodule.Quotient.restrictScalarsEquiv B N).symm x)).symm

theorem IsStrictlyClosed.of_restrictScalars
    {B R : Type*} [SeminormedCommRing B] [SeminormedRing R] [Algebra B R]
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    {N : Submodule R M} (h : (N.restrictScalars B).IsStrictlyClosed) :
    N.IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  rcases h ((N.restrictScalars B).mkQ m) with ⟨r, hrq, hrnorm⟩
  exact ⟨r, hrq, by simpa [hrnorm] using! Submodule.restrictScalars_quotient_norm N m⟩

theorem IsStrictlyClosed.to_restrictScalars
    {B R : Type*} [SeminormedCommRing B] [SeminormedRing R] [Algebra B R]
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    {N : Submodule R M} (h : N.IsStrictlyClosed) :
    (N.restrictScalars B).IsStrictlyClosed := by
  intro x
  rcases Quot.exists_rep x with ⟨m, rfl⟩
  rcases h (N.mkQ m) with ⟨r, hrq, hrnorm⟩
  exact ⟨r, hrq, hrnorm.trans (Submodule.restrictScalars_quotient_norm N m).symm⟩

theorem IsStrictlyClosed.of_ringEquiv
    {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    {M : Type*} [NormedAddCommGroup M] [Module S M]
    (e : R ≃+* S) {N : Submodule S M}
    (h : let : Algebra R S := e.toRingHom.toAlgebra
      let : Module R M := Module.compHom M e.toRingHom
      have : IsScalarTower R S M := by
        constructor
        intro r s m
        change (e r * s) • m = e r • s • m
        rw [mul_smul]
      (N.restrictScalars R).IsStrictlyClosed) :
    N.IsStrictlyClosed := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M e.toRingHom
  have : IsScalarTower R S M := by
    constructor
    intro r s m
    change (e r * s) • m = e r • s • m
    rw [mul_smul]
  exact Submodule.IsStrictlyClosed.of_restrictScalars h

theorem IsStrictlyClosed.of_isometry
    {V : Type*} [SeminormedAddCommGroup V] [Module A V]
    (L : M →ₗ[A] V) (hL : Function.Injective L) (hNorm : ∀ x : M, ‖L x‖ = ‖x‖)
    {N : Submodule A M} (hStrict : (N.map L).IsStrictlyClosed) :
    N.IsStrictlyClosed := by
  classical
  let e : M ≃ₗ[A] LinearMap.range L :=
    { toFun := fun x ↦ ⟨L x, ⟨x, rfl⟩⟩
      invFun := fun y ↦ Classical.choose y.2
      map_add' x y := Subtype.ext (by simp)
      map_smul' a x := Subtype.ext (by simp)
      left_inv := by
        intro x
        apply hL
        exact Classical.choose_spec (show L x ∈ LinearMap.range L from ⟨x, rfl⟩)
      right_inv := by
        intro y
        ext
        exact Classical.choose_spec y.2 }
  have hNK : N.map L ≤ LinearMap.range L := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  refine Submodule.IsStrictlyClosed.of_linearEquiv e hNorm ?_
  have hmap_eq : N.map e.toLinearMap = (N.map L).submoduleOf (LinearMap.range L) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
  simp [hmap_eq, Submodule.IsStrictlyClosed.submoduleOf hNK hStrict]

/-- The linear equivalence between `K ⧸ N.submoduleOf K` and `K.map N.mkQ` induced by
the quotient map `N.mkQ`. -/
noncomputable def quotientSubmoduleOfEquivMapMkQ {A M : Type*} [Ring A] [AddCommGroup M]
    [Module A M] (N K : Submodule A M) : (K ⧸ N.submoduleOf K) ≃ₗ[A] K.map N.mkQ := by
  let f : K →ₗ[A] K.map N.mkQ :=
    { toFun := fun k ↦ ⟨N.mkQ (k : M), ⟨(k : M), k.2, rfl⟩⟩
      map_add' x y := Subtype.ext (by simp)
      map_smul' a x := Subtype.ext (by simp) }
  have hker : (N.submoduleOf K) ≤ LinearMap.ker f := by
    intro x hx
    ext
    change Submodule.Quotient.mk (x : M) = Submodule.Quotient.mk 0
    rw [Submodule.Quotient.eq]
    simpa using! hx
  let fQ : (K ⧸ N.submoduleOf K) →ₗ[A] K.map N.mkQ :=
    (N.submoduleOf K).liftQ f hker
  refine LinearEquiv.ofBijective fQ ?_
  constructor
  · intro x y hxy
    rcases Quot.exists_rep x with ⟨x0, rfl⟩
    rcases Quot.exists_rep y with ⟨y0, rfl⟩
    change fQ ((N.submoduleOf K).mkQ x0) = fQ ((N.submoduleOf K).mkQ y0) at hxy
    change Submodule.Quotient.mk x0 = Submodule.Quotient.mk y0
    rw [Submodule.Quotient.eq]
    change (x0 : M) - (y0 : M) ∈ N
    rw [← Submodule.Quotient.eq]
    simpa [fQ, f, Submodule.liftQ_apply] using congrArg Subtype.val hxy
  · rintro ⟨_, ⟨k, hk, hkq⟩⟩
    refine ⟨(N.submoduleOf K).mkQ ⟨k, hk⟩, ?_⟩
    ext
    simpa [fQ, f, Submodule.liftQ_apply] using hkq

theorem quotientSubmoduleOfEquivMapMkQ_norm {N K : Submodule A M} (hNK : N ≤ K)
    (x : K ⧸ N.submoduleOf K) : ‖N.quotientSubmoduleOfEquivMapMkQ K x‖ = ‖x‖ := by
  rcases Quot.exists_rep x with ⟨k, rfl⟩
  refine le_antisymm ?_ ?_
  · refine (QuotientAddGroup.le_norm_iff (r := ‖N.mkQ (k : M)‖)).2 ?_
    intro y hy
    have hyN : N.mkQ (y : M) = N.mkQ (k : M) := by
      simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hymem : y - k ∈ N.submoduleOf K := by rwa [← Submodule.Quotient.eq]
      exact hymem
    rw [← hyN]
    exact Submodule.Quotient.norm_mk_le N (y : M)
  · refine (QuotientAddGroup.le_norm_iff (r := ‖(N.submoduleOf K).mkQ k‖)).2 ?_
    intro y hy
    have hymem : y - (k : M) ∈ N := by rwa [← Submodule.Quotient.eq]
    have hyK : y ∈ K := by simpa [sub_eq_add_neg, add_assoc] using K.add_mem (hNK hymem) k.2
    let yK : K := ⟨y, hyK⟩
    have hyDom : (N.submoduleOf K).mkQ yK = (N.submoduleOf K).mkQ k := by
      simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hymem
    rw [← hyDom]
    exact Submodule.Quotient.norm_mk_le (N.submoduleOf K) yK

theorem IsPseudoCartesian.of_strict_extension [IsUltrametricDist M] [IsBoundedSMul A M]
    {N K : Submodule A M}
    (hNstrict : (N.submoduleOf K).IsStrictlyClosed)
    [IsPseudoCartesian A (N.submoduleOf K)]
    [IsPseudoCartesian A (K ⧸ N.submoduleOf K)] : IsPseudoCartesian A K := by
  let Nₖ : Submodule A K := N.submoduleOf K
  rcases IsPseudoCartesian.out A Nₖ with ⟨σ, hσ, eN, heN⟩
  rcases IsPseudoCartesian.out A (K ⧸ Nₖ) with ⟨τ, hτ, eQ, heQ⟩
  choose lift hliftQ hliftNorm using fun j : τ ↦ hNstrict (eQ j)
  let e : Sum σ τ → K := fun
    | Sum.inl i => eN i
    | Sum.inr j => lift j
  refine ⟨Sum σ τ, inferInstance, e, ⟨?_⟩⟩
  intro x
  rcases heQ.exists_norm_le (Nₖ.mkQ x) with ⟨b, hb_repr, hb_norm⟩
  let y : K := ∑ j : τ, b j • lift j
  have hy_norm : ‖y‖ ≤ ‖x‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg x) fun j _ ↦ ?_
    have h : ‖b j • lift j‖ ≤ ‖b j‖ * ‖lift j‖ := norm_smul_le (b j) (lift j : M)
    grw [hliftNorm j, hb_norm j] at h
    exact h.trans (Submodule.Quotient.norm_mk_le Nₖ x)
  have hy_quot : Nₖ.mkQ y = Nₖ.mkQ x := by
    rw [hb_repr]
    simp only [y, Submodule.mkQ_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change b j • Nₖ.mkQ (lift j) = b j • eQ j
    rw [hliftQ j]
  let d : Nₖ := ⟨x - y, by rwa [← Submodule.Quotient.eq, eq_comm]⟩
  have hd_norm : ‖d‖ ≤ ‖x‖ := by
    change ‖x - y‖ ≤ ‖x‖
    grw [← max_eq_left hy_norm]
    simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  rcases heN.exists_norm_le d with ⟨a, ha_repr, ha_norm⟩
  let c : Sum σ τ → A := fun
    | Sum.inl i => a i
    | Sum.inr j => b j
  refine ⟨c, ?_, ?_⟩
  · have hsum :
        (∑ z : Sum σ τ, c z • e z) = (∑ i : σ, a i • (eN i : K)) + ∑ j : τ, b j • lift j := by
      simp [c, e]
    have hd_repr_K : (d : K) = ∑ i : σ, a i • (eN i : K) := by
      simpa using congrArg (fun z : Nₖ ↦ (z : K)) ha_repr
    rw [hsum, ← hd_repr_K]
    change x = (x - y) + y
    abel
  · rintro (i | j)
    · exact (ha_norm i).trans hd_norm
    · have h := hb_norm j
      grw [← hliftNorm j] at h
      exact h.trans (Submodule.Quotient.norm_mk_le Nₖ x)

theorem isPseudoCartesian_and_isStrictlyClosed_of_quotient
    [IsUltrametricDist M] [IsBoundedSMul A M] {N K : Submodule A M} (hNK : N ≤ K)
    [IsPseudoCartesian A N] (hNstrict : N.IsStrictlyClosed)
    [IsPseudoCartesian A (K ⧸ N.submoduleOf K)]
    (hQstrict : (K.map N.mkQ).IsStrictlyClosed) :
    IsPseudoCartesian A K ∧ K.IsStrictlyClosed := by
  constructor
  · have : IsPseudoCartesian A (N.submoduleOf K) := IsPseudoCartesian.submoduleOf hNK
    exact IsPseudoCartesian.of_strict_extension
      (Submodule.IsStrictlyClosed.submoduleOf hNK hNstrict)
  · exact Submodule.IsStrictlyClosed.of_quotient hNK hNstrict hQstrict

theorem IsStrictlyClosed.of_normedField {k M : Type*} [NormedField k]
    [NormedAddCommGroup M] [IsUltrametricDist M] [Module k M]
    [IsBoundedSMul k M] [IsCartesian k M] (N : Submodule k M) : N.IsStrictlyClosed := by
  classical
  rcases IsCartesian.exists_non_zero_cartesianGenerator k M with ⟨σ, hσ, e, hne, he⟩
  let B : Module.Basis σ k M := he.nonzeroBasis hne
  have hB_pos (i : σ) : 0 < ‖B i‖ := norm_pos_iff.mpr (B.ne_zero i)
  let row : σ → Module.Dual k N := fun i ↦ (B.coord i).comp N.subtype
  have hcoord_le (x : N) (i : σ) : ‖row i x‖ * ‖B i‖ ≤ ‖x‖ := by
    have hxsum : (x : M) = ∑ i : σ, row i x • B i := by simp [row, Module.Basis.coord_apply]
    simp only [IsCartesianGenerator.nonzeroBasis, Basis.coe_mk, B] at hxsum ⊢
    exact he.norm_le (x : M) (fun i : σ ↦ row i x) hxsum i
  have hambient_upper (x : N) (C : ℝ) (hC : 0 ≤ C)
      (hcoords : ∀ i : σ, ‖row i x‖ * ‖B i‖ ≤ C) : ‖x‖ ≤ C := by
    have hxsum : (x : M) = ∑ i : σ, row i x • B i := by simp [row, Module.Basis.coord_apply]
    change ‖(x : M)‖ ≤ C
    rw [hxsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC ?_
    intro i _
    exact (norm_smul_le (row i x) (B i)).trans (hcoords i)
  have hcoord_le_ambient (x : M) (i : σ) : ‖B.coord i x‖ * ‖B i‖ ≤ ‖x‖ := by
    have hxsum : x = ∑ i : σ, B.repr x i • B i := (B.sum_repr x).symm
    simp only [IsCartesianGenerator.nonzeroBasis, Basis.coe_mk, B] at hxsum ⊢
    exact he.norm_le x (fun i : σ ↦ B.repr x i) hxsum i
  have hrow_span : Submodule.span k (Set.range row) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    rcases LinearMap.exists_extend f with ⟨g, hg⟩
    have hf_decomp : f = ∑ i : σ, g (B i) • row i := by
      rw [← hg]
      ext x
      have hx : (x : M) = ∑ i : σ, (B.repr (x : M)) i • B i := by simp
      change g (x : M) = (∑ i : σ, g (B i) • row i) x
      rw [hx, map_sum]
      simp [row, Module.Basis.coord_apply, map_smul, smul_eq_mul, mul_comm]
    rw [hf_decomp]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rcases exists_linearIndependent k (Set.range row) with ⟨s, hss, hs_span, hs_li⟩
  have hs_top : Submodule.span k s = ⊤ := by rwa [hrow_span] at hs_span
  have : Fintype s := ((Set.finite_range row).subset hss).fintype
  let ψ : Module.Basis s k (Module.Dual k N) := by
    refine Module.Basis.mk hs_li ?_
    intro f _
    rw [show Set.range (Subtype.val : s → Module.Dual k N) = s by
      ext f
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hf
        exact ⟨⟨f, hf⟩, rfl⟩]
    simp [hs_top]
  let idx : s → σ := fun j ↦ Classical.choose (hss j.2)
  have hidx (j : s) : row (idx j) = ψ j := by simpa [idx, ψ] using (hss j.2).choose_spec
  let mat : (s → σ) → Matrix s s k := fun p i j ↦ ψ.equivFun (row (p j)) i
  have hmat_idx : mat idx = 1 := by
    ext i j
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [mat, hidx]
    · simp [mat, hidx, hij]
  let Candidate := {p : s → σ // (mat p).det ≠ 0}
  have : Nonempty Candidate := ⟨⟨idx, by simp [hmat_idx]⟩⟩
  let weight : Candidate → ℝ := fun p ↦ ‖(mat p.1).det‖ * ∏ j : s, ‖B (p.1 j)‖
  obtain ⟨pmax, -, hpmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  have hpmax_le (q : Candidate) : weight q ≤ weight pmax := hpmax q (by simp)
  let p : s → σ := pmax.1
  have hdetp : (mat p).det ≠ 0 := pmax.2
  have hcols' : LinearIndependent k (fun j : s ↦ ψ.equivFun (row (p j))) := by
    simpa [mat, p, Matrix.col] using! Matrix.linearIndependent_cols_of_det_ne_zero hdetp
  have hker : (ψ.equivFun.symm : (s → k) →ₗ[k] Module.Dual k N).ker = ⊥ :=
    LinearEquiv.ker ψ.equivFun.symm
  have hli_phi : LinearIndependent k (fun j : s ↦ row (p j)) := by
    have hmap := hcols'.map' (ψ.equivFun.symm : (s → k) →ₗ[k] Module.Dual k N) hker
    convert hmap using 1
    ext j
    simp [Function.comp, Module.Basis.equivFun_apply]
  have : Module.Finite k N := IsPseudoCartesian.module_finite k N
  have hspan_phi : Submodule.span k (Set.range (fun j : s ↦ row (p j))) = ⊤ :=
    hli_phi.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis ψ).symm
  let φBasis : Module.Basis s k (Module.Dual k N) :=
    Module.Basis.mk hli_phi <| fun f _ ↦ by simp [hspan_phi]
  have hφ_apply (j : s) : φBasis j = row (p j) := by simp [φBasis]
  let bN := Module.finBasis k N
  let evalE : N ≃ₗ[k] Module.Dual k (Module.Dual k N) :=
    bN.toDualEquiv.trans bN.dualBasis.toDualEquiv
  have heval (x : N) (f : Module.Dual k N) : evalE x f = f x := by
    change (bN.dualBasis.toDualEquiv (bN.toDualEquiv x)) f = f x
    rw [Module.Basis.toDualEquiv_apply, Module.Basis.toDualEquiv_apply]
    have h := LinearMap.congr_fun (Module.Basis.toDual_toDual bN) x
    exact LinearMap.congr_fun h f
  let uBasis : Module.Basis s k N := φBasis.dualBasis.map evalE.symm
  have hcoeff (f : Module.Dual k N) (j : s) : φBasis.equivFun f j = f (uBasis j) := by
    simpa [uBasis] using heval (uBasis j) f
  have hcoord_u (i j : s) : row (p i) (uBasis j) = if i = j then 1 else 0 := by
    rw [← heval (uBasis j) (row (p i))]
    simpa [uBasis, hφ_apply, eq_comm] using Module.Basis.dualBasis_apply_self φBasis j i
  have hdet_update (k0 : σ) (j : s) :
      (mat (Function.update p j k0)).det = (mat p).det * row k0 (uBasis j) := by
    let A := mat p
    let c : s → k := φBasis.equivFun (row k0)
    have hb : ψ.equivFun (row k0) = A.mulVec c := by
      ext i
      rw [show row k0 = φBasis.equivFun.symm c by simp [c], Module.Basis.equivFun_symm_apply]
      trans ∑ l : s, c l * ψ.equivFun (row (p l)) i
      · simp [hφ_apply]
      trans ∑ l : s, A i l * c l
      · refine Finset.sum_congr rfl fun l _ ↦ ?_
        simp [A, mat, mul_comm]
      · rfl
    have hmat_update : mat (Function.update p j k0) = A.updateCol j (ψ.equivFun (row k0)) := by
      ext i l
      by_cases hlj : l = j
      · subst hlj
        simp [A, mat]
      · simp [A, mat, Function.update, hlj]
    rw [hmat_update]
    trans A.cramer (ψ.equivFun (row k0)) j
    · rw [Matrix.cramer_apply]
    trans (A.det • c) j
    · rw [hb, Matrix.cramer_mulVec_eq_det_smul A hdetp c]
    · change A.det * c j = A.det * row k0 (uBasis j)
      rw [show c j = row k0 (uBasis j) by simpa [c] using hcoeff (row k0) j]
  have hcoeff_bound (k0 : σ) (j : s) : ‖row k0 (uBasis j)‖ * ‖B k0‖ ≤ ‖B (p j)‖ := by
    let c := row k0 (uBasis j)
    by_cases hc : c = 0
    · simp [c, hc, norm_nonneg]
    let qfun : s → σ := Function.update p j k0
    have hdetq : (mat qfun).det ≠ 0 := by
      rw [hdet_update k0 j]
      exact mul_ne_zero hdetp hc
    let qCand : Candidate := ⟨qfun, hdetq⟩
    let E : ℝ := ∏ l ∈ (Finset.univ.erase j), ‖B (p l)‖
    have hEpos : 0 < E := Finset.prod_pos fun l _ ↦ hB_pos (p l)
    have hDpos : 0 < ‖(mat p).det‖ := norm_pos_iff.mpr hdetp
    have hprod_q : (∏ l : s, ‖B (qfun l)‖) = ‖B k0‖ * E := by
      have hupdate :
          (∏ l : s, Function.update (fun l : s ↦ ‖B (p l)‖) j ‖B k0‖ l) = ‖B k0‖ * E := by
        simpa [E, Finset.sdiff_singleton_eq_erase] using
          Finset.prod_update_of_mem (by simp) (fun l : s ↦ ‖B (p l)‖) ‖B k0‖
      trans ∏ l : s, Function.update (fun l : s ↦ ‖B (p l)‖) j ‖B k0‖ l
      · refine Finset.prod_congr rfl fun l _ ↦ ?_
        by_cases hlj : l = j
        · subst hlj
          simp [qfun]
        · simp [qfun, Function.update, hlj]
      · exact hupdate
    have hprod_p : (∏ l : s, ‖B (p l)‖) = ‖B (p j)‖ * E :=
      (Finset.mul_prod_erase Finset.univ (fun l : s ↦ ‖B (p l)‖) (Finset.mem_univ j)).symm
    have hmain : (‖(mat p).det‖ * E) * (‖c‖ * ‖B k0‖) ≤
        (‖(mat p).det‖ * E) * ‖B (p j)‖ := by
      have hmaxq := hpmax_le qCand
      dsimp [weight, qCand, qfun, p] at hmaxq
      rw [hprod_q, hprod_p, hdet_update k0 j, norm_mul] at hmaxq
      nlinarith [hmaxq]
    exact (mul_le_mul_iff_of_pos_left (mul_pos hDpos hEpos)).mp hmain
  have hu_norm (j : s) : ‖uBasis j‖ = ‖B (p j)‖ := by
    refine le_antisymm ?_ ?_
    · exact hambient_upper (uBasis j) ‖B (p j)‖ (norm_nonneg _) fun i ↦ hcoeff_bound i j
    · have hlow := hcoord_le (uBasis j) (p j)
      simpa [show row (p j) (uBasis j) = 1 by simpa using hcoord_u j j] using hlow
  let γ := Fin (Fintype.card s)
  let finEquiv : s ≃ γ := Fintype.equivFin s
  let uFinBasis : Module.Basis γ k N := uBasis.reindex finEquiv
  have huFin_norm (j : γ) : ‖uFinBasis j‖ = ‖B (p (finEquiv.symm j))‖ := by
    simpa [uFinBasis, finEquiv] using hu_norm (finEquiv.symm j)
  have hcoord_uFin (i j : γ) :
      row (p (finEquiv.symm i)) (uFinBasis j) = if i = j then 1 else 0 := by
    simpa [uFinBasis, finEquiv] using hcoord_u (finEquiv.symm i) (finEquiv.symm j)
  let P : M →ₗ[k] M :=
    ∑ j : γ, LinearMap.smulRight (B.coord (p (finEquiv.symm j))) (uFinBasis j : M)
  let Q : M →ₗ[k] M := LinearMap.id - P
  refine Submodule.IsStrictlyClosed.of_contracting_quotient_projection Q ?_ ?_ ?_
  · intro x
    simp [Q, P, LinearMap.sum_apply, LinearMap.smulRight_apply,
      Submodule.sum_mem _ fun j _ ↦ N.smul_mem _ (uFinBasis j).2]
  · intro x hx
    let xN : N := ⟨x, hx⟩
    have hrow_repr (j : γ) : B.coord (p (finEquiv.symm j)) x = uFinBasis.repr xN j := by
      have hx_sum : xN = ∑ l : γ, (uFinBasis.repr xN) l • uFinBasis l := by simp
      have hrow_sum : row (p (finEquiv.symm j)) xN = uFinBasis.repr xN j := by
        rw [hx_sum, map_sum]
        trans ∑ l : γ, (uFinBasis.repr xN) l *
            row (p (finEquiv.symm j)) (uFinBasis l)
        · refine Finset.sum_congr rfl fun l _ ↦ ?_
          simp [map_smul, smul_eq_mul]
        · rw [Finset.sum_eq_single j]
          · simp [hcoord_uFin]
          · intro l _ hlj
            have hne : j ≠ l := fun h ↦ hlj h.symm
            simp [hcoord_uFin, hne]
          · exact fun hj ↦ (hj (Finset.mem_univ j)).elim
      simpa [row, xN] using hrow_sum
    have hP : P x = x := by
      dsimp [P]
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
      trans ∑ j : γ, (uFinBasis.repr xN j) • (uFinBasis j)
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hrow_repr j]
      · exact map_sum N.subtype (fun j : γ ↦ (uFinBasis.repr xN j) • uFinBasis j)
          Finset.univ |>.symm.trans <| congrArg Subtype.val (uFinBasis.sum_repr xN)
    simp [Q, hP]
  · intro x
    have hP_norm : ‖P x‖ ≤ ‖x‖ := by
      simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg x) fun j _ ↦ ?_
      have hnorm : ‖(uFinBasis j : M)‖ = ‖B (p (finEquiv.symm j))‖ := huFin_norm j
      grw [norm_smul_le, hnorm, hcoord_le_ambient x (p (finEquiv.symm j))]
    change ‖x - P x‖ ≤ ‖x‖
    grw [← max_eq_left hP_norm]
    simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (- P x)

theorem _root_.Module.quotient_smul_top_isCartesian_of_scalar_quotient
    {B R : Type*} [NormedCommRing B] [NormedCommRing R] [Algebra B R]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [Module R F] [Module B F] [IsScalarTower B R F] [IsBoundedSMul R F]
    [IsCartesian R F] (ω : R)
    (hIstrict : (ω • (⊤ : Submodule R R)).IsStrictlyClosed)
    (hFstrict : (ω • (⊤ : Submodule R F)).IsStrictlyClosed)
    [IsCartesian B (R ⧸ (ω • (⊤ : Submodule R R)))] :
    IsCartesian B (F ⧸ (ω • (⊤ : Submodule R F))) := by
  classical
  let I : Submodule R R := ω • (⊤ : Submodule R R)
  let N : Submodule R F := ω • (⊤ : Submodule R F)
  rcases IsCartesian.exists_non_zero_cartesianGenerator R F with ⟨ι, hι, eF, hFne, heF⟩
  let BF : Module.Basis ι R F := heF.nonzeroBasis hFne
  have hBFcart : IsCartesianGenerator R (fun i : ι ↦ BF i) := by
    simpa [BF, IsCartesianGenerator.nonzeroBasis]
  rcases IsCartesian.out B (R ⧸ I) with ⟨τ, hτ, g, hg⟩
  choose lift hliftQ hliftNorm using fun j : τ ↦ hIstrict (g j)
  let gen : ι × τ → F ⧸ N := fun p ↦ N.mkQ (lift p.2 • BF p.1)
  have hgen_norm (i : ι) (j : τ) : ‖gen (i, j)‖ ≤ ‖g j‖ * ‖BF i‖ := by
    refine (Submodule.Quotient.norm_mk_le N (lift j • BF i)).trans ?_
    grw [norm_smul_le (lift j) (BF i), hliftNorm j]
  refine ⟨ι × τ, inferInstance, gen, ⟨⟨?_⟩, ?_⟩⟩
  · intro x
    rcases hFstrict x with ⟨m, hmx, hmnorm⟩
    let a : ι → R := BF.repr m
    have hm_sum : m = ∑ i : ι, a i • BF i := by simp [a]
    choose b hb_repr hb_norm using fun i : ι ↦ hg.exists_norm_le (I.mkQ (a i))
    let c : ι × τ → B := fun p ↦ b p.1 p.2
    refine ⟨c, ?_, ?_⟩
    · rw [← hmx]
      let S : ι → R := fun i ↦ ∑ j : τ, (algebraMap B R (b i j)) * lift j
      have hcoord_mem (i : ι) : a i - S i ∈ I := by
        have hq : I.mkQ (a i) = I.mkQ (S i) := by
          rw [hb_repr i]
          symm
          trans ∑ j : τ, b i j • I.mkQ (lift j)
          · simp [S, Submodule.mkQ_apply, map_sum, Algebra.smul_def]
          · refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hliftQ j]
        have hmem' : S i - a i ∈ I := by rwa [← Submodule.Quotient.eq, eq_comm]
        simpa [sub_eq_add_neg, add_comm] using I.neg_mem hmem'
      choose u hu using fun i ↦ by
        have hi := hcoord_mem i
        rw [Submodule.mem_smul_pointwise_iff_exists] at hi
        exact hi
      have hz_sum : (∑ p : ι × τ, c p • (lift p.2 • BF p.1)) = ∑ i : ι, S i • BF i := by
        trans ∑ i : ι, ∑ j : τ, c (i, j) • (lift j • BF i)
        · exact Finset.sum_product _ _ (fun p : ι × τ ↦ c p • (lift p.2 • BF p.1))
        · refine Finset.sum_congr rfl fun i _ ↦ ?_
          trans ∑ j : τ, ((algebraMap B R (c (i, j))) * lift j) • BF i
          · refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [← smul_assoc, Algebra.smul_def]
          · rw [Finset.sum_smul]
      have hdiff : m - (∑ p : ι × τ, c p • (lift p.2 • BF p.1)) = ∑ i : ι, (a i - S i) • BF i := by
        simp [hz_sum, hm_sum, sub_smul]
      let z : F := ∑ p : ι × τ, c p • (lift p.2 • BF p.1)
      have hzmem : m - z ∈ N := by
        rw [hdiff, Submodule.mem_smul_pointwise_iff_exists]
        refine ⟨∑ i : ι, u i • BF i, Submodule.mem_top, ?_⟩
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hui : ω • u i = a i - S i := by simpa [Algebra.smul_def] using (hu i).2
        rw [smul_smul]
        change (ω • u i) • BF i = (a i - S i) • BF i
        rw [hui]
      have hzq : N.mkQ m = N.mkQ z := by simp [Submodule.mkQ_apply, Submodule.Quotient.eq, hzmem]
      rw [hzq]
      simp [z, gen, N, Submodule.mkQ_apply, map_sum]
    · intro ⟨i, j⟩
      have hcoord_bound : ‖a i‖ * ‖BF i‖ ≤ ‖m‖ := hBFcart.norm_le m a hm_sum i
      have hq_le : ‖I.mkQ (a i)‖ ≤ ‖a i‖ := Submodule.Quotient.norm_mk_le I (a i)
      apply (mul_le_mul_of_nonneg_left (hgen_norm i j) (norm_nonneg (c (i, j)))).trans
      grw [← mul_assoc, hb_norm i j, hq_le, hcoord_bound, hmnorm]
  · intro x c hx p
    rcases p with ⟨i, j⟩
    rcases hFstrict x with ⟨m, hmx, hmnorm⟩
    let a : ι → R := BF.repr m
    have hm_sum : m = ∑ i : ι, a i • BF i := by simp [a]
    let S : ι → R := fun i ↦ ∑ j : τ, (algebraMap B R (c (i, j))) * lift j
    have hz_sum : (∑ p : ι × τ, c p • (lift p.2 • BF p.1)) =
        ∑ i : ι, S i • BF i := by
      trans ∑ i : ι, ∑ j : τ, c (i, j) • (lift j • BF i)
      · exact Finset.sum_product _ _ (fun p : ι × τ ↦ c p • (lift p.2 • BF p.1))
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        trans ∑ j : τ, ((algebraMap B R (c (i, j))) * lift j) • BF i
        · refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← smul_assoc, Algebra.smul_def]
        · rw [Finset.sum_smul]
    have hq_m_z : N.mkQ m = N.mkQ (∑ p : ι × τ, c p • (lift p.2 • BF p.1)) := by
      rw [hmx, hx]
      simp [gen, N, Submodule.mkQ_apply, map_sum]
    have hmem : m - (∑ p : ι × τ, c p • (lift p.2 • BF p.1)) ∈ N := by
      rwa [← Submodule.Quotient.eq]
    have hcoord_mem : a i - S i ∈ I := by
      have hrepr_mem : BF.repr (m - (∑ p : ι × τ, c p • (lift p.2 • BF p.1))) i ∈ I := by
        rw [Submodule.mem_smul_pointwise_iff_exists] at hmem
        rcases hmem with ⟨y, -, hy⟩
        rw [← hy, Submodule.mem_smul_pointwise_iff_exists]
        refine ⟨BF.repr y i, Submodule.mem_top, ?_⟩
        simp [map_smul]
      have hrepr_eq : BF.repr (m - (∑ p : ι × τ, c p • (lift p.2 • BF p.1))) i = a i - S i := by
        rw [hz_sum, map_sub]
        have hmrepr : BF.repr m i = a i := by simp [a]
        have hSrepr : BF.repr (∑ i : ι, S i • BF i) i = S i := by
          trans BF.equivFun (∑ i : ι, S i • BF i) i
          · rw [Module.Basis.equivFun_apply]
          trans BF.equivFun (BF.equivFun.symm S) i
          · rw [Module.Basis.equivFun_symm_apply]
          · exact congrFun (LinearEquiv.apply_symm_apply BF.equivFun S) i
        change (BF.repr m) i - (BF.repr (∑ i : ι, S i • BF i)) i = a i - S i
        rw [hmrepr, hSrepr]
      rw [hrepr_eq] at hrepr_mem
      exact hrepr_mem
    have hcoord_repr : I.mkQ (a i) = ∑ j : τ, c (i, j) • g j := by
      have hq : I.mkQ (a i) = I.mkQ (S i) := by
        simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact hcoord_mem
      rw [hq]
      trans ∑ j : τ, c (i, j) • I.mkQ (lift j)
      · simp [S, Submodule.mkQ_apply, map_sum, Algebra.smul_def]
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hliftQ j]
    have hcoord_bound : ‖a i‖ * ‖BF i‖ ≤ ‖m‖ :=
      hBFcart.norm_le m a hm_sum i
    have hq_le : ‖I.mkQ (a i)‖ ≤ ‖a i‖ := Submodule.Quotient.norm_mk_le I (a i)
    have h := mul_le_mul_of_nonneg_left (hgen_norm i j) (norm_nonneg (c (i, j)))
    grw [show ‖c (i, j)‖ * (‖g j‖ * ‖BF i‖) = (‖c (i, j)‖ * ‖g j‖) * ‖BF i‖ by ring,
      hg.norm_le (I.mkQ (a i)) (fun j ↦ c (i, j)) hcoord_repr j,
      hq_le, hcoord_bound, hmnorm] at h
    exact h

end Submodule

end Cartesian

section norm_localization

variable (A : Type*) [NormedCommRing A] [IsDomain A] [NormMulClass A]
  (M : Type*) [SeminormedAddCommGroup M] [Module A M] [IsBoundedSMul A M]

/-- The canonical ring norm on the fraction field of `A`. -/
noncomputable def ringNormLocalization : RingNorm (Localization A⁰) := by
  let f : Localization A⁰ → ℝ := fun x ↦
    Localization.liftOn x (fun a b ↦ ‖a‖ / ‖(b : A)‖) <| by
      intro a c b d h
      have hEq : a * (d : A) = (b : A) * c :=
        (Localization.r_iff_of_le_nonZeroDivisors (le_refl A⁰) a c b d).mp h
      have hb0 : ‖(b : A)‖ ≠ 0 := norm_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero b)
      have hd0 : ‖(d : A)‖ ≠ 0 := norm_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero d)
      have hnorm : ‖a‖ * ‖(d : A)‖ = ‖(b : A)‖ * ‖c‖ := by rw [← norm_mul, hEq, norm_mul]
      rw [div_eq_div_iff hb0 hd0]
      simp [mul_comm, hnorm]
  have f_mk (a : A) (b : A⁰) : f (Localization.mk a b) = ‖a‖ / ‖(b : A)‖ := rfl
  refine
    { toFun := f
      map_zero' := ?_
      add_le' := ?_
      neg' := ?_
      mul_le' := ?_
      eq_zero_of_map_eq_zero' := ?_ }
  · rw [← Localization.mk_zero (1 : A⁰), f_mk]
    simp
  · intro x y
    refine Localization.induction_on x ?_
    intro ⟨a, b⟩
    refine Localization.induction_on y ?_
    intro ⟨c, d⟩
    have hbpos : 0 < ‖(b : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero b)
    have hdpos : 0 < ‖(d : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero d)
    have hnorm : ‖(b : A) * c + (d : A) * a‖ ≤ ‖(b : A)‖ * ‖c‖ + ‖(d : A)‖ * ‖a‖ := by
      simpa [norm_mul] using norm_add_le ((b : A) * c) ((d : A) * a)
    rw [Localization.add_mk, f_mk, f_mk, f_mk, Submonoid.coe_mul, norm_mul]
    grw [(div_le_div_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
    field_simp [hbpos.ne', hdpos.ne']
    linarith
  · intro x
    refine Localization.induction_on x ?_
    intro ⟨a, b⟩
    rw [Localization.neg_mk, f_mk, f_mk]
    simp
  · intro x y
    refine Localization.induction_on x ?_
    intro ⟨a, b⟩
    refine Localization.induction_on y ?_
    intro ⟨c, d⟩
    rw [Localization.mk_mul, f_mk, f_mk, f_mk]
    simp [div_mul_div_comm]
  · intro x
    refine Localization.induction_on x ?_
    intro ⟨a, b⟩ hx
    rw [f_mk] at hx
    have hbpos : 0 < ‖(b : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero b)
    have ha0 : ‖a‖ = 0 := (div_eq_zero_iff.mp hx).resolve_right hbpos.ne'
    simp [norm_eq_zero.mp ha0]

noncomputable instance : NormedRing (Localization A⁰) where
  __ := (ringNormLocalization A).toNormedRing

lemma norm_localization_mk (a : A) (b : A⁰) : ‖Localization.mk a b‖ = ‖a‖ / ‖(b : A)‖ :=
  rfl

noncomputable instance : NormedField (Localization A⁰) where
  __ := (ringNormLocalization A).toNormedRing
  __ : Field (Localization A⁰) := inferInstance
  norm_mul x y := by
    refine Localization.induction_on x ?_
    intro ⟨a, b⟩
    refine Localization.induction_on y ?_
    intro ⟨c, d⟩
    rw [Localization.mk_mul, norm_localization_mk, norm_localization_mk, norm_localization_mk]
    rw [Submonoid.coe_mul, norm_mul, norm_mul]
    field_simp

lemma norm_algebraMap_localization [NormOneClass A] (a : A) :
    ‖algebraMap A (Localization A⁰) a‖ = ‖a‖ := by
  rw [show algebraMap A (Localization A⁰) a = Localization.mk a 1 from rfl, norm_localization_mk]
  simp

instance [IsUltrametricDist A] : IsUltrametricDist (Localization A⁰) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ?_
  intro x y
  refine Localization.induction_on x ?_
  intro ⟨a, b⟩
  refine Localization.induction_on y ?_
  intro ⟨c, d⟩
  rw [Localization.add_mk, norm_localization_mk, norm_localization_mk, norm_localization_mk]
  have hbpos : 0 < ‖(b : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero b)
  have hdpos : 0 < ‖(d : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero d)
  have hnorm : ‖(b : A) * c + (d : A) * a‖ ≤
      max (‖(b : A)‖ * ‖c‖) (‖(d : A)‖ * ‖a‖) := by
    simpa [norm_mul] using
      IsUltrametricDist.norm_add_le_max ((b : A) * c) ((d : A) * a)
  rw [Submonoid.coe_mul, norm_mul, div_le_iff₀ (mul_pos hbpos hdpos)]
  refine hnorm.trans <| max_le ?_ ?_
  · have hle : ‖c‖ / ‖(d : A)‖ ≤ max (‖a‖ / ‖(b : A)‖) (‖c‖ / ‖(d : A)‖) := le_max_right _ _
    rw [show ‖(b : A)‖ * ‖c‖ = (‖c‖ / ‖(d : A)‖) * (‖(b : A)‖ * ‖(d : A)‖) by
      field_simp [hdpos.ne']]
    exact mul_le_mul_of_nonneg_right hle (mul_nonneg hbpos.le hdpos.le)
  · have hle : ‖a‖ / ‖(b : A)‖ ≤ max (‖a‖ / ‖(b : A)‖) (‖c‖ / ‖(d : A)‖) := le_max_left _ _
    rw [show ‖(d : A)‖ * ‖a‖ = (‖a‖ / ‖(b : A)‖) * (‖(b : A)‖ * ‖(d : A)‖) by
      field_simp [hbpos.ne']]
    exact mul_le_mul_of_nonneg_right hle (mul_nonneg hbpos.le hdpos.le)

/-- The set of values `‖m‖ / ‖s‖` for all representations `m / s` of a given element in the
localization of a module `M` by `A⁰`. -/
def localizedModuleSeminormValues (x : LocalizedModule A⁰ M) : Set ℝ :=
  { r | ∃ (m : M) (s : A⁰), LocalizedModule.mk m s = x ∧ r = ‖m‖ / ‖(s : A)‖ }

omit [IsDomain A] [NormMulClass A] [IsBoundedSMul A M] in
lemma localizedModuleSeminormValues_nonempty (x : LocalizedModule A⁰ M) :
    (localizedModuleSeminormValues A M x).Nonempty := by
  induction x using LocalizedModule.induction_on with
  | h m s => exact ⟨‖m‖ / ‖(s : A)‖, m, s, rfl, rfl⟩

omit [IsDomain A] [NormMulClass A] [IsBoundedSMul A M] in
lemma localizedModuleSeminormValues_bddBelow (x : LocalizedModule A⁰ M) :
    BddBelow (localizedModuleSeminormValues A M x) := by
  refine ⟨0, ?_⟩
  rintro r ⟨m, s, -, rfl⟩
  positivity

omit [IsDomain A] [NormMulClass A] [IsBoundedSMul A M] in
lemma localizedModuleSeminormValues_neg (x : LocalizedModule A⁰ M) :
    localizedModuleSeminormValues A M (-x) = localizedModuleSeminormValues A M x := by
  ext r
  constructor <;> rintro ⟨m, s, hm, rfl⟩
  · exact ⟨- m, s, by rw [LocalizedModule.mk_neg, hm, neg_neg], by simp⟩
  · exact ⟨- m, s, by rw [LocalizedModule.mk_neg, hm], by simp⟩

lemma localizedModuleSeminorm_add_mk_le (m n : M) (s t : A⁰) :
    sInf (localizedModuleSeminormValues A M (LocalizedModule.mk m s + LocalizedModule.mk n t)) ≤
      ‖m‖ / ‖(s : A)‖ + ‖n‖ / ‖(t : A)‖ := by
  refine csInf_le (localizedModuleSeminormValues_bddBelow A M _)
    ⟨t • m + s • n, s * t, LocalizedModule.mk_add_mk.symm, rfl⟩ |>.trans ?_
  rw [Submonoid.coe_mul, norm_mul]
  have hnorm : ‖t • m + s • n‖ ≤ ‖(t : A)‖ * ‖m‖ + ‖(s : A)‖ * ‖n‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_smul_le (t : A) m) (norm_smul_le (s : A) n))
  have hmain : (‖(t : A)‖ * ‖m‖ + ‖(s : A)‖ * ‖n‖) / (‖(s : A)‖ * ‖(t : A)‖) =
      ‖m‖ / ‖(s : A)‖ + ‖n‖ / ‖(t : A)‖ := by field_simp
  rw [← hmain]
  exact div_le_div_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The canonical seminorm on the localization of a module `M` by `A⁰`. -/
noncomputable def addGroupSeminormLocalized : AddGroupSeminorm (LocalizedModule A⁰ M) where
  toFun x := sInf (localizedModuleSeminormValues A M x)
  map_zero' := by
    refine le_antisymm ?_ ?_
    · refine csInf_le (localizedModuleSeminormValues_bddBelow A M 0) ⟨0, 1, by simp, by simp⟩
    · refine le_csInf (localizedModuleSeminormValues_nonempty A M 0) ?_
      rintro r ⟨-, -, -, rfl⟩
      positivity
  add_le' x y := by
    rw [← csInf_add (localizedModuleSeminormValues_nonempty A M x)
      (localizedModuleSeminormValues_bddBelow A M x) (localizedModuleSeminormValues_nonempty A M y)
      (localizedModuleSeminormValues_bddBelow A M y)]
    refine le_csInf ((localizedModuleSeminormValues_nonempty A M x).add
      (localizedModuleSeminormValues_nonempty A M y)) ?_
    intro r hr
    rw [Set.mem_add] at hr
    rcases hr with ⟨_, hrx, _, hry, rfl⟩
    rcases hrx with ⟨m, s, hx, rfl⟩
    rcases hry with ⟨n, t, hy, rfl⟩
    simpa [hx, hy] using localizedModuleSeminorm_add_mk_le A M m n s t
  neg' x := by rw [localizedModuleSeminormValues_neg]

noncomputable instance : SeminormedAddCommGroup (LocalizedModule A⁰ M) :=
  (addGroupSeminormLocalized A M).toSeminormedAddCommGroup

lemma localizedModuleSeminorm_add_mk_le_max [IsUltrametricDist M] (m n : M) (s t : A⁰) :
    sInf (localizedModuleSeminormValues A M (LocalizedModule.mk m s + LocalizedModule.mk n t)) ≤
      max (‖m‖ / ‖(s : A)‖) (‖n‖ / ‖(t : A)‖) := by
  refine (csInf_le (localizedModuleSeminormValues_bddBelow A M _)
    ⟨t • m + s • n, s * t, LocalizedModule.mk_add_mk.symm, rfl⟩).trans ?_
  rw [Submonoid.coe_mul, norm_mul]
  have hspos : 0 < ‖(s : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero s)
  have htpos : 0 < ‖(t : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero t)
  have hnorm : ‖t • m + s • n‖ ≤ max (‖(t : A)‖ * ‖m‖) (‖(s : A)‖ * ‖n‖) :=
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (norm_smul_le (t : A) m) (norm_smul_le (s : A) n))
  rw [div_le_iff₀ (mul_pos hspos htpos)]
  refine hnorm.trans <| max_le ?_ ?_
  · have hle : ‖m‖ / ‖(s : A)‖ ≤ max (‖m‖ / ‖(s : A)‖) (‖n‖ / ‖(t : A)‖) := le_max_left _ _
    rw [show ‖(t : A)‖ * ‖m‖ = (‖m‖ / ‖(s : A)‖) * (‖(s : A)‖ * ‖(t : A)‖) by
      field_simp [hspos.ne']]
    exact mul_le_mul_of_nonneg_right hle (mul_nonneg hspos.le htpos.le)
  · have hle : ‖n‖ / ‖(t : A)‖ ≤
        max (‖m‖ / ‖(s : A)‖) (‖n‖ / ‖(t : A)‖) := le_max_right _ _
    rw [show ‖(s : A)‖ * ‖n‖ =
        (‖n‖ / ‖(t : A)‖) * (‖(s : A)‖ * ‖(t : A)‖) by
      field_simp [htpos.ne']]
    exact mul_le_mul_of_nonneg_right hle (mul_nonneg hspos.le htpos.le)

instance [IsUltrametricDist M] : IsUltrametricDist (LocalizedModule A⁰ M) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ?_
  intro x y
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨rx, ⟨m, s, hx, rfl⟩, hrx_lt⟩ :=
    Real.lt_sInf_add_pos (localizedModuleSeminormValues_nonempty A M x) hε
  obtain ⟨ry, ⟨n, t, hy, rfl⟩, hry_lt⟩ :=
    Real.lt_sInf_add_pos (localizedModuleSeminormValues_nonempty A M y) hε
  have hxy : ‖x + y‖ ≤ max (‖m‖ / ‖(s : A)‖) (‖n‖ / ‖(t : A)‖) := by
    simpa [hx, hy] using! localizedModuleSeminorm_add_mk_le_max A M m n s t
  rw [← max_add_add_right]
  exact hxy.trans (max_lt_max hrx_lt hry_lt).le

theorem Module.IsCartesianGenerator.smul_ne_zero {k E ι : Type*} [NormedField k]
    [NormedAddCommGroup E] [Module k E] [IsBoundedSMul k E] [Fintype ι]
    {e : ι → E} (h : IsCartesianGenerator k e) (c : ι → k) (hc : ∀ i, c i ≠ 0) :
    IsCartesianGenerator k (fun i ↦ c i • e i) where
  exists_norm_le m := by
    rcases h.exists_norm_le m with ⟨a, hm, ha⟩
    refine ⟨fun i ↦ (c i)⁻¹ * a i, ?_, ?_⟩
    · rw [hm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul]
      congr 1
      field_simp [hc i]
    · intro i
      have : NormSMulClass k E := NormedDivisionRing.toNormSMulClass
      rw [show ‖(c i)⁻¹ * a i‖ * ‖c i • e i‖ = ‖a i‖ * ‖e i‖ by
        rw [norm_mul, norm_inv, norm_smul]
        field_simp [norm_ne_zero_iff.mpr (hc i)]]
      exact ha i
  norm_le m a hm i := by
    have hm' : m = ∑ i, (a i * c i) • e i := by
      rw [hm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul]
    have : NormSMulClass k E := NormedDivisionRing.toNormSMulClass
    rw [show ‖a i‖ * ‖c i • e i‖ = ‖a i * c i‖ * ‖e i‖ by
      rw [norm_smul, norm_mul]
      ring]
    exact h.norm_le m (fun i ↦ a i * c i) hm' i

theorem localizedModule_norm_mk_of_isCartesian
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] (m : F) (s : A⁰) :
    ‖(LocalizedModule.mk m s : LocalizedModule A⁰ F)‖ = ‖m‖ / ‖(s : A)‖ := by
  rcases Module.IsCartesian.exists_non_zero_cartesianGenerator A F with ⟨σ, hσ, e, hne, he⟩
  let B : Module.Basis σ A F := he.nonzeroBasis hne
  have hBcart : Module.IsCartesianGenerator A (fun i : σ ↦ B i) := by
    simpa [B, Module.IsCartesianGenerator.nonzeroBasis]
  have hspos : 0 < ‖(s : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero s)
  refine le_antisymm ?_ ?_
  · exact csInf_le (localizedModuleSeminormValues_bddBelow A F _) ⟨m, s, rfl, rfl⟩
  · refine le_csInf (localizedModuleSeminormValues_nonempty A F _) ?_
    rintro r ⟨n, t, hnt, rfl⟩
    have htpos : 0 < ‖(t : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero t)
    rw [LocalizedModule.mk_eq] at hnt
    rcases hnt with ⟨u, hu⟩
    have hu_ne : (u : A) ≠ 0 := nonZeroDivisors.coe_ne_zero u
    have hcoord (i : σ) : (s : A) * (B.repr n i) = (t : A) * (B.repr m i) := by
      have h := congrArg (fun x : F ↦ B.coord i x) hu
      simp only [smul_smul, LinearMap.map_smul_of_tower, Basis.coord_apply] at h
      change (((u * s : A⁰) : A) * (B.repr n i)) = (((u * t : A⁰) : A) * (B.repr m i)) at h
      exact mul_left_cancel₀ hu_ne <| by
        simpa [Submonoid.coe_mul, mul_assoc, mul_comm, mul_left_comm] using h
    have hn_bound (i : σ) : ‖B.repr n i‖ * ‖B i‖ ≤ ‖n‖ :=
      hBcart.norm_le n (fun i ↦ B.repr n i) (B.sum_repr n).symm i
    have hm_coeff_bound (i : σ) :
        ‖B.repr m i‖ * ‖B i‖ ≤ ‖(s : A)‖ * (‖n‖ / ‖(t : A)‖) := by
      have hnorm_coord : ‖(t : A)‖ * ‖B.repr m i‖ = ‖(s : A)‖ * ‖B.repr n i‖ := by
        rw [← norm_mul, ← hcoord i, norm_mul]
      rw [← mul_div_assoc, le_div_iff₀ htpos]
      nlinarith [hnorm_coord, hn_bound i, norm_nonneg (B i), norm_nonneg (s : A)]
    have hm_bound : ‖m‖ ≤ ‖(s : A)‖ * (‖n‖ / ‖(t : A)‖) := by
      grw [← B.sum_repr m]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ?_ ?_
      · positivity
      · exact fun i _ ↦ (norm_smul_le (B.repr m i) (B i)).trans (hm_coeff_bound i)
    rw [div_le_iff₀ hspos]
    nlinarith [hm_bound]

theorem localizedModule_mkLinearMap_norm_of_isCartesian [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] (m : F) :
    ‖(mkLinearMap A⁰ F m : LocalizedModule A⁰ F)‖ = ‖m‖ := by
  simp [LocalizedModule.mkLinearMap_apply, localizedModule_norm_mk_of_isCartesian]

noncomputable instance (M : Type*) [NormedAddCommGroup M] [IsUltrametricDist M] [Module A M]
    [IsBoundedSMul A M] [IsCartesian A M] : NormedAddCommGroup (LocalizedModule A⁰ M) := by
  refine NormedAddCommGroup.ofSeparation ?_
  intro x hx
  induction x using LocalizedModule.induction_on with
  | h m s =>
    have hspos : 0 < ‖(s : A)‖ := norm_pos_iff.mpr (nonZeroDivisors.coe_ne_zero s)
    rw [localizedModule_norm_mk_of_isCartesian A m s] at hx
    have hm0 : ‖m‖ = 0 := (div_eq_zero_iff.mp hx).resolve_right hspos.ne'
    simp [norm_eq_zero.mp hm0]

theorem localizedModule_mkLinearMap_injective_of_isCartesian [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] : Function.Injective (mkLinearMap A⁰ F : F →ₗ[A] LocalizedModule A⁰ F) := by
  intro x y hxy
  rw [← sub_eq_zero, ← norm_eq_zero]
  simpa [map_sub, hxy] using (localizedModule_mkLinearMap_norm_of_isCartesian A (x - y)).symm

theorem norm_smul_of_isCartesian [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] (ω : A) (hω : ω ≠ 0) (m : F) :
    ‖ω • m‖ = ‖ω‖ * ‖m‖ := by
  let s : A⁰ := ⟨ω, mem_nonZeroDivisors_of_ne_zero hω⟩
  have hdiv : ‖ω • m‖ / ‖ω‖ = ‖m‖ := by
    rw [show ‖ω • m‖ / ‖ω‖ =
        ‖(LocalizedModule.mk (s • m) s : LocalizedModule A⁰ F)‖ by
      rw [localizedModule_norm_mk_of_isCartesian]
      rfl]
    simp [localizedModule_norm_mk_of_isCartesian]
  rw [div_eq_iff (norm_ne_zero_iff.mpr hω)] at hdiv
  simpa [s, mul_comm] using hdiv

variable {A} in
theorem module_smul_top_isCartesian [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] (ω : A) (hω : ω ≠ 0) :
    IsCartesian A (↥(ω • (⊤ : Submodule A F))) := by
  rcases IsCartesian.out A F with ⟨σ, hσ, e, he⟩
  let S : Submodule A F := ω • (⊤ : Submodule A F)
  let g : σ → S := fun i ↦
    ⟨ω • e i, by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨e i, Submodule.mem_top, rfl⟩⟩
  have hcancel (x y : F) (hxy : ω • x = ω • y) : x = y := by
    rw [← sub_eq_zero, ← norm_eq_zero]
    have hzero : ω • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
    have hnorm := norm_smul_of_isCartesian A ω hω (x - y)
    rw [hzero, norm_zero] at hnorm
    exact (mul_eq_zero.mp hnorm.symm).resolve_left (norm_ne_zero_iff.mpr hω)
  refine ⟨σ, hσ, g, ⟨⟨?_⟩, ?_⟩⟩
  · intro x
    have hxmem : (x : F) ∈ S := x.2
    rw [Submodule.mem_smul_pointwise_iff_exists] at hxmem
    rcases hxmem with ⟨y, -, hy⟩
    rcases he.exists_norm_le y with ⟨a, hay, ha_norm⟩
    refine ⟨a, ?_, ?_⟩
    · ext
      rw [← hy, hay, Finset.smul_sum]
      simp [g, smul_smul, mul_comm]
    · intro i
      have hle := mul_le_mul_of_nonneg_left (ha_norm i) (norm_nonneg ω)
      rw [show ‖a i‖ * ‖g i‖ = ‖ω‖ * (‖a i‖ * ‖e i‖) by
        rw [show ‖g i‖ = ‖ω‖ * ‖e i‖ from norm_smul_of_isCartesian A ω hω (e i)]
        ring]
      rwa [← norm_smul_of_isCartesian A ω hω y, hy] at hle
  · intro x a hx i
    have hxmem : (x : F) ∈ S := x.2
    rw [Submodule.mem_smul_pointwise_iff_exists] at hxmem
    rcases hxmem with ⟨y, -, hy⟩
    have hy_repr : y = ∑ i : σ, a i • e i := by
      apply hcancel
      rw [hy, congrArg Subtype.val hx, Finset.smul_sum]
      simp [g, smul_smul, mul_comm]
    have hle := mul_le_mul_of_nonneg_left (he.norm_le y a hy_repr i) (norm_nonneg ω)
    rw [show ‖a i‖ * ‖g i‖ = ‖ω‖ * (‖a i‖ * ‖e i‖) by
      rw [show ‖g i‖ = ‖ω‖ * ‖e i‖ from norm_smul_of_isCartesian A ω hω (e i)]
      ring]
    rwa [← norm_smul_of_isCartesian A ω hω y, hy] at hle

theorem Submodule.isPseudoCartesian_and_isStrictlyClosed_of_smul_top_quotient
    {B R : Type*} [NormedCommRing B] [NormedCommRing R] [IsDomain R] [NormOneClass R]
    [NormMulClass R] [Algebra B R] {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
    [Module R E] [Module B E] [IsScalarTower B R E] [IsBoundedSMul R E]
    [IsCartesian R E] (hnorm : ∀ b : B, ‖algebraMap B R b‖ = ‖b‖) (ω : R) (hω : ω ≠ 0)
    (hωstrict : (ω • (⊤ : Submodule R E)).IsStrictlyClosed)
    {K : Submodule R E} (hωK : ω • (⊤ : Submodule R E) ≤ K)
    (hKbar :
      let Nω : Submodule R E := ω • (⊤ : Submodule R E)
      let Kbar : Submodule R (E ⧸ Nω) := K.map Nω.mkQ
      Module.IsPseudoCartesian B (Kbar.restrictScalars B) ∧
        (Kbar.restrictScalars B).IsStrictlyClosed) :
    Module.IsPseudoCartesian R K ∧ K.IsStrictlyClosed := by
  let Nω : Submodule R E := ω • (⊤ : Submodule R E)
  let Kbar : Submodule R (E ⧸ Nω) := K.map Nω.mkQ
  have : Module.IsCartesian R Nω := module_smul_top_isCartesian ω hω
  have : Module.IsPseudoCartesian R Kbar := by
    have : Module.IsPseudoCartesian B Kbar := hKbar.1
    exact Module.IsPseudoCartesian.extendScalars_of_isometric_algebra hnorm
  have hKbarStrictR : Kbar.IsStrictlyClosed :=
    Submodule.IsStrictlyClosed.of_restrictScalars hKbar.2
  have : Module.IsPseudoCartesian R (K ⧸ Nω.submoduleOf K) :=
    Module.IsPseudoCartesian.of_linearEquiv (Nω.quotientSubmoduleOfEquivMapMkQ K)
      (Submodule.quotientSubmoduleOfEquivMapMkQ_norm hωK)
  exact Submodule.isPseudoCartesian_and_isStrictlyClosed_of_quotient hωK hωstrict hKbarStrictR

/-- The localization of a cartesian module is cartesian. -/
instance localizedModule_isCartesian_of_isCartesian [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] : IsCartesian (Localization A⁰) (LocalizedModule A⁰ F) := by
  let Q := Localization A⁰
  let V := LocalizedModule A⁰ F
  let L : F →ₗ[A] V := mkLinearMap A⁰ F
  rcases Module.IsCartesian.exists_non_zero_cartesianGenerator A F with ⟨σ, hσ, e, hne, he⟩
  let B : Module.Basis σ A F := he.nonzeroBasis hne
  let BQ : Module.Basis σ Q V := Module.Basis.ofIsLocalizedModule Q A⁰ L B
  have hBcart : Module.IsCartesianGenerator A (fun i : σ ↦ B i) := by
    simpa [B, Module.IsCartesianGenerator.nonzeroBasis]
  have hmk_smul (m : F) (s : A⁰) : LocalizedModule.mk m s = (Localization.mk 1 s : Q) • L m := by
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_smul_mk]
    simp
  have hcoord_bound (x : V) (i : σ) : ‖BQ.repr x i‖ * ‖BQ i‖ ≤ ‖x‖ := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      have hsnonneg : 0 ≤ ‖(s : A)‖ := norm_nonneg (s : A)
      have hrepr : BQ.repr (LocalizedModule.mk m s : V) i = Localization.mk (B.repr m i) s := by
        rw [hmk_smul]
        rw [show BQ.repr ((Localization.mk 1 s : Q) • L m) i =
            (Localization.mk 1 s : Q) * BQ.repr (L m) i by simp]
        rw [Module.Basis.ofIsLocalizedModule_repr_apply]
        change (Localization.mk 1 s : Q) * Localization.mk (B.repr m i) 1 =
          Localization.mk (B.repr m i) s
        rw [Localization.mk_mul]
        simp
      have hBnorm : ‖BQ i‖ = ‖B i‖ := by
        rw [Module.Basis.ofIsLocalizedModule_apply, LocalizedModule.mkLinearMap_apply,
          localizedModule_norm_mk_of_isCartesian]
        simp
      have hb : ‖B.repr m i‖ * ‖B i‖ ≤ ‖m‖ :=
        hBcart.norm_le m (fun i ↦ B.repr m i) (B.sum_repr m).symm i
      rw [hrepr, norm_localization_mk, hBnorm, localizedModule_norm_mk_of_isCartesian A m s]
      rw [show (‖B.repr m i‖ / ‖(s : A)‖) * ‖B i‖ = (‖B.repr m i‖ * ‖B i‖) / ‖(s : A)‖ by ring]
      exact div_le_div_of_nonneg_right hb hsnonneg
  refine ⟨σ, inferInstance, fun i ↦ BQ i, ⟨⟨?_⟩, ?_⟩⟩
  · exact fun x ↦ ⟨fun i ↦ BQ.repr x i, (BQ.sum_repr x).symm, hcoord_bound x⟩
  · intro x a hx i
    have hcoeff : a i = BQ.repr x i := by
      have hrepr_sum : BQ.repr (∑ j : σ, a j • BQ j) i = a i := by
        rw [show BQ.repr (∑ j : σ, a j • BQ j) i =
            BQ.equivFun (∑ j : σ, a j • BQ j) i by
          rw [Module.Basis.equivFun_apply]]
        have hsum_eq : (∑ j : σ, a j • BQ j) = BQ.equivFun.symm a := by
          rw [Module.Basis.equivFun_symm_apply]
        rw [hsum_eq]
        exact congrFun (LinearEquiv.apply_symm_apply BQ.equivFun a) i
      rw [← hrepr_sum, ← hx]
    simpa [hcoeff] using hcoord_bound x i

instance localizedModule_isBoundedSMul_of_isCartesian
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [Module A F] [IsBoundedSMul A F] [IsCartesian A F] :
    IsBoundedSMul A (LocalizedModule A⁰ F) := by
  refine IsBoundedSMul.of_norm_smul_le ?_
  intro a x
  induction x using LocalizedModule.induction_on with
  | h m s =>
      rw [← algebraMap_smul (Localization A⁰) a (LocalizedModule.mk m s)]
      change ‖Localization.mk a (1 : A⁰) • (LocalizedModule.mk m s : LocalizedModule A⁰ F)‖ ≤
        ‖a‖ * ‖(LocalizedModule.mk m s : LocalizedModule A⁰ F)‖
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_mul]
      rw [localizedModule_norm_mk_of_isCartesian A (a • m) s,
        localizedModule_norm_mk_of_isCartesian A m s]
      simpa [mul_div_assoc] using div_le_div_of_nonneg_right (norm_smul_le a m) (norm_nonneg s.1)

/-- Let `A` be a normed commutative ring, `F` be a cartesian `A`-module,
  `M` be a finite generated submodule of `F`. Then there exist an non-zero element `ω ∈ A` and
  a cartesian `A`-submodule `N ⊆ LocalizedModule A⁰ F` such that `ω • N ⊆ M ⊆ N`. -/
theorem Submodule.exists_cartesian_submodule_envelope [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F] [Module A F] [IsBoundedSMul A F]
    [IsCartesian A F] (M : Submodule A F) [Module.Finite A M] :
    ∃ (ω : A) (_ : ω ≠ 0) (N : Submodule A (LocalizedModule A⁰ F)) (_ : IsCartesian A N)
    (_ : ω • N ≤ M.map (mkLinearMap A⁰ F)), M.map (mkLinearMap A⁰ F) ≤ N := by
  classical
  let Q := Localization A⁰
  let V := LocalizedModule A⁰ F
  let L : F →ₗ[A] V := mkLinearMap A⁰ F
  let : NormedAddCommGroup Q := (NormedRing.toRingNorm Q).toAddGroupNorm.toNormedAddCommGroup
  let : SeminormedAddCommGroup Q := (inferInstance : NormedAddCommGroup Q).toSeminormedAddCommGroup
  have hnorm_smul_QV (q : Q) (x : V) : ‖q • x‖ ≤ ‖q‖ * ‖x‖ := by
    refine Localization.induction_on q ?_
    intro ⟨a, s⟩
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [LocalizedModule.mk_smul_mk, norm_localization_mk,
        localizedModule_norm_mk_of_isCartesian A, localizedModule_norm_mk_of_isCartesian A]
      grw [Submonoid.coe_mul, norm_mul, div_le_div_of_nonneg_right (norm_smul_le a m)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      field_simp
      simp
  have : IsBoundedSMul Q V :=
    { dist_smul_pair' := by
        intro q x y
        have hq0 : dist q 0 = ‖q‖ := dist_zero_right q
        rw [dist_eq_norm, dist_eq_norm, hq0]
        simpa [smul_sub, sub_zero] using hnorm_smul_QV q (x - y)
      dist_pair_smul' := by
        intro q r x
        have hqr : dist q r = ‖q - r‖ := by
          rw [SeminormedRing.dist_eq, show - q + r = - (q - r) by abel]
          simpa using! (norm_neg (q - r))
        rw [dist_eq_norm, hqr, dist_zero_right x]
        simpa [sub_smul] using hnorm_smul_QV (q - r) x }
  obtain ⟨n, g, hg_span⟩ : ∃ n g, Submodule.span A (Set.range g) = (⊤ : Submodule A M) :=
    Module.Finite.exists_fin
  let gV : Fin n → V := fun k ↦ L (g k : F)
  let MQ : Submodule Q V := Submodule.span Q (Set.range gV)
  have : IsBoundedSMul Q MQ :=
    { dist_smul_pair' := by
        intro q x y
        have hq0 : dist q 0 = ‖q‖ := dist_zero_right q
        rw [dist_eq_norm, dist_eq_norm, hq0]
        simpa [Submodule.coe_sub, smul_sub, sub_zero] using hnorm_smul_QV q (x - y).1
      dist_pair_smul' := by
        intro q r x
        have hqr : dist q r = ‖q - r‖ := by
          rw [SeminormedRing.dist_eq, show - q + r = - (q - r) by abel]
          simpa using! (norm_neg (q - r))
        rw [dist_eq_norm, hqr, dist_zero_right x]
        simpa [Submodule.coe_sub, sub_smul] using hnorm_smul_QV (q - r) (x : V) }
  rcases Module.IsCartesian.exists_non_zero_cartesianGenerator Q MQ with ⟨ι, hι, e, hne, he⟩
  have he_span (i : ι) : (e i : V) ∈ Submodule.span Q (Set.range gV) := (e i).2
  have he_repr (i : ι) : ∃ c : Fin n → Q, ∑ k, c k • gV k = (e i : V) :=
    (Submodule.mem_span_range_iff_exists_fun Q).mp (he_span i)
  choose eCoeff heCoeff using he_repr
  let eDenomCoeff : ι × Fin n → Q := fun p ↦ eCoeff p.1 p.2
  obtain ⟨δ, hδ_int⟩ :=
    IsLocalizedModule.exist_integer_multiples_of_finite A⁰ (Algebra.linearMap A Q) eDenomCoeff
  let δQ : Q := algebraMap A Q (δ : A)
  have hδQ : δQ ≠ 0 := by
    intro h
    rw [IsLocalization.to_map_eq_zero_iff Q (le_refl A⁰)] at h
    exact nonZeroDivisors.coe_ne_zero δ h
  choose eCoeffA heCoeffA using hδ_int
  let vMQ : ι → MQ := fun i ↦ δQ • e i
  have hv_cart : Module.IsCartesianGenerator Q vMQ :=
    he.smul_ne_zero (fun _ : ι ↦ δQ) (fun _ ↦ hδQ)
  have hv_ne (i : ι) : vMQ i ≠ 0 := by
    intro hi
    apply hne i
    have hi' : δQ • e i = 0 := by simpa [vMQ] using hi
    have h := congrArg (fun x : MQ ↦ δQ⁻¹ • x) hi'
    simpa [smul_smul, inv_mul_cancel₀ hδQ] using h
  let vBasis : Module.Basis ι Q MQ := hv_cart.nonzeroBasis hv_ne
  have hv_mem_map (i : ι) : (vMQ i : V) ∈ M.map L := by
    have hcoeff (k : Fin n) : algebraMap A Q (eCoeffA (i, k)) =
        δQ * eCoeff i k := by
      simpa [eDenomCoeff, δQ, Algebra.smul_def] using heCoeffA (i, k)
    have hsum : (vMQ i : V) = ∑ k, eCoeffA (i, k) • gV k := by
      change δQ • (e i : V) = ∑ k, eCoeffA (i, k) • gV k
      rw [← heCoeff i, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [smul_smul, ← hcoeff k]
      simp [gV]
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ ↦
      Submodule.smul_mem _ _ ⟨(g k : F), (g k).2, rfl⟩
  let gMQ : Fin n → MQ := fun k ↦ ⟨gV k, Submodule.subset_span ⟨k, rfl⟩⟩
  let coeff : Fin n × ι → Q := fun p ↦ vBasis.repr (gMQ p.1) p.2
  obtain ⟨ωS, hω_int⟩ :=
    IsLocalizedModule.exist_integer_multiples_of_finite A⁰ (Algebra.linearMap A Q) coeff
  let ω : A := ωS
  let ωQ : Q := algebraMap A Q ω
  have hω_ne : ω ≠ 0 := nonZeroDivisors.coe_ne_zero ωS
  have hωQ : ωQ ≠ 0 := by
    intro h
    rw [IsLocalization.to_map_eq_zero_iff Q (le_refl A⁰)] at h
    exact hω_ne h
  choose coeffA hcoeffA using hω_int
  let wMQ : ι → MQ := fun i ↦ ωQ⁻¹ • vMQ i
  let wV : ι → V := fun i ↦ (wMQ i : V)
  let N : Submodule A V := Submodule.span A (Set.range wV)
  have hN_le_MQ : N ≤ MQ.restrictScalars A := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact (wMQ i).2
  have hw_cart : Module.IsCartesianGenerator Q wMQ :=
    hv_cart.smul_ne_zero (fun _ : ι ↦ ωQ⁻¹) (fun _ ↦ inv_ne_zero hωQ)
  have hN_cart : IsCartesian A N := by
    let genN : ι → N := fun i ↦ ⟨wV i, Submodule.subset_span ⟨i, rfl⟩⟩
    have hgen_norm_le (x : N) (a : ι → A) (hx : x = ∑ i, a i • genN i) (i : ι) :
        ‖a i‖ * ‖genN i‖ ≤ ‖x‖ := by
      let xMQ : MQ := ⟨(x : V), hN_le_MQ x.2⟩
      have hxMQ : xMQ = ∑ i, (algebraMap A Q (a i)) • wMQ i := by
        ext
        simpa [xMQ, genN, wV] using congrArg Subtype.val hx
      have h := hw_cart.norm_le xMQ (fun i ↦ algebraMap A Q (a i)) hxMQ i
      rw [norm_algebraMap_localization] at h
      simpa [genN, xMQ, wV] using h
    have hgen : Module.IsCartesianGenerator A genN := by
      refine ⟨⟨?_⟩, ?_⟩
      · intro x
        have hxmem : (x : V) ∈ Submodule.span A (Set.range wV) := x.2
        rw [Submodule.mem_span_range_iff_exists_fun A] at hxmem
        rcases hxmem with ⟨a, ha⟩
        refine ⟨a, ?_, ?_⟩
        · ext
          simp [genN, wV, ← ha]
        · intro i
          exact hgen_norm_le x a (Subtype.ext (by simp [genN, wV, ← ha])) i
      · exact fun x a hx i ↦ hgen_norm_le x a hx i
    exact ⟨ι, inferInstance, genN, hgen⟩
  have hω_smul_w (i : ι) : ω • wV i = (vMQ i : V) := by
    change (ω : A) • (ωQ⁻¹ • (vMQ i : V)) = (vMQ i : V)
    rw [← smul_assoc, Algebra.smul_def, mul_inv_cancel₀ hωQ, one_smul]
  have hωN : ω • N ≤ M.map L := by
    intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx
    rcases hx with ⟨y, hy, hyx⟩
    rw [← hyx]
    rw [Submodule.mem_span_range_iff_exists_fun A] at hy
    rcases hy with ⟨a, ha⟩
    have hsum : ω • y = ∑ i, a i • (vMQ i : V) := by
      rw [← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, mul_comm ω (a i), ← smul_smul, hω_smul_w]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hv_mem_map i)
  have hg_mem_N (k : Fin n) : L (g k : F) ∈ N := by
    have hg_repr : gMQ k = ∑ i, (vBasis.repr (gMQ k) i) • vMQ i := by
      simpa [vBasis, Module.IsCartesianGenerator.nonzeroBasis] using (vBasis.sum_repr (gMQ k)).symm
    have hterm (i : ι) :
        (algebraMap A Q (coeffA (k, i))) • wMQ i = (vBasis.repr (gMQ k) i) • vMQ i := by
      have hc : algebraMap A Q (coeffA (k, i)) = ωQ * (vBasis.repr (gMQ k) i) := by
        simpa [coeff, ω, ωQ, Algebra.smul_def] using hcoeffA (k, i)
      rw [smul_smul, hc]
      congr 1
      rw [mul_assoc, mul_comm (vBasis.repr (gMQ k) i) ωQ⁻¹, ← mul_assoc, mul_inv_cancel₀ hωQ,
        one_mul]
    have hg_A : gMQ k = ∑ i, (algebraMap A Q (coeffA (k, i))) • wMQ i := by
      rw [hg_repr]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (hterm i).symm
    have hLV : L (g k : F) = ∑ i, coeffA (k, i) • wV i := by
      simpa [gMQ, gV, wV, L] using congrArg Subtype.val hg_A
    rw [hLV]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hM_le_N : M.map L ≤ N := by
    rintro x ⟨m, hm, rfl⟩
    let mM : M := ⟨m, hm⟩
    have hm_span : mM ∈ Submodule.span A (Set.range g) := by simp [hg_span]
    rw [Submodule.mem_span_range_iff_exists_fun A] at hm_span
    rcases hm_span with ⟨a, ha⟩
    have haF : (∑ k, a k • (g k : F)) = m := by simpa using congrArg Subtype.val ha
    simpa [← haF, map_sum] using Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hg_mem_N k)
  exact ⟨ω, hω_ne, N, hN_cart, hωN, hM_le_N⟩

end norm_localization

namespace TateAlgebra

theorem smul_top_isStrictlyClosed_of_ringEquiv
    {R S : Type*} [SeminormedCommRing R] [SeminormedCommRing S]
    (e : R ≃+* S) (he : ∀ x : R, ‖e x‖ = ‖x‖) (ω : R)
    (hS : (e ω • (⊤ : Submodule S S)).IsStrictlyClosed) :
    (ω • (⊤ : Submodule R R)).IsStrictlyClosed := by
  have he_symm (y : S) : ‖e.symm y‖ = ‖y‖ := by simpa using (he (e.symm y)).symm
  intro x
  rcases Quotient.mk_surjective x with ⟨h, rfl⟩
  rcases hS ((e ω • (⊤ : Submodule S S)).mkQ (e h)) with ⟨s, hsq, hsn⟩
  let r : R := e.symm s
  have hrq : (ω • (⊤ : Submodule R R)).mkQ r = (ω • (⊤ : Submodule R R)).mkQ h := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmemS : s - e h ∈ e ω • (⊤ : Submodule S S) := by rwa [← Submodule.Quotient.eq]
    rw [Submodule.mem_smul_pointwise_iff_exists] at hmemS
    rcases hmemS with ⟨t, -, ht⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨e.symm t, Submodule.mem_top, ?_⟩
    apply e.injective
    simpa [r, map_sub, smul_eq_mul] using ht
  refine ⟨r, hrq, ?_⟩
  change ‖r‖ = ‖(ω • (⊤ : Submodule R R)).mkQ h‖
  rw [← hrq]
  refine le_antisymm ?_ (Submodule.Quotient.norm_mk_le _ r)
  refine QuotientAddGroup.le_norm_iff.2 ?_
  intro y hy
  have hyS : (e y) - s ∈ e ω • (⊤ : Submodule S S) := by
    have hymem : y - r ∈ ω • (⊤ : Submodule R R) := by rwa [← Submodule.Quotient.eq]
    rw [Submodule.mem_smul_pointwise_iff_exists] at hymem
    rcases hymem with ⟨u, -, hu⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨e u, Submodule.mem_top, ?_⟩
    simpa [r, map_sub, smul_eq_mul] using congrArg e hu
  have hs_le : ‖s‖ ≤ ‖e y‖ := by
    rw [hsn, show (e ω • (⊤ : Submodule S S)).mkQ (e h) = (e ω • (⊤ : Submodule S S)).mkQ (e y) by
      simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hs_h : s - e h ∈ e ω • (⊤ : Submodule S S) := by rwa [← Submodule.Quotient.eq]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        Submodule.add_mem _ (Submodule.neg_mem _ hs_h) (Submodule.neg_mem _ hyS)]
    exact Submodule.Quotient.norm_mk_le (e ω • (⊤ : Submodule S S)) (e y)
  grw [he_symm s, hs_le, he y]

theorem weierstrass_smul_top_isStrictlyClosed {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {w : TateAlgebra Unit A} {n : ℕ} (hw : TateAlgebra.IsWeierstrassPolynomial w n) :
    (w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A))).IsStrictlyClosed := by
  have hwc (l : ℕ) : ‖PowerSeries.coeff l w.1‖ ≤ 1 :=
    (TateAlgebra.coeff_norm_le w (Finsupp.single () l)).trans hw.norm_le_one
  have hwt (l : ℕ) (hl : l > n) : ‖PowerSeries.coeff l w.1‖ < (1 / 2 : ℝ) := by
    rw [hw.isPoly l hl]
    norm_num
  have hw_tail_one (l : ℕ) (hl : l > n) : ‖PowerSeries.coeff l w.1‖ < (1 : ℝ) :=
    (hwt l hl).trans (by norm_num)
  intro x
  rcases Quotient.mk_surjective x with ⟨h, rfl⟩
  obtain ⟨q, r, hrdeg, hdiv, -, -⟩ := TateAlgebra.distinguished_division w
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hw.monic hwc hwt h
  let rep : TateAlgebra Unit A := TateAlgebra.polynomialToTate r
  have hrep_quot :
      (w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A))).mkQ rep =
        (w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A))).mkQ h := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : rep - h ∈ w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A)) := by
      rw [hdiv, Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨-q, Submodule.mem_top, ?_⟩
      simp [rep, sub_eq_add_neg, add_comm, add_left_comm, mul_comm]
    exact hmem
  refine ⟨rep, hrep_quot, ?_⟩
  change ‖rep‖ = ‖(w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A))).mkQ h‖
  rw [← hrep_quot]
  refine le_antisymm ?_ (Submodule.Quotient.norm_mk_le _ rep)
  refine QuotientAddGroup.le_norm_iff.2 ?_
  intro y hy
  rcases TateAlgebra.distinguished_division w (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hw.monic hwc hwt y with
    ⟨q₂, r₂, hr₂deg, hydiv, _, hr₂_bound⟩
  have hsame_rem : r₂ = r := by
    have hy_rep_mem : y - rep ∈ w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A)) := by
      rwa [← Submodule.Quotient.eq]
    rw [Submodule.mem_smul_pointwise_iff_exists] at hy_rep_mem
    rcases hy_rep_mem with ⟨t, -, ht⟩
    have hzero : (q₂ - t) * w + TateAlgebra.polynomialToTate (r₂ - r) = 0 := by
      rw [TateAlgebra.polynomialToTate_sub]
      calc _ = (q₂ * w + polynomialToTate r₂) - (t * w + polynomialToTate r) := by ring
        _ = 0 := by
          have ht' : t * w = y - rep := by simpa [Algebra.smul_def, mul_comm] using ht
          rw [← hydiv, ht']
          ring
    rw [← sub_eq_zero]
    exact (TateAlgebra.division_injective w hw.monic hwc hw_tail_one
      ((Polynomial.degree_sub_le r₂ r).trans_lt (max_lt hr₂deg hrdeg)) hzero).2
  change ‖TateAlgebra.polynomialToTate r‖ ≤ ‖y‖
  rw [← hsame_rem]
  exact TateAlgebra.norm_polynomialToTate_le_of_coeff_le r₂ hr₂_bound

lemma polynomialToTate_eq_sum_coeff_lt {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (r : Polynomial A) (hr : r.degree < n) :
    polynomialToTate r =
      ∑ i : Fin n, r.coeff i • polynomialToTate (Polynomial.X ^ (i : ℕ) : Polynomial A) := by
  let p : Polynomial A := ∑ i : Fin n, r.coeff i • (Polynomial.X ^ (i : ℕ) : Polynomial A)
  have hrpoly : r = p := by
    ext m
    dsimp [p]
    rw [Polynomial.finsetSum_coeff]
    by_cases hm : m < n
    · rw [Finset.sum_eq_single ⟨m, hm⟩ _ (fun hnot ↦ (hnot (by simp)).elim)]
      · simp
      · intro b _ hbne
        have hbm : (b : ℕ) ≠ m := fun hbval ↦ hbne (Fin.ext hbval)
        simp [Polynomial.coeff_X_pow, hbm.symm]
    · have hcoeff0 : r.coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast Nat.le_of_not_gt hm))
      rw [hcoeff0, Finset.sum_eq_zero]
      intro b _
      have hbm : (b : ℕ) ≠ m := fun h ↦ Nat.not_le_of_gt b.2 (h ▸ Nat.le_of_not_gt hm)
      simp [Polynomial.coeff_X_pow, hbm.symm]
  conv_lhs => rw [hrpoly]
  change polynomialToTateAlgHom p = _
  simp [p, polynomialToTateAlgHom, map_sum]

/-- The polynomial given by a finite family of coefficients. -/
noncomputable def polynomialOfFin {A : Type*} [Semiring A] {n : ℕ} (a : Fin n → A) : Polynomial A :=
  ∑ i : Fin n, a i • (Polynomial.X ^ (i : ℕ) : Polynomial A)

lemma polynomialOfFin_coeff {A : Type*} [Semiring A] {n : ℕ} (a : Fin n → A)
    {m : ℕ} (hm : m < n) : (polynomialOfFin a).coeff m = a ⟨m, hm⟩ := by
  dsimp [polynomialOfFin]
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
  · simp
  · intro b _ hbne
    have hbm : (b : ℕ) ≠ m := fun hbval ↦ hbne (Fin.ext hbval)
    simp [Polynomial.coeff_X_pow, hbm.symm]
  · exact fun hnot ↦ (hnot (by simp)).elim

lemma polynomialOfFin_coeff_of_le {A : Type*} [Semiring A] {n : ℕ} (a : Fin n → A)
    {m : ℕ} (hm : n ≤ m) : (polynomialOfFin a).coeff m = 0 := by
  dsimp [polynomialOfFin]
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero fun b _ ↦ by
    have hbm : (b : ℕ) ≠ m := fun h ↦ Nat.not_le_of_gt b.2 (h ▸ hm)
    simp [Polynomial.coeff_X_pow, hbm.symm]

lemma polynomialOfFin_degree_lt {A : Type*} [Semiring A] {n : ℕ}
    (a : Fin n → A) : (polynomialOfFin a).degree < n := by
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
  exact fun m hm ↦ polynomialOfFin_coeff_of_le a (by exact_mod_cast hm)

lemma polynomialToTate_polynomialOfFin {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {n : ℕ} (a : Fin n → A) :
    polynomialToTate (polynomialOfFin a) =
      ∑ i : Fin n, a i • polynomialToTate (Polynomial.X ^ (i : ℕ) : Polynomial A) := by
  change polynomialToTateAlgHom (polynomialOfFin a) = _
  simp [polynomialOfFin, polynomialToTateAlgHom, map_sum]

lemma polynomialToTate_X_pow_norm_le_one {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    (i : ℕ) : ‖polynomialToTate (Polynomial.X ^ i : Polynomial A)‖ ≤ 1 := by
  refine norm_polynomialToTate_le_of_coeff_le _ ?_
  intro j
  by_cases hji : j = i <;> simp [Polynomial.coeff_X_pow, hji]

/-- A Weierstrass quotient `A{T}/(w)` is cartesian over the coefficient ring. -/
lemma weierstrass_quotient_isCartesian {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {w : TateAlgebra Unit A} {n : ℕ} (hw : IsWeierstrassPolynomial w n) :
    IsCartesian A
      ((TateAlgebra Unit A) ⧸
        (w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A)))) := by
  let I : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A) :=
    w • (⊤ : Submodule (TateAlgebra Unit A) (TateAlgebra Unit A))
  let e : Fin n → (TateAlgebra Unit A) ⧸ I := fun i ↦
    I.mkQ (polynomialToTate (Polynomial.X ^ (i : ℕ) : Polynomial A))
  have hstrict : I.IsStrictlyClosed := weierstrass_smul_top_isStrictlyClosed hw
  have hw_le (l : ℕ) : ‖PowerSeries.coeff l w.1‖ ≤ 1 :=
    (TateAlgebra.coeff_norm_le w (Finsupp.single () l)).trans hw.norm_le_one
  have hwtail (l : ℕ) (hl : l > n) : ‖PowerSeries.coeff l w.1‖ < (1 / 2 : ℝ) := by
    rw [hw.isPoly l hl, norm_zero]
    norm_num
  have he_le_one (i : Fin n) : ‖e i‖ ≤ 1 := (Submodule.Quotient.norm_mk_le I _).trans
    (polynomialToTate_X_pow_norm_le_one (i : ℕ))
  refine ⟨Fin n, inferInstance, e, ⟨⟨?_⟩, ?_⟩⟩
  · intro x
    rcases hstrict x with ⟨h, hhq, hhnorm⟩
    obtain ⟨q, r, hrdeg, hdiv, -, hrcoeff⟩ :=
      distinguished_division w (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        hw.monic hw_le hwtail h
    refine ⟨fun i : Fin n ↦ r.coeff i, ?_, ?_⟩
    · rw [← hhq, hdiv]
      have hqw : I.mkQ (q * w + polynomialToTate r) = I.mkQ (polynomialToTate r) := by
        simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
        rw [Submodule.mem_smul_pointwise_iff_exists]
        refine ⟨q, Submodule.mem_top, ?_⟩
        ring
      rw [hqw, polynomialToTate_eq_sum_coeff_lt r hrdeg]
      simp [e, I, Submodule.mkQ_apply, map_sum]
    · intro i
      rw [← hhnorm]
      refine (mul_le_mul_of_nonneg_left (he_le_one i) (norm_nonneg _)).trans ?_
      simpa using hrcoeff i
  · intro x a hx i
    rcases hstrict x with ⟨h, hhq, hhnorm⟩
    obtain ⟨q, r, hrdeg, hdiv, -, hrcoeff⟩ :=
      distinguished_division w (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        hw.monic hw_le hwtail h
    let p : Polynomial A := polynomialOfFin a
    have hpdeg : p.degree < n := polynomialOfFin_degree_lt a
    have hpx : I.mkQ (polynomialToTate p) = x := by
      rw [hx]
      simp [p, polynomialToTate_polynomialOfFin, e, I, Submodule.mkQ_apply, map_sum]
    have hp_hr : I.mkQ (polynomialToTate p) = I.mkQ h := hpx.trans hhq.symm
    have hmem : polynomialToTate p - h ∈ I := by rwa [← Submodule.Quotient.eq]
    rw [Submodule.mem_smul_pointwise_iff_exists] at hmem
    rcases hmem with ⟨u, -, hu⟩
    have hzero : (u + q) * w + polynomialToTate (r - p) = 0 := by
      have hu' : polynomialToTate p - h = w * u := by
        simpa [smul_eq_mul, mul_comm] using hu.symm
      rw [hdiv] at hu'
      have : polynomialToTate p - (q * w + polynomialToTate r) = w * u := hu'
      rw [polynomialToTate_sub]
      have hmain : (u + q) * w + (polynomialToTate r - polynomialToTate p) =
          (w * u + q * w) + (polynomialToTate r - polynomialToTate p) := by
        ring
      rw [hmain, ← this]
      ring
    have hrpdeg : (r - p).degree < n := by
      refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
      intro m hm
      have hr0 : r.coeff m = 0 := Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hrdeg (by exact_mod_cast hm))
      have hp0 : p.coeff m = 0 := Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hpdeg (by exact_mod_cast hm))
      simp [hr0, hp0]
    obtain ⟨-, hrp0⟩ := division_injective w hw.monic hw_le (by
      intro l hl
      rw [hw.isPoly l hl, norm_zero]
      norm_num) hrpdeg hzero
    have hai : a i = r.coeff i := by
      have hcoeff := congrArg (fun P : Polynomial A ↦ P.coeff (i : ℕ)) hrp0
      have hpcoeff : p.coeff (i : ℕ) = a i := polynomialOfFin_coeff a i.2
      have hsub : r.coeff (i : ℕ) - a i = 0 := by
        simpa [Polynomial.coeff_sub, hpcoeff] using hcoeff
      exact (sub_eq_zero.mp hsub).symm
    rw [hai, ← hhnorm]
    refine (mul_le_mul_of_nonneg_left (he_le_one i) (norm_nonneg _)).trans ?_
    simpa using hrcoeff i

theorem smul_top_isStrictlyClosed_self_fin
    {k : Type*} [NormedField k] [IsUltrametricDist k] [CompleteSpace k] :
    ∀ (n : ℕ) (ω : TateAlgebra (Fin n) k), ω ≠ 0 →
      (ω • (⊤ : Ideal (TateAlgebra (Fin n) k))).IsStrictlyClosed
  | 0, ω, hω => by
      simp [Submodule.smul_pointwise_eq_self_of_isUnit (ω.fin_zero_isUnit hω),
        Submodule.top_isStrictlyClosed]
  | n + 1, ω, hω => by
      let eSucc := (tateAlgebraFinSuccEquiv k n).toRingEquiv
      let ω₀ : TateAlgebra (Option (Fin n)) k := eSucc ω
      have hω₀ : ω₀ ≠ 0 := fun h ↦ hω (by simpa [ω₀, eSucc] using congrArg eSucc.symm h)
      have hω₀_strict :
          (ω₀ • (⊤ : Submodule (TateAlgebra (Option (Fin n)) k)
            (TateAlgebra (Option (Fin n)) k))).IsStrictlyClosed := by
        rcases TateAlgebra.exists_coeff_norm_eq_norm ω₀ with ⟨e, he⟩
        let c : k := MvPowerSeries.coeff e ω₀.1
        have hc_norm : ‖c‖ = ‖ω₀‖ := he
        have hc_ne : c ≠ 0 := fun hc ↦ hω₀ (by rw [← norm_eq_zero, ← hc_norm, hc, norm_zero])
        let f : TateAlgebra (Option (Fin n)) k := c⁻¹ • ω₀
        have hf_ne : f ≠ 0 := fun hf ↦ hω₀ (by
          simpa [f, smul_smul, hc_ne] using congrArg (fun z ↦ c • z) hf)
        have hf_norm_le_one : ‖f‖ ≤ 1 := by
          refine TateAlgebra.norm_le_of_forall_coeff_le f ?_
          intro d
          rw [show (MvPowerSeries.coeff d) f.1 = c⁻¹ * (MvPowerSeries.coeff d) ω₀.1 from
            MvPowerSeries.coeff_smul ω₀.1 d c⁻¹, norm_mul]
          refine (mul_le_mul_of_nonneg_left (TateAlgebra.coeff_norm_le ω₀ d)
            (norm_nonneg _)).trans ?_
          rw [← hc_norm, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc_ne)]
        have hf_norm_ge_one : 1 ≤ ‖f‖ := by
          have hcoeff_le := TateAlgebra.coeff_norm_le f e
          have hcoeff : (MvPowerSeries.coeff e) f.1 = c⁻¹ * c := by
            rw [show (MvPowerSeries.coeff e) f.1 = c⁻¹ * (MvPowerSeries.coeff e) ω₀.1 from
              MvPowerSeries.coeff_smul ω₀.1 e c⁻¹]
          have hcoeff_norm : ‖(MvPowerSeries.coeff e) f.1‖ = 1 := by
            rw [hcoeff, norm_mul, norm_inv]
            exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc_ne)
          rwa [hcoeff_norm] at hcoeff_le
        obtain ⟨d, hd, m, hdist⟩ := TateAlgebra.exists_optionTriangularForward_distinguished f hf_ne
          (le_antisymm hf_norm_le_one hf_norm_ge_one)
        let tri := optionTriangularForwardRingEquiv k d hd
        have htri_strict :
            (tri f • (⊤ : Submodule (TateAlgebra (Option (Fin n)) k)
              (TateAlgebra (Option (Fin n)) k))).IsStrictlyClosed := by
          let opt := optionToTateAlgEquiv k (Fin n)
          have hopt_strict :
              (opt (tri f) • (⊤ : Submodule (TateAlgebra Unit (TateAlgebra (Fin n) k))
                (TateAlgebra Unit (TateAlgebra (Fin n) k)))).IsStrictlyClosed := by
            change ((optionToTate (optionTriangularForward k d hd f)) •
              (⊤ : Submodule _ _)).IsStrictlyClosed
            rcases TateAlgebra.weierstrass_preparation_exists hdist with ⟨we, hw, hu, hdecomp⟩
            rw [hdecomp, Submodule.mul_smul_pointwise_eq_of_isUnit hu]
            exact weierstrass_smul_top_isStrictlyClosed hw
          exact smul_top_isStrictlyClosed_of_ringEquiv opt.toRingEquiv
            (fun x ↦ optionToTateAlgEquiv_norm x) (tri f) hopt_strict
        have hf_strict :
            (f • (⊤ : Submodule (TateAlgebra (Option (Fin n)) k)
              (TateAlgebra (Option (Fin n)) k))).IsStrictlyClosed :=
          smul_top_isStrictlyClosed_of_ringEquiv tri
            (fun x ↦ optionTriangularForwardRingEquiv_norm d hd x) f htri_strict
        have hideal :
            ω₀ • (⊤ : Submodule (TateAlgebra (Option (Fin n)) k)
              (TateAlgebra (Option (Fin n)) k)) =
            f • (⊤ : Submodule (TateAlgebra (Option (Fin n)) k)
              (TateAlgebra (Option (Fin n)) k)) := by
          rw [show ω₀ = c • f by simp [f, smul_smul, mul_inv_cancel₀ hc_ne], Algebra.smul_def]
          exact Submodule.mul_smul_pointwise_eq_of_isUnit
            ((isUnit_iff_ne_zero.mpr hc_ne).map (algebraMap k (TateAlgebra (Option (Fin n)) k))) f
        rwa [hideal]
      exact smul_top_isStrictlyClosed_of_ringEquiv eSucc
        (fun x ↦ tateAlgebraFinSuccEquiv_norm n x) ω hω₀_strict

theorem smul_top_isStrictlyClosed_self (σ : Type*) [Finite σ]
    (k : Type*) [NormedField k] [IsUltrametricDist k] [CompleteSpace k]
    (ω : TateAlgebra σ k) (hω : ω ≠ 0) :
    (ω • (⊤ : Ideal (TateAlgebra σ k))).IsStrictlyClosed := by
  have : Fintype σ := Fintype.ofFinite σ
  let eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let e := (renameEquiv k eσ).toRingEquiv
  exact smul_top_isStrictlyClosed_of_ringEquiv e (fun x ↦ rename_norm_eq eσ x) ω <|
    smul_top_isStrictlyClosed_self_fin (Fintype.card σ) (e ω) <|
      fun h ↦ hω (by simpa using congrArg e.symm h)

theorem module_smul_top_isStrictlyClosed_of_ring
    {A : Type*} [NormedCommRing A] {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M]
    [Module A M] [IsBoundedSMul A M] [Module.IsCartesian A M]
    (ω : A) (hA : (ω • (⊤ : Submodule A A)).IsStrictlyClosed) :
    (ω • (⊤ : Submodule A M)).IsStrictlyClosed := by
  classical
  rcases Module.IsCartesian.exists_non_zero_cartesianGenerator A M with ⟨ι, hι, e, hne, he⟩
  let B : Module.Basis ι A M := he.nonzeroBasis hne
  intro x
  rcases Quotient.mk_surjective x with ⟨m, rfl⟩
  let a : ι → A := B.repr m
  have hm_sum : m = ∑ i : ι, a i • B i := by simp [a]
  choose r hr using fun i : ι ↦ hA ((ω • (⊤ : Submodule A A)).mkQ (a i))
  let m' : M := ∑ i : ι, r i • B i
  have hm'_quot : (ω • (⊤ : Submodule A M)).mkQ m' = (ω • (⊤ : Submodule A M)).mkQ m := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hdiff : m' - m = ∑ i : ι, (r i - a i) • B i := by
      simp [m', hm_sum, Finset.sum_sub_distrib, sub_smul]
    rw [hdiff]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hcoord_mem : r i - a i ∈ (ω • (⊤ : Submodule A A)) := by
      have hq := (hr i).1
      change Submodule.Quotient.mk (r i) = Submodule.Quotient.mk (a i) at hq
      rw [Submodule.Quotient.eq] at hq
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hq
    rw [Submodule.mem_smul_pointwise_iff_exists] at hcoord_mem
    rcases hcoord_mem with ⟨c, -, hc⟩
    rw [← hc, Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨c • B i, Submodule.mem_top, ?_⟩
    simpa [Algebra.smul_def] using (smul_smul ω c (B i))
  refine ⟨m', hm'_quot, ?_⟩
  change ‖m'‖ = ‖(ω • (⊤ : Submodule A M)).mkQ m‖
  rw [← hm'_quot]
  refine le_antisymm ?_ (Submodule.Quotient.norm_mk_le (ω • (⊤ : Submodule A M)) m')
  refine QuotientAddGroup.le_norm_iff.2 ?_
  intro y hy
  let b : ι → A := B.repr y
  have hy_sum : y = ∑ i : ι, b i • B i := by simp [b]
  have hquot : m' - y ∈ ω • (⊤ : Submodule A M) := by rwa [← Submodule.Quotient.eq, eq_comm]
  have hcoord_quot (i : ι) :
      (ω • (⊤ : Submodule A A)).mkQ (r i) = (ω • (⊤ : Submodule A A)).mkQ (b i) := by
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : r i - b i ∈ ω • (⊤ : Submodule A A) := by
      have hrepr_mem : B.repr (m' - y) i ∈ ω • (⊤ : Submodule A A) := by
        rw [Submodule.mem_smul_pointwise_iff_exists] at hquot
        rcases hquot with ⟨z, -, hz⟩
        rw [← hz]
        exact ⟨B.repr z i, Submodule.mem_top, by simp [map_smul]⟩
      have hrepr_eq : B.repr (m' - y) i = r i - b i := by
        have hm'_repr : B.repr m' i = r i := by
          change B.equivFun (∑ j : ι, r j • B j) i = r i
          rw [← Module.Basis.equivFun_symm_apply B r]
          exact congrFun (LinearEquiv.apply_symm_apply B.equivFun r) i
        have hy_repr : B.repr y i = b i := by
          simp [b]
        simp [map_sub, hm'_repr, hy_repr]
      rw [← hrepr_eq]
      exact hrepr_mem
    exact hmem
  have hr_min (i : ι) : ‖r i‖ ≤ ‖b i‖ := by
    grw [(hr i).2, ← (hr i).1, hcoord_quot i, Submodule.mkQ_apply, Submodule.Quotient.norm_mk_le]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg y) ?_
  refine fun i _ ↦ ?_
  have hcart : ‖b i‖ * ‖B i‖ ≤ ‖y‖ := by
    have hy_sum_e : y = ∑ i : ι, b i • e i := by
      simpa [B, Module.IsCartesianGenerator.nonzeroBasis] using hy_sum
    simpa [B, Module.IsCartesianGenerator.nonzeroBasis] using he.norm_le y b hy_sum_e i
  exact (norm_smul_le (r i) (B i)).trans
    ((mul_le_mul_of_nonneg_right (hr_min i) (norm_nonneg _)).trans hcart)

/-- If `F` is cartesian over `A{T}` and `w` is Weierstrass, then `F / wF`
is cartesian over `A`. -/
lemma weierstrass_module_quotient_isCartesian {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [Module (TateAlgebra Unit A) F] [Module A F]
    [IsScalarTower A (TateAlgebra Unit A) F] [IsBoundedSMul (TateAlgebra Unit A) F]
    [IsCartesian (TateAlgebra Unit A) F]
    {w : TateAlgebra Unit A} {n : ℕ} (hw : IsWeierstrassPolynomial w n) :
    IsCartesian A (F ⧸ (w • (⊤ : Submodule (TateAlgebra Unit A) F))) := by
  have hIstrict := weierstrass_smul_top_isStrictlyClosed hw
  have : IsCartesian A (TateAlgebra Unit A ⧸ w • ⊤) := weierstrass_quotient_isCartesian hw
  exact Module.quotient_smul_top_isCartesian_of_scalar_quotient w hIstrict <|
    module_smul_top_isStrictlyClosed_of_ring w hIstrict

lemma weierstrass_module_quotient_isCartesian_of_isUnit_mul {A : Type*}
    [NormedCommRing A] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [Module (TateAlgebra Unit A) F] [Module A F]
    [IsScalarTower A (TateAlgebra Unit A) F] [IsBoundedSMul (TateAlgebra Unit A) F]
    [IsCartesian (TateAlgebra Unit A) F]
    {u w : TateAlgebra Unit A} {n : ℕ} (hu : IsUnit u) (hw : IsWeierstrassPolynomial w n) :
    IsCartesian A (F ⧸ ((u * w) • (⊤ : Submodule (TateAlgebra Unit A) F))) := by
  rw [Submodule.mul_smul_pointwise_eq_of_isUnit hu]
  exact weierstrass_module_quotient_isCartesian hw

universe u v

variable (σ : Type*) [Finite σ] (k : Type u) [NormedField k] [IsUltrametricDist k] [CompleteSpace k]
  {F : Type v} [NormedAddCommGroup F] [IsUltrametricDist F] [Module (TateAlgebra σ k) F]
  [IsBoundedSMul (TateAlgebra σ k) F] [IsCartesian (TateAlgebra σ k) F]

/-- Let `𝒯` be a Tate algebra, `F` be a cartesian `𝒯`-module, `ω ∈ 𝒯` be a non-zero element.
  Then `ω • F` is a strictly closed submodule of `F`. -/
theorem smul_top_isStrictlyClosed (ω : TateAlgebra σ k) (hω : ω ≠ 0) :
    (ω • (⊤ : Submodule (TateAlgebra σ k) F)).IsStrictlyClosed :=
  module_smul_top_isStrictlyClosed_of_ring ω (smul_top_isStrictlyClosed_self σ k ω hω)

/-- Let `𝒯` be a Tate algebra, `F` be a cartesian `𝒯`-module. Then the image of `F` in
  `LocalizedModule 𝒯⁰ F` is strictly closed . -/
theorem isStrictlyClosed_in_fractionScalarExtension :
    (LinearMap.range (mkLinearMap (TateAlgebra σ k)⁰ F)).IsStrictlyClosed := by
  let A := TateAlgebra σ k
  let V := LocalizedModule A⁰ F
  let L : F →ₗ[A] V := mkLinearMap A⁰ F
  intro x
  rcases Quotient.mk_surjective x with ⟨y, rfl⟩
  induction y using LocalizedModule.induction_on with
  | h m s =>
      let ω : A := s
      let Nω : Submodule A F := ω • (⊤ : Submodule A F)
      have hω_ne : ω ≠ 0 := nonZeroDivisors.coe_ne_zero s
      have hstrict : Nω.IsStrictlyClosed := by
        simpa [A, Nω, ω] using smul_top_isStrictlyClosed σ k ω hω_ne
      rcases hstrict (Nω.mkQ m) with ⟨r, hrq, hrnorm⟩
      let z : V := LocalizedModule.mk r s
      have hmk_sub (a b : F) :
          (LocalizedModule.mk (a - b) s : V) = LocalizedModule.mk a s - LocalizedModule.mk b s := by
        symm
        rw [sub_eq_add_neg, ← LocalizedModule.mk_neg, LocalizedModule.mk_add_mk, smul_neg]
        simpa [sub_eq_add_neg] using LocalizedModule.mk_cancel_common_left s s (a - b)
      have hr_mem : r - m ∈ Nω := by rwa [← Submodule.Quotient.eq]
      rw [Submodule.mem_smul_pointwise_iff_exists] at hr_mem
      rcases hr_mem with ⟨u, -, hu⟩
      have hzq :
          (LinearMap.range L).mkQ z = (LinearMap.range L).mkQ (LocalizedModule.mk m s : V) := by
        change Submodule.Quotient.mk z = Submodule.Quotient.mk (LocalizedModule.mk m s)
        rw [Submodule.Quotient.eq, LinearMap.mem_range]
        refine ⟨u, ?_⟩
        rw [LocalizedModule.mkLinearMap_apply, ← LocalizedModule.mk_cancel s u]
        have hsu : s • u = r - m := hu
        rw [hsu, hmk_sub r m]
      refine ⟨z, hzq, ?_⟩
      have hz_norm : ‖z‖ = ‖(LinearMap.range L).mkQ z‖ := by
        refine le_antisymm ?_ (Submodule.Quotient.norm_mk_le (LinearMap.range L) z)
        refine QuotientAddGroup.le_norm_iff.2 ?_
        intro y hy
        have hy_mem : y - z ∈ LinearMap.range L := by rwa [← Submodule.Quotient.eq]
        rw [LinearMap.mem_range] at hy_mem
        rcases hy_mem with ⟨a, ha⟩
        have hy_repr : y = LocalizedModule.mk (r + (s : A) • a) s := by
          rw [← sub_add_cancel y z, ← ha, add_comm, LocalizedModule.mkLinearMap_apply,
            LocalizedModule.mk_add_mk, one_smul, mul_one]
          rfl
        have hquot_ra : Nω.mkQ (r + (s : A) • a) = Nω.mkQ r := by
          simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
          refine ⟨a, Submodule.mem_top, ?_⟩
          simp [ω, sub_eq_add_neg, add_assoc]
        have hquot_ram : Nω.mkQ (r + (s : A) • a) = Nω.mkQ m := hquot_ra.trans hrq
        have hr_min : ‖r‖ ≤ ‖r + (s : A) • a‖ := by
          rw [hrnorm, ← hquot_ram]
          exact Submodule.Quotient.norm_mk_le Nω (r + (s : A) • a)
        rw [hy_repr, localizedModule_norm_mk_of_isCartesian A r s,
          localizedModule_norm_mk_of_isCartesian A (r + (s : A) • a) s]
        exact div_le_div_of_nonneg_right hr_min (norm_nonneg (s : A))
      rw [hz_norm, hzq]
      rfl

omit [CompleteSpace k] in
theorem submodule_pullback_from_fractionScalarExtension
    (M : Submodule (TateAlgebra σ k) F) :
    Module.IsPseudoCartesian (TateAlgebra σ k) (M.map (mkLinearMap (TateAlgebra σ k)⁰ F)) ∧
      (M.map (mkLinearMap (TateAlgebra σ k)⁰ F)).IsStrictlyClosed →
        Module.IsPseudoCartesian (TateAlgebra σ k) M ∧ M.IsStrictlyClosed := by
  intro h
  let A := TateAlgebra σ k
  let V := LocalizedModule A⁰ F
  let L : F →ₗ[A] V := mkLinearMap A⁰ F
  have hL : Function.Injective L := localizedModule_mkLinearMap_injective_of_isCartesian A
  have hNorm (x : F) : ‖L x‖ = ‖x‖ := localizedModule_mkLinearMap_norm_of_isCartesian A x
  constructor
  · have : Module.IsPseudoCartesian A (M.map L) := h.1
    exact Module.IsPseudoCartesian.of_isometry L hL hNorm M
  · exact Submodule.IsStrictlyClosed.of_isometry L hL hNorm h.2

omit [CompleteSpace k] in
theorem submodule_isPseudoCartesian_and_isStrictlyClosed_of_ringEquiv
    {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    (eR : R ≃+* S) (heR : ∀ x : R, ‖eR x‖ = ‖x‖)
    {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
    [Module S E] [IsBoundedSMul S E] [Module.IsCartesian S E]
    (hR :
      ∀ [Module R E] [IsBoundedSMul R E] [Module.IsCartesian R E],
        ∀ N : Submodule R E, Module.IsPseudoCartesian R N ∧ N.IsStrictlyClosed)
    (N : Submodule S E) :
    Module.IsPseudoCartesian S N ∧ N.IsStrictlyClosed := by
  algebraize [eR.toRingHom]
  let : Module R E := Module.compHom E eR.toRingHom
  have : IsScalarTower R S E := by
    constructor
    intro r s m
    change (eR r * s) • m = eR r • s • m
    rw [mul_smul]
  have : IsBoundedSMul R E := IsBoundedSMul.of_ringEquiv eR heR
  have : Module.IsCartesian R E := Module.IsCartesian.of_ringEquiv eR heR
  let NR : Submodule R E := N.restrictScalars R
  constructor
  · have : Module.IsPseudoCartesian R N := (hR NR).1
    exact Module.IsPseudoCartesian.of_ringEquiv eR heR
  · exact Submodule.IsStrictlyClosed.of_ringEquiv eR (hR NR).2

omit [CompleteSpace k] in
theorem submodule_isPseudoCartesian_and_isStrictlyClosed_of_rename
    {σ τ : Type*} [Finite σ] [Finite τ] (eσ : σ ≃ τ)
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [Module (TateAlgebra τ k) F] [IsBoundedSMul (TateAlgebra τ k) F]
    [IsCartesian (TateAlgebra τ k) F]
    (hσ :
      ∀ [Module (TateAlgebra σ k) F] [IsBoundedSMul (TateAlgebra σ k) F]
        [IsCartesian (TateAlgebra σ k) F] (M : Submodule (TateAlgebra σ k) F),
        Module.IsPseudoCartesian (TateAlgebra σ k) M ∧ M.IsStrictlyClosed)
    (M : Submodule (TateAlgebra τ k) F) :
    Module.IsPseudoCartesian (TateAlgebra τ k) M ∧ M.IsStrictlyClosed := by
  let eR : TateAlgebra σ k ≃+* TateAlgebra τ k := (renameEquiv k eσ).toRingEquiv
  let : Algebra (TateAlgebra σ k) (TateAlgebra τ k) := eR.toRingHom.toAlgebra
  let : Module (TateAlgebra σ k) F := Module.compHom F eR.toRingHom
  have : IsScalarTower (TateAlgebra σ k) (TateAlgebra τ k) F := by
    constructor
    intro r s m
    change (eR r * s) • m = eR r • s • m
    rw [mul_smul]
  have : IsBoundedSMul (TateAlgebra σ k) F := IsBoundedSMul.of_ringEquiv eR (rename_norm_eq eσ)
  have : IsCartesian (TateAlgebra σ k) F := Module.IsCartesian.of_ringEquiv eR (rename_norm_eq eσ)
  let MR : Submodule (TateAlgebra σ k) F := M.restrictScalars (TateAlgebra σ k)
  constructor
  · have : Module.IsPseudoCartesian (TateAlgebra σ k) M := (hσ MR).1
    exact Module.IsPseudoCartesian.of_ringEquiv eR (rename_norm_eq eσ)
  · exact Submodule.IsStrictlyClosed.of_ringEquiv eR (hσ MR).2

theorem localizedModule_isBoundedSMul_fraction_of_isCartesian
    {A : Type*} [NormedCommRing A] [IsDomain A] [NormMulClass A] [NormOneClass A]
    {F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
    [Module A F] [IsBoundedSMul A F] [IsCartesian A F] :
    IsBoundedSMul (Localization A⁰) (LocalizedModule A⁰ F) := by
  refine IsBoundedSMul.of_norm_smul_le ?_
  intro q x
  rcases IsLocalization.mk'_surjective A⁰ q with ⟨⟨a, t⟩, rfl⟩
  let q0 : Localization A⁰ := IsLocalization.mk' (Localization A⁰) a t
  let Sx : Set ℝ := localizedModuleSeminormValues A F x
  let Sy : Set ℝ := localizedModuleSeminormValues A F (q0 • x)
  have hqnorm : ‖q0‖ = ‖a‖ / ‖(t : A)‖ := by
    simp only [q0, ← Localization.mk_eq_mk', norm_localization_mk A a t]
  have hscaled_nonempty : (‖q0‖ • Sx).Nonempty := by
    rcases localizedModuleSeminormValues_nonempty A F x with ⟨r, hr⟩
    exact ⟨‖q0‖ • r, ⟨r, hr, rfl⟩⟩
  have hsub : ‖q0‖ • Sx ⊆ Sy := by
    rintro y ⟨r, ⟨m, s, hmk, rfl⟩, rfl⟩
    refine ⟨a • m, t * s, ?_, ?_⟩
    · simp only [q0, ← hmk, ← Localization.mk_eq_mk'_apply a t, LocalizedModule.mk_smul_mk a m t s]
    · have ht_ne : (t : A) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).1 t.2
      have hs_ne : (s : A) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).1 s.2
      have ht_norm_ne : ‖(t : A)‖ ≠ 0 := norm_ne_zero_iff.mpr ht_ne
      have hs_norm_ne : ‖(s : A)‖ ≠ 0 := norm_ne_zero_iff.mpr hs_ne
      have ha_norm : ‖a • m‖ = ‖a‖ * ‖m‖ := by
        by_cases ha : a = 0
        · simp [ha]
        · exact norm_smul_of_isCartesian A a ha m
      change ‖q0‖ * (‖m‖ / ‖(s : A)‖) = ‖a • m‖ / ‖((t * s : A⁰) : A)‖
      rw [hqnorm, ha_norm, Submonoid.coe_mul, norm_mul]
      field_simp [ht_norm_ne, hs_norm_ne]
  have hle_sets : sInf Sy ≤ sInf (‖q0‖ • Sx) :=
    csInf_le_csInf (localizedModuleSeminormValues_bddBelow A F (q0 • x)) hscaled_nonempty hsub
  have hscale : sInf (‖q0‖ • Sx) = ‖q0‖ * sInf Sx := by
    have hq0_nonneg : 0 ≤ ‖q0‖ := by simp [hqnorm, div_nonneg (norm_nonneg a) (norm_nonneg _)]
    simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hq0_nonneg Sx
  change sInf Sy ≤ ‖q0‖ * sInf Sx
  simp [← hscale, hle_sets]

open IsPseudoCartesian in
set_option maxHeartbeats 250000 in
theorem submodule_isPseudoCartesian_and_isStrictlyClosed_option
    {k : Type u} [NormedField k] [IsUltrametricDist k] [CompleteSpace k] (n : ℕ)
    (ih :
      ∀ {E : Type (max u v)} [NormedAddCommGroup E] [IsUltrametricDist E]
        [Module (TateAlgebra (Fin n) k) E] [IsBoundedSMul (TateAlgebra (Fin n) k) E]
        [IsCartesian (TateAlgebra (Fin n) k) E],
        ∀ M : Submodule (TateAlgebra (Fin n) k) E,
          IsPseudoCartesian (TateAlgebra (Fin n) k) M ∧ M.IsStrictlyClosed)
    {E : Type (max u v)} [NormedAddCommGroup E] [IsUltrametricDist E]
    [Module (TateAlgebra (Option (Fin n)) k) E]
    [IsBoundedSMul (TateAlgebra (Option (Fin n)) k) E]
    [IsCartesian (TateAlgebra (Option (Fin n)) k) E]
    (M : Submodule (TateAlgebra (Option (Fin n)) k) E) :
    IsPseudoCartesian (TateAlgebra (Option (Fin n)) k) M ∧ M.IsStrictlyClosed := by
  let R := TateAlgebra (Option (Fin n)) k
  let B := TateAlgebra (Fin n) k
  let V := LocalizedModule R⁰ E
  let L : E →ₗ[R] V := mkLinearMap R⁰ E
  refine submodule_pullback_from_fractionScalarExtension (Option (Fin n)) k M ?_
  obtain ⟨ω, hω, N, _, hωN, hMN⟩ := Submodule.exists_cartesian_submodule_envelope R M
  have : IsBoundedSMul R N := IsBoundedSMul.of_norm_smul_le fun r x ↦ norm_smul_le r (x : V)
  let K : Submodule R V := M.map L
  let KInN : Submodule R N := K.submoduleOf N
  let Nω : Submodule R N := ω • (⊤ : Submodule R N)
  have hωKInN : ω • (⊤ : Submodule R N) ≤ KInN := Submodule.smul_top_submoduleOf_le_of_smul_le hωN
  have hωstrict : Nω.IsStrictlyClosed := smul_top_isStrictlyClosed (Option (Fin n)) k ω hω
  obtain ⟨c, hc, d, hd, m, u, w, hu, hw, hprep⟩ :=
    exists_optionTriangularForward_weierstrass_unit_mul ω hω
  let S := TateAlgebra Unit B
  let φ : R ≃+* R := optionTriangularForwardRingEquiv k d hd
  let ψ : R ≃+* S := (optionToTateAlgEquiv k (Fin n)).toRingEquiv
  let eRS : R ≃+* S := φ.trans ψ
  have heRS_norm (x : R) : ‖eRS x‖ = ‖x‖ := by
    change ‖(optionToTateAlgEquiv k (Fin n)) ((optionTriangularForwardRingEquiv k d hd) x)‖ = ‖x‖
    rw [optionToTateAlgEquiv_norm, optionTriangularForwardRingEquiv_norm]
  have heSR_norm (x : S) : ‖eRS.symm x‖ = ‖x‖ := by simpa using (heRS_norm (eRS.symm x)).symm
  algebraize [eRS.symm.toRingHom.comp (algebraMap B S)]
  let : Module B V := Module.compHom V (algebraMap B R)
  have : IsScalarTower B R V := by
    constructor
    intro b r x
    change ((algebraMap B R b) * r) • x = (algebraMap B R b) • r • x
    rw [mul_smul]
  let : Module B N := Module.compHom N (algebraMap B R)
  have : IsScalarTower B R N := by
    constructor
    intro b r x
    ext
    change ((algebraMap B R b) * r) • (x : V) = (algebraMap B R b) • r • (x : V)
    rw [mul_smul]
  have hnormBR (b : B) : ‖(algebraMap B R) b‖ = ‖b‖ := by
    change ‖eRS.symm ((algebraMap B S) b)‖ = ‖b‖
    rw [heSR_norm]
    exact TateAlgebra.norm_algebraMap Unit b
  have : IsCartesian B (N ⧸ Nω) := by
    let : Module S N := Module.compHom N eRS.symm.toRingHom
    have : IsBoundedSMul S N := IsBoundedSMul.of_ringEquiv eRS.symm heSR_norm
    have : IsCartesian S N := Module.IsCartesian.of_ringEquiv eRS.symm heSR_norm
    have : IsScalarTower B S N := by
      constructor
      intro b s x
      ext
      simp only [Algebra.smul_def, mul_smul, SetLike.val_smul_of_tower]
      rfl
    algebraize [eRS.toRingHom]
    have : IsScalarTower R S N := by
      constructor
      intro r s x
      ext
      rw [Algebra.smul_def]
      change (eRS.symm (eRS r * s)) • (x : V) = r • ((eRS.symm s) • (x : V))
      rw [map_mul, RingEquiv.symm_apply_apply, mul_smul]
    have : IsScalarTower B R S := by
      constructor
      intro b r s
      rw [Algebra.smul_def]
      change eRS ((algebraMap B R b) * r) * s = b • (eRS r * s)
      have hbe : eRS ((algebraMap B R) b) = (algebraMap B S) b := eRS.apply_symm_apply _
      rw [map_mul, hbe, Algebra.smul_def, mul_assoc]
    have hW : IsCartesian B (N ⧸ ((u * w) • (⊤ : Submodule S N))) :=
      weierstrass_module_quotient_isCartesian_of_isUnit_mul hu hw
    have hprep' : eRS (c⁻¹ • ω) = u * w := hprep
    have hscalar : (c⁻¹ • ω) • (⊤ : Submodule R N) = ω • (⊤ : Submodule R N) :=
      smul_top_eq_smul_top_of_field_smul (inv_ne_zero hc) ω
    have huweq : eRS.symm (u * w) = c⁻¹ • ω := by rw [← hprep', RingEquiv.symm_apply_apply]
    let Pw : Submodule S N := (u * w) • (⊤ : Submodule S N)
    have hsubB : Nω.restrictScalars B = Pw.restrictScalars B := by
      simp only [Nω, ← hscalar]
      refine Submodule.restrictScalars_smul_top_eq_of_smul_eq (c⁻¹ • ω) (u * w) (fun x ↦ ?_)
      rw [← huweq]
      rfl
    have : IsCartesian B (N ⧸ Nω.restrictScalars B) := by
      rw [hsubB]
      exact Module.IsCartesian.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv B Pw) <|
        Submodule.Quotient.restrictScalarsEquiv_norm Pw
    exact Module.IsCartesian.of_linearEquiv
      (Submodule.Quotient.restrictScalarsEquiv B Nω).symm
        (Submodule.Quotient.restrictScalarsEquiv_symm_norm Nω)
  let Nω : Submodule R N := ω • (⊤ : Submodule R N)
  have := hωstrict.isClosed
  have : IsUltrametricDist (N ⧸ Nω) :=
    Submodule.isUltrametricDistQuotientOfIsStrictlyClosed Nω hωstrict
  have : IsBoundedSMul R (N ⧸ Nω) :=
    Submodule.isBoundedSMulQuotientOfIsStrictlyClosed Nω hωstrict
  have : IsBoundedSMul B (N ⧸ Nω) := by
    refine IsBoundedSMul.of_norm_smul_le ?_
    intro b x
    rcases hωstrict x with ⟨m, hm, hmnorm⟩
    rw [← hmnorm, ← hm]
    change ‖Submodule.Quotient.mk ((algebraMap B R) b • m)‖ ≤ ‖b‖ * ‖m‖
    grw [Submodule.Quotient.norm_mk_le Nω, norm_smul_le, hnormBR b]
  have hKbar : IsPseudoCartesian B ((KInN.map Nω.mkQ).restrictScalars B) ∧
      ((KInN.map Nω.mkQ).restrictScalars B).IsStrictlyClosed :=
    ih ((KInN.map Nω.mkQ).restrictScalars B)
  have hKInN : IsPseudoCartesian R KInN ∧ KInN.IsStrictlyClosed :=
    Submodule.isPseudoCartesian_and_isStrictlyClosed_of_smul_top_quotient
      hnormBR ω hω hωstrict hωKInN hKbar
  have hNstrict : N.IsStrictlyClosed := by
    let Q := Localization R⁰
    have : IsLocalizedModule R⁰ (LinearMap.id : V →ₗ[R] V) := isLocalizedModule_id R⁰ V Q
    let W : Submodule Q V := Submodule.localized' Q R⁰ (LinearMap.id : V →ₗ[R] V) N
    have hW_eq_span : W = Submodule.span Q (N : Set V) := by simp [W, Submodule.localized'_eq_span]
    have hNW : N ≤ W.restrictScalars R := fun x hx ↦ by
      simpa [hW_eq_span] using Submodule.subset_span hx
    have : IsCartesian Q V := localizedModule_isCartesian_of_isCartesian R
    have : IsBoundedSMul Q V :=
      localizedModule_isBoundedSMul_fraction_of_isCartesian
    have hWstrict : (W.restrictScalars R).IsStrictlyClosed :=
      Submodule.IsStrictlyClosed.to_restrictScalars (Submodule.IsStrictlyClosed.of_normedField W)
    refine Submodule.IsStrictlyClosed.trans ?_ hWstrict hNW
    let fN : N →ₗ[R] LocalizedModule R⁰ N := mkLinearMap R⁰ N
    let gN : N →ₗ[R] W := Submodule.toLocalized' Q R⁰ (LinearMap.id : V →ₗ[R] V) N
    let e : LocalizedModule R⁰ N ≃ₗ[R] W := IsLocalizedModule.linearEquiv R⁰ fN gN
    have : IsBoundedSMul Q (LocalizedModule R⁰ N) :=
      localizedModule_isBoundedSMul_fraction_of_isCartesian
    have he_apply (n : N) : e (fN n) = gN n := IsLocalizedModule.linearEquiv_apply R⁰ fN gN n
    have hesymm_apply (n : N) : e.symm (gN n) = fN n := e.injective (by simp [he_apply n])
    have he_mk (n : N) (s : R⁰) :
        e (IsLocalizedModule.mk' fN n s) = IsLocalizedModule.mk' gN n s := by
      have hf : fN n = (s : R) • IsLocalizedModule.mk' fN n s :=
        (IsLocalizedModule.mk'_eq_iff).1 rfl
      have h : gN n = (s : R) • e (IsLocalizedModule.mk' fN n s) := by
        rw [← he_apply n, hf, e.map_smul]
      exact ((IsLocalizedModule.mk'_eq_iff).2 h).symm
    have he_norm (x : LocalizedModule R⁰ N) : ‖e x‖ = ‖x‖ := by
      rcases IsLocalizedModule.mk'_surjective R⁰ fN x with ⟨⟨n, s⟩, hx⟩
      rw [← hx]
      change ‖e (IsLocalizedModule.mk' fN n s)‖ = ‖IsLocalizedModule.mk' fN n s‖
      rw [he_mk n s, IsLocalizedModule.mk'_eq_localization_smul Q fN n s,
        IsLocalizedModule.mk'_eq_localization_smul Q gN n s]
      have : NormSMulClass Q V := NormedDivisionRing.toNormSMulClass
      have : NormSMulClass Q (LocalizedModule R⁰ N) := NormedDivisionRing.toNormSMulClass
      have hleft : ‖(IsLocalization.mk' Q (1 : R) s) • gN n‖ = _ * ‖gN n‖ :=
        norm_smul (IsLocalization.mk' Q (1 : R) s) (gN n : V)
      rw [hleft, norm_smul]
      have hfN_norm : ‖fN n‖ = ‖n‖ := localizedModule_mkLinearMap_norm_of_isCartesian R n
      have hgN_norm : ‖gN n‖ = ‖n‖ := rfl
      simp [hfN_norm, hgN_norm]
    have hesymm_norm (x : W) : ‖e.symm x‖ = ‖x‖ := by simpa using (he_norm (e.symm x)).symm
    have hstd : (LinearMap.range fN : Submodule R (LocalizedModule R⁰ N)).IsStrictlyClosed :=
      isStrictlyClosed_in_fractionScalarExtension (Option (Fin n)) k
    have hmap_eq : (LinearMap.range gN).map e.symm.toLinearMap = LinearMap.range fN := by
      ext y
      constructor
      · rintro ⟨_, ⟨n, rfl⟩, hxy⟩
        exact ⟨n, by simpa [hesymm_apply n] using hxy⟩
      · rintro ⟨n, rfl⟩
        exact ⟨gN n, ⟨n, rfl⟩, hesymm_apply n⟩
    have hgNstrict : (LinearMap.range gN).IsStrictlyClosed :=
      Submodule.IsStrictlyClosed.of_linearEquiv e.symm hesymm_norm (by simp [hmap_eq, hstd])
    have hgN_range : LinearMap.range gN = N.submoduleOf (W.restrictScalars R) := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩
        change ((gN n : W) : V) ∈ N
        have hval : ((gN n : W) : V) = (n : V) := rfl
        simp [hval]
      · intro hx
        let n : N := ⟨(x : V), hx⟩
        refine ⟨n, ?_⟩
        ext
        have hval : ((gN n : W) : V) = (n : V) := rfl
        simp [n, hval]
    simpa [hgN_range] using! hgNstrict
  have : IsPseudoCartesian R KInN := hKInN.1
  exact ⟨IsPseudoCartesian.of_submoduleOf hMN, hKInN.2.trans hNstrict hMN⟩

theorem submodule_isPseudoCartesian_and_isStrictlyClosed_fin
    {k : Type u} [NormedField k] [IsUltrametricDist k] [CompleteSpace k] (n : ℕ)
    {E : Type (max u v)} [NormedAddCommGroup E] [IsUltrametricDist E]
    [Module (TateAlgebra (Fin n) k) E] [IsBoundedSMul (TateAlgebra (Fin n) k) E]
    [IsCartesian (TateAlgebra (Fin n) k) E] (M : Submodule (TateAlgebra (Fin n) k) E) :
    IsPseudoCartesian (TateAlgebra (Fin n) k) M ∧ M.IsStrictlyClosed := by
  induction n generalizing E with
  | zero =>
      let eR : k ≃+* TateAlgebra (Fin 0) k := finZeroAlgEquiv.symm.toRingEquiv
      refine submodule_isPseudoCartesian_and_isStrictlyClosed_of_ringEquiv eR
        (norm_algebraMap' (TateAlgebra (Fin 0) k)) ?_ M
      intro _ _ _ N
      exact ⟨inferInstance, Submodule.IsStrictlyClosed.of_normedField N⟩
  | succ n ih =>
      let eR : TateAlgebra (Option (Fin n)) k ≃+* TateAlgebra (Fin (n + 1)) k :=
        (tateAlgebraFinSuccEquiv k n).symm.toRingEquiv
      have heR (x : TateAlgebra (Option (Fin n)) k) : ‖eR x‖ = ‖x‖ := by
        simpa [eR] using (tateAlgebraFinSuccEquiv_norm n (eR x)).symm
      refine submodule_isPseudoCartesian_and_isStrictlyClosed_of_ringEquiv eR heR ?_ M
      intro _ _ _
      exact submodule_isPseudoCartesian_and_isStrictlyClosed_option n ih

theorem submodule_isPseudoCartesian_and_isStrictlyClosed_fin_ulift
    {k : Type u} [NormedField k] [IsUltrametricDist k] [CompleteSpace k] (n : ℕ)
    {E : Type v} [NormedAddCommGroup E] [IsUltrametricDist E]
    [Module (TateAlgebra (Fin n) k) E] [IsBoundedSMul (TateAlgebra (Fin n) k) E]
    [IsCartesian (TateAlgebra (Fin n) k) E] (M : Submodule (TateAlgebra (Fin n) k) E) :
    IsPseudoCartesian (TateAlgebra (Fin n) k) M ∧ M.IsStrictlyClosed := by
  let R := TateAlgebra (Fin n) k
  let E' := ULift.{u} E
  let e : E ≃ₗ[R] E' := ULift.moduleEquiv.symm
  have : IsUltrametricDist E' := by
    refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ?_
    exact fun ⟨x⟩ ⟨y⟩ ↦ IsUltrametricDist.norm_add_le_max x y
  have : IsBoundedSMul R E' := IsBoundedSMul.of_norm_smul_le fun a ⟨x⟩ ↦ norm_smul_le a x
  have : IsCartesian R E' := Module.IsCartesian.of_linearEquiv e.symm fun _ ↦ rfl
  have hM' := submodule_isPseudoCartesian_and_isStrictlyClosed_fin n (M.map e.toLinearMap)
  constructor
  · have := hM'.1
    exact Module.IsPseudoCartesian.of_linearEquiv (e.submoduleMap M) (fun _ ↦ rfl)
  · exact Submodule.IsStrictlyClosed.of_linearEquiv e (fun _ ↦ rfl) hM'.2

/-- Let `𝒯` be a Tate algebra and `M` be a submodule of a cartesian `𝒯`-module `F`.
  Then `M` is pseudo-cartesian `𝒯`-module and strictly closed in `F`. -/
theorem submodule_isPseudoCartesian_and_isStrictlyClosed (M : Submodule (TateAlgebra σ k) F) :
    IsPseudoCartesian (TateAlgebra σ k) M ∧ M.IsStrictlyClosed := by
  have : Fintype σ := Fintype.ofFinite σ
  refine submodule_isPseudoCartesian_and_isStrictlyClosed_of_rename k (Fintype.equivFin σ).symm ?_ M
  intro _ _ _ N
  exact submodule_isPseudoCartesian_and_isStrictlyClosed_fin_ulift (Fintype.card σ) N

/-- Any ideal of a Tate algebra is strictly closed. -/
theorem ideal_isStrictlyClosed (I : Ideal (TateAlgebra σ k)) : I.IsStrictlyClosed :=
  (submodule_isPseudoCartesian_and_isStrictlyClosed σ k I).2

/-- Any ideal of a Tate algebra is boundedly generated. -/
theorem ideal_isBoundedlyGenerated (I : Ideal (TateAlgebra σ k)) :
    IsBoundedlyGenerated (TateAlgebra σ k) I := by
  have : IsPseudoCartesian (TateAlgebra σ k) I :=
    (submodule_isPseudoCartesian_and_isStrictlyClosed σ k I).1
  exact IsPseudoCartesian.isBoundedlyGenerated_of_value_group_subset k (TateAlgebra σ k) I
    fun x ↦ value_group_subset x.1

end TateAlgebra
