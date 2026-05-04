/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Data.Finset.Functor
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Separation.CompletelyRegular
public import StrictAffinoid.Reduction

public section

open Valued NormedField Module

open scoped BigOperators Topology

abbrev preImageNormSet {A B F : Type*} [SeminormedRing A] [SeminormedRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) (b : B) : Set ℝ :=
  {r : ℝ | ∃ a : A, f a = b ∧ ‖a‖ = r}

theorem bddBelow_preImageNormSet {A B F : Type*} [SeminormedRing A] [SeminormedRing B]
    [FunLike F A B] [RingHomClass F A B] (f : F) (b : B) : BddBelow (preImageNormSet f b) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, -, rfl⟩
  exact norm_nonneg a

section IsBoundedlyGenerated

/-- Let $ M $ be a seminormed $ R $-module, $ e_1, \dots, e_n \in M^\circ $. If for any $ a \in M $,
there exist $ a_i \in M $ such that $ a = \sum\limits_{i = 1}^n a_i • e_i $ and
$ \|a_i\| \le \|a\| $, then we say that $ e_1, \dots, e_n $ boundedly generate $ M $. -/
structure IsBoundedGenerator
    (R : Type*) [SeminormedRing R] {M : Type*} [SeminormedAddCommGroup M] [Module R M]
    {σ : Type*} [Fintype σ] (e : σ → M) : Prop where
  norm_le_one (i : σ) : ‖e i‖ ≤ 1
  boundedly_generate (m : M) : ∃ a : σ → R, m = ∑ i, a i • e i ∧ ∀ i : σ, ‖a i‖ ≤ ‖m‖

class IsBoundedlyGenerated
    (R M : Type*) [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M] : Prop where
  out (R M) : ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (e : σ → M), IsBoundedGenerator R e

variable {R M : Type*} [NormedCommRing R] [NormedAddCommGroup M] [Module R M]

instance (priority := low) IsBoundedlyGenerated.module_finite (R M : Type*) [SeminormedRing R]
    [SeminormedAddCommGroup M] [Module R M] [IsBoundedlyGenerated R M] :
    Module.Finite R M := by
  rcases IsBoundedlyGenerated.out R M with ⟨σ, hσ, _, e, _, he⟩
  refine Module.Finite.of_fg_top ?_
  have htop : Submodule.span R (Set.range e) = ⊤ := by
    apply top_unique
    intro m _
    rcases he m with ⟨a, hrepr, _⟩
    rw [hrepr]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← htop]
  exact Submodule.fg_span (Set.toFinite _)

end IsBoundedlyGenerated

namespace TateAlgebra

variable {σ : Type*} [Finite σ] {k : Type*} [NormedField k] [CompleteSpace k]
    [IsUltrametricDist k] (I : Ideal (TateAlgebra σ k))
    {A : Type*} [NormedCommRing A] [IsUltrametricDist A]

theorem ideal_isBoundedlyGenerated : IsBoundedlyGenerated (TateAlgebra σ k) I :=
  sorry

/-- Any ideal of a Tate algebra is strictly closed. -/
theorem exists_norm_eq_residue_norm (x : TateAlgebra σ k ⧸ I) :
    ∃ t : TateAlgebra σ k, Ideal.Quotient.mk I t = x ∧ ‖t‖ = ‖x‖ :=
  sorry

end TateAlgebra
