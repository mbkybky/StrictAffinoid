/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import StrictAffinoid.AlgebraResults
public import StrictAffinoid.Basic

@[expose] public section

open MvPowerSeries TateAlgebra

namespace TateAlgebra

variable {σ : Type*} [Finite σ] {A : Type*} [NormedCommRing A] [NormOneClass A] [NormMulClass A]
  [IsUltrametricDist A] [CompleteSpace A]

section weierstrass_preparation

/-- A one-variable Tate series is of order `n` if its Gauss norm is attained at
coefficient `n`, and all higher coefficients are strictly smaller. -/
structure IsOfOrder (f : TateAlgebra Unit A) (n : ℕ) : Prop where
  norm_le : ‖f‖ ≤ ‖PowerSeries.coeff n f.1‖
  maximal {l : ℕ} (_ : l > n) : ‖PowerSeries.coeff l f.1‖ < ‖PowerSeries.coeff n f.1‖

/-- A series of order `n` whose dominant coefficient is a unit. -/
structure IsDistinguishedOfOrder (f : TateAlgebra Unit A) (n : ℕ) : Prop extends IsOfOrder f n where
  isUnit : IsUnit (PowerSeries.coeff n f.1)

/-- A Weierstrass polynomial of degree and order `n`, viewed inside `A{T}`. -/
structure IsWeierstrassPolynomial (w : TateAlgebra Unit A) (n : ℕ) : Prop where
  norm_le_one : ‖w‖ ≤ 1
  monic : PowerSeries.coeff n w.1 = 1
  isPoly : ∀ l > n, PowerSeries.coeff l w.1 = 0

omit [IsUltrametricDist A] [CompleteSpace A] in
lemma norm_unit_mul_norm_inv_eq_one (u : Aˣ) : ‖(u : A)‖ * ‖((u⁻¹.1 : A))‖ = 1 := by
  rw [← norm_mul, Units.mul_inv, norm_one]

omit [IsUltrametricDist A] [CompleteSpace A] in
lemma norm_inv_unit_mul_norm_eq_one (u : Aˣ) :
    ‖((u⁻¹.1 : A))‖ * ‖(u : A)‖ = 1 := by
  rw [mul_comm]
  exact norm_unit_mul_norm_inv_eq_one u

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma coeff_smul_unit (a : A) (f : TateAlgebra Unit A) (n : ℕ) :
    PowerSeries.coeff n (((a • f : TateAlgebra Unit A) : MvPowerSeries Unit A))
      = a * PowerSeries.coeff n (f : MvPowerSeries Unit A) := by
  change (MvPowerSeries.coeff (Finsupp.single () n : Unit →₀ ℕ))
      (a • (f : MvPowerSeries Unit A)) =
    a * (MvPowerSeries.coeff (Finsupp.single () n : Unit →₀ ℕ)) (f : MvPowerSeries Unit A)
  exact MvPowerSeries.coeff_smul
    (f : MvPowerSeries Unit A) (Finsupp.single () n : Unit →₀ ℕ) a

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_lt_of_forall_coeff_lt {f : TateAlgebra Unit A} {C : ℝ}
    (hcoeff : ∀ n : ℕ, ‖PowerSeries.coeff n f.1‖ < C) :
    ‖f‖ < C := by
  by_contra h
  have hCf : C ≤ ‖f‖ := le_of_not_gt h
  by_cases hf : f = 0
  · have hCgt : 0 < C := by simpa [hf] using hcoeff 0
    exact (not_lt_of_ge (by simpa [hf] using hCf)) hCgt
  · obtain ⟨n, hn⟩ := f.exists_coeff_norm_eq_norm hf
    have hcoeffn : ‖PowerSeries.coeff (n ()) f.1‖ = ‖f‖ := by
      simpa [PowerSeries.coeff_def rfl] using hn
    exact (not_lt_of_ge (hCf.trans_eq hcoeffn.symm)) (hcoeff (n ()))

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_lt_one_of_forall_coeff_lt_one {f : TateAlgebra Unit A}
    (hcoeff : ∀ n : ℕ, ‖PowerSeries.coeff n f.1‖ < 1) :
    ‖f‖ < 1 := by
  exact norm_lt_of_forall_coeff_lt hcoeff

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_sum_lt_of_forall_lt {α : Type*} (s : Finset α) (f : α → A) {C : ℝ}
    (hC : 0 < C) (hf : ∀ a ∈ s, ‖f a‖ < C) :
    ‖s.sum f‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hC
  | @insert a s ha hs =>
      have hfa : ‖f a‖ < C := hf a (by simp [ha])
      have hfs : ∀ b ∈ s, ‖f b‖ < C := by
        intro b hb
        exact hf b (by simp [hb])
      have hslt : ‖s.sum f‖ < C := hs hfs
      rw [Finset.sum_insert ha]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hfa hslt)

omit [NormOneClass A] [NormMulClass A] in
lemma isUnit_of_norm_sub_one_lt_one (f : TateAlgebra Unit A) (h : ‖f - 1‖ < 1) :
    IsUnit f := by
  let u : TateAlgebra Unit A := 1 - f
  have hu : ‖u‖ < 1 := by
    have hu_eq : u = -(f - 1) := by
      dsimp [u]
      ring
    rw [hu_eq, norm_neg]
    exact h
  have hs : Summable (fun n : ℕ => u ^ n) := summable_geometric_of_norm_lt_one hu
  refine ⟨⟨f, ∑' n : ℕ, u ^ n, ?_, ?_⟩, rfl⟩
  · simpa [u, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hs.one_sub_mul_tsum_pow
  · simpa [u, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hs.tsum_pow_mul_one_sub

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma finite_nat_coeff_set_of_isTate_unit
    (f : TateAlgebra Unit A) {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | ε ≤ ‖PowerSeries.coeff n f.1‖}.Finite := by
  let u : ℕ ↪ Unit →₀ ℕ :=
    ⟨fun n => Finsupp.single () n, fun m n h ↦ by simpa using congrArg (fun e => e ()) h⟩
  let S : Set (Unit →₀ ℕ) := {e | ε ≤ ‖MvPowerSeries.coeff e f.1‖}
  have hEq : {n : ℕ | ε ≤ ‖PowerSeries.coeff n f.1‖} = u ⁻¹' S := by
    ext n
    simp [S, u, PowerSeries.coeff]
  simpa [hEq] using ((isTate_iff f.1).1 f.2 ε hε).preimage u.injective.injOn

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma exists_uniform_tail_bound (g : TateAlgebra Unit A) (m : ℕ)
    (htail : ∀ l > m, ‖PowerSeries.coeff l g.1‖ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ l > m, ‖PowerSeries.coeff l g.1‖ ≤ ε := by
  let hhp : 0 < (1 / 2 : ℝ) := by norm_num
  let t : Finset ℕ :=
    ((finite_nat_coeff_set_of_isTate_unit g hhp).toFinset).filter (fun l => m < l)
  let b : ℝ := if ht : t.Nonempty then t.sup' ht fun l => ‖PowerSeries.coeff l g.1‖ else 0
  let ε : ℝ := max (1 / 2 : ℝ) b
  refine ⟨ε, by positivity, ?_, ?_⟩
  · have hb_lt : b < 1 := by
      by_cases ht : t.Nonempty
      · dsimp [b]
        rw [dif_pos ht]
        refine (Finset.sup'_lt_iff ht).2 ?_
        intro l hl
        have hml : m < l := by
          exact (Finset.mem_filter.mp hl).2
        exact htail l hml
      · simp [b, ht]
    exact max_lt_iff.2 ⟨by norm_num, hb_lt⟩
  · intro l hl
    by_cases ht : l ∈ t
    · have hle : ‖PowerSeries.coeff l g.1‖ ≤ b := by
        by_cases htn : t.Nonempty
        · dsimp [b]
          rw [dif_pos htn]
          exact Finset.le_sup' (fun l => ‖PowerSeries.coeff l g.1‖) ht
        · exfalso
          exact htn ⟨l, ht⟩
      exact le_trans hle (le_max_right _ _)
    · have hsmall : ‖PowerSeries.coeff l g.1‖ < (1 / 2 : ℝ) := by
        by_contra hnot
        exact ht <| Finset.mem_filter.mpr ⟨Set.Finite.mem_toFinset
          (finite_nat_coeff_set_of_isTate_unit g hhp) |>.mpr (le_of_not_gt hnot), hl⟩
      exact hsmall.le.trans (le_max_left _ b)

/-- Embed a polynomial as the corresponding one-variable Tate series. -/
noncomputable def polynomialToTate (p : Polynomial A) : TateAlgebra Unit A := by
  refine ⟨(p : PowerSeries A), ?_⟩
  rw [mem_tateSubalgebra_iff]
  intro ε hε
  let u : ℕ ↪ Unit →₀ ℕ :=
    ⟨fun n => Finsupp.single () n, fun m n h ↦ by simpa using congrArg (fun e => e ()) h⟩
  refine (Set.finite_le_nat p.natDegree).image u |>.subset ?_
  intro e he
  refine ⟨e (), ?_, ?_⟩
  · by_contra hnp
    have he' : ε ≤ ‖PowerSeries.coeff (e ()) (p : PowerSeries A)‖ := by
      simpa [PowerSeries.coeff_def rfl] using he
    have : p.coeff (e ()) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hnp)
    rw [show PowerSeries.coeff (e ()) (p : PowerSeries A) = p.coeff (e ()) by simp, this] at he'
    exact (not_lt_of_ge he') (by simpa using hε)
  · simpa [u] using (Finsupp.unique_single e).symm

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma polynomialToTate_zero : polynomialToTate (0 : Polynomial A) = 0 := by
  apply Subtype.ext
  ext n
  simp [polynomialToTate]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma polynomialToTate_one : polynomialToTate (1 : Polynomial A) = 1 := by
  apply Subtype.ext
  ext n
  simp [polynomialToTate]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma polynomialToTate_C (a : A) :
    polynomialToTate (Polynomial.C a) = algebraMap A (TateAlgebra Unit A) a := by
  apply Subtype.ext
  ext n
  simp [polynomialToTate]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma polynomialToTate_add (p q : Polynomial A) :
    polynomialToTate (p + q) = polynomialToTate p + polynomialToTate q := by
  apply Subtype.ext
  ext n
  simp [polynomialToTate]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma polynomialToTate_mul (p q : Polynomial A) :
    polynomialToTate (p * q) = polynomialToTate p * polynomialToTate q := by
  apply Subtype.ext
  ext n
  simp [polynomialToTate]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma polynomialToTate_sub (p q : Polynomial A) :
    polynomialToTate (p - q) = polynomialToTate p - polynomialToTate q := by
  apply Subtype.ext
  ext n
  simp [polynomialToTate]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma polynomialToTate_injective :
    Function.Injective (polynomialToTate : Polynomial A → TateAlgebra Unit A) := by
  intro p q hpq
  ext i
  have := congrArg (fun f : TateAlgebra Unit A => PowerSeries.coeff i f.1) hpq
  simpa [polynomialToTate] using this

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
/-- The `A`-algebra homomorphism from polynomials to the one-variable Tate algebra. -/
noncomputable def polynomialToTateAlgHom : Polynomial A →ₐ[A] TateAlgebra Unit A where
  toFun := polynomialToTate
  map_zero' := polynomialToTate_zero
  map_one' := polynomialToTate_one
  map_add' := polynomialToTate_add
  map_mul' := polynomialToTate_mul
  commutes' := polynomialToTate_C

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma polynomial_coeff_norm_le (p : Polynomial A) (i : ℕ) : ‖p.coeff i‖ ≤ ‖polynomialToTate p‖ := by
  rw [show p.coeff i = PowerSeries.coeff i (polynomialToTate p).1 by simp [polynomialToTate]]
  exact (polynomialToTate p).coeff_norm_le (Finsupp.single () i : Unit →₀ ℕ)

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_polynomialToTate_le_of_coeff_le (p : Polynomial A) {C : ℝ}
    (hC : 0 ≤ C) (hp : ∀ i : ℕ, ‖p.coeff i‖ ≤ C) :
    ‖polynomialToTate p‖ ≤ C := by
  by_contra hgt
  have hpT_ne : polynomialToTate p ≠ 0 := by
    intro hp0
    have : ‖polynomialToTate p‖ = 0 := by simp [hp0]
    exact hgt (by simpa [this] using hC)
  obtain ⟨e, he⟩ := (polynomialToTate p).exists_coeff_norm_eq_norm hpT_ne
  have hcoeffe : ‖p.coeff (e ())‖ ≤ C := hp (e ())
  have hEq : ‖p.coeff (e ())‖ = ‖polynomialToTate p‖ := by
    simpa [polynomialToTate, PowerSeries.coeff_def rfl] using he
  exact hgt (hEq ▸ hcoeffe)

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma exists_max_poly_coeff (q : Polynomial A) (hq : q ≠ 0) :
    ∃ m : ℕ, ‖q.coeff m‖ = ‖polynomialToTate q‖ ∧
      ∀ i > m, ‖q.coeff i‖ < ‖polynomialToTate q‖ := by
  have hqT : polynomialToTate q ≠ 0 := by
    intro h
    exact hq (polynomialToTate_injective h)
  obtain ⟨e, he⟩ := (polynomialToTate q).exists_coeff_norm_eq_norm hqT
  let s : Finset ℕ := q.support.filter (fun i => ‖q.coeff i‖ = ‖polynomialToTate q‖)
  have hs_ne : s.Nonempty := by
    refine ⟨e (), ?_⟩
    have heq : ‖q.coeff (e ())‖ = ‖polynomialToTate q‖ := by
      simpa [polynomialToTate, PowerSeries.coeff_def rfl] using he
    have hqcoeff_ne : q.coeff (e ()) ≠ 0 := by
      intro h0
      have hnorm : ‖polynomialToTate q‖ = ‖q.coeff (e ())‖ := heq.symm
      rw [h0, norm_zero] at hnorm
      exact hqT <| norm_eq_zero.mp hnorm
    simp [s, Polynomial.mem_support_iff, hqcoeff_ne, heq]
  refine ⟨s.max' hs_ne, ?_, ?_⟩
  · have hm : s.max' hs_ne ∈ s := Finset.max'_mem s hs_ne
    have hm' := (Finset.mem_filter.mp hm).2
    simpa [s] using hm'
  · intro i hi
    have hle : ‖q.coeff i‖ ≤ ‖polynomialToTate q‖ := polynomial_coeff_norm_le q i
    by_cases hEq : ‖q.coeff i‖ = ‖polynomialToTate q‖
    · have hqcoeff_ne : q.coeff i ≠ 0 := by
        intro h0
        have hnorm : ‖polynomialToTate q‖ = ‖q.coeff i‖ := hEq.symm
        rw [h0, norm_zero] at hnorm
        exact hqT <| norm_eq_zero.mp hnorm
      have hi_mem : i ∈ s := by
        simp [s, Polynomial.mem_support_iff, hqcoeff_ne, hEq]
      have : i ≤ s.max' hs_ne := Finset.le_max' s i hi_mem
      exact (not_le_of_gt hi) this |>.elim
    · exact lt_of_le_of_ne hle hEq

omit [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] in
lemma _root_.Polynomial.monic_of_coeff_eq_one_of_high_zero {p : Polynomial A} (n : ℕ)
    (hp₁ : p.coeff n = 1) (hp : ∀ l > n, p.coeff l = 0) : p.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (p.natDegree_le_iff_coeff_eq_zero.mpr hp) hp₁

omit [NormOneClass A] [CompleteSpace A] in
lemma norm_divByMonic_le_and_norm_modByMonic_le
    (p h : Polynomial A) {n : ℕ} (hp₁ : p.coeff n = 1) (hp : ∀ l > n, p.coeff l = 0)
    (hp_le : ∀ l, ‖p.coeff l‖ ≤ 1) :
    ‖polynomialToTate (h.divByMonic p)‖ ≤ ‖polynomialToTate h‖ ∧
      ‖polynomialToTate (h.modByMonic p)‖ ≤ ‖polynomialToTate h‖ := by
  by_cases hA : Subsingleton A
  · simp [Subsingleton.elim p 0, Subsingleton.elim h 0]
  have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  let q := h.divByMonic p
  let r := h.modByMonic p
  have hpMonic : p.Monic := p.monic_of_coeff_eq_one_of_high_zero n hp₁ hp
  have hpne : p ≠ 0 := by
    intro hp0
    simp [hp0] at hp₁
  have hpnat : p.natDegree = n := by
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (p.natDegree_le_iff_coeff_eq_zero.mpr hp) (by simp [hp₁])
  have hpdeg : p.degree = n := by
    rw [Polynomial.degree_eq_natDegree hpne, hpnat]
  have hrdeg : r.degree < n := by
    simpa [r, hpdeg] using Polynomial.degree_modByMonic_lt h hpMonic
  have hEq : h = q * p + r := by
    dsimp [q, r]
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    ring
  have hq_le : ‖polynomialToTate q‖ ≤ ‖polynomialToTate h‖ := by
    by_cases hq0 : q = 0
    · simp [q, hq0]
    · obtain ⟨m, hmEq, hmGt⟩ := exists_max_poly_coeff q hq0
      have hrzero : r.coeff (m + n) = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le hrdeg (by exact_mod_cast Nat.le_add_left n m)
      have hrest_lt :
          ‖Finset.sum ((Finset.antidiagonal (m + n)).erase (m, n))
              (fun x => q.coeff x.1 * p.coeff x.2)‖ <
            ‖polynomialToTate q‖ := by
        have hqpos : 0 < ‖polynomialToTate q‖ := by
          have hqT' : polynomialToTate q ≠ 0 := by
            intro h0
            exact hq0 (polynomialToTate_injective h0)
          have hqnormne : ‖polynomialToTate q‖ ≠ 0 := by
            intro hz
            exact hqT' (norm_eq_zero.mp hz)
          exact lt_of_le_of_ne (norm_nonneg _) hqnormne.symm
        refine norm_sum_lt_of_forall_lt
          ((Finset.antidiagonal (m + n)).erase (m, n))
          (fun x : ℕ × ℕ => q.coeff x.1 * p.coeff x.2) hqpos ?_
        intro x hx
        rcases x with ⟨i, j⟩
        have hxmem : (i, j) ∈ Finset.antidiagonal (m + n) := Finset.mem_of_mem_erase hx
        have hij : i + j = m + n := by simpa using (Finset.mem_antidiagonal.mp hxmem)
        by_cases hjgt : n < j
        · have : p.coeff j = 0 := hp j hjgt
          simp [this, hqpos]
        · have hjle : j ≤ n := Nat.le_of_not_gt hjgt
          by_cases hjeq : j = n
          · have hieq : i = m := by omega
            exfalso
            exact (Finset.mem_erase.mp hx).1 (by simp [hieq, hjeq])
          · have hjlt : j < n := lt_of_le_of_ne hjle hjeq
            have him : m < i := by omega
            have hqi : ‖q.coeff i‖ < ‖polynomialToTate q‖ := hmGt i him
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_left (hp_le j) (norm_nonneg _)).trans_lt (by simpa using hqi)
      have hcoeff_mul :
          ‖(q * p).coeff (m + n)‖ = ‖polynomialToTate q‖ := by
        have hmem : (m, n) ∈ Finset.antidiagonal (m + n) := by simp
        have hsplit :
            (q * p).coeff (m + n) =
              q.coeff m * p.coeff n +
                Finset.sum ((Finset.antidiagonal (m + n)).erase (m, n))
                  (fun x => q.coeff x.1 * p.coeff x.2) := by
          rw [Polynomial.coeff_mul]
          rw [← Finset.sum_erase_add
            (Finset.antidiagonal (m + n))
            (fun x : ℕ × ℕ => q.coeff x.1 * p.coeff x.2)
            hmem]
          ring
        have hrest_lt' :
            ‖Finset.sum ((Finset.antidiagonal (m + n)).erase (m, n))
                (fun x => q.coeff x.1 * p.coeff x.2)‖ <
              ‖q.coeff m * p.coeff n‖ := by
          simpa [hmEq, hp₁] using hrest_lt
        rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hrest_lt')]
        rw [max_eq_left_of_lt hrest_lt']
        simp [hmEq, hp₁]
      have hcoeff_le : ‖(q * p).coeff (m + n)‖ ≤ ‖polynomialToTate h‖ := by
        rw [show (q * p).coeff (m + n) = h.coeff (m + n) by
          rw [hEq, Polynomial.coeff_add, hrzero, add_zero]]
        exact polynomial_coeff_norm_le h (m + n)
      exact hcoeff_mul.symm.trans_le hcoeff_le
  have hr_le : ‖polynomialToTate r‖ ≤ ‖polynomialToTate h‖ := by
    by_cases hqr : ‖polynomialToTate r‖ ≤ ‖polynomialToTate q‖
    · exact le_trans hqr hq_le
    · by_cases hr0 : r = 0
      · simp [r, hr0]
      · obtain ⟨l, hlEq, hlGt⟩ := exists_max_poly_coeff r hr0
        have hrnat : r.natDegree < n := by
          rwa [Polynomial.degree_eq_natDegree hr0, Nat.cast_lt] at hrdeg
        have hln : l < n := by
          have hlne : r.coeff l ≠ 0 := by
            intro h0
            have : ‖polynomialToTate r‖ = 0 := by
              rw [hlEq.symm, h0]
              simp
            exact hr0 (polynomialToTate_injective <| norm_eq_zero.mp this)
          exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero hlne) hrnat
        have hqpr_lt : ‖(q * p).coeff l‖ < ‖polynomialToTate r‖ := by
          have hqpr_le : ‖(q * p).coeff l‖ ≤ ‖polynomialToTate q‖ := by
            rw [Polynomial.coeff_mul]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
            rintro ⟨i, j⟩ hx
            rw [norm_mul]
            exact (mul_le_mul (polynomial_coeff_norm_le q i) (hp_le j) (norm_nonneg _)
                (norm_nonneg _)).trans_eq (by simp)
          exact lt_of_le_of_lt hqpr_le (lt_of_not_ge hqr)
        have hcoeff_le : ‖polynomialToTate r‖ ≤ ‖polynomialToTate h‖ := by
          have hrcoeff : ‖h.coeff l‖ = ‖polynomialToTate r‖ := by
            have hsum : h.coeff l = (q * p).coeff l + r.coeff l := by
              rw [hEq, Polynomial.coeff_add]
            have hlt' : ‖(q * p).coeff l‖ < ‖r.coeff l‖ := by simpa [hlEq] using hqpr_lt
            rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm ((ne_of_gt hlt').symm),
              max_eq_right_of_lt hlt', hlEq]
          rw [← hrcoeff]
          exact polynomial_coeff_norm_le h l
        exact hcoeff_le
  exact ⟨hq_le, hr_le⟩

omit [CompleteSpace A] in
lemma exists_approx_division (g : TateAlgebra Unit A) {n : ℕ} {ε : ℝ} (hε0 : 0 < ε)
    (hg₁ : PowerSeries.coeff n g.1 = 1) (hg_le : ∀ l, ‖PowerSeries.coeff l g.1‖ ≤ 1)
    (hgtail : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < ε) (h : TateAlgebra Unit A) :
    ∃ q r : Polynomial A, r.degree < n ∧ ‖polynomialToTate q‖ ≤ ‖h‖ ∧ ‖polynomialToTate r‖ ≤ ‖h‖ ∧
      ‖h - (polynomialToTate q * g + polynomialToTate r)‖ ≤ ε * ‖h‖ := by
  by_cases hh0 : h = 0
  · refine ⟨0, 0, by simp, by simp [hh0], by simp [hh0], by simp [hh0]⟩
  · let C : ℝ := ε * ‖h‖
    have hC0 : 0 < C := by
      dsimp [C]
      have hhnorm : 0 < ‖h‖ := by
        refine lt_of_le_of_ne (norm_nonneg _) ?_
        intro hnorm
        exact hh0 (norm_eq_zero.mp hnorm.symm)
      exact mul_pos hε0 hhnorm
    let s : Finset ℕ := (finite_nat_coeff_set_of_isTate_unit h (ε := C) hC0).toFinset
    let h0 : Polynomial A := Finset.sum s fun j => Polynomial.monomial j (PowerSeries.coeff j h.1)
    let p0 : Polynomial A := Finset.sum (Finset.range (n + 1)) fun j =>
      Polynomial.monomial j (PowerSeries.coeff j g.1)
    have hp0_coeff : ∀ i, p0.coeff i = if i ≤ n then PowerSeries.coeff i g.1 else 0 := by
      intro i
      by_cases hi : i ≤ n
      · rw [show p0.coeff i = Finset.sum (Finset.range (n + 1)) (fun b =>
          (Polynomial.monomial b (PowerSeries.coeff b g.1)).coeff i) by simp [p0]]
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro b _ hbi
          simp [Polynomial.coeff_monomial, hbi]
        · intro hii
          exact (hii (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).elim
      · rw [show p0.coeff i = Finset.sum (Finset.range (n + 1)) (fun b =>
          (Polynomial.monomial b (PowerSeries.coeff b g.1)).coeff i) by simp [p0]]
        have hzero : Finset.sum (Finset.range (n + 1))
          (fun b => (Polynomial.monomial b (PowerSeries.coeff b g.1)).coeff i) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          by_cases hbi : b = i
          · exfalso
            exact hi (hbi ▸ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)))
          · simp [Polynomial.coeff_monomial, hbi]
        simp [hzero, hi]
    have hp0₁ : p0.coeff n = 1 := by
      simp [hp0_coeff, hg₁]
    have hp0 : ∀ l > n, p0.coeff l = 0 := by
      intro l hl
      simp [hp0_coeff, Nat.not_le_of_gt hl]
    have hp0_le : ∀ l, ‖p0.coeff l‖ ≤ 1 := by
      intro l
      by_cases hl : l ≤ n
      · simp [hp0_coeff, hl, hg_le]
      · simp [hp0_coeff, hl, norm_zero]
    have h0_coeff : ∀ i, h0.coeff i = if C ≤ ‖PowerSeries.coeff i h.1‖ then PowerSeries.coeff i h.1
      else 0 := by
      intro i
      by_cases hi : C ≤ ‖PowerSeries.coeff i h.1‖
      · rw [show h0.coeff i = Finset.sum s (fun b =>
          (Polynomial.monomial b (PowerSeries.coeff b h.1)).coeff i) by simp [h0]]
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro b _ hbi
          simp [Polynomial.coeff_monomial, hbi]
        · intro hii
          exact (hii ((Set.Finite.mem_toFinset
            (finite_nat_coeff_set_of_isTate_unit h hC0)).2 hi)).elim
      · rw [show h0.coeff i = Finset.sum s (fun b =>
          (Polynomial.monomial b (PowerSeries.coeff b h.1)).coeff i) by simp [h0]]
        have hzero : Finset.sum s (fun b =>
          (Polynomial.monomial b (PowerSeries.coeff b h.1)).coeff i) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          by_cases hbi : b = i
          · exfalso
            exact hi <| (Set.Finite.mem_toFinset (finite_nat_coeff_set_of_isTate_unit h hC0)).1
              (hbi ▸ hb)
          · simp [Polynomial.coeff_monomial, hbi]
        simp [hzero, hi]
    have hh0_lt : ‖h - polynomialToTate h0‖ < C := by
      apply norm_lt_of_forall_coeff_lt
      intro i
      by_cases hi : C ≤ ‖PowerSeries.coeff i h.1‖
      · have hcoeff : PowerSeries.coeff i (h - polynomialToTate h0).1 = 0 := by
          simp [h0_coeff, hi, polynomialToTate]
        rw [hcoeff, norm_zero]
        exact hC0
      · have hlt : ‖PowerSeries.coeff i h.1‖ < C := lt_of_not_ge hi
        simpa [h0_coeff, hi, polynomialToTate] using hlt
    have h0_le : ‖polynomialToTate h0‖ ≤ ‖h‖ := by
      refine norm_polynomialToTate_le_of_coeff_le h0 (show 0 ≤ ‖h‖ by exact norm_nonneg _) ?_
      intro i
      by_cases hi : C ≤ ‖PowerSeries.coeff i h.1‖
      · simp [h0_coeff, hi]
        exact TateAlgebra.coeff_norm_le h (Finsupp.single () i)
      · simp [h0_coeff, hi, norm_zero, norm_nonneg]
    have hp0Monic : p0.Monic := p0.monic_of_coeff_eq_one_of_high_zero n hp0₁ hp0
    have h10 : (1 : A) ≠ 0 := by
      intro h10
      have : (1 : ℝ) = 0 := by rw [← norm_one (α := A), h10, norm_zero]
      norm_num at this
    letI : Nontrivial A := ⟨⟨0, 1, by simpa using h10.symm⟩⟩
    have hp0ne : p0 ≠ 0 := by
      intro hp0zero
      simp [hp0zero] at hp0₁
    have hp0deg : p0.degree = n := by
      have hp0nat : p0.natDegree = n :=
        Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
          (p0.natDegree_le_iff_coeff_eq_zero.mpr hp0) (by simp [hp0₁])
      rw [Polynomial.degree_eq_natDegree hp0ne, hp0nat]
    let q : Polynomial A := h0.divByMonic p0
    let r : Polynomial A := h0.modByMonic p0
    have hqr_le := norm_divByMonic_le_and_norm_modByMonic_le p0 h0 hp0₁ hp0 hp0_le
    have hqle : ‖polynomialToTate q‖ ≤ ‖h‖ := le_trans hqr_le.1 h0_le
    have hrle : ‖polynomialToTate r‖ ≤ ‖h‖ := le_trans hqr_le.2 h0_le
    have hrdeg : r.degree < n := by
      simpa [q, r, hp0deg] using Polynomial.degree_modByMonic_lt h0 hp0Monic
    have hgsub_lt : ‖g - polynomialToTate p0‖ < ε := by
      apply norm_lt_of_forall_coeff_lt
      intro i
      by_cases hi : i ≤ n
      · have hcoeff : PowerSeries.coeff i (g - polynomialToTate p0).1 = 0 := by
          simp [hp0_coeff, hi, polynomialToTate]
        rw [hcoeff, norm_zero]
        exact hε0
      · have hgt : i > n := Nat.lt_of_not_ge hi
        have hcoeff : PowerSeries.coeff i (g - polynomialToTate p0).1 = PowerSeries.coeff i g.1 :=
          by
          simp [hp0_coeff, hi, polynomialToTate]
        rw [hcoeff]
        exact hgtail i hgt
    have hmul_err : ‖polynomialToTate q * (polynomialToTate p0 - g)‖ ≤ ε * ‖h‖ := by
      rw [show ‖polynomialToTate q * (polynomialToTate p0 - g)‖ =
        ‖polynomialToTate q‖ * ‖g - polynomialToTate p0‖ by simp [norm_sub_rev]]
      exact (mul_le_mul hqle (le_of_lt hgsub_lt) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm ‖h‖ ε)
    have hdiv_eq : polynomialToTate h0 = polynomialToTate q * polynomialToTate p0 + polynomialToTate
      r := by
      dsimp [q, r]
      have hpoly : h0 = h0.divByMonic p0 * p0 + h0.modByMonic p0 := by
        rw [Polynomial.modByMonic_eq_sub_mul_div]
        ring
      exact Eq.trans (congrArg polynomialToTate hpoly) (by simp)
    refine ⟨q, r, hrdeg, hqle, hrle, ?_⟩
    have hres_eq :
        h - (polynomialToTate q * g + polynomialToTate r) =
          (h - polynomialToTate h0) + polynomialToTate q * (polynomialToTate p0 - g) := by
      rw [hdiv_eq]
      ring
    rw [hres_eq]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans <| max_le (le_of_lt hh0_lt) hmul_err

/-- Keep the coefficients of a one-variable Tate series up to degree `m`. -/
noncomputable def truncPolynomial (g : TateAlgebra Unit A) (m : ℕ) :
    Polynomial A := by
  let f : ℕ → A := fun i => if i ≤ m then PowerSeries.coeff i g.1 else 0
  have hfin : {i | f i ≠ 0}.Finite := by
    refine (Finset.finite_toSet (Finset.range (m + 1))).subset ?_
    intro i hi
    by_cases him : i ≤ m
    · simp [him]
    · simp [f, him] at hi
  exact Polynomial.ofFinsupp (Finsupp.ofSupportFinite f hfin)

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma coeff_truncPolynomial (g : TateAlgebra Unit A) (m i : ℕ) :
    (truncPolynomial g m).coeff i =
      if i ≤ m then PowerSeries.coeff i g.1 else 0 := by
  let f : ℕ → A := fun j =>
    if j ≤ m then PowerSeries.coeff j g.1 else 0
  have hfin : {j | f j ≠ 0}.Finite := by
    refine (Finset.finite_toSet (Finset.range (m + 1))).subset ?_
    intro j hj
    by_cases hjm : j ≤ m
    · simp [hjm]
    · simp [f, hjm] at hj
  dsimp [truncPolynomial]
  rw [Polynomial.coeff_ofFinsupp]
  simpa [f] using congrFun Finsupp.ofSupportFinite_coe i

lemma distinguished_division
    (g : TateAlgebra Unit A) {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hg₁ : PowerSeries.coeff n g.1 = 1) (hg_le : ∀ l, ‖PowerSeries.coeff l g.1‖ ≤ 1)
    (hgtail : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < ε) (h : TateAlgebra Unit A) :
    ∃ q : TateAlgebra Unit A, ∃ r : Polynomial A, r.degree < n ∧ h = q * g + polynomialToTate r ∧
      (∀ l, ‖PowerSeries.coeff l q.1‖ ≤ ‖h‖) ∧ ∀ l, ‖r.coeff l‖ ≤ ‖h‖ := by
  have hεnonneg : 0 ≤ ε := le_of_lt hε0
  let qApprox : TateAlgebra Unit A → Polynomial A := fun h0 =>
    Classical.choose (exists_approx_division g hε0 hg₁ hg_le hgtail h0)
  let rApprox : TateAlgebra Unit A → Polynomial A := fun h0 =>
    Classical.choose (Classical.choose_spec (exists_approx_division g hε0 hg₁ hg_le hgtail h0))
  have hApprox_spec (h0 : TateAlgebra Unit A) :
      (rApprox h0).degree < n ∧ ‖polynomialToTate (qApprox h0)‖ ≤ ‖h0‖ ∧
        ‖polynomialToTate (rApprox h0)‖ ≤ ‖h0‖ ∧
        ‖h0 - (polynomialToTate (qApprox h0) * g + polynomialToTate (rApprox h0))‖ ≤ ε * ‖h0‖ := by
    exact (exists_approx_division g hε0 hg₁ hg_le hgtail h0).choose_spec.choose_spec
  let hseq : ℕ → TateAlgebra Unit A :=
    Nat.rec h (fun _ hk => hk - (polynomialToTate (qApprox hk) * g + polynomialToTate (rApprox hk)))
  let qtail : ℕ → Polynomial A := fun k => qApprox (hseq k)
  let rtail : ℕ → Polynomial A := fun k => rApprox (hseq k)
  have hseq_zero : hseq 0 = h := rfl
  have hseq_succ (k : ℕ) :
      hseq (k + 1) = hseq k - (polynomialToTate (qtail k) * g + polynomialToTate (rtail k)) := rfl
  have hhseq_le : ∀ k, ‖hseq k‖ ≤ ‖h‖ * ε ^ k := by
    intro k
    induction k with
    | zero =>
        simp [hseq_zero]
    | succ k ih =>
        have h1 : ‖hseq (k + 1)‖ ≤ ε * ‖hseq k‖ :=
          by simpa only [hseq_succ, qtail, rtail] using (hApprox_spec (hseq k)).2.2.2
        exact h1.trans <|
          (mul_le_mul_of_nonneg_left ih hεnonneg).trans_eq (by rw [pow_succ]; ring)
  have hqtail_le : ∀ k, ‖polynomialToTate (qtail k)‖ ≤ ‖h‖ * ε ^ k := by
    intro k
    exact le_trans (by simpa [qtail] using (hApprox_spec (hseq k)).2.1) (hhseq_le k)
  have hrtail_le : ∀ k, ‖polynomialToTate (rtail k)‖ ≤ ‖h‖ * ε ^ k := by
    intro k
    exact le_trans (by simpa [rtail] using (hApprox_spec (hseq k)).2.2.1) (hhseq_le k)
  have hrtdeg : ∀ k, (rtail k).degree < n := by
    intro k
    simpa [rtail] using (hApprox_spec (hseq k)).1
  have hgeom0 : Summable (fun k : ℕ => ε ^ k) := by
    exact summable_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hεnonneg] using hε1)
  have hgeom : Summable (fun k : ℕ => ‖h‖ * ε ^ k) := by
    simpa using hgeom0.mul_left ‖h‖
  have hqSumm : Summable (fun k => polynomialToTate (qtail k)) := by
    refine Summable.of_norm_bounded hgeom ?_
    intro k
    exact hqtail_le k
  have hrSumm : Summable (fun k => polynomialToTate (rtail k)) := by
    refine Summable.of_norm_bounded hgeom ?_
    intro k
    exact hrtail_le k
  let q : TateAlgebra Unit A := ∑' k, polynomialToTate (qtail k)
  let Rtail : TateAlgebra Unit A := ∑' k, polynomialToTate (rtail k)
  have hpow_tend : Filter.Tendsto (fun k : ℕ => ε ^ k) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hεnonneg hε1
  have hmaj_tend : Filter.Tendsto (fun k : ℕ => ‖h‖ * ε ^ k) Filter.atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using Filter.Tendsto.const_mul ‖h‖ hpow_tend
  have hnorm_hseq_tend : Filter.Tendsto (fun k : ℕ => ‖hseq k‖) Filter.atTop (nhds 0) := by
    exact squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg _)
      (Filter.Eventually.of_forall fun k => hhseq_le k) hmaj_tend
  have hhseq_tend : Filter.Tendsto hseq Filter.atTop (nhds 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa using hnorm_hseq_tend
  have hpartial : ∀ m : ℕ, h = Finset.sum (Finset.range m)
      (fun k => polynomialToTate (qtail k) * g + polynomialToTate (rtail k)) + hseq m := by
    intro m
    induction m with
    | zero =>
        simp [hseq_zero]
    | succ m ihm =>
        have hstep : hseq m =
            polynomialToTate (qtail m) * g + polynomialToTate (rtail m) + hseq (m + 1) := by
          rw [hseq_succ]
          ring
        rw [Finset.sum_range_succ, ihm, hstep]
        ring
  have hQHas : HasSum (fun k => polynomialToTate (qtail k)) q := hqSumm.hasSum
  have hRHas : HasSum (fun k => polynomialToTate (rtail k)) Rtail := hrSumm.hasSum
  have hQRHas :
      HasSum (fun k => polynomialToTate (qtail k) * g + polynomialToTate (rtail k))
        (q * g + Rtail) := by
    exact (HasSum.mul_right g hQHas).add hRHas
  have hpartial_tend :
      Filter.Tendsto
        (fun m : ℕ =>
          Finset.sum (Finset.range m)
            (fun k => polynomialToTate (qtail k) * g + polynomialToTate (rtail k)))
        Filter.atTop (nhds (q * g + Rtail)) := by
    exact hQRHas.tendsto_sum_nat
  have hleft_tend :
      Filter.Tendsto
        (fun m : ℕ =>
          Finset.sum (Finset.range m)
            (fun k => polynomialToTate (qtail k) * g + polynomialToTate (rtail k)) +
          hseq m)
        Filter.atTop (nhds (q * g + Rtail + 0)) := by
    exact hpartial_tend.add hhseq_tend
  have hdivEq : h = q * g + Rtail := by
    have hconst : Filter.Tendsto (fun _ : ℕ => h) Filter.atTop (nhds h) := tendsto_const_nhds
    have hfun :
        (fun m : ℕ =>
          Finset.sum (Finset.range m)
            (fun k => polynomialToTate (qtail k) * g + polynomialToTate (rtail k)) +
          hseq m) = fun _ : ℕ => h := by
      funext m
      exact (hpartial m).symm
    have hleft' : Filter.Tendsto (fun _ : ℕ => h) Filter.atTop (nhds (q * g + Rtail)) := by
      simpa [hfun, q, Rtail] using hleft_tend
    exact tendsto_nhds_unique hconst hleft'
  have hQcoeff_tend (l : ℕ) :
      Filter.Tendsto
        (fun m : ℕ => Finset.sum (Finset.range m) (fun k => PowerSeries.coeff l (polynomialToTate
          (qtail k)).1))
        Filter.atTop (nhds (PowerSeries.coeff l q.1)) := by
    have hsum_tend :
        Filter.Tendsto
          (fun m : ℕ => Finset.sum (Finset.range m) (fun k => polynomialToTate (qtail k)))
          Filter.atTop (nhds q) := hQHas.tendsto_sum_nat
    have hcomp := ((TateAlgebra.coeff_lipschitz (Finsupp.single () l)).continuous.tendsto _).comp
      hsum_tend
    convert hcomp using 1
    · ext m
      induction m with
      | zero => simp [Function.comp]
      | succ m ih =>
          simp [Function.comp, Finset.sum_range_succ, ih]
          rfl
  have hRcoeff_tend (l : ℕ) :
      Filter.Tendsto
        (fun m : ℕ => Finset.sum (Finset.range m) (fun k => PowerSeries.coeff l (polynomialToTate
          (rtail k)).1))
        Filter.atTop (nhds (PowerSeries.coeff l Rtail.1)) := by
    have hsum_tend :
        Filter.Tendsto
          (fun m : ℕ => Finset.sum (Finset.range m) (fun k => polynomialToTate (rtail k)))
          Filter.atTop (nhds Rtail) := hRHas.tendsto_sum_nat
    have hcomp := ((TateAlgebra.coeff_lipschitz (Finsupp.single () l)).continuous.tendsto _).comp
      hsum_tend
    convert hcomp using 1
    · ext m
      induction m with
      | zero =>
          simp [Function.comp]
      | succ m ih =>
          simp [Function.comp, Finset.sum_range_succ, ih]
          rfl
  have hpow_le_one : ∀ k, ε ^ k ≤ 1 := by
    intro k
    exact pow_le_one₀ hεnonneg (le_of_lt hε1)
  have hQcoeff_le : ∀ l, ‖PowerSeries.coeff l q.1‖ ≤ ‖h‖ := by
    intro l
    have hcoeff_event :
        ∀ᶠ m : ℕ in Filter.atTop,
          ‖Finset.sum (Finset.range m) (fun k => PowerSeries.coeff l (polynomialToTate (qtail
            k)).1)‖ ≤ ‖h‖ := by
      refine Filter.Eventually.of_forall ?_
      intro m
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
      intro k hk
      exact (TateAlgebra.coeff_norm_le (polynomialToTate (qtail k)) (Finsupp.single () l)).trans <|
        (hqtail_le k).trans <|
          (mul_le_mul_of_nonneg_left (hpow_le_one k) (norm_nonneg _)).trans_eq (by ring)
    have hclosed : IsClosed {a : A | ‖a‖ ≤ ‖h‖} := isClosed_le continuous_norm continuous_const
    have hmem : PowerSeries.coeff l q.1 ∈ {a : A | ‖a‖ ≤ ‖h‖} := by
      exact hclosed.mem_of_tendsto (hQcoeff_tend l) hcoeff_event
    simpa using hmem
  have hRcoeff_le : ∀ l, ‖PowerSeries.coeff l Rtail.1‖ ≤ ‖h‖ := by
    intro l
    have hcoeff_event :
        ∀ᶠ m : ℕ in Filter.atTop,
          ‖Finset.sum (Finset.range m) (fun k => PowerSeries.coeff l (polynomialToTate (rtail
            k)).1)‖ ≤ ‖h‖ := by
      refine Filter.Eventually.of_forall ?_
      intro m
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
      intro k hk
      exact (TateAlgebra.coeff_norm_le (polynomialToTate (rtail k)) (Finsupp.single () l)).trans <|
        (hrtail_le k).trans <|
          (mul_le_mul_of_nonneg_left (hpow_le_one k) (norm_nonneg _)).trans_eq (by ring)
    have hclosed : IsClosed {a : A | ‖a‖ ≤ ‖h‖} := isClosed_le continuous_norm continuous_const
    have hmem : PowerSeries.coeff l Rtail.1 ∈ {a : A | ‖a‖ ≤ ‖h‖} := by
      exact hclosed.mem_of_tendsto (hRcoeff_tend l) hcoeff_event
    simpa using hmem
  have hRtail_coeff_zero : ∀ l, n ≤ l → PowerSeries.coeff l Rtail.1 = 0 := by
    intro l hl
    have hpartial_zero :
        ∀ m : ℕ,
          Finset.sum (Finset.range m) (fun k => PowerSeries.coeff l (polynomialToTate (rtail k)).1)
            = 0 := by
      intro m
      apply Finset.sum_eq_zero
      intro k hk
      have hkzero : (rtail k).coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le (hrtdeg k) (by exact_mod_cast hl))
      simp [polynomialToTate, hkzero]
    have hzero_tend :
        Filter.Tendsto
          (fun m : ℕ => Finset.sum (Finset.range m) (fun k => PowerSeries.coeff l (polynomialToTate
            (rtail k)).1))
          Filter.atTop (nhds (0 : A)) := by
      rw [show (fun m : ℕ => Finset.sum (Finset.range m)
          (fun k => PowerSeries.coeff l (polynomialToTate (rtail k)).1))
          = fun _ : ℕ => (0 : A) by
            funext m
            exact hpartial_zero m]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hRcoeff_tend l) hzero_tend
  let r : Polynomial A := truncPolynomial Rtail (n - 1)
  have hr_eq : polynomialToTate r = Rtail := by
    apply Subtype.ext
    ext l
    by_cases hl : l ≤ n - 1
    · simp [r, polynomialToTate, coeff_truncPolynomial, hl]
    · have hln : n ≤ l := by omega
      simp [r, polynomialToTate, coeff_truncPolynomial, hl, hRtail_coeff_zero l hln]
  have hr_deg : r.degree < n := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro l hl
    by_cases hll : l ≤ n - 1
    · simp [r, coeff_truncPolynomial, hll, hRtail_coeff_zero l hl]
    · simp [r, coeff_truncPolynomial, hll]
  have hr_coeff_le : ∀ l, ‖r.coeff l‖ ≤ ‖h‖ := by
    intro l
    have hEq := congrArg (fun z : TateAlgebra Unit A => PowerSeries.coeff l z.1) hr_eq
    have hEq' : r.coeff l = PowerSeries.coeff l Rtail.1 := by
      simpa [polynomialToTate] using hEq
    rw [hEq']
    exact hRcoeff_le l
  refine ⟨q, r, hr_deg, ?_, hQcoeff_le, hr_coeff_le⟩
  rw [hdivEq, hr_eq]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_sub_truncPolynomial_lt (g : TateAlgebra Unit A) (m : ℕ) {ε : ℝ}
    (hε : 0 < ε) (htail : ∀ l > m, ‖PowerSeries.coeff l g.1‖ < ε) :
    ‖g - polynomialToTate (truncPolynomial g m)‖ < ε := by
  refine norm_lt_of_forall_coeff_lt ?_
  intro i
  rw [show PowerSeries.coeff i (g - polynomialToTate (truncPolynomial g m)).1
      = PowerSeries.coeff i g.1 - (truncPolynomial g m).coeff i by
        simp [polynomialToTate]]
  rw [coeff_truncPolynomial g m i]
  by_cases hi : i ≤ m
  · rw [if_pos hi]
    simp [hε]
  · rw [if_neg hi]
    simpa using htail i (Nat.lt_of_not_ge hi)

/-- Keep exactly the coefficients whose norm is at least the positive threshold `C`. -/
noncomputable def largeCoeffTrunc (h : TateAlgebra Unit A) (C : ℝ) (hC : 0 < C) :
    Polynomial A := by
  let f : ℕ → A := fun i =>
    if C ≤ ‖PowerSeries.coeff i h.1‖ then PowerSeries.coeff i h.1 else 0
  have hfin : {i | f i ≠ 0}.Finite := by
    refine (finite_nat_coeff_set_of_isTate_unit h (ε := C) hC).subset ?_
    intro i hi
    dsimp [f] at hi
    by_cases hCi : C ≤ ‖PowerSeries.coeff i h.1‖
    · exact hCi
    · simp [hCi] at hi
  exact Polynomial.ofFinsupp (Finsupp.ofSupportFinite f hfin)

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma coeff_largeCoeffTrunc (h : TateAlgebra Unit A) (C : ℝ) (hC : 0 < C) (i : ℕ) :
    (largeCoeffTrunc h C hC).coeff i =
      if C ≤ ‖PowerSeries.coeff i h.1‖ then PowerSeries.coeff i h.1 else 0 := by
  let f : ℕ → A := fun j =>
    if C ≤ ‖PowerSeries.coeff j h.1‖ then PowerSeries.coeff j h.1 else 0
  have hfin : {j | f j ≠ 0}.Finite := by
    refine (finite_nat_coeff_set_of_isTate_unit h (ε := C) hC).subset ?_
    intro j hj
    by_cases hCj : C ≤ ‖PowerSeries.coeff j h.1‖
    · exact hCj
    · simp [f, hCj] at hj
  dsimp [largeCoeffTrunc]
  rw [Polynomial.coeff_ofFinsupp]
  simpa [f] using congrFun Finsupp.ofSupportFinite_coe i

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_largeCoeffTrunc_le (h : TateAlgebra Unit A) (C : ℝ) (hC : 0 < C) :
    ‖polynomialToTate (largeCoeffTrunc h C hC)‖ ≤ ‖h‖ := by
  by_contra hgt
  let p : TateAlgebra Unit A := polynomialToTate (largeCoeffTrunc h C hC)
  have hpne : p ≠ 0 := by
    intro hp0
    exact hgt (by simp [p, hp0])
  obtain ⟨i, hi⟩ := TateAlgebra.exists_coeff_norm_eq_norm p hpne
  have hcoeffi' : ‖PowerSeries.coeff (i ()) p.1‖ ≤ ‖h‖ := by
    rw [show PowerSeries.coeff (i ()) p.1 = (largeCoeffTrunc h C hC).coeff (i ()) by
      simp [p, polynomialToTate]]
    rw [coeff_largeCoeffTrunc h C hC (i ())]
    split_ifs with hCi
    · simpa [PowerSeries.coeff_def rfl] using TateAlgebra.coeff_norm_le h i
    · simp
  have hp_le : ‖p‖ ≤ ‖h‖ := by
    simpa [PowerSeries.coeff_def rfl, hi] using hcoeffi'
  exact hgt hp_le

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_sub_largeCoeffTrunc_lt (h : TateAlgebra Unit A) (C : ℝ) (hC : 0 < C) :
    ‖h - polynomialToTate (largeCoeffTrunc h C hC)‖ < C := by
  refine norm_lt_of_forall_coeff_lt ?_
  intro i
  rw [show PowerSeries.coeff i (h - polynomialToTate (largeCoeffTrunc h C hC)).1
      = PowerSeries.coeff i h.1 - (largeCoeffTrunc h C hC).coeff i by
        simp [polynomialToTate]]
  rw [coeff_largeCoeffTrunc h C hC i]
  split_ifs with hi
  · simp [hC]
  · simpa using (lt_of_not_ge hi : ‖PowerSeries.coeff i h.1‖ < C)

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma exists_max_tate_coeff (q : TateAlgebra Unit A) (hq : q ≠ 0) :
    ∃ m : ℕ, ‖PowerSeries.coeff m q.1‖ = ‖q‖ ∧
      ∀ i > m, ‖PowerSeries.coeff i q.1‖ < ‖q‖ := by
  have hqnormpos : 0 < ‖q‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) ?_
    intro h0
    exact hq (norm_eq_zero.mp h0.symm)
  let s : Finset ℕ := (finite_nat_coeff_set_of_isTate_unit q (ε := ‖q‖) hqnormpos).toFinset
  obtain ⟨e, he⟩ := TateAlgebra.exists_coeff_norm_eq_norm q hq
  have hs_ne : s.Nonempty := by
    refine ⟨e (), ?_⟩
    apply (Set.Finite.mem_toFinset (finite_nat_coeff_set_of_isTate_unit q (ε := ‖q‖)
      hqnormpos)).2
    simpa [PowerSeries.coeff_def rfl] using le_of_eq he.symm
  refine ⟨s.max' hs_ne, ?_, ?_⟩
  · have hm : s.max' hs_ne ∈ s := Finset.max'_mem s hs_ne
    exact le_antisymm (TateAlgebra.coeff_norm_le q (Finsupp.single () (s.max' hs_ne)))
      ((Set.Finite.mem_toFinset (finite_nat_coeff_set_of_isTate_unit q (ε := ‖q‖)
        hqnormpos)).1 hm)
  · intro i hi
    have hle : ‖PowerSeries.coeff i q.1‖ ≤ ‖q‖ := TateAlgebra.coeff_norm_le q (Finsupp.single () i)
    by_cases hEq : ‖PowerSeries.coeff i q.1‖ = ‖q‖
    · have hi_mem : i ∈ s := by
        apply (Set.Finite.mem_toFinset (finite_nat_coeff_set_of_isTate_unit q (ε := ‖q‖)
          hqnormpos)).2
        exact le_of_eq hEq.symm
      have : i ≤ s.max' hs_ne := Finset.le_max' s i hi_mem
      exact (not_le_of_gt hi) this |>.elim
    · exact lt_of_le_of_ne hle hEq

omit [NormOneClass A] [CompleteSpace A] in
lemma division_injective
    (g : TateAlgebra Unit A) {n : ℕ}
    (hg₁ : PowerSeries.coeff n g.1 = 1)
    (hg_le : ∀ l, ‖PowerSeries.coeff l g.1‖ ≤ 1)
    (hgtail : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < 1)
    {q : TateAlgebra Unit A} {r : Polynomial A}
    (hrdeg : r.degree < n)
    (hEq : q * g + polynomialToTate r = 0) :
    q = 0 ∧ r = 0 := by
  by_cases hq0 : q = 0
  · constructor
    · exact hq0
    · apply polynomialToTate_injective
      simpa [hq0] using hEq
  · have hqnormpos : 0 < ‖q‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) ?_
      intro h0
      exact hq0 (norm_eq_zero.mp h0.symm)
    obtain ⟨m, hmEq, hmGt⟩ := exists_max_tate_coeff q hq0
    have hrzero : r.coeff (m + n) = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hrdeg (by exact_mod_cast Nat.le_add_left n m)
    have hrest_lt :
        ‖Finset.sum ((Finset.antidiagonal (m + n)).erase (m, n))
            (fun x => PowerSeries.coeff x.1 q.1 * PowerSeries.coeff x.2 g.1)‖ < ‖q‖ := by
      refine norm_sum_lt_of_forall_lt ((Finset.antidiagonal (m + n)).erase (m, n))
        (fun x : ℕ × ℕ => PowerSeries.coeff x.1 q.1 * PowerSeries.coeff x.2 g.1) hqnormpos ?_
      intro x hx
      rcases x with ⟨i, j⟩
      have hxmem : (i, j) ∈ Finset.antidiagonal (m + n) := Finset.mem_of_mem_erase hx
      have hij : i + j = m + n := by simpa using (Finset.mem_antidiagonal.mp hxmem)
      by_cases hjgt : n < j
      · have hgj : ‖PowerSeries.coeff j g.1‖ < 1 := hgtail j hjgt
        have hqi_le : ‖PowerSeries.coeff i q.1‖ ≤ ‖q‖ :=
          TateAlgebra.coeff_norm_le q (Finsupp.single () i)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right hqi_le (norm_nonneg _)).trans_lt <|
          (mul_lt_mul_of_pos_left hgj hqnormpos).trans_eq (mul_one _)
      · have hjle : j ≤ n := Nat.le_of_not_gt hjgt
        by_cases hjeq : j = n
        · have hieq : i = m := by omega
          exfalso
          exact (Finset.mem_erase.mp hx).1 (by simp [hieq, hjeq])
        · have hjlt : j < n := lt_of_le_of_ne hjle hjeq
          have him : m < i := by omega
          have hqi : ‖PowerSeries.coeff i q.1‖ < ‖q‖ := hmGt i him
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (hg_le j) (norm_nonneg _)).trans_lt <|
            (by simpa using hqi)
    have hcoeff_mul : ‖PowerSeries.coeff (m + n) (q * g).1‖ = ‖q‖ := by
      have hmem : (m, n) ∈ Finset.antidiagonal (m + n) := by simp
      have hsplit :
          PowerSeries.coeff (m + n) (q * g).1 =
            PowerSeries.coeff m q.1 * PowerSeries.coeff n g.1 +
              Finset.sum ((Finset.antidiagonal (m + n)).erase (m, n))
                (fun x => PowerSeries.coeff x.1 q.1 * PowerSeries.coeff x.2 g.1) := by
        rw [show (q * g).1 = q.1 * g.1 by rfl, PowerSeries.coeff_mul]
        rw [← Finset.sum_erase_add
          (Finset.antidiagonal (m + n))
          (fun x : ℕ × ℕ => PowerSeries.coeff x.1 q.1 * PowerSeries.coeff x.2 g.1)
          hmem]
        ring
      have hrest_lt' :
          ‖Finset.sum ((Finset.antidiagonal (m + n)).erase (m, n))
              (fun x => PowerSeries.coeff x.1 q.1 * PowerSeries.coeff x.2 g.1)‖ <
            ‖PowerSeries.coeff m q.1 * PowerSeries.coeff n g.1‖ := by
        simpa [hmEq, hg₁, norm_mul] using hrest_lt
      rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hrest_lt')]
      rw [max_eq_left_of_lt hrest_lt']
      simp [hmEq, hg₁]
    have hcoeff_zero : PowerSeries.coeff (m + n) (q * g).1 = 0 := by
      have := congrArg (fun h : TateAlgebra Unit A => PowerSeries.coeff (m + n) h.1) hEq
      have hpoly :
          PowerSeries.coeff (m + n) (polynomialToTate r).1 = 0 := by
        simpa [polynomialToTate] using hrzero
      simpa [show (q * g).1 = q.1 * g.1 by rfl, hpoly] using this
    have : ‖q‖ = 0 := by
      rw [← hcoeff_mul]
      simpa using congrArg norm hcoeff_zero
    exact (hq0 <| norm_eq_zero.mp this).elim

omit [NormOneClass A] [CompleteSpace A] in
lemma division_unique
    (g : TateAlgebra Unit A) {n : ℕ}
    (hg₁ : PowerSeries.coeff n g.1 = 1)
    (hg_le : ∀ l, ‖PowerSeries.coeff l g.1‖ ≤ 1)
    (hgtail : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < 1)
    {q₁ q₂ : TateAlgebra Unit A} {r₁ r₂ : Polynomial A}
    (hr₁ : r₁.degree < n) (hr₂ : r₂.degree < n)
    (h₁ : polynomialToTate (Polynomial.X ^ n : Polynomial A) = q₁ * g + polynomialToTate r₁)
    (h₂ : polynomialToTate (Polynomial.X ^ n : Polynomial A) = q₂ * g + polynomialToTate r₂) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have hrsub : (r₁ - r₂).degree < n := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro l hl
    have h1z : r₁.coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hr₁ (by exact_mod_cast hl))
    have h2z : r₂.coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hr₂ (by exact_mod_cast hl))
    simp [h1z, h2z]
  have hzero : (q₁ - q₂) * g + polynomialToTate (r₁ - r₂) = 0 := by
    have hsub :
        (q₁ - q₂) * g + polynomialToTate (r₁ - r₂) =
          (q₁ * g + polynomialToTate r₁) - (q₂ * g + polynomialToTate r₂) := by
      rw [polynomialToTate_sub]
      ring
    rw [hsub, ← h₁, ← h₂]
    ring
  obtain ⟨hq, hr⟩ := division_injective g hg₁ hg_le hgtail hrsub hzero
  constructor
  · exact sub_eq_zero.mp hq
  · exact sub_eq_zero.mp hr

lemma weierstrass_preparation_exists {f : TateAlgebra Unit A} {n : ℕ}
    (hf : IsDistinguishedOfOrder f n) :
    ∃ we : TateAlgebra Unit A × TateAlgebra Unit A,
      IsWeierstrassPolynomial we.1 n ∧ IsUnit we.2 ∧ f = we.2 * we.1 := by
  rcases hf.isUnit with ⟨u, hu⟩
  let g : TateAlgebra Unit A := (u⁻¹.1 : A) • f
  have hg₁ : PowerSeries.coeff n g.1 = 1 := by
    dsimp [g]
    rw [coeff_smul_unit, ← hu]
    simp
  have hg_le : ∀ l, ‖PowerSeries.coeff l g.1‖ ≤ 1 := by
    intro l
    have hcoeff :
        ‖PowerSeries.coeff l g.1‖ = ‖(u⁻¹.1 : A)‖ * ‖PowerSeries.coeff l f.1‖ := by
      simp [g]
    rw [hcoeff]
    refine le_trans ?_ (le_of_eq (norm_inv_unit_mul_norm_eq_one u))
    gcongr
    exact (TateAlgebra.coeff_norm_le f (Finsupp.single () l)).trans
      (by simpa only [hu] using hf.toIsOfOrder.norm_le)
  have hgtail1 : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < 1 := by
    intro l hl
    have huinv_pos : 0 < ‖(u⁻¹.1 : A)‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) ?_
      intro h0
      have hzero : ‖(u⁻¹.1 : A)‖ * ‖(u : A)‖ = 0 := by simp [h0.symm]
      have h01 : (0 : ℝ) = 1 := by
        simpa [norm_inv_unit_mul_norm_eq_one u] using hzero.symm
      norm_num at h01
    have hcoeff :
        ‖PowerSeries.coeff l g.1‖ = ‖(u⁻¹.1 : A)‖ * ‖PowerSeries.coeff l f.1‖ := by
      simp [g]
    rw [hcoeff]
    exact (mul_lt_mul_of_pos_left (by simpa [hu] using hf.toIsOfOrder.maximal hl)
      huinv_pos).trans_eq
      (norm_inv_unit_mul_norm_eq_one u)
  obtain ⟨ε0, hε0pos, hε0lt1, hε0bound⟩ := exists_uniform_tail_bound g n hgtail1
  let ε : ℝ := (ε0 + 1) / 2
  have hε0 : 0 < ε := by simpa [ε] using by linarith
  have hε1 : ε < 1 := by simpa [ε] using by linarith
  have hgtail : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < ε := by
    intro l hl
    exact lt_of_le_of_lt (hε0bound l hl) (by
      dsimp [ε]
      linarith)
  let p0 : Polynomial A := truncPolynomial g n
  let Xn : TateAlgebra Unit A := polynomialToTate (Polynomial.X ^ n : Polynomial A)
  let RbasePoly : Polynomial A := Polynomial.X ^ n - p0
  let h0 : TateAlgebra Unit A := polynomialToTate p0 - g
  have hp0₁ : p0.coeff n = 1 := by
    simpa [p0, coeff_truncPolynomial] using hg₁
  have hp0 : ∀ l > n, p0.coeff l = 0 := by
    intro l hl
    simp [p0, coeff_truncPolynomial, Nat.not_le_of_gt hl]
  have hRbase_deg : RbasePoly.degree < n := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro l hl
    by_cases hln : l = n
    · subst hln
      simp [RbasePoly, hp0₁]
    · have hgt : n < l := lt_of_le_of_ne hl (Ne.symm hln)
      simp [RbasePoly, hp0 l hgt, Polynomial.coeff_X_pow, hln]
  have hRbase_coeff_le : ∀ l, ‖RbasePoly.coeff l‖ ≤ 1 := by
    intro l
    by_cases hln : l = n
    · subst hln
      simp [RbasePoly, hp0₁]
    · by_cases hlgt : n < l
      · simp [RbasePoly, hp0 l hlgt, Polynomial.coeff_X_pow, hln, norm_zero]
      · have hlt : l < n := lt_of_le_of_ne (Nat.le_of_not_gt hlgt) hln
        have hp0le : ‖p0.coeff l‖ ≤ 1 := by
          have hle : l ≤ n := Nat.le_of_lt hlt
          simpa [p0, coeff_truncPolynomial, hle] using hg_le l
        simpa [RbasePoly, Polynomial.coeff_X_pow, hln, norm_neg] using hp0le
  have hh0_lt : ‖h0‖ < ε := by
    simpa [h0, norm_sub_rev] using norm_sub_truncPolynomial_lt g n hε0 hgtail
  obtain ⟨q0, r0, hr0deg, h0eq, hq0_coeff_le, hr0_coeff_le⟩ :=
    distinguished_division g hε0 hε1 hg₁ hg_le hgtail h0
  have hq0_norm_lt : ‖q0‖ < 1 := by
    apply norm_lt_of_forall_coeff_lt
    intro l
    exact lt_of_le_of_lt (hq0_coeff_le l) (lt_trans hh0_lt hε1)
  let Q : TateAlgebra Unit A := 1 + q0
  have hQUnit : IsUnit Q := by
    apply isUnit_of_norm_sub_one_lt_one
    simpa [Q] using hq0_norm_lt
  let Rpoly : Polynomial A := RbasePoly + r0
  have hRpoly_deg : Rpoly.degree < n := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro l hl
    have hbase_zero : RbasePoly.coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hRbase_deg (by exact_mod_cast hl))
    have hr0_zero : r0.coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hr0deg (by exact_mod_cast hl))
    simp [Rpoly, hbase_zero, hr0_zero]
  have hr0_coeff_lt_one : ∀ l, ‖r0.coeff l‖ < 1 := by
    intro l
    exact lt_of_le_of_lt (hr0_coeff_le l) (lt_trans hh0_lt hε1)
  have hRpoly_coeff_le : ∀ i, ‖Rpoly.coeff i‖ ≤ 1 := by
    intro i
    by_cases hin : i = n
    · have hr0_zero : r0.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt hr0deg
      have hcoeff : Rpoly.coeff i = 0 := by
        rw [hin]
        simp [Rpoly, RbasePoly, hp0₁, hr0_zero]
      simp [hcoeff]
    · by_cases higt : n < i
      · have hbase_zero : RbasePoly.coeff i = 0 := by
          simp [RbasePoly, hp0 i higt, Polynomial.coeff_X_pow, hin]
        have hr0_zero : r0.coeff i = 0 := Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hr0deg (by exact_mod_cast Nat.le_of_lt higt))
        simp [Rpoly, hbase_zero, hr0_zero]
      · rw [show ‖Rpoly.coeff i‖ = ‖RbasePoly.coeff i + r0.coeff i‖ by simp [Rpoly]]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans <|
          max_le (hRbase_coeff_le i) (le_of_lt (hr0_coeff_lt_one i))
  let wPoly : Polynomial A := Polynomial.X ^ n - Rpoly
  have hwcoeff_le : ∀ l, ‖wPoly.coeff l‖ ≤ 1 := by
    intro l
    by_cases hln : l = n
    · have hRn : Rpoly.coeff l = 0 := by
        rw [hln]
        exact Polynomial.coeff_eq_zero_of_degree_lt hRpoly_deg
      have hwcoeff_eq : wPoly.coeff l = 1 - Rpoly.coeff l := by
        unfold wPoly
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
        simp [hln]
      simp [hwcoeff_eq, hRn]
    · by_cases hlgt : n < l
      · have hRzero : Rpoly.coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
        hRpoly_deg (by exact_mod_cast Nat.le_of_lt hlgt))
        simp [wPoly, Polynomial.coeff_X_pow, hln, hRzero, norm_zero]
      · have hlt : l < n := lt_of_le_of_ne (Nat.le_of_not_gt hlgt) hln
        simpa [wPoly, Polynomial.coeff_X_pow, hln, norm_neg] using hRpoly_coeff_le l
  have hwWeier : IsWeierstrassPolynomial (polynomialToTate wPoly) n := by
    refine ⟨?_, ?_, ?_⟩
    · exact norm_polynomialToTate_le_of_coeff_le wPoly (show (0 : ℝ) ≤ 1 by norm_num) hwcoeff_le
    · have hRn : Rpoly.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt hRpoly_deg
      simp [wPoly, polynomialToTate, hRn]
    · intro l hl
      have hRzero : Rpoly.coeff l = 0 := Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
        hRpoly_deg (by exact_mod_cast Nat.le_of_lt hl))
      simp [wPoly, polynomialToTate, PowerSeries.coeff_X_pow, Nat.ne_of_gt hl, hRzero]
  have hXnEq : Xn = Q * g + polynomialToTate Rpoly := by
    have hp0_eq : polynomialToTate p0 = g + (q0 * g + polynomialToTate r0) := by
      have : polynomialToTate p0 = (polynomialToTate p0 - g) + g := by ring
      rw [this, show polynomialToTate p0 - g = h0 by rfl, h0eq]
      ring
    have h1 : Xn = polynomialToTate p0 + polynomialToTate RbasePoly := by
      simp [Xn, RbasePoly, polynomialToTate_sub]
    rw [h1, hp0_eq]
    have h2 : g + (q0 * g + polynomialToTate r0) + polynomialToTate RbasePoly =
        (1 + q0) * g + (polynomialToTate RbasePoly + polynomialToTate r0) := by ring
    rw [h2]
    simp [Q, Rpoly, polynomialToTate_add, add_comm]
  have hQg : Q * g = polynomialToTate wPoly := by
    have h1 : Q * g = Xn - polynomialToTate Rpoly := by rw [hXnEq]; ring
    exact Eq.trans h1 (by simp [wPoly, Xn, ← polynomialToTate_sub])
  rcases hQUnit with ⟨UQ, hUQ⟩
  let e : TateAlgebra Unit A := (algebraMap A (TateAlgebra Unit A) (u : A)) * UQ⁻¹.1
  have heUnit : IsUnit e := by
    dsimp [e]
    exact (u.isUnit.map (algebraMap A (TateAlgebra Unit A))).mul UQ⁻¹.isUnit
  have hQgUQ : (UQ : TateAlgebra Unit A) * g = polynomialToTate wPoly := by
    simpa [Q, hUQ] using hQg
  have hgFact : g = UQ⁻¹.1 * polynomialToTate wPoly := by
    exact (by simp : g = UQ⁻¹.1 * ((UQ : TateAlgebra Unit A) * g)).trans (by rw [hQgUQ])
  have hfFact : f = e * polynomialToTate wPoly := by
    have h1 : f = (algebraMap A (TateAlgebra Unit A) (u : A)) * g := by
      dsimp [g]; rw [Algebra.smul_def]
      exact (by simp : f = (1 : TateAlgebra Unit A) * f).trans <|
            (by simp : (1 : TateAlgebra Unit A) * f = (algebraMap A (TateAlgebra Unit A) ((u : A) * (u⁻¹.1 : A))) * f).trans <|
            (by rw [map_mul] : (algebraMap A (TateAlgebra Unit A) ((u : A) * (u⁻¹.1 : A))) * f = ((algebraMap A (TateAlgebra Unit A) (u : A)) * (algebraMap A (TateAlgebra Unit A) (u⁻¹.1 : A))) * f).trans <|
            (by ring)
    exact h1.trans <| (by rw [hgFact] : (algebraMap A (TateAlgebra Unit A) (u : A)) * g = (algebraMap A (TateAlgebra Unit A) (u : A)) * (UQ⁻¹.1 * polynomialToTate wPoly)).trans <| (by simp [e, mul_assoc])
  exact ⟨⟨polynomialToTate wPoly, e⟩, hwWeier, heUnit, hfFact⟩

/-- ***Weierstrass Preparation theorem**: A distinguished series of order `n` factors uniquely as a
unit times a Weierstrass polynomial of degree `n`. -/
theorem weierstrass_preparation {f : TateAlgebra Unit A} {n : ℕ}
    (hf : IsDistinguishedOfOrder f n) :
    ∃! we : TateAlgebra Unit A × TateAlgebra Unit A,
      IsWeierstrassPolynomial we.1 n ∧ IsUnit we.2 ∧ f = we.2 * we.1 := by
  obtain ⟨we0, hwe0⟩ := weierstrass_preparation_exists hf
  rcases hf.isUnit with ⟨u, hu⟩
  let g : TateAlgebra Unit A := (u⁻¹.1 : A) • f
  have hg₁ : PowerSeries.coeff n g.1 = 1 := by
    dsimp [g]
    rw [coeff_smul_unit, ← hu]
    simp
  have hg_le : ∀ l, ‖PowerSeries.coeff l g.1‖ ≤ 1 := by
    intro l
    have hcoeff : ‖PowerSeries.coeff l g.1‖ = ‖(u⁻¹.1 : A)‖ * ‖PowerSeries.coeff l f.1‖ := by
      simp [g]
    rw [hcoeff]
    refine le_trans ?_ (le_of_eq (norm_inv_unit_mul_norm_eq_one u))
    gcongr
    exact le_trans (TateAlgebra.coeff_norm_le f (Finsupp.single () l))
      (by simpa [hu] using hf.toIsOfOrder.norm_le)
  have hgtail : ∀ l > n, ‖PowerSeries.coeff l g.1‖ < 1 := by
    intro l hl
    have huinv_pos : 0 < ‖(u⁻¹.1 : A)‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) ?_
      intro h0
      have hzero : ‖(u⁻¹.1 : A)‖ * ‖(u : A)‖ = 0 := by simp [h0.symm]
      have h01 : (0 : ℝ) = 1 := by
        simpa [norm_inv_unit_mul_norm_eq_one u] using hzero.symm
      norm_num at h01
    have hcoeff :
        ‖PowerSeries.coeff l g.1‖ = ‖(u⁻¹.1 : A)‖ * ‖PowerSeries.coeff l f.1‖ := by
      simp [g]
    rw [hcoeff]
    exact (mul_lt_mul_of_pos_left (by simpa [hu] using hf.toIsOfOrder.maximal hl)
      huinv_pos).trans_eq
      (norm_inv_unit_mul_norm_eq_one u)
  let Xn : TateAlgebra Unit A := polynomialToTate (Polynomial.X ^ n : Polynomial A)
  have hdiv_of_factorization :
      ∀ {w e : TateAlgebra Unit A},
        IsWeierstrassPolynomial w n → IsUnit e → f = e * w →
        ∃ q : TateAlgebra Unit A, ∃ r : Polynomial A,
          r.degree < n ∧ Xn = q * g + polynomialToTate r ∧
            polynomialToTate (truncPolynomial w n) = w ∧ r = Polynomial.X ^ n - truncPolynomial w n
              := by
    intro w e hw he hfw
    have hwpoly_eq : polynomialToTate (truncPolynomial w n) = w := by
      apply Subtype.ext
      ext l
      by_cases hl : l ≤ n
      · simp [polynomialToTate, coeff_truncPolynomial, hl]
      · have hzero : PowerSeries.coeff l w.1 = 0 := hw.isPoly l (Nat.lt_of_not_ge hl)
        simp [polynomialToTate, coeff_truncPolynomial, hl, hzero]
    have hrdeg : (Polynomial.X ^ n - truncPolynomial w n).degree < ↑n := by
      refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
      intro l hl
      by_cases hln : l = n
      · subst hln
        simp [coeff_truncPolynomial, hw.monic]
      · have hgt : n < l := lt_of_le_of_ne hl (Ne.symm hln)
        simp [Polynomial.coeff_X_pow, hln, coeff_truncPolynomial, Nat.not_le_of_gt hgt]
    have henUnit : IsUnit ((algebraMap A (TateAlgebra Unit A) (u⁻¹.1 : A)) * e) := by
      exact (u⁻¹).isUnit.map (algebraMap A (TateAlgebra Unit A)) |>.mul he
    rcases henUnit with ⟨Ue, hUe⟩
    refine ⟨Ue⁻¹.1, Polynomial.X ^ n - truncPolynomial w n, hrdeg, ?_, hwpoly_eq, rfl⟩
    have hgEq : g = (Ue : TateAlgebra Unit A) * w := by
      exact (by simp [g, Algebra.smul_def] : g = (algebraMap A (TateAlgebra Unit A) (u⁻¹.1 : A)) * f).trans <|
        (by rw [hfw] : _ = (algebraMap A (TateAlgebra Unit A) (u⁻¹.1 : A)) * (e * w)).trans <|
        (by ring : _ = ((algebraMap A (TateAlgebra Unit A) (u⁻¹.1 : A)) * e) * w).trans <|
        (by rw [hUe])
    exact (by simp [Xn, polynomialToTate_sub] : Xn = polynomialToTate (truncPolynomial w n) + polynomialToTate (Polynomial.X ^ n - truncPolynomial w n)).trans <|
      (by rw [hwpoly_eq] : _ = w + polynomialToTate (Polynomial.X ^ n - truncPolynomial w n)).trans <|
      by
        rw [hgEq]
        simp
  refine ⟨we0, hwe0, ?_⟩
  intro we hwe
  rcases we0 with ⟨w0, e0⟩
  rcases we with ⟨w1, e1⟩
  rcases hwe0 with ⟨hw0, he0, hf0⟩
  rcases hwe with ⟨hw1, he1, hf1⟩
  obtain ⟨q0, r0, hr0, hX0, hw0poly, hr0def⟩ := hdiv_of_factorization hw0 he0 hf0
  obtain ⟨q1, r1, hr1, hX1, hw1poly, hr1def⟩ := hdiv_of_factorization hw1 he1 hf1
  obtain ⟨hqEq, hrEq⟩ := division_unique g hg₁ hg_le hgtail hr0 hr1 hX0 hX1
  have hsub : Polynomial.X ^ n - truncPolynomial w0 n = Polynomial.X ^ n - truncPolynomial w1 n :=
    by
    simpa [hr0def, hr1def] using hrEq
  have hwpolyEq : truncPolynomial w0 n = truncPolynomial w1 n := by
    have := congrArg (fun p : Polynomial A => Polynomial.X ^ n - p) hsub
    simpa using this
  have hwEq : w0 = w1 := by
    exact (by simpa using hw0poly.symm : w0 = polynomialToTate (truncPolynomial w0 n)).trans <|
      (by rw [hwpolyEq] : _ = polynomialToTate (truncPolynomial w1 n)).trans <|
      hw1poly
  have hw0_le : ∀ l, ‖PowerSeries.coeff l w0.1‖ ≤ 1 := by
    intro l
    exact le_trans (TateAlgebra.coeff_norm_le w0 (Finsupp.single () l)) hw0.norm_le_one
  have hw0_tail : ∀ l > n, ‖PowerSeries.coeff l w0.1‖ < 1 := by
    intro l hl
    simp [hw0.isPoly l hl]
  have heEq : e1 = e0 := by
    have hmulEq : e1 * w0 = e0 * w0 := by
      exact (by rw [hwEq] : e1 * w0 = e1 * w1).trans <|
        hf1.symm.trans hf0
    have hdiff : (e1 - e0) * w0 + polynomialToTate (0 : Polynomial A) = 0 := by
      have hmulZero : (e1 - e0) * w0 = 0 := by
        exact (by ring : (e1 - e0) * w0 = e1 * w0 - e0 * w0).trans <| by rw [hmulEq]; ring
      simp [hmulZero]
    obtain ⟨hzero, _⟩ := division_injective w0 hw0.monic hw0_le hw0_tail (by simp) hdiff
    exact sub_eq_zero.mp hzero
  cases hwEq
  cases heEq
  rfl

lemma weierstrass_division {w : TateAlgebra Unit A} {n : ℕ}
    (hw : IsWeierstrassPolynomial w n) (h : TateAlgebra Unit A) :
    ∃ q : TateAlgebra Unit A, ∃ r : Polynomial A,
      r.degree < n ∧ h = q * w + polynomialToTate r := by
  let ε : ℝ := 1 / 2
  have hε0 : 0 < ε := by
    dsimp [ε]
    norm_num
  have hε1 : ε < 1 := by
    dsimp [ε]
    norm_num
  have hw_le : ∀ l, ‖PowerSeries.coeff l w.1‖ ≤ 1 := by
    intro l
    exact le_trans (TateAlgebra.coeff_norm_le w (Finsupp.single () l)) hw.norm_le_one
  have hwtail : ∀ l > n, ‖PowerSeries.coeff l w.1‖ < ε := by
    intro l hl
    rw [hw.isPoly l hl, norm_zero]
    exact hε0
  obtain ⟨q, r, hrdeg, hEq, -, -⟩ := distinguished_division w hε0 hε1 hw.monic hw_le hwtail h
  exact ⟨q, r, hrdeg, hEq⟩

theorem finite_quotient_of_isWeierstrassPolynomial {w : TateAlgebra Unit A} {n : ℕ}
    (hw : IsWeierstrassPolynomial w n) :
    Module.Finite A ((TateAlgebra Unit A) ⧸ Ideal.span {w}) := by
  let p : Polynomial A := truncPolynomial w n
  let I : Ideal (Polynomial A) := Ideal.span ({p} : Set (Polynomial A))
  let J : Ideal (TateAlgebra Unit A) := Ideal.span {w}
  have hp_eq : polynomialToTate p = w := by
    apply Subtype.ext
    ext l
    by_cases hl : l ≤ n
    · simp [p, polynomialToTate, coeff_truncPolynomial, hl]
    · have hzero : PowerSeries.coeff l w.1 = 0 := hw.isPoly l (Nat.lt_of_not_ge hl)
      simp [p, polynomialToTate, coeff_truncPolynomial, hl, hzero]
  have hp₁ : p.coeff n = 1 := by
    simpa [p, coeff_truncPolynomial] using hw.monic
  have hp0 : ∀ l > n, p.coeff l = 0 := by
    intro l hl
    simp [p, coeff_truncPolynomial, Nat.not_le_of_gt hl]
  have hpMonic : p.Monic := p.monic_of_coeff_eq_one_of_high_zero n hp₁ hp0
  let f : Polynomial A →ₐ[A] ((TateAlgebra Unit A) ⧸ J) :=
    (Ideal.Quotient.mkₐ A J).comp polynomialToTateAlgHom
  have hwJ : w ∈ J := Ideal.subset_span (by simp)
  have hwzero : (Ideal.Quotient.mkₐ A J) w = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk J w = Ideal.Quotient.mk J 0
    rw [Ideal.Quotient.eq]
    simpa using hwJ
  have hIker : I ≤ RingHom.ker f := by
    change Ideal.span ({p} : Set (Polynomial A)) ≤ RingHom.ker f
    rw [Ideal.span_singleton_le_iff_mem]
    change f p = 0
    rw [show f p = (Ideal.Quotient.mkₐ A J) (polynomialToTate p) by rfl]
    rw [hp_eq]
    exact hwzero
  let ψ : (Polynomial A ⧸ I) →ₐ[A] ((TateAlgebra Unit A) ⧸ J) :=
    Ideal.Quotient.liftₐ I f fun a ha => hIker ha
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mkₐ_surjective A J x
    obtain ⟨q, r, hrdeg, hdiv⟩ := weierstrass_division hw h
    refine ⟨Ideal.Quotient.mkₐ A I r, ?_⟩
    have hψr : ψ (Ideal.Quotient.mkₐ A I r) = (Ideal.Quotient.mkₐ A J) (polynomialToTate r) := by
      simp [ψ, f, polynomialToTateAlgHom, Ideal.Quotient.liftₐ_apply]
    rw [hψr, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    change polynomialToTate r - h ∈ J
    rw [hdiv]
    have hsub : polynomialToTate r - (q * w + polynomialToTate r) = -(q * w) := by
      ring
    rw [hsub]
    exact J.neg_mem (J.mul_mem_left q hwJ)
  have hψfinite : ψ.Finite := AlgHom.Finite.of_surjective ψ hψsurj
  have hIfinite₀ : Module.Finite A (Polynomial A ⧸ Ideal.span ({p} : Set (Polynomial A))) := by
    simpa using (Polynomial.Monic.finite_quotient hpMonic)
  have hIfinite : (algebraMap A (Polynomial A ⧸ I)).Finite := by
    exact (RingHom.finite_algebraMap).2 hIfinite₀
  have halg : ψ.toRingHom.comp (algebraMap A (Polynomial A ⧸ I)) =
      algebraMap A ((TateAlgebra Unit A) ⧸ J) := by
    ext a
    exact AlgHom.commutes ψ a
  have hfinite : (algebraMap A ((TateAlgebra Unit A) ⧸ J)).Finite := by
    rw [← halg]
    exact RingHom.Finite.comp hψfinite hIfinite
  simpa [J] using hfinite

/-- **Weierstrass Finiteness theorem**: Let `B` be a finite `A{T}`-algebra, and assume that the
kernel of the corresponding homomorphism `A{T} → B` contains a Weierstrass polynomial.
Then `B` is a finite `A`-algebra. -/
theorem weierstrass_finiteness {B : Type*} [CommRing B] [Algebra A B]
    {φ : TateAlgebra Unit A →ₐ[A] B} (hφ : φ.Finite) {w : TateAlgebra Unit A} {n : ℕ}
    (hw : IsWeierstrassPolynomial w n) (hker : w ∈ RingHom.ker φ) :
    Module.Finite A B := by
  let I : Ideal (TateAlgebra Unit A) := Ideal.span {w}
  have hIker : I ≤ RingHom.ker φ :=
    (Ideal.span_singleton_le_iff_mem (RingHom.ker φ)).2 hker
  let ψ : ((TateAlgebra Unit A) ⧸ I) →ₐ[A] B := Ideal.Quotient.liftₐ I φ fun a ha => hIker ha
  have hcomp : ψ.comp (Ideal.Quotient.mkₐ A I) = φ := by
    ext x
    simp [ψ, Ideal.Quotient.liftₐ_apply]
  have hψ : ψ.Finite := by
    have hφ' : (ψ.comp (Ideal.Quotient.mkₐ A I)).Finite := by
      rw [hcomp]
      exact hφ
    exact RingHom.Finite.of_comp_finite hφ'
  have hI : (algebraMap A ((TateAlgebra Unit A) ⧸ I)).Finite :=
    RingHom.finite_algebraMap.mpr (finite_quotient_of_isWeierstrassPolynomial hw)
  have halg : ψ.toRingHom.comp (algebraMap A ((TateAlgebra Unit A) ⧸ I)) = algebraMap A B := by
    ext a
    simp [ψ]
  simpa using RingHom.Finite.comp hψ hI

end weierstrass_preparation

/-- Reindex `n + 1` Tate variables as one distinguished variable plus `n` others. -/
noncomputable def tateAlgebraFinSuccEquiv (n : ℕ) :
    TateAlgebra (Fin (n + 1)) A ≃ₐ[A] TateAlgebra (Option (Fin n)) A :=
  AlgEquiv.ofAlgHom
    (TateAlgebra.rename A (finSuccEquiv n).toEmbedding)
    (TateAlgebra.rename A (finSuccEquiv n).symm.toEmbedding)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      simp [TateAlgebra.rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id])
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      simp [TateAlgebra.rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id])

/-- Identify the Tate algebra in no variables with its coefficient ring. -/
noncomputable def finZeroAlgEquiv : TateAlgebra (Fin 0) A ≃ₐ[A] A :=
  AlgEquiv.ofAlgHom constantCoeff C (by ext) <| by
    ext
    apply Subtype.ext
    ext e
    simp [Subsingleton.elim e 0]
    rfl

section OptionDecomposition

/-- View an `Option σ` power series as a power series in `none`
with coefficients in power series in `σ`. -/
noncomputable def optionToPowerSeries  (f : MvPowerSeries (Option σ) A) :
    PowerSeries (MvPowerSeries σ A) :=
  PowerSeries.mk fun n => fun d => MvPowerSeries.coeff (Finsupp.optionElim n d) f

/-- Flatten a power series in the `none` variable with `σ`-series coefficients. -/
noncomputable def powerSeriesToOption (f : PowerSeries (MvPowerSeries σ A)) :
    MvPowerSeries (Option σ) A :=
  fun e => MvPowerSeries.coeff e.some (PowerSeries.coeff (e none) f)

omit [Finite σ] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] in
@[simp]
lemma coeff_optionToPowerSeries (f : MvPowerSeries (Option σ) A) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optionToPowerSeries f)) =
      MvPowerSeries.coeff (Finsupp.optionElim n d) f := by
  unfold optionToPowerSeries
  rw [PowerSeries.coeff_mk]
  rfl

omit [Finite σ] [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A] in
@[simp]
lemma coeff_powerSeriesToOption
    (f : PowerSeries (MvPowerSeries σ A))
    (e : Option σ →₀ ℕ) :
    MvPowerSeries.coeff e (powerSeriesToOption f) =
      MvPowerSeries.coeff e.some (PowerSeries.coeff (e none) f) := by
  rfl

/-- The coefficient-wise equivalence splitting off the `none` variable. -/
noncomputable def optionPowerSeriesEquiv :
    MvPowerSeries (Option σ) A ≃ PowerSeries (MvPowerSeries σ A) where
  toFun := optionToPowerSeries
  invFun := powerSeriesToOption
  left_inv f := by
    apply MvPowerSeries.ext
    intro e
    simp
  right_inv f := by
    apply PowerSeries.ext
    intro n
    apply MvPowerSeries.ext
    intro d
    simp [coeff_optionToPowerSeries, coeff_powerSeriesToOption]

omit [Finite σ] [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma isTate_coeff_optionToPowerSeries (f : MvPowerSeries (Option σ) A)
    (hf : IsTate (Option σ) A f) (n : ℕ) :
    IsTate σ A (PowerSeries.coeff n (optionToPowerSeries f)) := by
  let e : (σ →₀ ℕ) ↪ (Option σ →₀ ℕ) :=
    ⟨Finsupp.optionElim n, by
      intro d₁ d₂ h
      simpa using congrArg Finsupp.some h⟩
  rw [isTate_iff]
  intro ε hε
  have hfin : {a : Option σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff a f‖}.Finite :=
    (isTate_iff f).mp hf ε hε
  have hpre : {d : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff (e d) f‖}.Finite :=
    Set.Finite.preimage_embedding e hfin
  have hEq :
      {d : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff d (PowerSeries.coeff n (optionToPowerSeries f))‖} =
        {d : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff (e d) f‖} := by
    ext d
    change ε ≤ ‖MvPowerSeries.coeff d (PowerSeries.coeff n (optionToPowerSeries f))‖ ↔
      ε ≤ ‖MvPowerSeries.coeff (e d) f‖
    rw [show MvPowerSeries.coeff d (PowerSeries.coeff n (optionToPowerSeries f)) =
        MvPowerSeries.coeff (e d) f from coeff_optionToPowerSeries f n d]
  rw [hEq]
  exact hpre

/-- The coefficient of `none^n`, regarded as a Tate series in the remaining variables. -/
noncomputable def optionCoeffTate (f : TateAlgebra (Option σ) A) (n : ℕ) : TateAlgebra σ A :=
  ⟨PowerSeries.coeff n (optionToPowerSeries f.1),
    isTate_coeff_optionToPowerSeries f.1 f.2 n⟩

omit [Finite σ] [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma isTate_optionToTate (f : TateAlgebra (Option σ) A) :
    IsTate Unit (TateAlgebra σ A) (PowerSeries.mk (optionCoeffTate f)) := by
  rw [isTate_iff]
  intro ε hε
  let T : Set ℕ := {n : ℕ | ε ≤ ‖optionCoeffTate f n‖}
  let S : Set (Option σ →₀ ℕ) := {e : Option σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e f.1‖}
  have hSfin : S.Finite := (isTate_iff f.1).mp f.2 ε hε
  let g : ℕ → Option σ →₀ ℕ := fun n =>
    if hn : n ∈ T then
      let a : TateAlgebra σ A := optionCoeffTate f n
      let hne : a ≠ 0 := by
        intro ha
        have : ‖a‖ = 0 := by simp [ha]
        exact (not_lt_of_ge (by simpa [T] using hn : ε ≤ ‖a‖)) (by simpa [this] using hε)
      let d : σ →₀ ℕ := Classical.choose (TateAlgebra.exists_coeff_norm_eq_norm a hne)
      Finsupp.optionElim n d
    else 0
  have hg_inj : Set.InjOn g T := by
    intro m hm n hn hmn
    have hnone := congrArg (fun e => e none) hmn
    simp [g, hm, hn] at hnone
    exact hnone
  have hg_mem : Set.MapsTo g T S := by
    intro n hn
    simp only [S, Set.mem_setOf_eq]
    have hn' : n ∈ T := hn
    simp only [g, hn', dif_pos]
    let a : TateAlgebra σ A := optionCoeffTate f n
    let hne : a ≠ 0 := by
      intro ha
      have : ‖a‖ = 0 := by simp [ha]
      exact (not_lt_of_ge (by simpa [T] using hn : ε ≤ ‖a‖)) (by simpa [this] using hε)
    let d : σ →₀ ℕ := Classical.choose (TateAlgebra.exists_coeff_norm_eq_norm a hne)
    have hd : ‖MvPowerSeries.coeff d a.1‖ = ‖a‖ :=
      Classical.choose_spec (TateAlgebra.exists_coeff_norm_eq_norm a hne)
    have hεa : ε ≤ ‖MvPowerSeries.coeff d a.1‖ := by
      simpa [hd] using (show ε ≤ ‖a‖ by simpa [T] using hn)
    have hεa' :
        ε ≤ ‖MvPowerSeries.coeff d
          (PowerSeries.coeff n (optionToPowerSeries f.1))‖ := by
      simpa [a, optionCoeffTate] using hεa
    rw [← coeff_optionToPowerSeries f.1 n d]
    exact hεa'
  have hTfin : T.Finite := by
    exact Set.Finite.of_injOn hg_mem hg_inj hSfin
  have hU :
      {e : Unit →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e (PowerSeries.mk (optionCoeffTate f))‖}.Finite :=
        by
    let u : ℕ ↪ Unit →₀ ℕ :=
      ⟨fun n => Finsupp.single () n, fun m n h ↦ by simpa using congrArg (fun e => e ()) h⟩
    have hEq :
        {e : Unit →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e (PowerSeries.mk (optionCoeffTate f))‖} =
          u '' T := by
      ext e
      constructor
      · intro he
        refine ⟨e (), ?_, ?_⟩
        · change ε ≤ ‖optionCoeffTate f (e ())‖
          simpa [PowerSeries.coeff_def rfl, PowerSeries.coeff_mk]
            using he
        · simpa [u] using (Finsupp.unique_single e).symm
      · rintro ⟨n, hn, rfl⟩
        change ε ≤ ‖optionCoeffTate f n‖ at hn
        change ε ≤ ‖PowerSeries.coeff n (PowerSeries.mk (optionCoeffTate f))‖
        rw [PowerSeries.coeff_mk]
        simpa [u] using hn
    simpa [hEq] using hTfin.image u
  simpa using hU

/-- Regard `A{Option σ}` as a one-variable Tate algebra over `A{σ}`. -/
noncomputable def optionToTate (f : TateAlgebra (Option σ) A) :
    TateAlgebra Unit (TateAlgebra σ A) :=
  ⟨PowerSeries.mk (optionCoeffTate f), isTate_optionToTate f⟩

/-- Flatten a one-variable Tate algebra over `A{σ}` back to `A{Option σ}`. -/
noncomputable def tateToOption (f : TateAlgebra Unit (TateAlgebra σ A)) :
    TateAlgebra (Option σ) A := by
  let F0 : PowerSeries (MvPowerSeries σ A) := PowerSeries.map (algebraMap _ _) f.1
  refine ⟨powerSeriesToOption F0, ?_⟩
  rw [mem_tateSubalgebra_iff]
  intro ε hε
  let T : Set ℕ := {n : ℕ | ε ≤ ‖PowerSeries.coeff n f.1‖}
  have hTfin : T.Finite := finite_nat_coeff_set_of_isTate_unit f hε
  let D : ℕ → Set (σ →₀ ℕ) := fun n =>
    {d : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff d ((PowerSeries.coeff n f.1 : TateAlgebra σ A).1)‖}
  have hDfin : ∀ n ∈ T, (D n).Finite :=
    fun n hn ↦ (isTate_iff ((PowerSeries.coeff n f.1).1)).mp (PowerSeries.coeff n f.1).2 ε hε
  have hsubset : {e : Option σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e (powerSeriesToOption F0)‖} ⊆
      ⋃ n ∈ T, (Finsupp.optionElim n) '' D n := by
    intro e he
    refine Set.mem_iUnion.2 ⟨e none, Set.mem_iUnion.2 ⟨?_, ⟨e.some, he, Finsupp.optionElim_some e⟩⟩⟩
    have hle : ‖MvPowerSeries.coeff e.some (PowerSeries.coeff (e none) F0)‖ ≤
        ‖PowerSeries.coeff (e none) f.1‖ :=
      TateAlgebra.coeff_norm_le (PowerSeries.coeff (e none) f.1) e.some
    exact le_trans he hle
  have hfin : (⋃ n ∈ T, (Finsupp.optionElim n) '' D n).Finite := by
    refine hTfin.biUnion ?_
    intro n hn
    exact (hDfin n hn).image (Finsupp.optionElim n)
  exact hfin.subset hsubset

omit [Finite σ] [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma tateToOption_optionToTate (f : TateAlgebra (Option σ) A) :
    tateToOption (optionToTate f) = f := by
  apply Subtype.ext
  ext e
  simp [tateToOption, optionToTate, coeff_powerSeriesToOption]
  change (MvPowerSeries.coeff e.some : MvPowerSeries σ A → A)
      (((optionCoeffTate f (e none) : TateAlgebra σ A) : MvPowerSeries σ A)) =
    (MvPowerSeries.coeff e : MvPowerSeries (Option σ) A → A)
      (((f : TateAlgebra (Option σ) A) : MvPowerSeries (Option σ) A))
  simp [optionCoeffTate]

omit [Finite σ] [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
@[simp]
lemma optionToTate_tateToOption (f : TateAlgebra Unit (TateAlgebra σ A)) :
    optionToTate (tateToOption f) = f := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  apply Subtype.ext
  ext d
  have hmap : optionToPowerSeries ((tateToOption f).1) = PowerSeries.map (algebraMap _ _) f.1 := by
    apply PowerSeries.ext
    intro n
    apply MvPowerSeries.ext
    intro d
    simp [tateToOption, coeff_optionToPowerSeries, coeff_powerSeriesToOption]
  simpa [PowerSeries.coeff_map, optionCoeffTate, optionToTate, coeff_optionToPowerSeries] using
    congrArg (MvPowerSeries.coeff d) (congrArg (PowerSeries.coeff n) hmap)

private noncomputable def optionAntidiagonalEmbedding :
    (Sigma fun _ : ℕ × ℕ => (σ →₀ ℕ) × (σ →₀ ℕ)) ↪ ((Option σ →₀ ℕ) × (Option σ →₀ ℕ)) where
  toFun x := (Finsupp.optionElim x.1.1 x.2.1, Finsupp.optionElim x.1.2 x.2.2)
  inj' := by
    intro x y h
    have h11 : x.1.1 = y.1.1 := by
      simpa [Finsupp.optionElim_apply_none] using congrArg (fun p => p.1 none) h
    have h12 : x.1.2 = y.1.2 := by
      simpa [Finsupp.optionElim_apply_none] using congrArg (fun p => p.2 none) h
    have h21 : x.2.1 = y.2.1 := by
      ext t
      simpa [Finsupp.optionElim_apply_some] using congrArg (fun p => p.1 (some t)) h
    have h22 : x.2.2 = y.2.2 := by
      ext t
      simpa [Finsupp.optionElim_apply_some] using congrArg (fun p => p.2 (some t)) h
    cases x with
    | mk x₁ x₂ =>
      cases y with
      | mk y₁ y₂ =>
        have hx1 : x₁ = y₁ := by
          cases x₁
          cases y₁
          simpa using And.intro h11 h12
        have hx2 : x₂ = y₂ := by
          cases x₂
          cases y₂
          simpa using And.intro h21 h22
        have hxy : (x₁, x₂) = (y₁, y₂) := by
          cases hx1
          cases hx2
          rfl
        exact congrArg Prod.toSigma hxy

private lemma antidiagonal_optionElim_eq_map {τ : Type*} [DecidableEq τ] (n : ℕ) (d : τ →₀ ℕ) :
    Finset.map optionAntidiagonalEmbedding
        ((Finset.antidiagonal n).sigma fun _ => Finset.antidiagonal d) =
      Finset.antidiagonal (Finsupp.optionElim n d) := by
  ext p
  simp only [Finset.mem_map, Finset.mem_sigma, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    ext a
    cases a with
    | none =>
        simpa [optionAntidiagonalEmbedding, Finsupp.optionElim_apply_none] using hx1
    | some t =>
        simpa [optionAntidiagonalEmbedding, Finsupp.optionElim_apply_some] using
          congrArg (fun e => e t) hx2
  · intro hp
    refine ⟨⟨(p.1 none, p.2 none), (p.1.some, p.2.some)⟩, ?_, ?_⟩
    · constructor
      · simpa [Finsupp.optionElim_apply_none] using congrArg (fun e => e none) hp
      · ext t
        simpa [Finsupp.optionElim_apply_some] using congrArg (fun e => e (some t)) hp
    · ext a <;> cases a <;> simp [optionAntidiagonalEmbedding]

private lemma sum_antidiagonal_optionElim {τ β : Type*} [DecidableEq τ] [AddCommMonoid β]
    (n : ℕ) (d : τ →₀ ℕ) (F : (Option τ →₀ ℕ) × (Option τ →₀ ℕ) → β) :
    ∑ p ∈ Finset.antidiagonal (Finsupp.optionElim n d), F p =
      ∑ x ∈ Finset.antidiagonal n,
        ∑ y ∈ Finset.antidiagonal d, F (Finsupp.optionElim x.1 y.1, Finsupp.optionElim x.2 y.2) :=
          by
  have h1 : ∑ p ∈ Finset.antidiagonal (Finsupp.optionElim n d), F p = ∑ p ∈ Finset.map (optionAntidiagonalEmbedding) ((Finset.antidiagonal n).sigma fun _ => Finset.antidiagonal d), F p := by rw [antidiagonal_optionElim_eq_map n d]
  have h2 : ∑ p ∈ Finset.map (optionAntidiagonalEmbedding) ((Finset.antidiagonal n).sigma fun _ => Finset.antidiagonal d), F p = ∑ z ∈ (Finset.antidiagonal n).sigma fun _ => Finset.antidiagonal d, F (optionAntidiagonalEmbedding z) := by rw [Finset.sum_map]
  have h3 : ∑ z ∈ (Finset.antidiagonal n).sigma fun _ => Finset.antidiagonal d, F (optionAntidiagonalEmbedding z) = ∑ x ∈ Finset.antidiagonal n, ∑ y ∈ Finset.antidiagonal d, F (Finsupp.optionElim x.1 y.1, Finsupp.optionElim x.2 y.2) := by rw [Finset.sum_sigma']; rfl
  exact h1.trans (h2.trans h3)

noncomputable instance {τ : Type*} : Algebra A (TateAlgebra Unit (TateAlgebra τ A)) :=
  ((algebraMap (TateAlgebra τ A) (TateAlgebra Unit (TateAlgebra τ A))).comp
    (algebraMap A (TateAlgebra τ A))).toAlgebra

noncomputable instance {τ : Type*} :
    IsScalarTower A (TateAlgebra τ A) (TateAlgebra Unit (TateAlgebra τ A)) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma coeff_sum_optionCoeffTate_mul {τ : Type*}
    (f g : TateAlgebra (Option τ) A) (n : ℕ) (d : τ →₀ ℕ) :
    (coeff d) (∑ x ∈ Finset.antidiagonal n, optionCoeffTate f x.1 * optionCoeffTate g x.2).1 =
      ∑ x ∈ Finset.antidiagonal n, ∑ y ∈ Finset.antidiagonal d,
        MvPowerSeries.coeff (Finsupp.optionElim x.1 y.1) f.1 *
          MvPowerSeries.coeff (Finsupp.optionElim x.2 y.2) g.1 := by
  have hsum : (∑ x ∈ Finset.antidiagonal n, optionCoeffTate f x.1 * optionCoeffTate g x.2).1 =
      ∑ x ∈ Finset.antidiagonal n, ((optionCoeffTate f x.1) * optionCoeffTate g x.2).1 := by
    induction Finset.antidiagonal n using Finset.induction_on with
    | empty => simp
    | @insert x s hx hs => simp [hx, hs]
  calc
    _ = (coeff d) (∑ x ∈ Finset.antidiagonal n,
          (((optionCoeffTate f x.1) *
              optionCoeffTate g x.2).1)) := congrArg (coeff d) hsum
    _ = ∑ x ∈ Finset.antidiagonal n,
          ∑ y ∈ Finset.antidiagonal d,
            MvPowerSeries.coeff (Finsupp.optionElim x.1 y.1) (f : MvPowerSeries (Option τ) A) *
              MvPowerSeries.coeff (Finsupp.optionElim x.2 y.2) (g : MvPowerSeries (Option τ) A) :=
                by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp [optionCoeffTate, MvPowerSeries.coeff_mul]

variable (A) in
/-- The algebra equivalence `A{Option τ} ≃ A{τ}{T}` splitting off `none`. -/
noncomputable def optionToTateAlgEquiv (τ : Type*) :
    TateAlgebra (Option τ) A ≃ₐ[A] TateAlgebra Unit (TateAlgebra τ A) where
  toFun := optionToTate
  invFun := tateToOption
  left_inv := tateToOption_optionToTate
  right_inv := optionToTate_tateToOption
  map_mul' := by
    classical
    intro f g
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    apply Subtype.ext
    ext d
    simp [optionToTate, optionCoeffTate, coeff_optionToPowerSeries, PowerSeries.coeff_mul,
      MvPowerSeries.coeff_mul]
    exact (by exact sum_antidiagonal_optionElim n d (fun p : ((Option τ →₀ ℕ) × (Option τ →₀ ℕ)) => MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1) : ∑ p ∈ Finset.antidiagonal (Finsupp.optionElim n d), (coeff p.1) ↑f * (coeff p.2) ↑g = _).trans (coeff_sum_optionCoeffTate_mul f g n d).symm
  map_add' := by
    intro f g
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    apply Subtype.ext
    ext d
    simp [optionToTate, optionCoeffTate, coeff_optionToPowerSeries]
  commutes' := by
    intro r
    classical
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        apply Subtype.ext
        ext d
        have hleft :
            (coeff d) ↑((PowerSeries.coeff 0)
              (↑(((algebraMap A (TateAlgebra (Option τ) A)) r).optionToTate) :
                PowerSeries (TateAlgebra τ A))) =
              (coeff (Finsupp.optionElim 0 d)) ((algebraMap A (MvPowerSeries (Option τ) A)) r) := by
          simpa [optionToTate, optionCoeffTate] using
            (coeff_optionToPowerSeries
              ((algebraMap A (MvPowerSeries (Option τ) A)) r) 0 d)
        rw [hleft]
        have hright :
            (PowerSeries.coeff 0)
              (↑((algebraMap A (TateAlgebra Unit (TateAlgebra τ A))) r) :
                PowerSeries (TateAlgebra τ A)) =
              (algebraMap A (TateAlgebra τ A)) r := by
          change (PowerSeries.coeff 0) (PowerSeries.C ((algebraMap A (TateAlgebra τ A)) r)) =
            (algebraMap A (TateAlgebra τ A)) r
          rw [PowerSeries.coeff_C]
          simp
        rw [hright]
        by_cases hd : d = 0
        · subst hd
          change (coeff (Finsupp.optionElim 0 0)) (MvPowerSeries.C r) = (coeff 0) (MvPowerSeries.C
            r)
          simp [MvPowerSeries.coeff_C]
        · have hne : Finsupp.optionElim 0 d ≠ 0 := by
            intro h
            apply hd
            ext t
            simpa using congrArg (fun e => e (some t)) h
          change (coeff (Finsupp.optionElim 0 d)) (MvPowerSeries.C r) = (coeff d) (MvPowerSeries.C
            r)
          simp [MvPowerSeries.coeff_C, hd, hne]
    | succ n =>
        apply Subtype.ext
        ext d
        simp [optionToTate, optionCoeffTate]
        have hright : (PowerSeries.coeff (n + 1))
            ((algebraMap A (TateAlgebra Unit (TateAlgebra τ A))) r).1 = 0 := by
          change (PowerSeries.coeff _) (PowerSeries.C ((algebraMap A (TateAlgebra τ A)) r)) = 0
          simp
        rw [hright]
        have hne : Finsupp.optionElim (n + 1) d ≠ 0 := by
          intro h
          exact Nat.succ_ne_zero n (by simpa using congrArg (fun e => e none) h)
        change (coeff (Finsupp.optionElim (n + 1) d)) (MvPowerSeries.C r : MvPowerSeries (Option τ)
          A) = 0
        simp [MvPowerSeries.coeff_C, hne]

end OptionDecomposition

section PolynomialSubstitution

variable {ι τ : Type*} [Finite ι] [Finite τ]

omit [Finite τ] in
omit [NormMulClass A] [CompleteSpace A] in
lemma toTate_mvPolynomialProd_norm_le_one
    (d : ι →₀ ℕ) (a : ι → MvPolynomial τ A)
    (ha : ∀ i, ‖(a i).toTate‖ ≤ 1) :
    ‖(d.prod fun i n => a i ^ n).toTate‖ ≤ 1 := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [show d.prod (fun i n => a i ^ n) = ∏ i, a i ^ d i by
    rw [Finsupp.prod_fintype]
    intro i
    simp]
  rw [show (∏ i, a i ^ d i).toTate = ∏ i, (a i ^ d i).toTate by
    simp [_root_.MvPolynomial.toTate]]
  refine le_trans (Finset.norm_prod_le _ _) ?_
  refine Finset.prod_le_one (fun i hi => norm_nonneg _) ?_
  intro i hi
  calc _ = ‖(((a i).toTate) ^ d i)‖ := by simp [MvPolynomial.toTate]
    _ ≤ ‖(a i).toTate‖ ^ d i := norm_pow_le (((a i).toTate)) (d i)
    _ ≤ 1 := pow_le_one₀ (norm_nonneg _) (ha i)

omit [Finite τ] [NormMulClass A] [CompleteSpace A] in
lemma coeff_mvPolynomialProd_norm_le_one
    (d : ι →₀ ℕ) (a : ι → MvPolynomial τ A)
    (ha : ∀ i, ‖(a i).toTate‖ ≤ 1) (e : τ →₀ ℕ) :
    ‖MvPolynomial.coeff e (d.prod fun i n => a i ^ n)‖ ≤ 1 := by
  have hcoeff : ‖MvPowerSeries.coeff e (((d.prod fun i n => a i ^ n).toTate).1)‖ ≤
      ‖(d.prod fun i n => a i ^ n).toTate‖ := by
    exact TateAlgebra.coeff_norm_le _ _
  exact le_trans (by simpa [MvPolynomial.toTate_coe] using hcoeff)
    (toTate_mvPolynomialProd_norm_le_one d a ha)

/-- Evaluate a multivariable polynomial at chosen elements of a Tate algebra. -/
noncomputable def mvPolynomialSubstTate
    (a : ι → TateAlgebra τ A) : MvPolynomial ι A →ₐ[A] TateAlgebra τ A :=
  MvPolynomial.aeval a

end PolynomialSubstitution

section TatePolynomialSubstitution

variable {ι τ : Type*} [Fintype ι] [Finite τ]

omit [CompleteSpace A] [Finite τ] in
omit [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] in
lemma hasSubst_mvPolynomial
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0) :
    MvPowerSeries.HasSubst (fun i => (a i : MvPowerSeries τ A)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro i
  simpa [MvPolynomial.constantCoeff_eq] using ha0 i

omit [Finite τ] [CompleteSpace A] in
lemma isTate_subst_mvPolynomial
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i, ‖((a i).toTate)‖ ≤ 1)
    {f : MvPowerSeries ι A} (hf : IsTate ι A f) :
    IsTate τ A (MvPowerSeries.subst (fun i => (a i : MvPowerSeries τ A)) f) := by
  let aPS : ι → MvPowerSeries τ A := fun i => (a i : MvPowerSeries τ A)
  have haPS : MvPowerSeries.HasSubst aPS := hasSubst_mvPolynomial a ha0
  rw [isTate_iff] at hf ⊢
  intro ε hε
  let S : Set (ι →₀ ℕ) := {d | ε ≤ ‖MvPowerSeries.coeff d f‖}
  have hSfin : S.Finite := hf ε hε
  let p : (ι →₀ ℕ) → MvPolynomial τ A := fun d => d.prod fun i n => a i ^ n
  let T : Set (τ →₀ ℕ) :=
    {e | ε ≤ ‖MvPowerSeries.coeff e (MvPowerSeries.subst aPS f)‖}
  have hAeval (q : MvPolynomial ι A) :
      MvPolynomial.aeval aPS q = ((MvPolynomial.aeval a q : MvPolynomial τ A) : MvPowerSeries τ A)
        := by
    let coeAlg : MvPolynomial τ A →ₐ[A] MvPowerSeries τ A :=
      MvPolynomial.coeToMvPowerSeries.algHom A
    have hcomp : coeAlg.comp (MvPolynomial.aeval a) = MvPolynomial.aeval aPS := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [aPS, coeAlg]
    have hq := congrArg (fun F : MvPolynomial ι A →ₐ[A] MvPowerSeries τ A => F q) hcomp
    simpa [coeAlg] using hq.symm
  have hpcast :
      ∀ d : ι →₀ ℕ,
        ((p d : MvPolynomial τ A) : MvPowerSeries τ A) = d.prod fun s e => aPS s ^ e := by
    intro d
    have hp : MvPolynomial.aeval a (MvPolynomial.monomial d (1 : A)) = p d := by
      rw [MvPolynomial.aeval_monomial]
      simp [p]
    calc
      ((p d : MvPolynomial τ A) : MvPowerSeries τ A)
          = ((MvPolynomial.aeval a (MvPolynomial.monomial d (1 : A)) : MvPolynomial τ A) :
              MvPowerSeries τ A) := by
                rw [hp]
      _ = MvPolynomial.aeval aPS (MvPolynomial.monomial d (1 : A)) := by
            rw [hAeval]
      _ = MvPowerSeries.subst aPS
            (((MvPolynomial.monomial d (1 : A) : MvPolynomial ι A)) : MvPowerSeries ι A) := by
            rw [MvPowerSeries.subst_coe (MvPolynomial.monomial d (1 : A))]
      _ = (algebraMap A (MvPowerSeries τ A) (1 : A)) * d.prod (fun s e => aPS s ^ e) := by
            simpa using (MvPowerSeries.subst_monomial haPS d (1 : A))
      _ = d.prod (fun s e => aPS s ^ e) := by simp
  have hTsubset : T ⊆ ⋃ d ∈ S, ((p d).support : Set (τ →₀ ℕ)) := by
    intro e he
    have hcoeff :
        MvPowerSeries.coeff e (MvPowerSeries.subst aPS f) =
          ∑ᶠ d : ι →₀ ℕ,
            MvPowerSeries.coeff d f •
              MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A) := by
      rw [MvPowerSeries.coeff_subst haPS f e]
      apply finsum_congr
      intro d
      rw [hpcast d]
    let g : (ι →₀ ℕ) → A := fun d =>
      MvPowerSeries.coeff d f •
        MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A)
    have hgfin : Function.HasFiniteSupport g := by
      simpa [g, hpcast] using MvPowerSeries.coeff_subst_finite haPS f e
    let s : Finset (ι →₀ ℕ) := (show (Function.support g).Finite from hgfin).toFinset
    have hs_eq : ∑ᶠ d : ι →₀ ℕ, g d = ∑ d ∈ s, g d := by
      simpa [s] using finsum_eq_sum g (show (Function.support g).Finite from hgfin)
    have he_sum : ε ≤ ‖∑ d ∈ s, g d‖ := by
      have : ε ≤ ‖∑ᶠ d : ι →₀ ℕ, g d‖ := by
        simpa [T, hcoeff, g] using he
      rw [hs_eq] at this
      simpa [T, aPS] using this
    have hsne : s.Nonempty := by
      by_contra hs
      have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have : ‖∑ d ∈ s, g d‖ = 0 := by simp [hs0]
      exact (not_lt_of_ge he_sum) (by simpa [this] using hε)
    obtain ⟨d, hd, hsum⟩ := IsUltrametricDist.exists_norm_finset_sum_le s g
    have hdmem : d ∈ s := hd hsne
    have hdlarge : ε ≤ ‖g d‖ := le_trans he_sum hsum
    have hcoeff_bd_poly : ‖MvPolynomial.coeff e (p d)‖ ≤ 1 := by
      simpa [p] using coeff_mvPolynomialProd_norm_le_one d a ha1 e
    have hcoeff_bd :
        ‖MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A)‖ ≤ 1 := by
      simpa [MvPolynomial.coeff_coe] using hcoeff_bd_poly
    have hdS : d ∈ S := by
      change ε ≤ ‖MvPowerSeries.coeff d f‖
      calc
        ε ≤ ‖g d‖ := hdlarge
        _ ≤ ‖MvPowerSeries.coeff d f‖ * ‖MvPowerSeries.coeff e ((p d : MvPolynomial τ A) :
          MvPowerSeries τ A)‖ := by
          simp [g, smul_eq_mul, norm_mul]
        _ ≤ ‖MvPowerSeries.coeff d f‖ * 1 := by
          gcongr
        _ = ‖MvPowerSeries.coeff d f‖ := by ring
    have hgd_ne : g d ≠ 0 := by
      intro h0
      have : ‖g d‖ = 0 := by simp [h0]
      exact (not_lt_of_ge hdlarge) (by simpa [this] using hε)
    have hpe_ne :
        MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A) ≠ 0 := by
      intro h0
      apply hgd_ne
      dsimp [g]
      have h0' : MvPolynomial.coeff e (p d) = 0 := by
        simpa [MvPolynomial.coeff_coe] using h0
      rw [h0', mul_zero]
    refine Set.mem_iUnion.2 ⟨d, Set.mem_iUnion.2 ⟨hdS, ?_⟩⟩
    exact MvPolynomial.mem_support_iff.mpr (by simpa [MvPolynomial.coeff_coe] using hpe_ne)
  exact (hSfin.biUnion fun d hd => (p d).support.finite_toSet).subset hTsubset

/-- Substitute bounded zero-constant polynomials for Tate variables, as an algebra map. -/
noncomputable def tateMvPolynomialSubst
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i,
      ‖(((a i).toTate) :
          TateAlgebra τ A)‖ ≤ 1) :
    TateAlgebra ι A →ₐ[A] TateAlgebra τ A := by
  let aPS : ι → MvPowerSeries τ A := fun i => (a i : MvPowerSeries τ A)
  let haPS : MvPowerSeries.HasSubst aPS := hasSubst_mvPolynomial a ha0
  let φ : MvPowerSeries ι A →ₐ[A] MvPowerSeries τ A := MvPowerSeries.substAlgHom haPS
  refine (φ.comp (IsScalarTower.toAlgHom A (TateAlgebra ι A) (MvPowerSeries ι A))).codRestrict _
    ?_
  intro f
  simpa [tateSubalgebra, φ, aPS] using isTate_subst_mvPolynomial a ha0 ha1 f.2

omit [Finite τ] [CompleteSpace A] in
@[simp]
lemma tateMvPolynomialSubst_coe
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i, ‖((a i).toTate)‖ ≤ 1) (f : TateAlgebra ι A) :
    (((tateMvPolynomialSubst a ha0 ha1) f) : MvPowerSeries τ A) =
      MvPowerSeries.subst (fun i => (a i : MvPowerSeries τ A)) (f : MvPowerSeries ι A) := by
  let aPS : ι → MvPowerSeries τ A := fun i => (a i : MvPowerSeries τ A)
  let haPS : MvPowerSeries.HasSubst aPS := hasSubst_mvPolynomial a ha0
  let φ : MvPowerSeries ι A →ₐ[A] MvPowerSeries τ A := MvPowerSeries.substAlgHom haPS
  have hφ : ∀ x : TateAlgebra ι A,
      φ ((IsScalarTower.toAlgHom A (TateAlgebra ι A) (MvPowerSeries ι A)) x) ∈ tateSubalgebra τ A :=
        by
    intro x
    simpa [tateSubalgebra, φ, aPS] using isTate_subst_mvPolynomial a ha0 ha1 x.2
  change
    ((((φ.comp (IsScalarTower.toAlgHom A (TateAlgebra ι A) (MvPowerSeries ι A))).codRestrict
        (tateSubalgebra τ A) hφ) f)) =
      MvPowerSeries.subst (fun i => (a i : MvPowerSeries τ A)) (f : MvPowerSeries ι A)
  have hcod :
      ((((φ.comp (IsScalarTower.toAlgHom A (TateAlgebra ι A) (MvPowerSeries ι A))).codRestrict
          (tateSubalgebra τ A) hφ) f)) =
        (φ.comp (IsScalarTower.toAlgHom A (TateAlgebra ι A) (MvPowerSeries ι A))) f :=
    RingHom.codRestrict_apply
      ((φ.comp (IsScalarTower.toAlgHom A (TateAlgebra ι A) (MvPowerSeries ι A))).toRingHom)
        (tateSubalgebra τ A) hφ f
  rw [hcod]
  simpa [φ, aPS] using
    congrArg (MvPowerSeries.subst (fun i => (a i : MvPowerSeries τ A)))
      (show ((algebraMap (TateAlgebra ι A) (MvPowerSeries ι A)) f) = ↑f from rfl)

omit [Finite τ] [CompleteSpace A] in
@[simp]
lemma tateMvPolynomialSubst_X
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i, ‖((a i).toTate)‖ ≤ 1)
    (i : ι) :
    tateMvPolynomialSubst a ha0 ha1 (TateAlgebra.X i) = (a i).toTate := by
  let aPS : ι → MvPowerSeries τ A := fun j => (a j : MvPowerSeries τ A)
  have haPS : MvPowerSeries.HasSubst aPS := hasSubst_mvPolynomial a ha0
  apply Subtype.ext
  calc
    (((tateMvPolynomialSubst a ha0 ha1) (TateAlgebra.X i)) : MvPowerSeries τ A) =
        MvPowerSeries.subst aPS (MvPowerSeries.X i) := by
      rw [tateMvPolynomialSubst_coe a ha0 ha1
        (TateAlgebra.X i)]
      rfl
    _ = aPS i := (MvPowerSeries.subst_X haPS i)
    _ = (((a i).toTate) : MvPowerSeries τ A) := by
      simp [aPS, MvPolynomial.toTate_coe]

omit [Finite τ] [CompleteSpace A] in
lemma tateMvPolynomialSubst_comp {υ : Type*} [Fintype τ]
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i, ‖((a i).toTate)‖ ≤ 1)
    (b : τ → MvPolynomial υ A)
    (hb0 : ∀ i, MvPolynomial.constantCoeff (b i) = 0)
    (hb1 : ∀ i, ‖((b i).toTate : TateAlgebra υ A)‖ ≤ 1)
    (c : ι → MvPolynomial υ A)
    (hc : ∀ i, c i = MvPolynomial.aeval b (a i))
    (hc0 : ∀ i, MvPolynomial.constantCoeff (c i) = 0)
    (hc1 : ∀ i, ‖((c i).toTate : TateAlgebra υ A)‖ ≤ 1) :
    (tateMvPolynomialSubst b hb0 hb1).comp (tateMvPolynomialSubst a ha0 ha1) =
      tateMvPolynomialSubst c hc0 hc1 := by
  let aPS : ι → MvPowerSeries τ A := fun i => (a i : MvPowerSeries τ A)
  let bPS : τ → MvPowerSeries υ A := fun i => (b i : MvPowerSeries υ A)
  let cPS : ι → MvPowerSeries υ A := fun i => (c i : MvPowerSeries υ A)
  have haPS : MvPowerSeries.HasSubst aPS := hasSubst_mvPolynomial a ha0
  have hbPS : MvPowerSeries.HasSubst bPS := hasSubst_mvPolynomial b hb0
  have hBaeval (q : MvPolynomial τ A) : MvPolynomial.aeval bPS q = (MvPolynomial.aeval b q) := by
    have hcomp : (MvPolynomial.coeToMvPowerSeries.algHom A).comp (MvPolynomial.aeval b) =
        MvPolynomial.aeval bPS := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [bPS]
    exact (congrArg (fun F : MvPolynomial τ A →ₐ[A] MvPowerSeries υ A => F q) hcomp).symm
  have hBC : (fun i => MvPowerSeries.subst bPS (aPS i)) = cPS := by
    funext i
    rw [MvPowerSeries.subst_coe (a i)]
    simpa [aPS, cPS, hc i] using hBaeval (a i)
  apply AlgHom.ext
  intro f
  apply Subtype.ext
  calc
    _ = MvPowerSeries.subst bPS (MvPowerSeries.subst aPS f.1) := by simp [aPS, bPS]
    _ = MvPowerSeries.subst (fun i => MvPowerSeries.subst bPS (aPS i)) f.1 :=
      congrArg (fun F => F ((f : TateAlgebra ι A) : MvPowerSeries ι A))
        (MvPowerSeries.subst_comp_subst haPS hbPS)
    _ = MvPowerSeries.subst cPS ((f : TateAlgebra ι A) : MvPowerSeries ι A) := by
      simpa using congrArg (fun D => MvPowerSeries.subst D (f : MvPowerSeries ι A)) hBC
    _ = (((tateMvPolynomialSubst c hc0 hc1) f : TateAlgebra υ A) : MvPowerSeries υ A) := by
      simp [cPS]

omit [Finite τ] [CompleteSpace A] in
lemma forall_coeff_le_tateMvPolynomialSubst
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i, ‖((a i).toTate)‖ ≤ 1)
    (f : TateAlgebra ι A) {C : ℝ} (hC : 0 ≤ C) (hcoeff : ∀ d, ‖MvPowerSeries.coeff d f.1‖ ≤ C) :
    ∀ e, ‖MvPowerSeries.coeff e ((tateMvPolynomialSubst a ha0 ha1 f).1)‖ ≤ C := by
  let aPS : ι → MvPowerSeries τ A := fun i => (a i : MvPowerSeries τ A)
  have haPS : MvPowerSeries.HasSubst aPS := hasSubst_mvPolynomial a ha0
  let p : (ι →₀ ℕ) → MvPolynomial τ A := fun d => d.prod fun i n => a i ^ n
  have hpcast : ∀ d : ι →₀ ℕ, d.prod (fun s e => aPS s ^ e) =
      ((p d : MvPolynomial τ A) : MvPowerSeries τ A) := by
    intro d
    simp [aPS, p, Finsupp.prod]
    trans MvPolynomial.coeToMvPowerSeries.ringHom (∏ x ∈ d.support, a x ^ d x)
    · rw [map_prod]
      simp
    · rfl
  intro e
  have hcoeff_subst :
      MvPowerSeries.coeff e ((tateMvPolynomialSubst a ha0 ha1 f).1) =
        ∑ᶠ d : ι →₀ ℕ,
          MvPowerSeries.coeff d f.1 •
            MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A) := by
    calc
      MvPowerSeries.coeff e ((tateMvPolynomialSubst a ha0 ha1 f).1) =
          MvPowerSeries.coeff e (MvPowerSeries.subst aPS ((f : TateAlgebra ι A) : MvPowerSeries ι
            A)) := by
        simp [aPS]
      _ = ∑ᶠ d : ι →₀ ℕ,
            MvPowerSeries.coeff d f.1 •
              MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A) := by
        simpa [smul_eq_mul, p, hpcast] using MvPowerSeries.coeff_subst haPS f.1 e
  let g : (ι →₀ ℕ) → A := fun d =>
    MvPowerSeries.coeff d f.1 •
      MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A)
  have hgfin : Function.HasFiniteSupport g := by
    simpa [g, p, hpcast] using
      (MvPowerSeries.coeff_subst_finite haPS f.1 e)
  let s : Finset (ι →₀ ℕ) := Set.Finite.toFinset hgfin
  have hs_eq : (∑ᶠ d : ι →₀ ℕ, g d) = s.sum g := by
    simpa [s] using finsum_eq_sum g hgfin
  have hterm : ∀ d ∈ s, ‖g d‖ ≤ C := by
    intro d hd
    have hcoeff_bd_poly :
        ‖MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A)‖ ≤ 1 := by
      simpa [p] using coeff_mvPolynomialProd_norm_le_one d a ha1 e
    calc
      ‖g d‖ = ‖MvPowerSeries.coeff d f.1‖ *
          ‖MvPowerSeries.coeff e ((p d : MvPolynomial τ A) : MvPowerSeries τ A)‖ := by
        simp [g, smul_eq_mul, norm_mul]
      _ ≤ ‖MvPowerSeries.coeff d f.1‖ * 1 := by
        gcongr
      _ = ‖MvPowerSeries.coeff d f.1‖ := by ring
      _ ≤ C := hcoeff d
  have hsum_le :
      ∀ t : Finset (ι →₀ ℕ), (∀ d ∈ t, ‖g d‖ ≤ C) → ‖t.sum g‖ ≤ C := by
    intro t ht
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC ht
  rw [hcoeff_subst, hs_eq]
  simpa [g] using hsum_le s hterm

omit [Finite τ] [CompleteSpace A] in
lemma forall_coeff_le_one_tateMvPolynomialSubst
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i, ‖((a i).toTate)‖ ≤ 1)
    (f : TateAlgebra ι A) (hcoeff : ∀ d, ‖MvPowerSeries.coeff d f.1‖ ≤ 1) :
    ∀ e, ‖MvPowerSeries.coeff e ((tateMvPolynomialSubst a ha0 ha1 f).1)‖ ≤ 1 := by
  exact forall_coeff_le_tateMvPolynomialSubst a ha0 ha1 f (show 0 ≤ (1 : ℝ) by norm_num) hcoeff

omit [Finite τ] [CompleteSpace A] in
lemma isContractiveHom_tateMvPolynomialSubst
    (a : ι → MvPolynomial τ A) (ha0 : ∀ i, MvPolynomial.constantCoeff (a i) = 0)
    (ha1 : ∀ i,
      ‖(((a i).toTate) :
          TateAlgebra τ A)‖ ≤ 1) :
    IsContractiveHom (tateMvPolynomialSubst a ha0 ha1) := by
  intro f
  change ‖tateMvPolynomialSubst a ha0 ha1 f‖ ≤ ‖f‖
  by_cases hzero : tateMvPolynomialSubst a ha0 ha1 f = 0
  · simp [hzero]
  · obtain ⟨e, he⟩ :=
      TateAlgebra.exists_coeff_norm_eq_norm (tateMvPolynomialSubst a ha0 ha1 f) hzero
    rw [← he]
    exact forall_coeff_le_tateMvPolynomialSubst a ha0 ha1 f (norm_nonneg _)
      (fun d => TateAlgebra.coeff_norm_le f d) e

end TatePolynomialSubstitution

section TriangularAutomorphism

variable {τ : Type*} [Fintype τ]

variable (A) in
/-- Polynomial coordinates for the triangular map `X_t ↦ X_t + T ^ d t`. -/
noncomputable def optionTriangularForwardPoly (d : τ → ℕ) :
    Option τ → MvPolynomial (Option τ) A
  | none => MvPolynomial.X none
  | some t => MvPolynomial.X (some t) + MvPolynomial.X none ^ d t

variable (A) in
/-- Polynomial coordinates for the inverse triangular map `X_t ↦ X_t - T ^ d t`. -/
noncomputable def optionTriangularInversePoly (d : τ → ℕ) :
    Option τ → MvPolynomial (Option τ) A
  | none => MvPolynomial.X none
  | some t => MvPolynomial.X (some t) - MvPolynomial.X none ^ d t

omit [CompleteSpace A] [Fintype τ] in
omit [NormOneClass A] [NormMulClass A] in
lemma toTate_option_X (i : Option τ) :
    ((MvPolynomial.X i).toTate : TateAlgebra (Option τ) A) = TateAlgebra.X i := by
  simp [MvPolynomial.toTate]

/-- Weighted degree where `none` has weight `1` and `some t` has weight `d t`. -/
noncomputable def optionWeight (d : τ → ℕ) (e : Option τ →₀ ℕ) : ℕ :=
  e none + ∑ t, e (some t) * d t

/-- Encode a finite tuple of base-`B` digits as a natural number. -/
noncomputable def finEncode (B : ℕ) : ∀ n : ℕ, (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, a => a 0 + B * finEncode B n (fun i => a i.succ)

/-- Exponential weights used to make `optionWeight` injective on a finite set. -/
noncomputable def optionDigitWeight {n : ℕ} (B : ℕ) : Fin n → ℕ :=
  fun i => B ^ (i.1 + 1)

lemma finEncode_injective {B : ℕ} (hB : 1 < B) :
    ∀ {n : ℕ} {a b : Fin n → ℕ},
      (∀ i, a i < B) → (∀ i, b i < B) → finEncode B n a = finEncode B n b → a = b
  | 0, a, b, ha, hb, h => by
      funext i
      exact Fin.elim0 i
  | n + 1, a, b, ha, hb, h => by
      have hmod := congrArg (fun x : ℕ => x % B) h
      have h0 : a 0 = b 0 := by
        simpa [finEncode, Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt (ha 0),
          Nat.mod_eq_of_lt (hb 0)] using hmod
      have htailEq :
          finEncode B n (fun i : Fin n => a i.succ) = finEncode B n (fun i : Fin n => b i.succ) :=
            by
        have hmul : B * finEncode B n (fun i : Fin n => a i.succ) =
            B * finEncode B n (fun i : Fin n => b i.succ) := by
          simpa [finEncode, h0] using h
        have hB0 : 0 < B := by omega
        exact Nat.eq_of_mul_eq_mul_left hB0 hmul
      have htail : (fun i : Fin n => a i.succ) = fun i : Fin n => b i.succ :=
        finEncode_injective hB (fun i => ha i.succ) (fun i => hb i.succ) htailEq
      funext i
      cases i using Fin.cases with
      | zero => exact h0
      | succ i => exact congrFun htail i

lemma finEncode_eq_sum {n B : ℕ} (a : Fin (n + 1) → ℕ) :
    finEncode B (n + 1) a = a 0 + ∑ i : Fin n, a i.succ * B ^ (i.1 + 1) := by
  induction n with
  | zero =>
      simp [finEncode]
  | succ n ih =>
      rw [finEncode, ih (fun i : Fin (n + 1) => a i.succ)]
      rw [mul_add, Finset.mul_sum, Fin.sum_univ_succ]
      simp [pow_succ, mul_assoc, mul_comm, add_left_comm, add_comm]

lemma optionWeight_optionDigitWeight_eq_finEncode {n B : ℕ} (e : Option (Fin n) →₀ ℕ) :
    optionWeight (optionDigitWeight B) e =
      finEncode B (n + 1) (fun i => e ((finSuccEquiv n) i)) := by
  rw [finEncode_eq_sum]
  simp [optionWeight, optionDigitWeight, finSuccEquiv_zero, finSuccEquiv_succ]

lemma optionWeight_optionDigitWeight_injective {n B : ℕ} (hB : 1 < B)
    {e₁ e₂ : Option (Fin n) →₀ ℕ}
    (h₁ : ∀ i, e₁ i < B) (h₂ : ∀ i, e₂ i < B)
    (hEq : optionWeight (optionDigitWeight B) e₁ = optionWeight (optionDigitWeight B) e₂) :
    e₁ = e₂ := by
  have hEnc :
      finEncode B (n + 1) (fun i => e₁ ((finSuccEquiv n) i)) =
        finEncode B (n + 1) (fun i => e₂ ((finSuccEquiv n) i)) := by
    rw [← optionWeight_optionDigitWeight_eq_finEncode,
      ← optionWeight_optionDigitWeight_eq_finEncode]
    exact hEq
  have hfun := finEncode_injective hB
      (fun i => by simpa [finSuccEquiv_zero, finSuccEquiv_succ] using h₁ ((finSuccEquiv n) i))
      (fun i => by simpa [finSuccEquiv_zero, finSuccEquiv_succ] using h₂ ((finSuccEquiv n) i))
      hEnc
  ext i
  have := congrFun hfun ((finSuccEquiv n).symm i)
  simpa using this

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] [NormOneClass A] [NormMulClass A] in
lemma optionEquivLeft_optionTriangularForwardPoly_none (d : τ → ℕ) :
    (MvPolynomial.optionEquivLeft A τ) (optionTriangularForwardPoly A d none) =
      Polynomial.X := by
  simp [optionTriangularForwardPoly, MvPolynomial.optionEquivLeft_X_none]

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] in
omit [NormOneClass A] [NormMulClass A] in
lemma optionEquivLeft_optionTriangularForwardPoly_some (d : τ → ℕ) (t : τ) :
    (MvPolynomial.optionEquivLeft A τ) (optionTriangularForwardPoly A d (some t)) =
      Polynomial.C (MvPolynomial.X t) + Polynomial.X ^ d t := by
  simp [optionTriangularForwardPoly, MvPolynomial.optionEquivLeft_X_some,
    MvPolynomial.optionEquivLeft_X_none]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma coeff_constantCoeff_optionEquivLeft_monomial (d : τ → ℕ)
    (e : Option τ →₀ ℕ) (n : ℕ) :
    MvPolynomial.constantCoeff
      (((MvPolynomial.optionEquivLeft A τ)
        (MvPolynomial.monomial e (1 : A) |>
          MvPolynomial.aeval (optionTriangularForwardPoly A d))).coeff n) =
      if n = optionWeight d e then 1 else 0 := by
  let p : MvPolynomial (Option τ) A :=
    (MvPolynomial.aeval (optionTriangularForwardPoly A d))
      (MvPolynomial.monomial e (1 : A))
  have hpow (t : τ) :
      Polynomial.map (MvPolynomial.constantCoeff : MvPolynomial τ A →+* A)
        ((Polynomial.C (MvPolynomial.X t) + Polynomial.X ^ d t) ^ e (some t)) =
        Polynomial.X ^ (d t * e (some t)) := by
    rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow]
    simp [MvPolynomial.constantCoeff_X]
    rw [pow_mul]
  have hp :
      (Polynomial.map (MvPolynomial.constantCoeff : MvPolynomial τ A →+* A))
          ((MvPolynomial.optionEquivLeft A τ) p) =
        (Polynomial.X ^ optionWeight d e : Polynomial A) := by
    subst p
    rw [MvPolynomial.aeval_monomial]
    calc
      Polynomial.map MvPolynomial.constantCoeff
          ((MvPolynomial.optionEquivLeft A τ)
            (algebraMap A (MvPolynomial (Option τ) A) 1 *
              e.prod fun i m => optionTriangularForwardPoly A d i ^ m))
          =
          Polynomial.X ^ e none *
            Polynomial.map MvPolynomial.constantCoeff
              (∏ t, (Polynomial.C (MvPolynomial.X t) + Polynomial.X ^ d t) ^ e (some t)) := by
        simp [optionEquivLeft_optionTriangularForwardPoly_none,
          optionEquivLeft_optionTriangularForwardPoly_some]
      _ = Polynomial.X ^ e none * Polynomial.X ^ ∑ t, d t * e (some t) := by
        rw [show Polynomial.map MvPolynomial.constantCoeff
            (∏ t, (Polynomial.C (MvPolynomial.X t) + Polynomial.X ^ d t) ^ e (some t)) =
            Polynomial.X ^ ∑ t, d t * e (some t) by
          rw [show (∏ t, (Polynomial.C (MvPolynomial.X t) + Polynomial.X ^ d t) ^ e (some t)) =
              ∏ t ∈ Finset.univ, (Polynomial.C (MvPolynomial.X t) + Polynomial.X ^ d t) ^ e (some t)
                by
            simp]
          rw [Polynomial.map_prod]
          simp_rw [hpow]
          rw [show (∏ x, Polynomial.X ^ (d x * e (some x)) : Polynomial A) =
              ∏ x ∈ Finset.univ, Polynomial.X ^ (d x * e (some x)) by simp]
          exact Finset.prod_pow_eq_pow_sum Finset.univ
            (fun t => d t * e (some t)) (Polynomial.X : Polynomial A)]
      _ = Polynomial.X ^ optionWeight d e := by
        rw [← pow_add]
        congr
        simp [Nat.mul_comm]
  have hcoeff := congrArg (fun q : Polynomial A => q.coeff n) hp
  simpa [Polynomial.coeff_map] using hcoeff

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] in
omit [NormOneClass A] [NormMulClass A] in
lemma monomial_eq_smul_monomial_one (e : Option τ →₀ ℕ) (a : A) :
    MvPolynomial.monomial e a = a • MvPolynomial.monomial e (1 : A) := by
  classical
  ext d
  by_cases hd : d = e
  · subst hd
    simp
  · simp [MvPolynomial.coeff_monomial]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma coeff_constantCoeff_optionEquivLeft_monomial' (d : τ → ℕ)
    (e : Option τ →₀ ℕ) (a : A) (n : ℕ) :
    MvPolynomial.constantCoeff
      (((MvPolynomial.optionEquivLeft A τ)
        (MvPolynomial.monomial e a |>
          MvPolynomial.aeval (optionTriangularForwardPoly A d))).coeff n) =
      if n = optionWeight d e then a else 0 := by
  rw [monomial_eq_smul_monomial_one]
  simp only [map_smul, Polynomial.coeff_smul, MvPolynomial.constantCoeff_smul]
  rw [coeff_constantCoeff_optionEquivLeft_monomial d e n]
  split_ifs with h
  · simp
  · simp

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma coeff_constantCoeff_optionEquivLeft_sum_monomial (d : τ → ℕ)
    (s : Finset (Option τ →₀ ℕ)) (c : (Option τ →₀ ℕ) → A) (n : ℕ) :
    MvPolynomial.constantCoeff
      (((MvPolynomial.optionEquivLeft A τ)
        ((Finset.sum s fun e => MvPolynomial.monomial e (c e)) |>
          MvPolynomial.aeval (optionTriangularForwardPoly A d))).coeff n) =
      Finset.sum s fun e => if n = optionWeight d e then c e else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp only [map_add, Polynomial.coeff_add]
      rw [coeff_constantCoeff_optionEquivLeft_monomial' d a (c a) n]
      congr 1

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] [NormOneClass A] [NormMulClass A] in
lemma optionTriangularForwardPoly_constantCoeff (d : τ → ℕ) (hd : ∀ t, 0 < d t) (i : Option τ) :
    MvPolynomial.constantCoeff (optionTriangularForwardPoly A d i) = 0 := by
  classical
  cases i with
  | none =>
      simp [optionTriangularForwardPoly]
  | some t =>
      rw [optionTriangularForwardPoly]
      have hne : (Finsupp.single (none : Option τ) (d t) : Option τ →₀ ℕ) ≠ 0 := by
        intro h
        have h' := congrArg (fun e => e none) h
        exact (hd t).ne' (by simpa using h')
      simp [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_X_pow, hne]

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] in
omit [NormOneClass A] [NormMulClass A] in
lemma optionTriangularInversePoly_constantCoeff (d : τ → ℕ) (hd : ∀ t, 0 < d t) (i : Option τ) :
    MvPolynomial.constantCoeff (optionTriangularInversePoly A d i) = 0 := by
  classical
  cases i with
  | none =>
      simp [optionTriangularInversePoly]
  | some t =>
      rw [optionTriangularInversePoly, sub_eq_add_neg]
      have hne : (Finsupp.single (none : Option τ) (d t) : Option τ →₀ ℕ) ≠ 0 := by
        intro h
        have h' := congrArg (fun e => e none) h
        exact (hd t).ne' (by simpa using h')
      simp [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_X_pow, hne]

omit [NormMulClass A] [CompleteSpace A] [Fintype τ] in
lemma optionTriangularForwardPoly_norm_le_one (d : τ → ℕ) :
    ∀ i, ‖((optionTriangularForwardPoly A d i).toTate :
      TateAlgebra (Option τ) A)‖ ≤ 1 := by
  intro i
  cases i with
  | none =>
      simpa [optionTriangularForwardPoly, toTate_option_X] using
        (TateAlgebra.norm_X_le_one (none : Option τ))
  | some t =>
      rw [optionTriangularForwardPoly, map_add]
      have hpow : ‖(((MvPolynomial.X (none : Option τ) ^ d t).toTate) :
          TateAlgebra (Option τ) A)‖ ≤ 1 := by
        rw [map_pow, toTate_option_X none]
        exact le_trans
          (by
            simpa using
              norm_pow_le
                (TateAlgebra.X (none : Option τ) : TateAlgebra (Option τ) A) (d t))
          (pow_le_one₀ (norm_nonneg _) (TateAlgebra.norm_X_le_one (none : Option τ)))
      refine le_trans
        (IsUltrametricDist.norm_add_le_max
          ((((MvPolynomial.X (some t : Option τ))).toTate :
            TateAlgebra (Option τ) A))
          ((((MvPolynomial.X (none : Option τ) ^ d t)).toTate :
            TateAlgebra (Option τ) A))) ?_
      refine max_le ?_ ?_
      · rw [toTate_option_X (some t)]
        exact TateAlgebra.norm_X_le_one (some t : Option τ)
      · exact hpow

omit [NormMulClass A] [CompleteSpace A] [Fintype τ] in
lemma optionTriangularInversePoly_norm_le_one (d : τ → ℕ) :
    ∀ i, ‖((optionTriangularInversePoly A d i).toTate :
      TateAlgebra (Option τ) A)‖ ≤ 1 := by
  intro i
  cases i with
  | none =>
      simpa [optionTriangularInversePoly, toTate_option_X] using
        (TateAlgebra.norm_X_le_one (none : Option τ))
  | some t =>
      rw [optionTriangularInversePoly, sub_eq_add_neg, map_add, map_neg]
      have hpow : ‖((MvPolynomial.X none ^ d t).toTate : TateAlgebra (Option τ) A)‖ ≤ 1 := by
        rw [map_pow, toTate_option_X none]
        exact (norm_pow_le (TateAlgebra.X (none : Option τ) : TateAlgebra (Option τ) A) (d t)).trans
          (pow_le_one₀ (norm_nonneg _) (TateAlgebra.norm_X_le_one (none : Option τ)))
      refine le_trans
        (IsUltrametricDist.norm_add_le_max
          ((((MvPolynomial.X (some t : Option τ))).toTate :
            TateAlgebra (Option τ) A))
          (-(((MvPolynomial.X (none : Option τ) ^ d t)).toTate :
            TateAlgebra (Option τ) A))) ?_
      refine max_le ?_ ?_
      · rw [toTate_option_X (some t)]
        exact TateAlgebra.norm_X_le_one (some t : Option τ)
      · simpa using hpow

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] in
omit [NormOneClass A] [NormMulClass A] in
lemma optionTriangularForward_comp_inverse_eval (d : τ → ℕ) (i : Option τ) :
      MvPolynomial.aeval (optionTriangularInversePoly A d)
        (optionTriangularForwardPoly A d i) = MvPolynomial.X i := by
  cases i with
  | none => simp [optionTriangularForwardPoly, optionTriangularInversePoly]
  | some t => simp [optionTriangularForwardPoly, optionTriangularInversePoly]

omit [CompleteSpace A] [IsUltrametricDist A] [Fintype τ] in
omit [NormOneClass A] [NormMulClass A] in
lemma optionTriangularInverse_comp_forward_eval (d : τ → ℕ) (i : Option τ) :
      MvPolynomial.aeval (optionTriangularForwardPoly A d)
        (optionTriangularInversePoly A d i) = MvPolynomial.X i := by
  cases i with
  | none => simp [optionTriangularForwardPoly, optionTriangularInversePoly]
  | some t => simp [optionTriangularForwardPoly, optionTriangularInversePoly]

variable (A) in
/-- The Tate algebra endomorphism induced by the forward triangular coordinate change. -/
noncomputable def optionTriangularForward (d : τ → ℕ) (hd : ∀ t, 0 < d t) :
    TateAlgebra (Option τ) A →ₐ[A] TateAlgebra (Option τ) A :=
  tateMvPolynomialSubst (optionTriangularForwardPoly A d)
    (optionTriangularForwardPoly_constantCoeff d hd)
    (optionTriangularForwardPoly_norm_le_one d)

variable (A) in
/-- The Tate algebra endomorphism induced by the inverse triangular coordinate change. -/
noncomputable def optionTriangularInverse (d : τ → ℕ) (hd : ∀ t, 0 < d t) :
    TateAlgebra (Option τ) A →ₐ[A] TateAlgebra (Option τ) A :=
  tateMvPolynomialSubst (optionTriangularInversePoly A d)
    (optionTriangularInversePoly_constantCoeff d hd)
    (optionTriangularInversePoly_norm_le_one d)

omit [CompleteSpace A] in
lemma isContractiveHom_optionTriangularForward (d : τ → ℕ) (hd : ∀ t, 0 < d t) :
    IsContractiveHom (optionTriangularForward A d hd) := by
  simpa [optionTriangularForward] using
    isContractiveHom_tateMvPolynomialSubst
      (optionTriangularForwardPoly A d)
      (ha0 := optionTriangularForwardPoly_constantCoeff d hd)
      (ha1 := optionTriangularForwardPoly_norm_le_one d)

omit [CompleteSpace A] in
lemma isContractiveHom_optionTriangularInverse (d : τ → ℕ) (hd : ∀ t, 0 < d t) :
    IsContractiveHom (optionTriangularInverse A d hd) := by
  simpa [optionTriangularInverse] using
    isContractiveHom_tateMvPolynomialSubst
      (optionTriangularInversePoly A d)
      (ha0 := optionTriangularInversePoly_constantCoeff d hd)
      (ha1 := optionTriangularInversePoly_norm_le_one d)

omit [CompleteSpace A] in
lemma optionTriangularForward_comp_inverse (d : τ → ℕ) (hd : ∀ t, 0 < d t) :
    (optionTriangularForward A d hd).comp (optionTriangularInverse A d hd) =
      AlgHom.id A (TateAlgebra (Option τ) A) := by
  let c : Option τ → MvPolynomial (Option τ) A := fun i => MvPolynomial.X i
  have hc : ∀ i,
      c i = MvPolynomial.aeval (optionTriangularForwardPoly A d)
        (optionTriangularInversePoly A d i) := by
    intro i
    symm
    simpa [c] using optionTriangularInverse_comp_forward_eval d i
  have hc0 : ∀ i, MvPolynomial.constantCoeff (c i) = 0 := by
    intro i
    simp [c]
  have hc1 : ∀ i, ‖((c i).toTate : TateAlgebra (Option τ) A)‖ ≤ 1 := by
    intro i
    simpa [c, toTate_option_X] using
      (TateAlgebra.norm_X_le_one i)
  rw [optionTriangularForward, optionTriangularInverse]
  rw [tateMvPolynomialSubst_comp (optionTriangularInversePoly A d)
    (optionTriangularInversePoly_constantCoeff d hd) (optionTriangularInversePoly_norm_le_one d)
    (optionTriangularForwardPoly A d) (optionTriangularForwardPoly_constantCoeff d hd)
    (optionTriangularForwardPoly_norm_le_one d) c hc hc0 hc1]
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  calc
    _ = MvPowerSeries.subst (fun i : Option τ => MvPowerSeries.X i)
        ((x : TateAlgebra (Option τ) A) : MvPowerSeries (Option τ) A) := by
      simp [c]
    _ = _ := congrArg (fun f => f ((x : TateAlgebra (Option τ) A) : MvPowerSeries (Option τ) A))
      MvPowerSeries.subst_self

omit [CompleteSpace A] in
lemma optionTriangularInverse_comp_forward (d : τ → ℕ) (hd : ∀ t, 0 < d t) :
    (optionTriangularInverse A d hd).comp (optionTriangularForward A d hd) =
      AlgHom.id A (TateAlgebra (Option τ) A) := by
  let c : Option τ → MvPolynomial (Option τ) A := fun i => MvPolynomial.X i
  have hc : ∀ i,
      c i = MvPolynomial.aeval (optionTriangularInversePoly A d)
        (optionTriangularForwardPoly A d i) := by
    intro i
    symm
    simpa [c] using optionTriangularForward_comp_inverse_eval d i
  have hc0 : ∀ i, MvPolynomial.constantCoeff (c i) = 0 := by
    intro i
    simp [c]
  have hc1 : ∀ i, ‖((c i).toTate : TateAlgebra (Option τ) A)‖ ≤ 1 := by
    intro i
    simpa [c, toTate_option_X] using
      (TateAlgebra.norm_X_le_one i)
  rw [optionTriangularInverse, optionTriangularForward]
  rw [tateMvPolynomialSubst_comp (optionTriangularForwardPoly A d)
    (optionTriangularForwardPoly_constantCoeff d hd) (optionTriangularForwardPoly_norm_le_one d)
    (optionTriangularInversePoly A d) (optionTriangularInversePoly_constantCoeff d hd)
    (optionTriangularInversePoly_norm_le_one d) c hc hc0 hc1]
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  simpa [c] using congrArg (fun f => f x.1) MvPowerSeries.subst_self

end TriangularAutomorphism

section WeierstrassPrelude

omit [CompleteSpace A] [NormOneClass A] [NormMulClass A] in
lemma finite_set_coeff_norm_eq_norm {τ : Type*} (f : TateAlgebra τ A) (hf : f ≠ 0) :
    {e : τ →₀ ℕ | ‖MvPowerSeries.coeff e f.1‖ = ‖f‖}.Finite := by
  have hnorm_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  refine ((isTate_iff f.1).mp f.2 ‖f‖ hnorm_pos).subset ?_
  intro e he
  change ‖f‖ ≤ ‖MvPowerSeries.coeff e f.1‖
  have he' : ‖MvPowerSeries.coeff e f.1‖ = ‖f‖ := he
  simp [he']

omit [CompleteSpace A] [NormOneClass A] [NormMulClass A] in
lemma coeff_sub_toTate_maxNorm_lt_one {τ : Type*}
    (f : TateAlgebra τ A) (s : Finset (τ →₀ ℕ))
    (hs : ∀ e, e ∈ s ↔ ‖MvPowerSeries.coeff e f.1‖ = 1)
    (hcoeff : ∀ e, ‖MvPowerSeries.coeff e f.1‖ ≤ 1)  (e : τ →₀ ℕ) :
      ‖MvPowerSeries.coeff e (f -
        (s.sum fun d => MvPolynomial.monomial d (MvPowerSeries.coeff d f.1)).toTate).1‖ < 1 := by
  classical
  let p : MvPolynomial τ A := s.sum fun d => MvPolynomial.monomial d (MvPowerSeries.coeff d f.1)
  let g := p.toTate
  have hpoly :
      MvPowerSeries.coeff e g.1 = if e ∈ s then MvPowerSeries.coeff e f.1 else 0 := by
    rw [MvPolynomial.toTate_coe]
    dsimp [p]
    rw [MvPolynomial.coeff_sum]
    by_cases he : e ∈ s
    · rw [if_pos he]
      rw [Finset.sum_eq_single e]
      · simp [MvPolynomial.coeff_monomial]
      · intro d hd hde
        simp [MvPolynomial.coeff_monomial, hde]
      · intro hne
        contradiction
    · rw [if_neg he]
      refine Finset.sum_eq_zero ?_
      intro d hd
      simp [MvPolynomial.coeff_monomial, ne_of_mem_of_not_mem hd he]
  change ‖MvPowerSeries.coeff e f.1 - MvPowerSeries.coeff e g.1‖ < 1
  rw [hpoly]
  by_cases he : e ∈ s
  · simp [he]
  · have hne : ‖MvPowerSeries.coeff e f.1‖ ≠ 1 := by
      intro hEq
      exact he ((hs e).2 hEq)
    simpa [g, he] using lt_of_le_of_ne (hcoeff e) hne

omit [NormOneClass A] [NormMulClass A] [IsUltrametricDist A] in
lemma isUnit_of_norm_sub_lt_unit
    (f : A) (u : Aˣ) (hclose : ‖f - u.1‖ < ‖u.2‖⁻¹) : IsUnit f := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (u.add (f - u) hclose).isUnit

omit [Finite σ] [CompleteSpace A] [NormOneClass A] [NormMulClass A] in
lemma norm_le_of_forall_coeff_le
    (f : TateAlgebra σ A) {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f.1‖ ≤ C) : ‖f‖ ≤ C := by
  by_contra hgt
  by_cases hf : f = 0
  · simp [hf, hC] at hgt
  · obtain ⟨e, he⟩ := TateAlgebra.exists_coeff_norm_eq_norm f hf
    exact (not_lt_of_ge (hcoeff e)) (by simpa [he] using hgt)

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma norm_le_of_forall_powerSeriesCoeff_le
    (f : TateAlgebra Unit A) {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ l : ℕ, ‖PowerSeries.coeff l f.1‖ ≤ C) : ‖f‖ ≤ C := by
  by_contra hgt
  by_cases hf : f = 0
  · simp [hf, hC] at hgt
  · obtain ⟨e, he⟩ := TateAlgebra.exists_coeff_norm_eq_norm f hf
    exact (not_lt_of_ge (hcoeff (e ()))) (by
      simpa [PowerSeries.coeff_def rfl, he] using hgt)

end WeierstrassPrelude

section NoetherNormalizationPrelude

lemma optionDigitWeight_pos {n B : ℕ} (hB : 1 < B) (t : Fin n) :
    0 < optionDigitWeight B t := by
  simp [optionDigitWeight, lt_trans Nat.zero_lt_one hB]

lemma optionWeight_eq_finsuppWeight {n : ℕ} (d : Fin n → ℕ) (e : Option (Fin n) →₀ ℕ) :
    optionWeight d e = Finsupp.weight (fun o : Option (Fin n) => o.elim 1 d) e := by
  rw [Finsupp.weight_apply, Finsupp.sum_option_index]
  · rw [Finsupp.sum_fintype]
    · simp [optionWeight]
    · intro t
      simp
  · intro o
    simp
  · intro o m₁ m₂
    cases o <;> simp [right_distrib]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma optionTriangularForwardPoly_isWeightedHomogeneous {n : ℕ} (d : Fin n → ℕ) :
    let w : Option (Fin n) → ℕ := fun o => o.elim 1 d
    ∀ i, MvPolynomial.IsWeightedHomogeneous w
      (optionTriangularForwardPoly A d i) (w i) := by
  intro w i
  cases i with
  | none =>
      simpa [optionTriangularForwardPoly] using
        (MvPolynomial.isWeightedHomogeneous_X A w (none : Option (Fin n)))
  | some t =>
      refine (MvPolynomial.isWeightedHomogeneous_X A w (some t)).add ?_
      simpa [w] using
        (MvPolynomial.IsWeightedHomogeneous.pow
          (MvPolynomial.isWeightedHomogeneous_X A w (none : Option (Fin n))) (d t))

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma aeval_optionTriangularForwardPoly_monomial_isWeightedHomogeneous {n : ℕ}
    (d : Fin n → ℕ) (e : Option (Fin n) →₀ ℕ) (a : A) :
    let w : Option (Fin n) → ℕ := fun o => o.elim 1 d
    MvPolynomial.IsWeightedHomogeneous w
      ((MvPolynomial.aeval (optionTriangularForwardPoly A d)) (MvPolynomial.monomial e a))
      (optionWeight d e) := by
  intro w
  rw [MvPolynomial.aeval_monomial]
  have hC : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C a : MvPolynomial (Option (Fin n)) A) 0 :=
    MvPolynomial.isWeightedHomogeneous_C w a
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod e.support
    (fun i => optionTriangularForwardPoly A d i ^ e i)
    (fun i => e i • w i) (by
      intro i hi
      exact (optionTriangularForwardPoly_isWeightedHomogeneous d i).pow (e i))
  simpa [optionWeight_eq_finsuppWeight, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod, w] using
    hC.mul hprod

lemma optionWeight_optionElim_eq {n : ℕ} (d : Fin n → ℕ) (m : ℕ) (d₀ : Fin n →₀ ℕ) :
    optionWeight d (Finsupp.optionElim m d₀) = m + ∑ t, d₀ t * d t := by
  simp [optionWeight]

lemma lt_optionWeight_optionElim {n : ℕ} (d : Fin n → ℕ) (hd : ∀ t, 0 < d t)
    (m : ℕ) {d₀ : Fin n →₀ ℕ} (hd₀ : d₀ ≠ 0) :
    m < optionWeight d (Finsupp.optionElim m d₀) := by
  rw [optionWeight_optionElim_eq]
  rcases Finsupp.support_nonempty_iff.mpr hd₀ with ⟨t, ht⟩
  have hne : d₀ t ≠ 0 := Finsupp.mem_support_iff.mp ht
  have hpos_term : 0 < d₀ t * d t := Nat.mul_pos (Nat.pos_iff_ne_zero.mpr hne) (hd t)
  have hle_sum : d₀ t * d t ≤ ∑ x, d₀ x * d x :=
    Finset.single_le_sum (f := fun x => d₀ x * d x) (fun i hi ↦ Nat.zero_le _) (by simp)
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos_term) (by gcongr)

omit [CompleteSpace A] in
lemma optionTriangularForward_apply_toTate {n : ℕ} (d : Fin n → ℕ)
    (hd : ∀ t, 0 < d t) (p : MvPolynomial (Option (Fin n)) A) :
    optionTriangularForward A d hd p.toTate =
      ((MvPolynomial.aeval (optionTriangularForwardPoly A d) p).toTate) := by
  let Φ₁ : MvPolynomial (Option (Fin n)) A →ₐ[A] TateAlgebra (Option (Fin n)) A :=
    (optionTriangularForward A d hd).comp
      (MvPolynomial.toTate : MvPolynomial (Option (Fin n)) A →ₐ[A] TateAlgebra (Option (Fin n)) A)
  let Φ₂ : MvPolynomial (Option (Fin n)) A →ₐ[A] TateAlgebra (Option (Fin n)) A :=
    (MvPolynomial.toTate : MvPolynomial (Option (Fin n)) A →ₐ[A]
      TateAlgebra (Option (Fin n)) A).comp
      (MvPolynomial.aeval (optionTriangularForwardPoly A d))
  have hΦ : Φ₁ = Φ₂ := by
    apply MvPolynomial.algHom_ext
    intro i
    apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, toTate_option_X, optionTriangularForward,
      tateMvPolynomialSubst_X]
    simp
  exact congrArg (fun F : MvPolynomial (Option (Fin n)) A →ₐ[A] TateAlgebra (Option (Fin n)) A => F
    p) hΦ

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma coeff_optionToTate_toTate {n : ℕ} (p : MvPolynomial (Option (Fin n)) A)
    (l : ℕ) (d₀ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d₀
        (PowerSeries.coeff l
          (optionToTate (p.toTate)).1).1 =
      MvPolynomial.coeff (Finsupp.optionElim l d₀) p := by
  simp [optionToTate, optionCoeffTate, coeff_optionToPowerSeries, MvPolynomial.toTate_coe]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma coeff_optionToTate {n : ℕ} (x : TateAlgebra (Option (Fin n)) A)
    (l : ℕ) (d₀ : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d₀ (PowerSeries.coeff l (optionToTate x).1).1 =
      MvPowerSeries.coeff (Finsupp.optionElim l d₀) x.1 := by
  simp [optionToTate, optionCoeffTate, coeff_optionToPowerSeries]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma coeff_optionElim_zero_eq_constantCoeff_coeff_optionEquivLeft {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) A) (m : ℕ) :
    MvPolynomial.coeff (Finsupp.optionElim m 0) p =
      MvPolynomial.constantCoeff (((MvPolynomial.optionEquivLeft A (Fin n)) p).coeff m) := by
  rw [MvPolynomial.constantCoeff_eq, MvPolynomial.optionEquivLeft_coeff_coeff]

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] [IsUltrametricDist A] in
lemma coeff_aeval_optionTriangularForwardPoly_monomial_eq_zero_of_weight_ne {n : ℕ}
    (d : Fin n → ℕ) (e : Option (Fin n) →₀ ℕ) (a : A) (l : ℕ) (d₀ : Fin n →₀ ℕ)
    (hne : optionWeight d (Finsupp.optionElim l d₀) ≠ optionWeight d e) :
    MvPolynomial.coeff (Finsupp.optionElim l d₀)
      ((MvPolynomial.aeval (optionTriangularForwardPoly A d)) (MvPolynomial.monomial e a)) =
        0 := by
  let w : Option (Fin n) → ℕ := fun o => o.elim 1 d
  have hwh := aeval_optionTriangularForwardPoly_monomial_isWeightedHomogeneous
    d e a
  exact hwh.coeff_eq_zero _ (by simpa [w, optionWeight_eq_finsuppWeight] using hne)

lemma exists_optionDigitWeight_bound {n : ℕ} (s : Finset (Option (Fin n) →₀ ℕ)) :
    ∃ B, 1 < B ∧ ∀ e ∈ s, ∀ i, e i < B := by
  let B : ℕ := s.sup (fun e => Finset.univ.sup fun i : Option (Fin n) => e i) + 2
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    omega
  · intro e he i
    dsimp [B]
    have hi : e i ≤ Finset.univ.sup (fun j : Option (Fin n) => e j) := by
      exact Finset.le_sup (by simp)
    have hs : Finset.univ.sup (fun j : Option (Fin n) => e j) ≤
        s.sup (fun e => Finset.univ.sup fun j : Option (Fin n) => e j) := by
      exact Finset.le_sup
        (f := fun e : Option (Fin n) →₀ ℕ => Finset.univ.sup fun j : Option (Fin n) => e j) he
    omega

end NoetherNormalizationPrelude

section NormedField

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

lemma isDistinguishedOfOrder_of_optionToTate_data {n m : ℕ}
    {h : TateAlgebra Unit (TateAlgebra (Fin n) k)} {gp gr : TateAlgebra (Option (Fin n)) k} {c₀ : k}
    (hh_norm_le : ‖h‖ ≤ 1) (hopt_add : h = optionToTate gp + optionToTate gr)
    (hgp_coeff_high : ∀ {l : ℕ}, l > m → (PowerSeries.coeff l) (optionToTate gp).1 = 0)
    (hgr_powerCoeff_lt : ∀ l : ℕ, ‖(PowerSeries.coeff l) (optionToTate gr).1‖ < 1)
    (hh_coeff_m_eq : (PowerSeries.coeff m) h.1 =
      (algebraMap k (TateAlgebra (Fin n) k)) c₀ + (PowerSeries.coeff m) (optionToTate gr).1)
    (hc₀_norm : ‖c₀‖ = 1) (hc₀_ne : c₀ ≠ 0) : h.IsDistinguishedOfOrder m := by
  have hh_coeff_m_close :
      ‖PowerSeries.coeff m h.1 - algebraMap k (TateAlgebra (Fin n) k) c₀‖ < 1 := by
    have : PowerSeries.coeff m h.1 - algebraMap k (TateAlgebra (Fin n) k) c₀ =
        PowerSeries.coeff m (optionToTate gr).1 := by
      rw [hh_coeff_m_eq]
      ring
    rw [this]
    exact hgr_powerCoeff_lt m
  have hh_coeff_m_ge_one : 1 ≤ ‖PowerSeries.coeff m h.1‖ := by
    have hc₀_tate_norm :
        ‖(algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k)‖ = 1 := by
      rw [norm_algebraMap', hc₀_norm]
    by_cases hlt : ‖PowerSeries.coeff m h.1‖ < 1
    · have hsub_lt :
          ‖(algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) -
              PowerSeries.coeff m h.1‖ < 1 := by
        simpa [norm_sub_rev] using hh_coeff_m_close
      have hEq :
          (PowerSeries.coeff m h.1 : TateAlgebra (Fin n) k) +
              ((algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) -
                PowerSeries.coeff m h.1) =
            (algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) := by
        ring
      have hnorm :
          ‖(algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k)‖ ≤
            max ‖(PowerSeries.coeff m h.1 : TateAlgebra (Fin n) k)‖
              ‖(algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) -
                PowerSeries.coeff m h.1‖ := by
        have hnorm' :
            ‖(PowerSeries.coeff m h.1 : TateAlgebra (Fin n) k) +
                ((algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) -
                  PowerSeries.coeff m h.1)‖ ≤
              max ‖(PowerSeries.coeff m h.1 : TateAlgebra (Fin n) k)‖
                ‖(algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) -
                  PowerSeries.coeff m h.1‖ := by
          exact IsUltrametricDist.norm_add_le_max _ _
        simpa [hEq] using hnorm'
      rw [hc₀_tate_norm] at hnorm
      have : max ‖PowerSeries.coeff m h.1‖
          ‖(algebraMap k (TateAlgebra (Fin n) k) c₀ : TateAlgebra (Fin n) k) -
              PowerSeries.coeff m h.1‖ < 1 :=
        max_lt hlt hsub_lt
      exact (not_lt_of_ge hnorm) this |>.elim
    · exact le_of_not_gt hlt
  have hh_coeff_m_isUnit : IsUnit (PowerSeries.coeff m h.1) := by
    let u : (TateAlgebra (Fin n) k)ˣ :=
      Units.map (algebraMap k (TateAlgebra (Fin n) k)) (Units.mk0 _ hc₀_ne)
    have huinv : ‖((u⁻¹.1 : TateAlgebra (Fin n) k))‖⁻¹ = 1 := by
      simp [u, hc₀_norm]
    have hclose :
        ‖PowerSeries.coeff m h.1 - (u : TateAlgebra (Fin n) k)‖ <
          ‖((u⁻¹.1 : TateAlgebra (Fin n) k))‖⁻¹ := by
      simpa [u, huinv, hc₀_norm] using hh_coeff_m_close
    exact isUnit_of_norm_sub_lt_unit (PowerSeries.coeff m h.1) u hclose
  exact
    { norm_le := le_trans hh_norm_le hh_coeff_m_ge_one
      maximal := by
        intro l hl
        have hh_coeff_l_eq :
            PowerSeries.coeff l h.1 = PowerSeries.coeff l (optionToTate gr).1 := by
          rw [hopt_add]
          simp [hgp_coeff_high hl]
        have hh_coeff_l_lt : ‖PowerSeries.coeff l h.1‖ < 1 := by
          rw [hh_coeff_l_eq]
          exact hgr_powerCoeff_lt l
        exact lt_of_lt_of_le hh_coeff_l_lt hh_coeff_m_ge_one
      isUnit := hh_coeff_m_isUnit }

/-- Every nonzero element becomes distinguished in the last variable after a
triangular automorphism of the Tate algebra. -/
lemma exists_optionTriangularForward_distinguished {n : ℕ}
    (f : TateAlgebra (Option (Fin n)) k) (hf : f ≠ 0) (hnorm : ‖f‖ = 1) :
    ∃ (d : Fin n → ℕ) (hd : ∀ t, 0 < d t) (m : ℕ),
      TateAlgebra.IsDistinguishedOfOrder
        (optionToTate (optionTriangularForward k d hd f)) m := by
  let s : Finset (Option (Fin n) →₀ ℕ) :=
    (finite_set_coeff_norm_eq_norm f hf).toFinset
  have hs : ∀ e, e ∈ s ↔ ‖MvPowerSeries.coeff e f.1‖ = 1 := by
    intro e
    simp [s, hnorm]
  have hs_nonempty : s.Nonempty := by
    obtain ⟨e, he⟩ := TateAlgebra.exists_coeff_norm_eq_norm f hf
    exact ⟨e, (hs e).2 (by simpa only [hnorm] using he)⟩
  obtain ⟨B, hB, hbound⟩ := exists_optionDigitWeight_bound s
  let d : Fin n → ℕ := optionDigitWeight B
  have hd : ∀ t, 0 < d t := optionDigitWeight_pos hB
  let wset : Finset ℕ := s.image (optionWeight d)
  have hwset_nonempty : wset.Nonempty := hs_nonempty.image (optionWeight d)
  let m : ℕ := wset.max' hwset_nonempty
  obtain ⟨e₀, he₀s, hm⟩ : ∃ e₀ ∈ s, optionWeight d e₀ = m := by
    have hm_mem : m ∈ wset := Finset.max'_mem wset hwset_nonempty
    rcases Finset.mem_image.mp hm_mem with ⟨e₀, he₀s, hm⟩
    exact ⟨e₀, he₀s, hm⟩
  have hs_inj :
      ∀ {e₁ e₂ : Option (Fin n) →₀ ℕ}, e₁ ∈ s → e₂ ∈ s →
        optionWeight d e₁ = optionWeight d e₂ → e₁ = e₂ := by
    intro e₁ e₂ he₁ he₂ hEq
    refine optionWeight_optionDigitWeight_injective hB ?_ ?_ hEq
    · intro i
      exact hbound e₁ he₁ i
    · intro i
      exact hbound e₂ he₂ i
  have hm_max : ∀ e ∈ s, optionWeight d e ≤ m := by
    intro e he
    exact Finset.le_max' wset (optionWeight d e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  let p : MvPolynomial (Option (Fin n)) k :=
    ∑ e ∈ s, MvPolynomial.monomial e (MvPowerSeries.coeff e f.1)
  have hcoeff_le (e) : ‖MvPowerSeries.coeff e f.1‖ ≤ 1 := by
    simpa [hnorm] using TateAlgebra.coeff_norm_le f e
  have hr_coeff_lt : ∀ e, ‖MvPowerSeries.coeff e (f - p.toTate).1‖ < 1 := by
    refine coeff_sub_toTate_maxNorm_lt_one f s ?_ hcoeff_le
    intro e
    simpa [p, Finset.sum_sigma'] using hs e
  have hr_norm_lt : ‖f - p.toTate‖ < 1 := by
    by_contra hnot
    have hge : 1 ≤ ‖f - p.toTate‖ := le_of_not_gt hnot
    by_cases hf0 : f - p.toTate = 0
    · have : (1 : ℝ) ≤ 0 := by simpa [hf0] using hge
      linarith
    · obtain ⟨e, he⟩ := TateAlgebra.exists_coeff_norm_eq_norm (f - p.toTate) hf0
      exact (not_lt_of_ge (hge.trans_eq he.symm)) (hr_coeff_lt e)
  let g : TateAlgebra (Option (Fin n)) k := optionTriangularForward k d hd f
  let gp : TateAlgebra (Option (Fin n)) k :=
    optionTriangularForward k d hd p.toTate
  let gr : TateAlgebra (Option (Fin n)) k :=
    optionTriangularForward k d hd (f - p.toTate)
  have hg_split : g = gp + gr := by
    simp [g, gp, gr, sub_eq_add_neg, add_left_comm, add_comm]
  have hgr_norm_lt : ‖gr‖ < 1 :=
    lt_of_le_of_lt ((isContractiveHom_optionTriangularForward d hd) _) hr_norm_lt
  have hgp_eq :
      gp =
        ((MvPolynomial.aeval (optionTriangularForwardPoly k d) p).toTate) := by
    simpa [gp] using optionTriangularForward_apply_toTate d hd p
  let h : TateAlgebra Unit (TateAlgebra (Fin n) k) := optionToTate g
  let p' : MvPolynomial (Option (Fin n)) k :=
    (MvPolynomial.aeval (optionTriangularForwardPoly k d)) p
  have hp'_coeff_zero_of_gt :
      ∀ {l : ℕ} {d₀ : Fin n →₀ ℕ},
        m < optionWeight d (Finsupp.optionElim l d₀) →
          MvPolynomial.coeff (Finsupp.optionElim l d₀) p' = 0 := by
    intro l d₀ hgt
    dsimp [p', p]
    rw [map_sum, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero ?_
    intro e he
    have hne : optionWeight d (Finsupp.optionElim l d₀) ≠ optionWeight d e := by
      exact ne_of_gt (lt_of_le_of_lt (hm_max e he) hgt)
    exact coeff_aeval_optionTriangularForwardPoly_monomial_eq_zero_of_weight_ne
      d e (MvPowerSeries.coeff e f.1) l d₀ hne
  have hp'_coeff_m_zero :
      MvPolynomial.coeff (Finsupp.optionElim m 0) p' = MvPowerSeries.coeff e₀ f.1 := by
    rw [coeff_optionElim_zero_eq_constantCoeff_coeff_optionEquivLeft p' m]
    have hsum :
        MvPolynomial.constantCoeff
            (((MvPolynomial.optionEquivLeft k (Fin n)) p').coeff m) =
          Finset.sum s
            (fun e => if m = optionWeight d e then MvPowerSeries.coeff e f.1 else 0) := by
      simpa [p', p] using
        (coeff_constantCoeff_optionEquivLeft_sum_monomial
          d s (fun e => MvPowerSeries.coeff e f.1) m)
    rw [hsum]
    have hsum' :
        Finset.sum s
            (fun e : Option (Fin n) →₀ ℕ =>
              if m = optionWeight d e then (MvPowerSeries.coeff e f.1 : k) else (0 : k)) =
          MvPowerSeries.coeff e₀ f.1 := by
      simpa [hm] using
        (Finset.sum_eq_single
          (f := fun e : Option (Fin n) →₀ ℕ =>
            if m = optionWeight d e then (MvPowerSeries.coeff e f.1 : k) else (0 : k))
          e₀
          (by
            intro e he hes
            have hne : optionWeight d e ≠ m := by
              intro hEq
              have : e = e₀ := hs_inj he he₀s (by simpa [hm] using hEq)
              exact hes this
            have hne' : m ≠ optionWeight d e := by simpa [eq_comm] using hne
            simp [hne'])
          (by
            intro he₀not
            exact False.elim (he₀not he₀s)))
    exact hsum'
  have hgp_coeff_m :
      PowerSeries.coeff m (optionToTate gp).1 =
        algebraMap k (TateAlgebra (Fin n) k) (MvPowerSeries.coeff e₀ f.1) := by
    apply Subtype.ext
    ext d₀
    by_cases hd₀ : d₀ = 0
    · subst hd₀
      rw [hgp_eq, coeff_optionToTate_toTate]
      simpa [hp'_coeff_m_zero]
    · rw [hgp_eq, coeff_optionToTate_toTate]
      have hgt : m < optionWeight d (Finsupp.optionElim m d₀) := by
        exact lt_optionWeight_optionElim d hd m hd₀
      change MvPolynomial.coeff (Finsupp.optionElim m d₀)
          ((MvPolynomial.aeval (optionTriangularForwardPoly k d)) p) =
        MvPowerSeries.coeff d₀
          (((algebraMap k (TateAlgebra (Fin n) k)) (MvPowerSeries.coeff e₀ f.1) :
            TateAlgebra (Fin n) k).1)
      rw [hp'_coeff_zero_of_gt hgt]
      have hscalar : MvPowerSeries.coeff d₀
            ((algebraMap k (TateAlgebra (Fin n) k)) (MvPowerSeries.coeff e₀ f.1)).1 = 0 := by
        simpa [MvPowerSeries.algebraMap_apply, hd₀] using
          (MvPowerSeries.coeff_C d₀ (MvPowerSeries.coeff e₀ f.1))
      rw [hscalar]
  have hgp_coeff_high :
      ∀ {l : ℕ}, l > m → PowerSeries.coeff l (optionToTate gp).1 = 0 := by
    intro l hl
    apply Subtype.ext
    ext d₀
    rw [hgp_eq, coeff_optionToTate_toTate]
    by_cases hd₀ : d₀ = 0
    · subst hd₀
      have hgt : m < optionWeight d (Finsupp.optionElim l 0) := by
        rw [optionWeight_optionElim_eq]
        simpa using hl
      simpa using hp'_coeff_zero_of_gt hgt
    · have hgt : m < optionWeight d (Finsupp.optionElim l d₀) := by
        exact lt_trans hl (lt_optionWeight_optionElim d hd l hd₀)
      exact hp'_coeff_zero_of_gt hgt
  have hgr_powerCoeff_lt :
      ∀ l : ℕ, ‖PowerSeries.coeff l (optionToTate gr).1‖ < 1 := by
    intro l
    by_contra hnot
    have hge : 1 ≤ ‖PowerSeries.coeff l (optionToTate gr).1‖ := le_of_not_gt hnot
    by_cases hzero : PowerSeries.coeff l (optionToTate gr).1 = 0
    · have : (1 : ℝ) ≤ 0 := by simpa [hzero] using hge
      linarith
    · obtain ⟨d₀, hd₀⟩ := TateAlgebra.exists_coeff_norm_eq_norm
        (PowerSeries.coeff l (optionToTate gr).1) hzero
      rw [coeff_optionToTate gr l d₀] at hd₀
      exact (not_lt_of_ge (hge.trans_eq hd₀.symm))
        (lt_of_le_of_lt
          (TateAlgebra.coeff_norm_le gr (Finsupp.optionElim l d₀))
          hgr_norm_lt)
  have hg_norm_le : ‖g‖ ≤ 1 := by
    dsimp [g]
    simpa [hnorm] using (isContractiveHom_optionTriangularForward d hd) f
  have hpl (l : ℕ) : ‖PowerSeries.coeff l h.1‖ ≤ 1 := by
    apply norm_le_of_forall_coeff_le (PowerSeries.coeff l h.1) (by positivity)
    intro d₀
    rw [show h = optionToTate g by rfl, coeff_optionToTate g l d₀]
    exact le_trans (TateAlgebra.coeff_norm_le g (Finsupp.optionElim l d₀)) hg_norm_le
  have hh_norm_le : ‖h‖ ≤ 1 := norm_le_of_forall_powerSeriesCoeff_le h (by positivity) hpl
  have hopt_add :
      optionToTate g =
        optionToTate gp + optionToTate gr := by
    rw [hg_split]
    exact (optionToTateAlgEquiv k (Fin n)).map_add gp gr
  have hc₀_norm : ‖MvPowerSeries.coeff e₀ f.1‖ = 1 := (hs e₀).1 he₀s
  have hc₀_ne : MvPowerSeries.coeff e₀ f.1 ≠ 0 := by
    intro hzero
    simp [hzero] at hc₀_norm
  have hh_coeff_m_eq :
      PowerSeries.coeff m h.1 =
        algebraMap k (TateAlgebra (Fin n) k) (MvPowerSeries.coeff e₀ f.1) +
          PowerSeries.coeff m (optionToTate gr).1 := by
    rw [show h = optionToTate g by rfl, hopt_add]
    change
      (PowerSeries.coeff m)
          (((optionToTate gp : TateAlgebra Unit (TateAlgebra (Fin n) k)) : PowerSeries _) +
            ((optionToTate gr : TateAlgebra Unit (TateAlgebra (Fin n) k)) : PowerSeries _)) =
        (algebraMap k (TateAlgebra (Fin n) k)) ((coeff e₀) ↑f) +
          (PowerSeries.coeff m) ↑(optionToTate gr)
    simp [hgp_coeff_m]
  have hdist : TateAlgebra.IsDistinguishedOfOrder h m :=
    isDistinguishedOfOrder_of_optionToTate_data hh_norm_le hopt_add hgp_coeff_high hgr_powerCoeff_lt
      hh_coeff_m_eq hc₀_norm hc₀_ne
  exact ⟨d, hd, m, hdist⟩

section IsNoetherianRing

theorem isNoetherianRing_fin (k : Type*) [NormedField k] [CompleteSpace k] [IsUltrametricDist k] :
    ∀ n : ℕ, IsNoetherianRing (TateAlgebra (Fin n) k) := by
  intro n
  induction n with
  | zero =>
      exact isNoetherianRing_of_surjective k (TateAlgebra (Fin 0) k) finZeroAlgEquiv.symm.toRingHom
        finZeroAlgEquiv.symm.surjective
  | succ n ih =>
      let e : TateAlgebra (Fin (n + 1)) k ≃ₐ[k] TateAlgebra (Option (Fin n)) k :=
            tateAlgebraFinSuccEquiv n
      have hopt : IsNoetherianRing (TateAlgebra (Option (Fin n)) k) := by
        rw [isNoetherianRing_iff_ideal_fg]
        intro J
        by_cases hJ0 : J = ⊥
        · exact ⟨∅, by simp [hJ0]⟩
        · have hne : ∃ f : TateAlgebra (Option (Fin n)) k, f ∈ J ∧ f ≠ 0 := by
            by_contra h
            push Not at h
            apply hJ0
            ext f
            constructor
            · intro hf
              have : f = 0 := h f hf
              simp [this]
            · intro hf
              have hzero : f = 0 := by
                simpa [Submodule.mem_bot] using hf
              exact hzero ▸ J.zero_mem
          rcases hne with ⟨f, hfJ, hfne⟩
          obtain ⟨e₀, he₀⟩ := TateAlgebra.exists_coeff_norm_eq_norm f hfne
          let c : k := MvPowerSeries.coeff e₀ f.1
          have hc_ne : c ≠ 0 := by
            intro hc
            have : ‖f‖ = 0 := by
              simpa [c, hc] using he₀.symm
            exact hfne (norm_eq_zero.mp this)
          let f₁ : TateAlgebra (Option (Fin n)) k :=
            (algebraMap k (TateAlgebra (Option (Fin n)) k) (c⁻¹)) * f
          have hf₁J : f₁ ∈ J := J.mul_mem_left _ hfJ
          have hnorm_f₁ : ‖f₁‖ = 1 := by
            have hcoeff_e₀ : ‖MvPowerSeries.coeff e₀ f₁.1‖ = 1 := by
              rw [show f₁.1 = f.1 * MvPowerSeries.C c⁻¹ by
                change (algebraMap k (MvPowerSeries (Option (Fin n)) k) c⁻¹ * f.1) =
                  f.1 * MvPowerSeries.C c⁻¹
                rw [MvPowerSeries.algebraMap_apply, mul_comm]
                simp]
              rw [MvPowerSeries.coeff_mul_C]
              simp [c, hc_ne]
            have hcoeff_le : ∀ e, ‖MvPowerSeries.coeff e f₁.1‖ ≤ 1 := by
              intro e
              rw [show f₁.1 = f.1 * MvPowerSeries.C c⁻¹ by
                change (algebraMap k (MvPowerSeries (Option (Fin n)) k) c⁻¹ * f.1) =
                  f.1 * MvPowerSeries.C c⁻¹
                rw [MvPowerSeries.algebraMap_apply, mul_comm]
                simp]
              rw [MvPowerSeries.coeff_mul_C]
              calc
                ‖MvPowerSeries.coeff e f.1 * c⁻¹‖ = ‖MvPowerSeries.coeff e f.1‖ * ‖c‖⁻¹ := by
                  rw [norm_mul, norm_inv]
                _ ≤ ‖f‖ * ‖c‖⁻¹ := by
                  gcongr
                  exact TateAlgebra.coeff_norm_le f e
                _ = 1 := by
                  rw [he₀]
                  field_simp [norm_ne_zero_iff.mpr hfne]
            have hnorm_le : ‖f₁‖ ≤ 1 :=
              norm_le_of_forall_coeff_le f₁ (by positivity) hcoeff_le
            have hone_le : 1 ≤ ‖f₁‖ := by
              rw [← hcoeff_e₀]
              exact TateAlgebra.coeff_norm_le f₁ e₀
            exact le_antisymm hnorm_le hone_le
          have hf₁ne : f₁ ≠ 0 := by
            intro hf₁zero
            have : ‖f₁‖ = 0 := by simp [hf₁zero]
            linarith [hnorm_f₁]
          obtain ⟨d, hd, m, hdist⟩ :=
            exists_optionTriangularForward_distinguished f₁ hf₁ne hnorm_f₁
          let φ := optionTriangularForward k d hd
          let ψ := optionTriangularInverse k d hd
          let J' : Ideal (TateAlgebra (Option (Fin n)) k) := Ideal.map φ J
          have hαf₁J' : φ f₁ ∈ J' := Ideal.mem_map_of_mem φ hf₁J
          let eopt := optionToTateAlgEquiv k (Fin n)
          let K : Ideal (TateAlgebra Unit (TateAlgebra (Fin n) k)) := Ideal.map eopt J'
          have hopt_mem : optionToTate (φ f₁) ∈ K := Ideal.mem_map_of_mem eopt hαf₁J'
          obtain ⟨we, hwWeier, hunit, hdecomp⟩ :=
            (weierstrass_preparation (f := optionToTate (φ f₁)) hdist).exists
          have hwK : we.1 ∈ K := by
            rcases hunit with ⟨u, hu⟩
            have : u⁻¹.1 * optionToTate (φ f₁) ∈ K := K.mul_mem_left _ hopt_mem
            have htmp : ((u⁻¹.1 : TateAlgebra Unit (TateAlgebra (Fin n) k)) *
                (u : TateAlgebra Unit (TateAlgebra (Fin n) k)) * we.1) ∈ K := by
              simpa [hu, hdecomp, mul_assoc] using this
            simp at htmp
            exact htmp
          let Jw : Ideal (TateAlgebra Unit (TateAlgebra (Fin n) k)) := Ideal.span {we.1}
          let φq := Ideal.Quotient.mkₐ (TateAlgebra (Fin n) k) Jw
          have hφq : φq.Finite :=
            AlgHom.Finite.of_surjective φq (Ideal.Quotient.mkₐ_surjective _ _)
          have hwker : we.1 ∈ RingHom.ker φq := by
            simpa [RingHom.mem_ker] using
              Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span (by simp)
          have : Module.Finite
              (TateAlgebra (Fin n) k) ((TateAlgebra Unit (TateAlgebra (Fin n) k)) ⧸ Jw) :=
            weierstrass_finiteness hφq hwWeier hwker
          have hquo_noeth : IsNoetherianRing ((TateAlgebra Unit (TateAlgebra (Fin n) k)) ⧸ Jw) :=
            Algebra.FiniteType.isNoetherianRing
              (TateAlgebra (Fin n) k) ((TateAlgebra Unit (TateAlgebra (Fin n) k)) ⧸ Jw)
          have hJw_fg : Jw.FG := ⟨{we.1}, by simp [Jw]⟩
          have hJw_le_K : Jw ≤ K := (Ideal.span_singleton_le_iff_mem K).2 hwK
          have hmap_fg : (Ideal.map φq K).FG := Ideal.FG.of_isNoetherianRing _
          have hsurjφ : Function.Surjective φ := by
            intro x
            exact ⟨ψ x, congrArg (fun f => f x) (optionTriangularForward_comp_inverse d hd)⟩
          have hsurjψ : Function.Surjective ψ := by
            intro x
            exact ⟨φ x, congrArg (fun f => f x) (optionTriangularInverse_comp_forward d hd)⟩
          have hJ'_fg : J'.FG := by
            have hfg : (Ideal.map eopt.symm.toRingHom K).FG :=
              Ideal.FG.map (Ideal.fg_of_quotient_map_fg hmap_fg hJw_fg hJw_le_K) eopt.symm.toRingHom
            have hback : Ideal.map eopt.symm.toRingHom K = J' := by
              ext x
              constructor
              · intro hx
                rcases (Ideal.mem_map_iff_of_surjective eopt.symm eopt.symm.surjective).1
                  hx with
                  ⟨y, hyK, hyEq⟩
                rcases (Ideal.mem_map_iff_of_surjective eopt eopt.surjective).1 hyK with
                  ⟨z, hzJ', hzEq⟩
                have : x = z := by
                  rw [← hyEq, ← hzEq]
                  exact eopt.left_inv z
                simpa [this] using hzJ'
              · intro hx
                exact (Ideal.mem_map_iff_of_surjective eopt.symm eopt.symm.surjective).2
                  ⟨eopt x, Ideal.mem_map_of_mem eopt hx, eopt.left_inv x⟩
            exact hback ▸ hfg
          have hJ_fg : (Ideal.map ψ.toRingHom J').FG := Ideal.FG.map hJ'_fg ψ.toRingHom
          have hmap_back : Ideal.map ψ.toRingHom J' = J := by
            ext x
            constructor
            · intro hx
              rcases (Ideal.mem_map_iff_of_surjective ψ hsurjψ).1 hx with
                ⟨y, hyJ', hyEq⟩
              rcases (Ideal.mem_map_iff_of_surjective φ hsurjφ).1 hyJ' with
                ⟨z, hzJ, hzEq⟩
              have : x = z := by
                rw [← hyEq, ← hzEq]
                exact congrArg (fun f => f z) (optionTriangularInverse_comp_forward d hd)
              simpa [this] using hzJ
            · intro hx
              exact (Ideal.mem_map_iff_of_surjective ψ hsurjψ).2
                ⟨φ x, Ideal.mem_map_of_mem φ hx,
                  congrArg (fun f ↦ f x) (optionTriangularInverse_comp_forward d hd)⟩
          exact hmap_back ▸ hJ_fg
      exact isNoetherianRing_of_surjective (TateAlgebra (Option (Fin n)) k)
        (TateAlgebra (Fin (n + 1)) k) e.symm e.symm.surjective

instance {σ : Type*} [Finite σ] : IsNoetherianRing (TateAlgebra σ k) := by
  let : Fintype σ := Fintype.ofFinite σ
  let n : ℕ := Fintype.card σ
  let τ := Fin (Fintype.card σ)
  let e : σ ≃ τ := Fintype.equivFin σ
  let ρ : TateAlgebra (Fin n) k →ₐ[k] TateAlgebra σ k := TateAlgebra.rename k e.symm.toEmbedding
  have hfin : IsNoetherianRing (TateAlgebra (Fin n) k) := isNoetherianRing_fin k n
  refine isNoetherianRing_of_surjective (TateAlgebra (Fin n) k) (TateAlgebra σ k) ρ ?_
  intro y
  refine ⟨TateAlgebra.rename k e.toEmbedding y, ?_⟩
  apply Subtype.ext
  simp [ρ, TateAlgebra.rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id]

end IsNoetherianRing

end NormedField

omit [NormOneClass A] [NormMulClass A] [CompleteSpace A] in
lemma tateToOption_optionToTate_mul {n : ℕ} (f g : TateAlgebra (Option (Fin n)) A) :
    tateToOption (optionToTate f * optionToTate g) = f * g := by
  have hmul : optionToTate (f * g) = optionToTate f * optionToTate g :=
    (optionToTateAlgEquiv A (Fin n)).map_mul f g
  rw [← hmul]
  simp

end TateAlgebra

section noether_normalization

variable {σ : Type*} [Finite σ] {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
  {A : Type*} [NormedCommRing A] [NormedAlgebra k A] [IsStrictAffinoid k A]

namespace IsStrictAffinoid

include k in
variable (k) (A) in
theorem isNoetherianRing : IsNoetherianRing A := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, -, hs⟩
  exact isNoetherianRing_of_surjective (TateAlgebra σ k) A φ hs

omit [CompleteSpace k] [IsStrictAffinoid k A] in
lemma noether_normalization_drop_option
    {n : ℕ} (φ : TateAlgebra (Fin (n + 1)) k →ₐ[k] A)
    (hcontr : IsContractiveHom φ) (hfin : φ.Finite)
    (hinj : ¬ Function.Injective φ) :
    ∃ φ₁ : TateAlgebra (Option (Fin n)) k →ₐ[k] A,
      IsContractiveHom φ₁ ∧ φ₁.Finite ∧ ¬ Function.Injective φ₁ := by
  let e₁ : TateAlgebra (Fin (n + 1)) k ≃ₐ[k] TateAlgebra (Option (Fin n)) k :=
    tateAlgebraFinSuccEquiv n
  let φ₁ : TateAlgebra (Option (Fin n)) k →ₐ[k] A := φ.comp e₁.symm
  have hcontr₁ : IsContractiveHom φ₁ := by
    refine IsContractiveHom.comp ?_ hcontr
    simpa [φ₁, e₁, tateAlgebraFinSuccEquiv] using
      rename_isContractiveHom (finSuccEquiv n).symm.toEmbedding
  have hfin₁ : φ₁.Finite := RingHom.Finite.comp hfin e₁.symm.toRingEquiv.finite
  have hninj₁ : ¬ Function.Injective φ₁ := by
    intro hφ₁
    apply hinj
    intro x y hxy
    apply e₁.injective
    exact hφ₁ <| by simpa [φ₁] using hxy
  exact ⟨φ₁, hcontr₁, hfin₁, hninj₁⟩

omit [IsStrictAffinoid k A] in
theorem noether_normalization_drop {n : ℕ} (φ : TateAlgebra (Fin (n + 1)) k →ₐ[k] A)
    (hcontr : IsContractiveHom φ) (hfin : φ.Finite) (hinj : ¬ Function.Injective φ) :
    ∃ ψ : TateAlgebra (Fin n) k →ₐ[k] A, IsContractiveHom ψ ∧ ψ.Finite := by
  obtain ⟨φ₁, hcontr₁, hfin₁, hninj₁⟩ :=
    noether_normalization_drop_option φ hcontr hfin hinj
  obtain ⟨f, hfker, hfne⟩ :
      ∃ f : TateAlgebra (Option (Fin n)) k, φ₁ f = 0 ∧ f ≠ 0 := by
    rcases not_forall.mp hninj₁ with ⟨x, hx⟩
    rcases not_forall.mp hx with ⟨y, hxy⟩
    rcases Classical.not_imp.mp hxy with ⟨hφxy, hxy'⟩
    exact ⟨x - y, by simp [map_sub, hφxy], sub_ne_zero.mpr hxy'⟩
  obtain ⟨e, he⟩ := TateAlgebra.exists_coeff_norm_eq_norm f hfne
  let c : k := MvPowerSeries.coeff e f.1
  have hc_ne : c ≠ 0 := by
    intro hc
    have : ‖f‖ = 0 := by simpa [c, hc] using he.symm
    exact hfne (norm_eq_zero.mp this)
  let f₁ : TateAlgebra (Option (Fin n)) k := c⁻¹ • f
  have hf₁ker : φ₁ f₁ = 0 := by
    simp [f₁, hfker]
  have hf₁ne : f₁ ≠ 0 := by
    intro hf₁zero
    apply hfne
    have hc_inv_ne : c⁻¹ ≠ 0 := inv_ne_zero hc_ne
    exact smul_eq_zero.mp hf₁zero |>.resolve_left hc_inv_ne
  have hnorm_f₁ : ‖f₁‖ = 1 := by
    dsimp [f₁, c]
    rw [norm_smul, norm_inv, he]
    field_simp [hc_ne]
  obtain ⟨d, hd, m, hdist⟩ := exists_optionTriangularForward_distinguished f₁ hf₁ne hnorm_f₁
  obtain ⟨we, hw, hunit, hdecomp⟩ := TateAlgebra.weierstrass_preparation_exists hdist
  have hbij₂ : Function.Bijective (optionTriangularInverse k d hd) := by
    refine Function.bijective_iff_has_inverse.mpr ?_
    refine ⟨optionTriangularForward k d hd, ?_, ?_⟩
    · intro x
      simpa [AlgHom.comp_apply] using
        congrArg
          (fun F =>
            F x)
          (optionTriangularForward_comp_inverse d hd)
    · intro x
      simpa [AlgHom.comp_apply] using
        congrArg
          (fun F =>
            F x)
          (optionTriangularInverse_comp_forward d hd)
  have hfin_inv : (optionTriangularInverse k d hd).Finite :=
    (RingEquiv.ofBijective (optionTriangularInverse k d hd) hbij₂).finite
  have hopt_mul (f g : TateAlgebra (Option (Fin n)) k) :
      optionToTate (f * g) = optionToTate f * optionToTate g := by
    calc
      optionToTate (f * g) = optionToTate (tateToOption (optionToTate f * optionToTate g)) := by
        rw [tateToOption_optionToTate_mul f g]
      _ = optionToTate f * optionToTate g := by simp [optionToTate_tateToOption]
  have coeff_rename_some (a : TateAlgebra (Fin n) k) (e : Option (Fin n) →₀ ℕ) :
      (MvPowerSeries.coeff e) ((MvPowerSeries.rename some) (a : MvPowerSeries (Fin n) k)) =
        if e none = 0 then (MvPowerSeries.coeff e.some) (a : MvPowerSeries (Fin n) k) else 0 := by
    by_cases h : e none = 0
    · rw [MvPowerSeries.coeff_rename, if_pos h]
      have hmap : Finsupp.mapDomain some e.some = e := by
        ext x
        cases x with
        | none =>
            simp [Finsupp.mapDomain, h]
        | some i =>
            rw [Finsupp.mapDomain_apply_eq_sum]
            by_cases hi : e (some i) = 0
            · rw [hi]
              refine Finset.sum_eq_zero ?_
              intro j hj
              have hji : j = i := by
                simpa using (Finset.mem_filter.mp hj).2
              simpa [hji] using hi
            · rw [Finset.sum_eq_single i]
              · simp
              · intro j hj hji
                exfalso
                apply hji
                simpa using (Finset.mem_filter.mp hj).2
              · intro hnotmem
                by_contra hzero
                exact hnotmem (by simpa [Finsupp.mem_support_iff, hzero])
      refine Finset.sum_eq_single_of_mem e.some ?_ ?_
      · simp [hmap]
      · intro b hb hbeq
        exfalso
        apply hbeq
        apply Finsupp.mapDomain_injective Function.Embedding.some.injective
        simpa [hmap] using hb
    · rw [MvPowerSeries.coeff_rename, if_neg h]
      refine Finset.sum_eq_zero ?_
      intro b hb
      exfalso
      exact h <| by
        simpa [Finsupp.mapDomain] using (congrArg (fun f => f none)
          (show Finsupp.mapDomain some b = e by simpa using hb)).symm
  have htate_algMap (a : TateAlgebra (Fin n) k) :
      tateToOption
        ((algebraMap (TateAlgebra (Fin n) k) (TateAlgebra Unit (TateAlgebra (Fin n) k))) a) =
          TateAlgebra.rename k Function.Embedding.some a := by
    apply Subtype.ext
    ext e
    by_cases h : e none = 0
    · simpa [tateToOption, TateAlgebra.rename, PowerSeries.coeff_C, h, coeff_rename_some] using by
        rfl
    · rw [tateToOption, TateAlgebra.rename]
      simp [PowerSeries.coeff_C, h, coeff_rename_some]
  let Φ0 : TateAlgebra (Option (Fin n)) k →ₐ[k] A := φ₁.comp (optionTriangularInverse k d hd)
  have hcontr₀ : IsContractiveHom Φ0 := by
    refine IsContractiveHom.comp ?_ hcontr₁
    simpa using isContractiveHom_optionTriangularInverse d hd
  have hfin₀ : Φ0.Finite := by
    refine RingHom.Finite.comp hfin₁ hfin_inv
  have hker₀ : Φ0 ((optionTriangularForward k d hd) f₁) = 0 := by
    rw [show Φ0 ((optionTriangularForward k d hd) f₁) = φ₁ f₁ by
      simpa [Φ0, AlgHom.comp_apply] using
        congrArg (fun F => φ₁ (F f₁)) (optionTriangularInverse_comp_forward d hd)]
    exact hf₁ker
  let e₂ := optionToTateAlgEquiv k (Fin n)
  let ψ0 : TateAlgebra (Fin n) k →ₐ[k] A :=
    Φ0.comp (TateAlgebra.rename k Function.Embedding.some)
  have hcontrRenameSome :
      IsContractiveHom
        ((TateAlgebra.rename k Function.Embedding.some :
          TateAlgebra (Fin n) k →ₐ[k] TateAlgebra (Option (Fin n)) k)) := by
    intro r
    refine norm_le_of_forall_coeff_le (TateAlgebra.rename k Function.Embedding.some r)
      (norm_nonneg r) ?_
    intro e
    by_cases h : e none = 0
    · simpa [TateAlgebra.rename, coeff_rename_some, h] using TateAlgebra.coeff_norm_le r e.some
    · simp [TateAlgebra.rename, coeff_rename_some, h]
  have hcontrψ0 : IsContractiveHom ψ0 := hcontrRenameSome.comp hcontr₀
  letI : Algebra (TateAlgebra (Fin n) k) A := ψ0.toAlgebra
  let Φk : TateAlgebra Unit (TateAlgebra (Fin n) k) →ₐ[k] A := Φ0.comp e₂.symm.toAlgHom
  have hΦcomm (a : TateAlgebra (Fin n) k) :
      Φk ((algebraMap (TateAlgebra (Fin n) k) (TateAlgebra Unit (TateAlgebra (Fin n) k))) a) =
        algebraMap (TateAlgebra (Fin n) k) A a := by
    change Φ0 (tateToOption _) = ψ0 a
    rw [htate_algMap]
    rfl
  let Φ : TateAlgebra Unit (TateAlgebra (Fin n) k) →ₐ[TateAlgebra (Fin n) k] A :=
    { toRingHom := Φk
      commutes' := hΦcomm }
  have hfinΦk : Φk.Finite :=
    RingHom.Finite.comp hfin₀ <| AlgHom.Finite.of_surjective e₂.symm.toAlgHom e₂.symm.surjective
  have hkerΦ : optionToTate ((optionTriangularForward k d hd) f₁) ∈ RingHom.ker Φ := by
    rw [RingHom.mem_ker]
    change Φ0 (tateToOption (optionToTate ((optionTriangularForward k d hd) f₁))) = 0
    simpa using hker₀
  have hwker : we.1 ∈ RingHom.ker Φ := by
    rw [RingHom.mem_ker]
    have hmul0 : Φ we.2 * Φ we.1 = 0 := by
      simpa [hdecomp, map_mul] using hkerΦ
    rcases hunit.map Φ with ⟨u, hu⟩
    have htmp : (u⁻¹.1 : A) * (Φ we.2 * Φ we.1) = 0 := by
      rw [hmul0, mul_zero]
    have htmp' : ((u⁻¹.1 : A) * Φ we.2) * Φ we.1 = 0 := by
      exact (mul_assoc (u⁻¹.1 : A) (Φ we.2) (Φ we.1)).symm ▸ htmp
    have hu' : (u⁻¹.1 : A) * Φ we.2 = 1 := by
      rw [← hu]
      exact u.inv_mul
    have hwe1 : Φ we.1 = ((u⁻¹.1 : A) * Φ we.2) * Φ we.1 := by
      rw [hu', one_mul]
    exact hwe1.trans htmp'
  have hfinψ0 : ψ0.Finite := TateAlgebra.weierstrass_finiteness hfinΦk hw hwker
  exact ⟨ψ0, hcontrψ0, hfinψ0⟩

variable (k) (A) in
/-- **Noether normalization**: Any nonzero strictly affinoid algebra admits a finite injective map
from a Tate algebra. -/
theorem noether_normalization : ∃ (σ : Type) (_ : Fintype σ) (φ : TateAlgebra σ k →ₐ[k] A)
    (_ : Function.Injective φ) (_ : IsContractiveHom φ), φ.Finite := by
  rcases exists_fin_contractve_presentation k A with ⟨n, φ, hcontr, hsurj⟩
  have hfin : φ.Finite := AlgHom.Finite.of_surjective φ hsurj
  clear hsurj
  induction n with
  | zero =>
      have hcomp_apply (r : k) :
          φ ((algebraMap k (TateAlgebra (Fin 0) k)) r) = (algebraMap k A) r := by simp
      have hcomp_inj : Function.Injective (φ.comp finZeroAlgEquiv.symm.toAlgHom) := by
        intro a b hab
        apply (algebraMap_isometry k A).injective
        rw [← hcomp_apply a, ← hcomp_apply b]
        exact hab
      have hinj : Function.Injective φ := by
        intro x y hxy
        apply finZeroAlgEquiv.injective
        apply hcomp_inj
        simpa [AlgHom.comp_apply] using hxy
      exact ⟨Fin 0, inferInstance, φ, hinj, hcontr, hfin⟩
  | succ n ih =>
      by_cases hinj : Function.Injective φ
      · exact ⟨Fin (n + 1), inferInstance, φ, hinj, hcontr, hfin⟩
      · rcases noether_normalization_drop φ hcontr hfin hinj with ⟨ψ, hψcontr, hψfin⟩
        exact ih ψ hψcontr hψfin

end IsStrictAffinoid

end noether_normalization
