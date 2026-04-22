/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.Valued.NormedValued

@[expose] public section

open Valued NormedField Filter

open scoped Topology

variable {σ τ : Type*} (s : σ)

section TateAlgebra

variable {R : Type*} [NormedCommRing R]

/-- Restricted multivariate power series: coefficients tend to `0` along `Filter.cofinite`. -/
def IsTate (σ : Type*) (R : Type*) [NormedCommRing R] (F : MvPowerSeries σ R) : Prop :=
  Tendsto (fun e : σ →₀ ℕ => ‖MvPowerSeries.coeff e F‖) cofinite (𝓝 0)

lemma isTate_iff (F : MvPowerSeries σ R) :
    IsTate σ R F ↔ ∀ ε > 0, {e : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e F‖}.Finite := by
  rw [IsTate, ← tendsto_zero_iff_norm_tendsto_zero, NormedAddGroup.tendsto_nhds_zero]
  constructor
  · intro h ε hε
    have h' := h ε hε
    rw [Filter.eventually_cofinite] at h'
    simpa [not_lt] using h'
  · intro h ε hε
    rw [Filter.eventually_cofinite]
    simpa [not_lt] using h ε hε

lemma coeff_le_of_isTate (F : MvPowerSeries σ R) (hF : IsTate σ R F) :
    ∃ C > 0, ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e F‖ ≤ C := by
  let s : Set ℝ := Set.range fun e : σ →₀ ℕ => ‖MvPowerSeries.coeff e F‖
  have hs : Bornology.IsBounded s := by
    simpa [s] using Metric.isBounded_range_of_tendsto_cofinite hF
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le hs
  refine ⟨max C 1, by positivity, ?_⟩
  intro e
  have hCe : ‖‖MvPowerSeries.coeff e F‖‖ ≤ C := hC _ ⟨e, rfl⟩
  have : ‖MvPowerSeries.coeff e F‖ ≤ C := by simpa using hCe
  exact this.trans (le_max_left _ _)

lemma isTate_C (r : R) : IsTate σ R (algebraMap R (MvPowerSeries σ R) r) := by
  classical
  rw [isTate_iff]
  intro ε hε
  refine (Set.finite_singleton (0 : σ →₀ ℕ)).subset ?_
  intro e he
  rw [Set.mem_setOf_eq] at he
  by_cases h : e = 0
  · simp [h]
  · exfalso
    change ε ≤ ‖MvPowerSeries.coeff e (MvPowerSeries.C r)‖ at he
    rw [MvPowerSeries.coeff_C, if_neg h, norm_zero] at he
    exact (not_le_of_gt hε) he

lemma isTate_X (s : σ) : IsTate σ R (MvPowerSeries.X s) := by
  classical
  rw [isTate_iff]
  intro ε hε
  refine (Set.finite_singleton (Finsupp.single s 1)).subset ?_
  intro e he
  rw [Set.mem_setOf_eq] at he
  by_cases h : e = Finsupp.single s 1
  · simp [h]
  · exfalso
    rw [MvPowerSeries.coeff_X, if_neg h, norm_zero] at he
    exact (not_le_of_gt hε) he

variable {α : Type*} [IsUltrametricDist R]

/-- The Tate algebra in variables `σ` over `k`, modelled as restricted multivariate power series. -/
def tateSubalgebra (σ : Type*) (R : Type*) [NormedCommRing R] [IsUltrametricDist R] :
    Subalgebra R (MvPowerSeries σ R) where
  carrier := {F : MvPowerSeries σ R | IsTate σ R F}
  mul_mem' {F} {G} hF hG := by
    classical
    obtain ⟨a, ha, hFa⟩ := coeff_le_of_isTate F hF
    obtain ⟨b, hb, hGb⟩ := coeff_le_of_isTate G hG
    simp only [isTate_iff] at hF hG ⊢
    intro ε hε
    let δ : ℝ := ε / max a b
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let SF : Set (σ →₀ ℕ) := {e | δ ≤ ‖MvPowerSeries.coeff e F‖}
    let SG : Set (σ →₀ ℕ) := {e | δ ≤ ‖MvPowerSeries.coeff e G‖}
    have hSF : SF.Finite := hF δ hδ
    have hSG : SG.Finite := hG δ hδ
    let T : Set (σ →₀ ℕ) := (fun pq : (σ →₀ ℕ) × (σ →₀ ℕ) => pq.1 + pq.2) '' (SF ×ˢ SG)
    have hT : T.Finite := (hSF.prod hSG).image _
    refine hT.subset ?_
    intro n hn
    simp only [T, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq] at hn ⊢
    by_contra hnot
    let t : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) := Finset.antidiagonal n
    have htne : t.Nonempty := by
      refine ⟨(0, n), ?_⟩
      simp [t]
    obtain ⟨i, hi, hsum⟩ := IsUltrametricDist.exists_norm_finset_sum_le t
      (fun pq => MvPowerSeries.coeff pq.1 F * MvPowerSeries.coeff pq.2 G)
    have hi' : i ∈ t := hi htne
    have hsum' : ‖MvPowerSeries.coeff n (F * G)‖ ≤
        ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ := by
      simpa [t, MvPowerSeries.coeff_mul] using hsum
    have hprodlt : ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ < ε := by
      have hnotboth : ¬ (i.1 ∈ SF ∧ i.2 ∈ SG) := by
        intro hiSG
        apply hnot
        refine ⟨i, ?_, ?_⟩
        · simpa [Set.mem_prod] using hiSG
        · simpa [t] using (Finset.mem_antidiagonal.mp hi')
      rcases not_and_or.mp hnotboth with hiF | hiG
      · have h1 : ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ ≤
            ‖MvPowerSeries.coeff i.1 F‖ * b := by
          calc
            ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖
                ≤ ‖MvPowerSeries.coeff i.1 F‖ * ‖MvPowerSeries.coeff i.2 G‖ := norm_mul_le _ _
            _ ≤ ‖MvPowerSeries.coeff i.1 F‖ * b := by
              exact mul_le_mul_of_nonneg_left (hGb _) (norm_nonneg _)
        have h2 : ‖MvPowerSeries.coeff i.1 F‖ * b < δ * b := by
          exact mul_lt_mul_of_pos_right (lt_of_not_ge hiF) hb
        have h3 : δ * b ≤ ε := by
          have hmb : b ≤ max a b := le_max_right _ _
          have hpos : 0 < max a b := lt_of_lt_of_le hb hmb
          have haux : ε * b / max a b ≤ ε := by
            exact (div_le_iff₀ hpos).2 (by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hmb hε.le)
          simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) h3
      · have h1 : ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ ≤
            a * ‖MvPowerSeries.coeff i.2 G‖ := by
          calc
            ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖
                ≤ ‖MvPowerSeries.coeff i.1 F‖ * ‖MvPowerSeries.coeff i.2 G‖ := norm_mul_le _ _
            _ ≤ a * ‖MvPowerSeries.coeff i.2 G‖ := by
              exact mul_le_mul_of_nonneg_right (hFa _) (norm_nonneg _)
        have h2 : a * ‖MvPowerSeries.coeff i.2 G‖ < a * δ := by
          exact mul_lt_mul_of_pos_left (lt_of_not_ge hiG) ha
        have h3 : a * δ ≤ ε := by
          have hma : a ≤ max a b := le_max_left _ _
          have hpos : 0 < max a b := lt_of_lt_of_le ha hma
          have haux : a * ε / max a b ≤ ε := by
            exact (div_le_iff₀ hpos).2 (by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hma hε.le)
          simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) h3
    exact (not_lt_of_ge hn) (lt_of_le_of_lt hsum' hprodlt)
  add_mem' {F} {G} hF hG := by
    simp only [isTate_iff] at hF hG ⊢
    intro ε hε
    refine ((hF ε hε).union (hG ε hε)).subset ?_
    intro e he
    simp only [Set.mem_union, Set.mem_setOf_eq] at he ⊢
    by_cases hFe : ε ≤ ‖MvPowerSeries.coeff e F‖
    · exact Or.inl hFe
    · right
      by_contra hGe
      have hsumlt : ‖MvPowerSeries.coeff e F + MvPowerSeries.coeff e G‖ < ε := by
        apply lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        exact max_lt (lt_of_not_ge hFe) (lt_of_not_ge hGe)
      exact (not_lt_of_ge he) (by simpa using hsumlt)
  algebraMap_mem' := by
    intro r
    exact isTate_C r

lemma mem_tateSubalgebra_iff (F : MvPowerSeries σ R) :
    F ∈ tateSubalgebra σ R ↔ ∀ ε > 0, {e : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e F‖}.Finite :=
  isTate_iff F

/-- The Tate algebra in variables `σ` over `R`, formed by restricted multivariate power series. -/
def TateAlgebra (σ : Type*) (R : Type*) [NormedCommRing R] [IsUltrametricDist R] : Type _ :=
  tateSubalgebra σ R

namespace TateAlgebra

deriving noncomputable instance CommRing for TateAlgebra

section inst

noncomputable instance : Algebra R (TateAlgebra σ R) :=
  inferInstanceAs (Algebra R (tateSubalgebra σ R))

noncomputable instance : Algebra (TateAlgebra σ R) (MvPowerSeries σ R) :=
  inferInstanceAs (Algebra (tateSubalgebra σ R) (MvPowerSeries σ R))

instance : IsScalarTower R (TateAlgebra τ R) (MvPowerSeries τ R) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance : Coe (TateAlgebra σ R) (MvPowerSeries σ R) where
  coe F := F.1

end inst

lemma coe_mk (F : MvPowerSeries σ R) (hF : IsTate σ R F) :
    ((⟨F, hF⟩ : TateAlgebra σ R) : MvPowerSeries σ R) = F := rfl

@[simp]
lemma coe_zero :
    ((0 : TateAlgebra σ R) : MvPowerSeries σ R) = 0 := rfl

@[simp]
lemma coe_one :
    ((1 : TateAlgebra σ R) : MvPowerSeries σ R) = 1 := rfl

@[simp]
lemma coe_add (F G : TateAlgebra σ R) :
    ((F + G : TateAlgebra σ R) : MvPowerSeries σ R) = (F : MvPowerSeries σ R) + G := rfl

@[simp]
lemma coe_mul (F G : TateAlgebra σ R) :
    ((F * G : TateAlgebra σ R) : MvPowerSeries σ R) = (F : MvPowerSeries σ R) * G := rfl

@[simp]
lemma coe_neg (F : TateAlgebra σ R) :
    ((- F : TateAlgebra σ R) : MvPowerSeries σ R) = - (F : MvPowerSeries σ R) := rfl

@[simp]
lemma coe_sub (F G : TateAlgebra σ R) :
    ((F - G : TateAlgebra σ R) : MvPowerSeries σ R) = (F : MvPowerSeries σ R) - G := rfl

@[simp]
lemma coe_algebraMap (r : R) :
    ((algebraMap R (TateAlgebra σ R) r : TateAlgebra σ R) : MvPowerSeries σ R) =
      algebraMap R (MvPowerSeries σ R) r := rfl

/-- The indeterminate `s` in the Tate algebra in variables `σ`. -/
noncomputable def X (s : σ) : TateAlgebra σ R := ⟨MvPowerSeries.X s, isTate_X s⟩

@[simp]
lemma coe_X (s : σ) : ((X s : TateAlgebra σ R) : MvPowerSeries σ R) = MvPowerSeries.X s := rfl

/-- The constant multivariate power series corresponding to an element of the base ring `R`. -/
noncomputable def C : R →ₐ[R] TateAlgebra σ R := IsScalarTower.toAlgHom R R (TateAlgebra σ R)

/-- The constant coefficient of a multivariate power series. -/
noncomputable def constantCoeff : TateAlgebra σ R →ₐ[R] R where
  toRingHom := MvPowerSeries.constantCoeff.comp (algebraMap (TateAlgebra σ R) (MvPowerSeries σ R))
  commutes' _ := rfl

theorem constantCoeff_apply (F : TateAlgebra σ R) : constantCoeff F = MvPowerSeries.coeff 0 F.1 :=
  rfl

@[simp]
theorem constantCoeff_C (r : R) : constantCoeff (σ := σ) (C r) = r :=
  rfl

section gaussNorm

/-- The Gauss norm on multivariate power series. -/
noncomputable def gaussNorm (F : TateAlgebra σ R) : ℝ := ⨆ e : σ →₀ ℕ, ‖F.1.coeff e‖

lemma gaussNorm_bddAbove (F : TateAlgebra σ R) :
    BddAbove (Set.range fun e : σ →₀ ℕ => ‖MvPowerSeries.coeff e F.val‖) := by
  obtain ⟨C, -, hC⟩ := coeff_le_of_isTate F.1 F.2
  exact ⟨C, by rintro y ⟨e, rfl⟩; exact hC e⟩

lemma gaussNorm_nonneg (F : TateAlgebra σ R) : 0 ≤ F.gaussNorm :=
  le_trans (norm_nonneg _) (le_ciSup (gaussNorm_bddAbove F) 0)

lemma gaussNorm_eq_zero (F : TateAlgebra σ R) (hF : F.gaussNorm = 0) : F = 0 := by
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro e
  have hle : ‖MvPowerSeries.coeff e F.1‖ ≤ F.gaussNorm := le_ciSup (gaussNorm_bddAbove F) e
  exact norm_eq_zero.mp (le_antisymm (by simpa [hF] using hle) (norm_nonneg _))

lemma gaussNorm_add_le (F G : TateAlgebra σ R) :
    (F + G).gaussNorm ≤ F.gaussNorm + G.gaussNorm := by
  refine ciSup_le ?_
  intro e
  calc
    _ ≤ ‖MvPowerSeries.coeff e F.1‖ + ‖MvPowerSeries.coeff e G.1‖ := by
      simpa using norm_add_le (MvPowerSeries.coeff e F.1) (MvPowerSeries.coeff e G.1)
    _ ≤ F.gaussNorm + G.gaussNorm := by
      exact add_le_add (le_ciSup F.gaussNorm_bddAbove e) (le_ciSup G.gaussNorm_bddAbove e)

lemma gaussNorm_add_le_max (F G : TateAlgebra σ R) :
    (F + G).gaussNorm ≤ max (F.gaussNorm) (G.gaussNorm) := by
  refine ciSup_le ?_
  intro e
  calc
    _ ≤ max ‖MvPowerSeries.coeff e F.1‖ ‖MvPowerSeries.coeff e G.1‖ :=
      IsUltrametricDist.norm_add_le_max (MvPowerSeries.coeff e F.1) (MvPowerSeries.coeff e G.1)
    _ ≤ max (F.gaussNorm) (G.gaussNorm) :=
      max_le_max (le_ciSup F.gaussNorm_bddAbove e) (le_ciSup G.gaussNorm_bddAbove e)

lemma gaussNorm_mul_le (F G : TateAlgebra σ R) :
    (F * G).gaussNorm ≤ F.gaussNorm * G.gaussNorm := by
  classical
  refine ciSup_le ?_
  intro n
  let t : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) := Finset.antidiagonal n
  have htne : t.Nonempty := by
    refine ⟨(0, n), ?_⟩
    simp [t]
  obtain ⟨i, hi, hsum⟩ := IsUltrametricDist.exists_norm_finset_sum_le t
    (fun pq => MvPowerSeries.coeff pq.1 F.1 * MvPowerSeries.coeff pq.2 G.1)
  have hsum' : ‖MvPowerSeries.coeff n (F.1 * G.1)‖ ≤
      ‖MvPowerSeries.coeff i.1 F.1 * MvPowerSeries.coeff i.2 G.1‖ := by
    simpa [t, MvPowerSeries.coeff_mul] using hsum
  calc
    ‖MvPowerSeries.coeff n (F.1 * G.1)‖ ≤
        ‖MvPowerSeries.coeff i.1 F.1 * MvPowerSeries.coeff i.2 G.1‖ := hsum'
    _ ≤ ‖MvPowerSeries.coeff i.1 F.1‖ * ‖MvPowerSeries.coeff i.2 G.1‖ := norm_mul_le _ _
    _ ≤ ‖MvPowerSeries.coeff i.1 F.1‖ * G.gaussNorm :=
      mul_le_mul_of_nonneg_left (le_ciSup G.gaussNorm_bddAbove i.2) (norm_nonneg _)
    _ ≤ F.gaussNorm * G.gaussNorm :=
      mul_le_mul_of_nonneg_right (le_ciSup F.gaussNorm_bddAbove i.1) (gaussNorm_nonneg G)

lemma gaussNorm_neg (F : TateAlgebra σ R) : (-F).gaussNorm = F.gaussNorm := by
  unfold gaussNorm
  congr with e
  simp

lemma gaussNorm_C (r : R) : (C (σ := σ) r).gaussNorm = ‖r‖ := by
  classical
  refine le_antisymm ?_ ?_
  · refine ciSup_le ?_
    intro e
    by_cases h : e = 0
    · subst h
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      change ‖MvPowerSeries.constantCoeff (MvPowerSeries.C r)‖ ≤ ‖r‖
      simp
    · change ‖(MvPowerSeries.coeff e) (MvPowerSeries.C r)‖ ≤ ‖r‖
      simp [MvPowerSeries.coeff_C, h]
  · exact le_ciSup (gaussNorm_bddAbove (C (σ := σ) r)) (0 : σ →₀ ℕ)

end gaussNorm

/-- The Gauss norm equips the Tate algebra with a `RingNorm`. -/
noncomputable def ringNorm : RingNorm (TateAlgebra σ R) where
  toFun F := F.gaussNorm
  map_zero' := by simp [gaussNorm]
  add_le' := gaussNorm_add_le
  neg' := gaussNorm_neg
  mul_le' := gaussNorm_mul_le
  eq_zero_of_map_eq_zero' := gaussNorm_eq_zero

noncomputable instance : NormedCommRing (TateAlgebra σ R) where
  toNormedRing := RingNorm.toNormedRing ringNorm
  mul_comm := mul_comm

lemma norm_def (F : TateAlgebra σ R) : ‖F‖ = F.gaussNorm := rfl

lemma coeff_norm_le (F : TateAlgebra σ R) (e : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff e F.1‖ ≤ ‖F‖ :=
  le_ciSup (gaussNorm_bddAbove F) e

instance : IsUltrametricDist (TateAlgebra σ R) where
  dist_triangle_max x y z := by
    calc
      dist x z = ‖(x - y) + (y - z)‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ ≤ max ‖x - y‖ ‖y - z‖ := gaussNorm_add_le_max (x - y) (y - z)
      _ = max (dist x y) (dist y z) := by simp [dist_eq_norm]

lemma coeff_dist_le (e : σ →₀ ℕ) (F G : TateAlgebra σ R) :
    dist (MvPowerSeries.coeff e F.1) (MvPowerSeries.coeff e G.1) ≤ dist F G := by
  simpa [dist_eq_norm, dist_eq_norm] using coeff_norm_le (F - G) e

lemma coeff_lipschitz (e : σ →₀ ℕ) :
    LipschitzWith 1 (fun F : TateAlgebra σ R => MvPowerSeries.coeff e F.1) := by
  intro F G
  simpa [edist_dist, ENNReal.coe_one, one_mul] using
    ENNReal.ofReal_le_ofReal (coeff_dist_le e F G)

instance [CompleteSpace R] : CompleteSpace (TateAlgebra σ R) := by
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  let f : MvPowerSeries σ R := fun e => limUnder atTop (fun n => MvPowerSeries.coeff e (u n).1)
  have hcoeffCauchy (e : σ →₀ ℕ) :
      CauchySeq (fun n => MvPowerSeries.coeff e (u n).1) := by
    exact (coeff_lipschitz e).cauchySeq_comp hu
  have hcoeff_tendsto (e : σ →₀ ℕ) :
      Tendsto (fun n => MvPowerSeries.coeff e (u n).1) atTop (nhds (MvPowerSeries.coeff e f)) := by
    simpa [f] using CauchySeq.tendsto_limUnder (hcoeffCauchy e)
  have hclose_to_fixed {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
      (hN : ∀ n ≥ N, dist (u n) (u N) < ε) :
      ∀ e : σ →₀ ℕ, dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1) ≤ ε := by
    intro e
    have hmem : MvPowerSeries.coeff e f ∈ Metric.closedBall (MvPowerSeries.coeff e (u N).1) ε := by
      apply IsClosed.mem_of_tendsto Metric.isClosed_closedBall (hcoeff_tendsto e)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      rw [Metric.mem_closedBall]
      exact (coeff_dist_le e (u n) (u N)).trans (le_of_lt (hN n hn))
    simpa [Metric.mem_closedBall] using hmem
  have hf_tate : IsTate σ R f := by
    rw [isTate_iff]
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by positivity
    have hδε : δ < ε := by
      dsimp [δ]
      linarith
    rcases (Metric.cauchySeq_iff'.mp hu) δ hδ with ⟨N, hN⟩
    refine ((isTate_iff (u N).1).mp (u N).2 δ hδ).subset ?_
    intro e he
    rw [Set.mem_setOf_eq] at he ⊢
    have hdist : dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1) ≤ δ :=
      hclose_to_fixed hδ.le N hN e
    by_contra hsmall
    have huNlt : ‖MvPowerSeries.coeff e (u N).1‖ < δ := lt_of_not_ge hsmall
    have hnorm :
        ‖MvPowerSeries.coeff e f‖ ≤
          max (dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1))
            (dist (MvPowerSeries.coeff e (u N).1) 0) := by
      simpa [dist_eq_norm] using
        (dist_triangle_max (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1) (0 : R))
    have hmaxlt :
        max (dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1))
            (dist (MvPowerSeries.coeff e (u N).1) 0) < ε := by
      apply max_lt_iff.mpr
      constructor
      · exact lt_of_le_of_lt hdist hδε
      · simpa [dist_eq_norm] using lt_of_lt_of_le huNlt (le_of_lt hδε)
    exact (not_lt_of_ge he) (lt_of_le_of_lt hnorm hmaxlt)
  let F : TateAlgebra σ R := ⟨f, hf_tate⟩
  refine ⟨F, (Metric.tendsto_atTop.2 ?_)⟩
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by positivity
  have hδε : δ < ε := by
    dsimp [δ]
    linarith
  rcases (Metric.cauchySeq_iff'.mp hu) δ hδ with ⟨N, hN⟩
  have hNF :
      ∀ e : σ →₀ ℕ, dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1) ≤ δ :=
    hclose_to_fixed hδ.le N hN
  refine ⟨N, ?_⟩
  intro n hn
  have hdist : dist (u n) F ≤ δ := by
    rw [dist_eq_norm]
    refine ciSup_le ?_
    intro e
    have htri :
        dist (MvPowerSeries.coeff e (u n).1) (MvPowerSeries.coeff e f) ≤
          max (dist (MvPowerSeries.coeff e (u n).1) (MvPowerSeries.coeff e (u N).1))
            (dist (MvPowerSeries.coeff e (u N).1) (MvPowerSeries.coeff e f)) := by
      simpa [max_comm, max_left_comm, max_assoc] using
        (dist_triangle_max (MvPowerSeries.coeff e (u n).1)
          (MvPowerSeries.coeff e (u N).1) (MvPowerSeries.coeff e f))
    have hcoeff :
        dist (MvPowerSeries.coeff e (u n).1) (MvPowerSeries.coeff e f) ≤ δ := by
      exact le_trans htri <| max_le
        ((coeff_dist_le e (u n) (u N)).trans (le_of_lt (hN n hn)))
        (by simpa [dist_comm] using hNF e)
    simpa [dist_eq_norm] using hcoeff
  exact lt_of_le_of_lt hdist hδε

omit [IsUltrametricDist R] in
lemma isTate_rename (e : σ ↪ τ) (F : MvPowerSeries σ R) (hF : IsTate σ R F) :
    IsTate τ R (MvPowerSeries.rename e F) := by
  rw [isTate_iff] at hF ⊢
  intro ε hε
  refine ((hF ε hε).image (Finsupp.embDomain e)).subset ?_
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  by_cases hxr : x ∈ Set.range (Finsupp.embDomain e)
  · rcases hxr with ⟨y, rfl⟩
    refine ⟨y, ?_, rfl⟩
    simpa using hx
  · exfalso
    have hzero : MvPowerSeries.coeff x (MvPowerSeries.rename e F) = 0 :=
      MvPowerSeries.coeff_rename_eq_zero e F (by
        simpa [Finsupp.embDomain_eq_mapDomain] using hxr)
    have : ε ≤ (0 : ℝ) := by simpa [hzero] using hx
    exact (not_le_of_gt hε) this

variable (R) in
/-- Reindex the variables of a Tate algebra along an injection, giving an algebra homomorphism. -/
noncomputable def rename (e : σ ↪ τ) : TateAlgebra σ R →ₐ[R] TateAlgebra τ R where
  toFun F := ⟨MvPowerSeries.rename e F.1, isTate_rename e F.1 F.2⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_one' := by
    apply Subtype.ext
    simp
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_mul' _ _ := by
    apply Subtype.ext
    simp
  commutes' := by
    intro r
    apply Subtype.ext
    simp

@[simp]
lemma coe_rename (e : σ ↪ τ) (F : TateAlgebra σ R) :
    (rename R e F).1 = MvPowerSeries.rename e (F : MvPowerSeries σ R) := rfl

@[simp]
lemma rename_X (e : σ ↪ τ) (s : σ) :
    rename R e (X s) = X (e s) := by
  apply Subtype.ext
  simp [rename]

lemma rename_norm_le (e : σ ↪ τ) (F : TateAlgebra σ R) :
    ‖rename R e F‖ ≤ ‖F‖ := by
  refine ciSup_le ?_
  intro x
  by_cases hxr : x ∈ Set.range (Finsupp.embDomain e)
  · rcases hxr with ⟨y, rfl⟩
    simpa using coeff_norm_le F y
  · have hzero :
        MvPowerSeries.coeff x
            (show MvPowerSeries τ R from (rename R e F : TateAlgebra τ R)) = 0 := by
      exact MvPowerSeries.coeff_rename_eq_zero e F.1
        (by simpa [Finsupp.embDomain_eq_mapDomain] using hxr)
    rw [hzero, norm_zero]
    exact gaussNorm_nonneg F

lemma rename_norm_eq (e : σ ≃ τ) (F : TateAlgebra σ R) :
    ‖rename R e.toEmbedding F‖ = ‖F‖ := by
  apply le_antisymm
  · exact rename_norm_le e.toEmbedding F
  · have hleft :
        rename R e.symm.toEmbedding
            (rename R e.toEmbedding F) = F := by
      apply Subtype.ext
      simp
    calc
      ‖F‖ = ‖rename R e.symm.toEmbedding
          (rename R e.toEmbedding F)‖ := by
          simp [hleft]
      _ ≤ ‖rename R e.toEmbedding F‖ :=
        rename_norm_le e.symm.toEmbedding _

lemma exists_coeff_norm_eq_norm (F : TateAlgebra σ R) (hF : F ≠ 0) :
    ∃ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e F.1‖ = ‖F‖ := by
  let M : ℝ := ‖F‖
  let S : Set (σ →₀ ℕ) := {e | M / 2 ≤ ‖MvPowerSeries.coeff e F.1‖}
  have hMpos : 0 < M := by
    simpa [M] using (norm_pos_iff.mpr hF)
  have hSfin : S.Finite := by
    simpa [M, S] using (isTate_iff F.1).mp F.2 (M / 2) (by positivity)
  have hSne : S.Nonempty := by
    by_contra hSempty
    have hbound : ‖F‖ ≤ M / 2 := by
      refine ciSup_le ?_
      intro e
      have heS : e ∉ S := by
        intro heS
        exact hSempty ⟨e, heS⟩
      exact le_of_lt (lt_of_not_ge heS)
    have : M ≤ M / 2 := by simpa [M] using hbound
    linarith
  let s : Finset (σ →₀ ℕ) := hSfin.toFinset
  have hsne : s.Nonempty := by
    simpa [s] using (hSfin.toFinset_nonempty.mpr hSne)
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image s
    (fun e : σ →₀ ℕ => ‖MvPowerSeries.coeff e F.1‖) hsne
  have heS : e ∈ S := by
    simpa [s] using (hSfin.mem_toFinset.mp he)
  have heHalf : M / 2 ≤ ‖MvPowerSeries.coeff e F.1‖ := heS
  have heUpper : ‖MvPowerSeries.coeff e F.1‖ ≤ M := by
    simpa [M] using coeff_norm_le F e
  have hnorm_le : ‖F‖ ≤ ‖MvPowerSeries.coeff e F.1‖ := by
    refine ciSup_le ?_
    intro d
    by_cases hdS : d ∈ S
    · have hd : d ∈ s := by
        simpa [s] using (hSfin.mem_toFinset.mpr hdS)
      exact hmax d hd
    · exact le_trans (le_of_lt (lt_of_not_ge hdS)) heHalf
  refine ⟨e, le_antisymm heUpper ?_⟩
  simpa [M] using hnorm_le

lemma exists_lex_min_coeff_norm_eq_norm [LinearOrder σ] (F : TateAlgebra σ R) (hF : F ≠ 0) :
    ∃ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e F.1‖ = ‖F‖ ∧
      ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d F.1‖ = ‖F‖ → (toLex e : Lex (σ →₀ ℕ)) ≤ toLex d := by
  let S : Set (σ →₀ ℕ) := {e | ‖F‖ ≤ ‖MvPowerSeries.coeff e F.1‖}
  have hnorm_pos : 0 < ‖F‖ := by
    simpa using (norm_pos_iff.mpr hF)
  have hSfin : S.Finite := (isTate_iff F.1).mp F.2 ‖F‖ hnorm_pos
  obtain ⟨e₀, he₀⟩ := exists_coeff_norm_eq_norm F hF
  have hSne : S.Nonempty := by
    refine ⟨e₀, ?_⟩
    simp [S, he₀]
  let s : Finset (σ →₀ ℕ) := hSfin.toFinset
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image s
    (fun e : σ →₀ ℕ => (toLex e : Lex (σ →₀ ℕ))) (hSfin.toFinset_nonempty.mpr hSne)
  refine ⟨e, ?_, ?_⟩
  · exact le_antisymm (coeff_norm_le F e) (hSfin.mem_toFinset.mp he)
  · intro d hd
    have hdS : d ∈ S := by simp [S, hd]
    exact hmin d (hSfin.mem_toFinset.mpr hdS)

section NormOneClass

variable [NormOneClass R]

instance : NormOneClass (TateAlgebra σ R) where
  norm_one := (TateAlgebra.gaussNorm_C (σ := σ) (R := R) 1).trans <| by simp

lemma norm_X_le_one : ‖(X s : TateAlgebra σ R)‖ ≤ 1 := by
  classical
  refine ciSup_le ?_
  intro n
  by_cases h : n = Finsupp.single s 1 <;> simp [MvPowerSeries.coeff_X, h]

end NormOneClass

section NormMulClass

variable [NormMulClass R]

lemma norm_mul_eq_of_ordered [LinearOrder σ] (F G : TateAlgebra σ R) : ‖F * G‖ = ‖F‖ * ‖G‖ := by
  by_cases hF : F = 0
  · simp [hF]
  by_cases hG : G = 0
  · simp [hG]
  have hFpos : 0 < ‖F‖ := by
    simpa using (norm_pos_iff.mpr hF)
  have hGpos : 0 < ‖G‖ := by
    simpa using (norm_pos_iff.mpr hG)
  obtain ⟨p, hpnorm, hpmin⟩ := exists_lex_min_coeff_norm_eq_norm F hF
  obtain ⟨q, hqnorm, hqmin⟩ := exists_lex_min_coeff_norm_eq_norm G hG
  let i0 : (σ →₀ ℕ) × (σ →₀ ℕ) := (p, q)
  let t : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) := Finset.antidiagonal (p + q)
  let u : ((σ →₀ ℕ) × (σ →₀ ℕ)) → R := fun ij =>
    MvPowerSeries.coeff ij.1 F.1 * MvPowerSeries.coeff ij.2 G.1
  have hi0 : i0 ∈ t := by
    simp [i0, t]
  have hi0norm : ‖u i0‖ = ‖F‖ * ‖G‖ := by
    simp [u, i0, hpnorm, hqnorm, norm_mul]
  have hrestlt : ∀ ij ∈ t.erase i0, ‖u ij‖ < ‖u i0‖ := by
    intro ij hij
    have hij_ne : ij ≠ i0 := (Finset.mem_erase.mp hij).1
    have hij_mem : ij ∈ t := (Finset.mem_erase.mp hij).2
    have hadd : ij.1 + ij.2 = p + q := by
      simpa [t] using (Finset.mem_antidiagonal.mp hij_mem)
    have h1le : ‖MvPowerSeries.coeff ij.1 F.1‖ ≤ ‖F‖ := coeff_norm_le F ij.1
    have h2le : ‖MvPowerSeries.coeff ij.2 G.1‖ ≤ ‖G‖ := coeff_norm_le G ij.2
    have hnotboth :
        ¬ (‖MvPowerSeries.coeff ij.1 F.1‖ = ‖F‖ ∧ ‖MvPowerSeries.coeff ij.2 G.1‖ = ‖G‖) := by
      intro hboth
      have hp_le : (toLex p : Lex (σ →₀ ℕ)) ≤ toLex ij.1 := hpmin ij.1 hboth.1
      have hq_le : (toLex q : Lex (σ →₀ ℕ)) ≤ toLex ij.2 := hqmin ij.2 hboth.2
      have hadd' : (toLex ij.1 : Lex (σ →₀ ℕ)) + toLex ij.2 = toLex p + toLex q := by
        simpa using congrArg toLex hadd
      rcases trichotomy_of_add_eq_add hadd' with hEq | hiLt | hjLt
      · have hEq1 : ij.1 = p := by
          simpa using congrArg ofLex hEq.1
        have hEq2 : ij.2 = q := by
          simpa using congrArg ofLex hEq.2
        exact hij_ne (Prod.ext hEq1 hEq2)
      · exact hiLt.not_ge hp_le
      · exact hjLt.not_ge hq_le
    have hstrict :
        ‖MvPowerSeries.coeff ij.1 F.1‖ < ‖F‖ ∨ ‖MvPowerSeries.coeff ij.2 G.1‖ < ‖G‖ := by
      by_cases h1 : ‖MvPowerSeries.coeff ij.1 F.1‖ = ‖F‖
      · right
        have h2ne : ‖MvPowerSeries.coeff ij.2 G.1‖ ≠ ‖G‖ := by
          intro h2
          exact hnotboth ⟨h1, h2⟩
        exact lt_of_le_of_ne h2le h2ne
      · left
        exact lt_of_le_of_ne h1le h1
    rcases hstrict with h1lt | h2lt
    · calc
        ‖u ij‖ = ‖MvPowerSeries.coeff ij.1 F.1‖ * ‖MvPowerSeries.coeff ij.2 G.1‖ := by
          simp [u, norm_mul]
        _ ≤ ‖MvPowerSeries.coeff ij.1 F.1‖ * ‖G‖ := by
          exact mul_le_mul_of_nonneg_left h2le (norm_nonneg _)
        _ < ‖F‖ * ‖G‖ := by
          exact mul_lt_mul_of_pos_right h1lt hGpos
        _ = ‖u i0‖ := hi0norm.symm
    · calc
        ‖u ij‖ = ‖MvPowerSeries.coeff ij.1 F.1‖ * ‖MvPowerSeries.coeff ij.2 G.1‖ := by
          simp [u, norm_mul]
        _ ≤ ‖F‖ * ‖MvPowerSeries.coeff ij.2 G.1‖ := by
          exact mul_le_mul_of_nonneg_right h1le (norm_nonneg _)
        _ < ‖F‖ * ‖G‖ := by
          exact mul_lt_mul_of_pos_left h2lt hFpos
        _ = ‖u i0‖ := hi0norm.symm
  have hrest : ‖∑ ij ∈ t.erase i0, u ij‖ < ‖u i0‖ := by
    by_cases hrestne : (t.erase i0).Nonempty
    · obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (t.erase i0) (fun ij => ‖u ij‖) hrestne
      have hsumle : ‖∑ ij ∈ t.erase i0, u ij‖ ≤ ‖u j‖ := by
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty hrestne hjmax
      exact lt_of_le_of_lt hsumle (hrestlt j hj)
    · have hEq : t.erase i0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrestne
      rw [hEq, Finset.sum_empty, hi0norm]
      simpa using mul_pos hFpos hGpos
  have hcoeff :
      MvPowerSeries.coeff (p + q) ((F * G).1) = u i0 + ∑ ij ∈ t.erase i0, u ij := by
    calc
      MvPowerSeries.coeff (p + q) ((F * G).1) = ∑ ij ∈ t, u ij := by
        simp [t, u, MvPowerSeries.coeff_mul]
      _ = u i0 + ∑ ij ∈ t.erase i0, u ij := by
        exact (Finset.add_sum_erase t u hi0).symm
  have hcoeffnorm : ‖MvPowerSeries.coeff (p + q) ((F * G).1)‖ = ‖u i0‖ := by
    rw [hcoeff]
    have hne : ‖u i0‖ ≠ ‖∑ ij ∈ t.erase i0, u ij‖ := ne_of_gt hrest
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left_of_lt hrest]
  have hlow : ‖F‖ * ‖G‖ ≤ ‖F * G‖ := by
    calc
      ‖F‖ * ‖G‖ = ‖MvPowerSeries.coeff (p + q) ((F * G).1)‖ := by
        rw [hcoeffnorm, hi0norm]
      _ ≤ ‖F * G‖ := coeff_norm_le (F * G) (p + q)
  exact le_antisymm (gaussNorm_mul_le F G) hlow

instance [Finite σ] : NormMulClass (TateAlgebra σ R) where
  norm_mul F G := by
    let : Fintype σ := Fintype.ofFinite σ
    let τ := Fin (Fintype.card σ)
    let e : σ ≃ τ := Fintype.equivFin σ
    let φ : TateAlgebra σ R →ₐ[R] TateAlgebra τ R := rename R e.toEmbedding
    calc
      ‖F * G‖ = ‖φ (F * G)‖ := (rename_norm_eq e (F * G)).symm
      _ = ‖φ F * φ G‖ := by simp [φ]
      _ = ‖φ F‖ * ‖φ G‖ := norm_mul_eq_of_ordered (φ F) (φ G)
      _ = ‖F‖ * ‖G‖ := by
        rw [rename_norm_eq e F, rename_norm_eq e G]

end NormMulClass

end TateAlgebra

section toTate

namespace MvPolynomial

/-- The natural embedding of multivariate polynomials into the Tate algebra. -/
noncomputable def toTate : MvPolynomial σ R →ₐ[R] TateAlgebra σ R :=
  MvPolynomial.aeval TateAlgebra.X

noncomputable instance : Coe (MvPolynomial σ R) (TateAlgebra σ R) := ⟨toTate⟩

lemma toTate_X :  (MvPolynomial.X s).toTate = TateAlgebra.X (σ := σ) (R := R) s := by
  simp [toTate]

lemma toTate_coe (p : MvPolynomial σ R) :
    (p.toTate : MvPowerSeries σ R) = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [toTate]
      rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [toTate_X, hp]

variable (σ R) in
lemma toTate_denseRange : DenseRange (toTate (σ := σ) (R := R)) := by
  classical
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by positivity
  let S : Set (σ →₀ ℕ) := {e | δ ≤ ‖MvPowerSeries.coeff e f.1‖}
  have hSfin : S.Finite := (isTate_iff f.1).mp f.2 δ hδ
  let s : Finset (σ →₀ ℕ) := hSfin.toFinset
  let n : σ →₀ ℕ := s.sup id
  let p : MvPolynomial σ R := (MvPowerSeries.trunc' R n) f.1
  let q : TateAlgebra σ R := p.toTate
  refine ⟨q, ⟨p, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have hcoeff (m : σ →₀ ℕ) : MvPowerSeries.coeff m (f.1 - q.1) =
      if m ≤ n then 0 else MvPowerSeries.coeff m f.1 := by
    rw [toTate_coe p]
    rw [LinearMap.map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc']
    split_ifs <;> simp
  have hbound (m : σ →₀ ℕ) : ‖MvPowerSeries.coeff m (f.1 - q.1)‖ ≤ δ := by
    rw [hcoeff]
    by_cases hm : m ≤ n
    · simp [hm, le_of_lt hδ]
    · have hmS : m ∉ S := by
        intro hm'
        exact hm (show id m ≤ s.sup id from Finset.le_sup (hSfin.mem_toFinset.mpr hm'))
      simpa [hm] using le_of_lt (lt_of_not_ge hmS)
  have hδε : δ < ε := by
    dsimp [δ]
    linarith
  exact lt_of_le_of_lt (ciSup_le hbound) hδε

end MvPolynomial

end toTate

/-- A morphism of normed commutative rings is contractive if it does not increase norms. -/
def IsContractiveHom {A B : Type*} [SeminormedRing A] [SeminormedRing B] (f : A →+* B) : Prop :=
  ∀ a : A, ‖f a‖ ≤ ‖a‖

lemma IsContractiveHom.comp {A B C : Type*} [SeminormedRing A] [SeminormedRing B] [SeminormedRing C]
    {f : A →+* B} {g : B →+* C} (hf : IsContractiveHom f) (hg : IsContractiveHom g) :
    IsContractiveHom (g.comp f) := by
  intro x
  exact le_trans (hg _) (hf _)

lemma TateAlgebra.rename_isContractiveHom (e : σ ↪ τ) :
    IsContractiveHom (rename R e).toRingHom :=
  rename_norm_le e

/-- A morphism of normed commutative rings is admissible if the induced quotient norm on its
image is equivalent to the restricted norm from the target. -/
def IsAdmissibleHom {A B : Type*} [SeminormedRing A] [SeminormedRing B] (f : A →+* B) : Prop :=
  ∃ C > 0, ∀ x : A, sInf {r : ℝ | ∃ a : A, f a = f x ∧ ‖a‖ = r} ≤ C * ‖f x‖ ∧ ‖f x‖ ≤ C * ‖x‖

section NormField

variable {k : Type*} [NormedField k] [IsUltrametricDist k]

noncomputable instance (σ : Type*) : NormedAlgebra k (TateAlgebra σ k) where
  norm_smul_le r x := by
    rw [Algebra.smul_def]
    calc _ ≤ ‖algebraMap k (TateAlgebra σ k) r‖ * ‖x‖ := norm_mul_le _ _
      _ = ‖r‖ * ‖x‖ := by
        congr
        exact TateAlgebra.gaussNorm_C r

/-- A strict and reduced `k`-affinoid algebra with its spectral norm, modeled here as a
non-Archimedean normed algebra admitting an admissible surjective Tate algebra presentation. -/
class IsStrictAffinoid (k : Type*) [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (A : Type*) [NormedCommRing A] [NormedAlgebra k A] :
    Prop extends NormOneClass A, CompleteSpace A, IsUltrametricDist A where
  withSpectralNorm (n : ℕ) (a : A) : ‖a ^n‖ = ‖a‖ ^ n
  presentation (k A) : ∃ (σ : Type) (_ : Fintype σ) (φ : TateAlgebra σ k →ₐ[k] A)
    (_ : IsAdmissibleHom φ.toRingHom), Function.Surjective φ

variable [CompleteSpace k] {A : Type*} [NormedCommRing A] [NormedAlgebra k A] [IsStrictAffinoid k A]

namespace IsStrictAffinoid

instance {σ : Type*} [Finite σ] : IsStrictAffinoid k (TateAlgebra σ k) where
  withSpectralNorm n a := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, ih]
  presentation := by
    let τ : Type := Shrink.{0} σ
    let e : σ ≃ τ := equivShrink.{0} σ
    let φ : TateAlgebra τ k →ₐ[k] TateAlgebra σ k := TateAlgebra.rename k e.symm.toEmbedding
    let ψ : TateAlgebra σ k →ₐ[k] TateAlgebra τ k := TateAlgebra.rename k e.toEmbedding
    have hψφ : ψ.comp φ = AlgHom.id k (TateAlgebra τ k) := by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      simp [φ, ψ, TateAlgebra.rename]
    have hφψ : φ.comp ψ = AlgHom.id k (TateAlgebra σ k) := by
      ext
      simp [φ, ψ, TateAlgebra.rename]
    refine ⟨τ, Fintype.ofFinite τ, φ, ?_, ?_⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x
      constructor
      · let Q : Set ℝ := {r : ℝ | ∃ a : TateAlgebra τ k, φ.toRingHom a = φ.toRingHom x ∧ ‖a‖ = r}
        have hQbdd : BddBelow Q := by
          refine ⟨0, ?_⟩
          intro r hr
          rcases hr with ⟨a, -, rfl⟩
          exact norm_nonneg _
        have hxmem : ‖x‖ ∈ Q := ⟨x, rfl, rfl⟩
        refine le_trans (csInf_le hQbdd hxmem) ?_
        have hcontract := TateAlgebra.rename_isContractiveHom e.toEmbedding (φ x)
        have hleft : ψ (φ x) = x := by
          have h := congrArg (fun f : TateAlgebra τ k →ₐ[k] TateAlgebra τ k => f x) hψφ
          simpa [AlgHom.comp_apply, φ, ψ] using h
        simpa [φ, ψ, hleft, one_mul] using hcontract
      · simpa [φ, one_mul] using TateAlgebra.rename_isContractiveHom e.symm.toEmbedding x
    · intro y
      refine ⟨ψ y, ?_⟩
      have h := congrArg (fun f : TateAlgebra σ k →ₐ[k] TateAlgebra σ k => f y) hφψ
      simpa [AlgHom.comp_apply, φ, ψ] using h

lemma isContractiveHom_of_admissible {B : Type*} [NormedCommRing B] [NormedAlgebra k B]
    [IsStrictAffinoid k B] {f : A →ₐ[k] B} (ha : IsAdmissibleHom f.toRingHom) :
    IsContractiveHom f.toRingHom := by
  rcases ha with ⟨C, hCpos, hC⟩
  intro x
  by_cases hx0 : ‖x‖ = 0
  · have hx : x = 0 := norm_eq_zero.mp hx0
    simp [hx]
  · by_contra hfx
    have hlt : ‖x‖ < ‖f x‖ := lt_of_not_ge hfx
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
    let r : ℝ := ‖f x‖ / ‖x‖
    have hr : 1 < r := by
      dsimp [r]
      have hdiv : ‖x‖ / ‖x‖ < ‖f x‖ / ‖x‖ := by
        exact div_lt_div_of_pos_right hlt hxpos
      simpa [hxpos.ne'] using hdiv
    have hpow (n : ℕ) : r ^ n ≤ C := by
      dsimp [r]
      have hmain : ‖f x‖ ^ n ≤ C * ‖x‖ ^ n := by
        calc
          ‖f x‖ ^ n = ‖(f x) ^ n‖ := by
            rw [IsStrictAffinoid.withSpectralNorm k n (f x)]
          _ = ‖f (x ^ n)‖ := by simp
          _ ≤ C * ‖x ^ n‖ := (hC (x ^ n)).2
          _ = C * ‖x‖ ^ n := by
            rw [IsStrictAffinoid.withSpectralNorm k n x]
      have hxpowpos : 0 < ‖x‖ ^ n := pow_pos hxpos _
      rw [div_pow]
      exact (div_le_iff₀ hxpowpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hr
    exact (not_lt_of_ge (hpow n)) hn

variable (k) (A) in
lemma exists_fin_contractve_presentation :
    ∃ (n : ℕ) (φ : TateAlgebra (Fin n) k →ₐ[k] A) (_ : IsContractiveHom φ.toRingHom),
    Function.Surjective φ := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, hφadm, hφsurj⟩
  let n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let ρ : TateAlgebra (Fin n) k →ₐ[k] TateAlgebra σ k := TateAlgebra.rename k e.symm.toEmbedding
  let τ : TateAlgebra σ k →ₐ[k] TateAlgebra (Fin n) k := TateAlgebra.rename k e.toEmbedding
  have hρτ : ∀ x : TateAlgebra σ k, ρ (τ x) = x := by
    intro x
    apply Subtype.ext
    simp [ρ, τ, TateAlgebra.rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id]
  have hτρ : ∀ x : TateAlgebra (Fin n) k, τ (ρ x) = x := by
    intro x
    apply Subtype.ext
    simp [ρ, τ, TateAlgebra.rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id]
  let ψ : TateAlgebra (Fin n) k →ₐ[k] A := φ.comp ρ
  refine ⟨n, ψ, ?_, ?_⟩
  · intro x
    simpa [ψ, ρ, TateAlgebra.rename_norm_eq] using isContractiveHom_of_admissible hφadm (ρ x)
  · intro y
    rcases hφsurj y with ⟨x, rfl⟩
    exact ⟨τ x, by simp [ψ, hρτ x]⟩

end IsStrictAffinoid

end NormField
