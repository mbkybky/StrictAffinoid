/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Topology.Algebra.Valued.NormedValued

@[expose] public section

open Valued NormedField Filter

open scoped Topology

variable {σ τ : Type*} (s : σ)

section TateAlgebra

variable {R : Type*} [NormedCommRing R]

/-- Restricted multivariate power series: coefficients tend to `0` along `Filter.cofinite`. -/
def IsTate (σ : Type*) (R : Type*) [NormedCommRing R] (F : MvPowerSeries σ R) : Prop :=
  Tendsto (fun e : σ →₀ ℕ ↦ ‖MvPowerSeries.coeff e F‖) cofinite (𝓝 0)

lemma isTate_iff (F : MvPowerSeries σ R) :
    IsTate σ R F ↔ ∀ ε > 0, {e : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e F‖}.Finite := by
  rw [IsTate, ← tendsto_zero_iff_norm_tendsto_zero, NormedAddGroup.tendsto_nhds_zero]
  simp [Filter.eventually_cofinite, not_lt]

lemma coeff_le_of_isTate (F : MvPowerSeries σ R) (hF : IsTate σ R F) :
    ∃ C > 0, ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e F‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bddAbove_range_of_cofinite
  refine ⟨max C 1, by positivity, ?_⟩
  intro e
  exact (hC ⟨e, rfl⟩).trans (le_max_left _ _)

lemma isTate_monomial (n : σ →₀ ℕ) (a : R) : IsTate σ R (MvPowerSeries.monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  simp [Set.Subsingleton, MvPowerSeries.coeff_monomial]

lemma isTate_C (r : R) : IsTate σ R (MvPowerSeries.C r) := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply]
  exact isTate_monomial 0 r

lemma isTate_X (s : σ) : IsTate σ R (MvPowerSeries.X s) := by
  rw [MvPowerSeries.X_def]
  exact isTate_monomial (Finsupp.single s 1) (1 : R)

lemma isTate_add {F G : MvPowerSeries σ R} (hF : IsTate σ R F) (hG : IsTate σ R G) :
    IsTate σ R (F + G) := by
  rw [IsTate, ← tendsto_zero_iff_norm_tendsto_zero] at hF hG ⊢
  simpa using hF.add hG

variable [IsUltrametricDist R]

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
    have hδmul_le (c : ℝ) (hc : c ≤ max a b) : δ * c ≤ ε := by
      have hpos : 0 < max a b := lt_of_lt_of_le ha (le_max_left _ _)
      have haux : ε * c / max a b ≤ ε := (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hc hε.le
      simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux
    let SF : Set (σ →₀ ℕ) := {e | δ ≤ ‖MvPowerSeries.coeff e F‖}
    let SG : Set (σ →₀ ℕ) := {e | δ ≤ ‖MvPowerSeries.coeff e G‖}
    have hSF : SF.Finite := hF δ hδ
    have hSG : SG.Finite := hG δ hδ
    let T : Set (σ →₀ ℕ) := (fun pq : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ pq.1 + pq.2) '' (SF ×ˢ SG)
    have hT : T.Finite := (hSF.prod hSG).image _
    refine hT.subset ?_
    intro n hn
    simp only [T, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq] at hn ⊢
    by_contra hnot
    let t : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) := Finset.antidiagonal n
    have htne : t.Nonempty := by
      refine ⟨(0, n), ?_⟩
      simp [t]
    obtain ⟨i, hi, hsum⟩ := IsUltrametricDist.exists_norm_finsetSum_le t
      (fun pq ↦ MvPowerSeries.coeff pq.1 F * MvPowerSeries.coeff pq.2 G)
    have hi' : i ∈ t := hi htne
    have hsum' : ‖MvPowerSeries.coeff n (F * G)‖ ≤
        ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ := by
      simpa [t, MvPowerSeries.coeff_mul] using hsum
    have hprodlt : ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ < ε := by
      have hnotboth : ¬ (i.1 ∈ SF ∧ i.2 ∈ SG) := by
        intro hiSG
        exact hnot ⟨i, hiSG, Finset.mem_antidiagonal.mp hi'⟩
      rcases not_and_or.mp hnotboth with hiF | hiG
      · have h1 : ‖MvPowerSeries.coeff i.1 F * MvPowerSeries.coeff i.2 G‖ ≤
            ‖MvPowerSeries.coeff i.1 F‖ * b := by
          grw [norm_mul_le, mul_le_mul_of_nonneg_left (hGb _) (norm_nonneg _)]
        have h2 : ‖MvPowerSeries.coeff i.1 F‖ * b < δ * b :=
          mul_lt_mul_of_pos_right (lt_of_not_ge hiF) hb
        have h3 : δ * b ≤ ε := hδmul_le b (le_max_right _ _)
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) h3
      · have h : a * δ ≤ ε := by simpa [mul_comm] using hδmul_le a (le_max_left _ _)
        grw [norm_mul_le, mul_le_mul_of_nonneg_right (hFa _) (norm_nonneg _), ← h]
        exact mul_lt_mul_of_pos_left (lt_of_not_ge hiG) ha
    exact (not_lt_of_ge hn) (lt_of_le_of_lt hsum' hprodlt)
  add_mem' {F} {G} hF hG := isTate_add hF hG
  algebraMap_mem' := isTate_C

lemma mem_tateSubalgebra_iff (F : MvPowerSeries σ R) :
    F ∈ tateSubalgebra σ R ↔ ∀ ε > 0, {e : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff e F‖}.Finite :=
  isTate_iff F

/-- The Tate algebra in variables `σ` over `R`, formed by restricted multivariate power series. -/
def TateAlgebra (σ : Type*) (R : Type*) [NormedCommRing R] [IsUltrametricDist R] : Type _ :=
  tateSubalgebra σ R

namespace TateAlgebra

section inst

deriving noncomputable instance CommRing for TateAlgebra

noncomputable instance : Algebra R (TateAlgebra σ R) :=
  inferInstanceAs (Algebra R (tateSubalgebra σ R))

noncomputable instance : Algebra (TateAlgebra σ R) (MvPowerSeries σ R) :=
  inferInstanceAs (Algebra (tateSubalgebra σ R) (MvPowerSeries σ R))

instance : IsScalarTower R (TateAlgebra τ R) (MvPowerSeries τ R) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance : Coe (TateAlgebra σ R) (MvPowerSeries σ R) where
  coe F := F.1

end inst

@[ext]
lemma subtype_ext {F G : TateAlgebra σ R} (h : F.1 = G.1) : F = G := Subtype.ext h

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
    (F + G : TateAlgebra σ R) = F.val + G.val := rfl

@[simp]
lemma coe_mul (F G : TateAlgebra σ R) :
    (F * G : TateAlgebra σ R) = F.val * G.val := rfl

@[simp]
lemma coe_pow (F : TateAlgebra σ R) (n : ℕ) :
  (F ^ n : TateAlgebra σ R) = F.val ^ n := rfl

@[simp]
lemma coe_neg (F : TateAlgebra σ R) :
    (- F : TateAlgebra σ R) = - F.val := rfl

@[simp]
lemma coe_sub (F G : TateAlgebra σ R) :
    (F - G : TateAlgebra σ R) = F.val - G.val := rfl

@[simp]
lemma coe_algebraMap (r : R) :
    algebraMap R (TateAlgebra σ R) r = algebraMap R (MvPowerSeries σ R) r := rfl

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
theorem constantCoeff_C (r : R) : constantCoeff (C r : TateAlgebra σ R) = r :=
  rfl

section gaussNorm

/-- The Gauss norm on multivariate power series. -/
noncomputable def gaussNorm (F : TateAlgebra σ R) : ℝ := ⨆ e : σ →₀ ℕ, ‖F.1.coeff e‖

lemma gaussNorm_bddAbove (F : TateAlgebra σ R) :
    BddAbove (Set.range fun e : σ →₀ ℕ ↦ ‖MvPowerSeries.coeff e F.val‖) :=
  F.2.bddAbove_range_of_cofinite

lemma gaussNorm_nonneg (F : TateAlgebra σ R) : 0 ≤ F.gaussNorm :=
  le_trans (norm_nonneg _) (le_ciSup (gaussNorm_bddAbove F) 0)

lemma gaussNorm_eq_zero (F : TateAlgebra σ R) (hF : F.gaussNorm = 0) : F = 0 := by
  ext e
  have hle : ‖MvPowerSeries.coeff e F.1‖ ≤ F.gaussNorm := le_ciSup (gaussNorm_bddAbove F) e
  exact norm_eq_zero.mp (le_antisymm (by simpa [hF] using hle) (norm_nonneg _))

lemma gaussNorm_add_le (F G : TateAlgebra σ R) :
    (F + G).gaussNorm ≤ F.gaussNorm + G.gaussNorm := by
  refine ciSup_le ?_
  intro e
  exact (norm_add_le _ _).trans <|
    add_le_add (le_ciSup F.gaussNorm_bddAbove e) (le_ciSup G.gaussNorm_bddAbove e)

lemma gaussNorm_add_le_max (F G : TateAlgebra σ R) :
    (F + G).gaussNorm ≤ max (F.gaussNorm) (G.gaussNorm) := by
  refine ciSup_le ?_
  intro e
  exact IsUltrametricDist.norm_add_le_max (MvPowerSeries.coeff e F.1) (MvPowerSeries.coeff e G.1)
    |>.trans <| max_le_max (le_ciSup F.gaussNorm_bddAbove e) (le_ciSup G.gaussNorm_bddAbove e)

lemma gaussNorm_mul_le (F G : TateAlgebra σ R) :
    (F * G).gaussNorm ≤ F.gaussNorm * G.gaussNorm := by
  classical
  refine ciSup_le ?_
  intro n
  change ‖MvPowerSeries.coeff n ((F * G).1)‖ ≤ F.gaussNorm * G.gaussNorm
  simp only [coe_mul, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ?_ ?_
  · exact mul_nonneg (gaussNorm_nonneg F) (gaussNorm_nonneg G)
  · rintro ⟨i, j⟩ -
    exact (norm_mul_le _ _).trans <|
      mul_le_mul (le_ciSup F.gaussNorm_bddAbove i) (le_ciSup G.gaussNorm_bddAbove j)
        (norm_nonneg _) (gaussNorm_nonneg F)

lemma gaussNorm_neg (F : TateAlgebra σ R) : (- F).gaussNorm = F.gaussNorm := by
  simp [gaussNorm]

@[simp]
lemma gaussNorm_C (r : R) : (C r : TateAlgebra σ R).gaussNorm = ‖r‖ := by
  classical
  apply le_antisymm
  · refine ciSup_le ?_
    intro e
    by_cases h : e = 0 <;> simp [C, ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.coeff_C, h]
  · simpa [gaussNorm, C, ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.coeff_C] using
      le_ciSup (gaussNorm_bddAbove (C r)) (0 : σ →₀ ℕ)

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

variable (σ) in
@[simp]
lemma norm_algebraMap (r : R) : ‖algebraMap R (TateAlgebra σ R) r‖ = ‖r‖ :=
  TateAlgebra.gaussNorm_C r

lemma coeff_norm_le (F : TateAlgebra σ R) (e : σ →₀ ℕ) : ‖MvPowerSeries.coeff e F.1‖ ≤ ‖F‖ :=
  le_ciSup (gaussNorm_bddAbove F) e

instance : IsUltrametricDist (TateAlgebra σ R) where
  dist_triangle_max x y z := by
    grw [dist_eq_norm, dist_eq_norm, dist_eq_norm, show x - z = (x - y) + (y - z) by abel]
    exact gaussNorm_add_le_max (x - y) (y - z)

lemma coeff_dist_le (e : σ →₀ ℕ) (F G : TateAlgebra σ R) :
    dist (MvPowerSeries.coeff e F.1) (MvPowerSeries.coeff e G.1) ≤ dist F G := by
  simpa [dist_eq_norm, dist_eq_norm] using coeff_norm_le (F - G) e

lemma coeff_lipschitz (e : σ →₀ ℕ) :
    LipschitzWith 1 (fun F : TateAlgebra σ R ↦ MvPowerSeries.coeff e F.1) := by
  intro F G
  simpa [edist_dist, ENNReal.coe_one, one_mul] using
    ENNReal.ofReal_le_ofReal (coeff_dist_le e F G)

instance [CompleteSpace R] : CompleteSpace (TateAlgebra σ R) := by
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  let f : MvPowerSeries σ R := fun e ↦ limUnder atTop (fun n ↦ MvPowerSeries.coeff e (u n).1)
  have hcoeffCauchy (e : σ →₀ ℕ) :  CauchySeq (fun n ↦ MvPowerSeries.coeff e (u n).1) :=
    (coeff_lipschitz e).cauchySeq_comp hu
  have hcoeff_tendsto (e : σ →₀ ℕ) :
      Tendsto (fun n ↦ MvPowerSeries.coeff e (u n).1) atTop (nhds (MvPowerSeries.coeff e f)) :=
    CauchySeq.tendsto_limUnder (hcoeffCauchy e)
  have hclose_to_fixed {ε : ℝ} (N : ℕ) (hN : ∀ n ≥ N, dist (u n) (u N) < ε)
      (e : σ →₀ ℕ) : dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1) ≤ ε := by
    have hmem : MvPowerSeries.coeff e f ∈ Metric.closedBall (MvPowerSeries.coeff e (u N).1) ε := by
      apply IsClosed.mem_of_tendsto Metric.isClosed_closedBall (hcoeff_tendsto e)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      simpa [Metric.mem_closedBall] using (coeff_dist_le e (u n) (u N)).trans (hN n hn).le
    simpa [Metric.mem_closedBall] using hmem
  have hnorm_le_max (x y : R) : ‖x‖ ≤ max (dist x y) (dist y 0) := by
    simpa [dist_eq_norm] using dist_triangle_max x y (0 : R)
  have hdist_le_max (x y z : R) : dist x z ≤ max (dist x y) (dist y z) := by
    simpa [max_comm, max_left_comm, max_assoc] using dist_triangle_max x y z
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
    by_contra hsmall
    have huNlt : ‖MvPowerSeries.coeff e (u N).1‖ < δ := lt_of_not_ge hsmall
    have hmaxlt : max (dist (MvPowerSeries.coeff e f) (MvPowerSeries.coeff e (u N).1))
        (dist (MvPowerSeries.coeff e (u N).1) 0) < ε := by
      rw [max_lt_iff]
      constructor
      · exact (hclose_to_fixed N hN e).trans_lt hδε
      · simpa [dist_eq_norm] using lt_of_lt_of_le huNlt (le_of_lt hδε)
    exact (not_lt_of_ge he) (lt_of_le_of_lt (hnorm_le_max _ _) hmaxlt)
  let F : TateAlgebra σ R := ⟨f, hf_tate⟩
  refine ⟨F, (Metric.tendsto_atTop.2 ?_)⟩
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by positivity
  have hδε : δ < ε := by
    dsimp [δ]
    linarith
  rcases (Metric.cauchySeq_iff'.mp hu) δ hδ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdist : dist (u n) F ≤ δ := by
    rw [dist_eq_norm]
    refine ciSup_le ?_
    intro e
    have hcoeff : dist (MvPowerSeries.coeff e (u n).1) (MvPowerSeries.coeff e f) ≤ δ :=
      (hdist_le_max _ _ _).trans <| max_le ((coeff_dist_le e (u n) (u N)).trans (hN n hn).le)
        (by simpa [dist_comm] using hclose_to_fixed N hN e)
    simpa [dist_eq_norm] using hcoeff
  exact hdist.trans_lt hδε

omit [IsUltrametricDist R] in
lemma isTate_rename (e : σ ↪ τ) (F : MvPowerSeries σ R) (hF : IsTate σ R F) :
    IsTate τ R (MvPowerSeries.rename e F) := by
  rw [isTate_iff] at hF ⊢
  intro ε hε
  refine ((hF ε hε).image (Finsupp.embDomain e)).subset ?_
  intro x hx
  by_cases hxr : x ∈ Set.range (Finsupp.embDomain e)
  · rcases hxr with ⟨y, rfl⟩
    exact ⟨y, by simpa [Set.mem_setOf_eq] using hx, rfl⟩
  · have hzero : MvPowerSeries.coeff x (MvPowerSeries.rename e F) = 0 :=
      MvPowerSeries.coeff_rename_eq_zero e F (by simpa [Finsupp.embDomain_eq_mapDomain] using hxr)
    exact ((not_le_of_gt hε) (by simpa [Set.mem_setOf_eq, hzero] using hx)).elim

variable (R) in
/-- Reindex the variables of a Tate algebra along an injection, giving an algebra homomorphism. -/
noncomputable def rename (e : σ ↪ τ) : TateAlgebra σ R →ₐ[R] TateAlgebra τ R where
  toFun F := ⟨MvPowerSeries.rename e F.1, isTate_rename e F.1 F.2⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp)

@[simp]
lemma coe_rename (e : σ ↪ τ) (F : TateAlgebra σ R) :
    (rename R e F).1 = MvPowerSeries.rename e (F : MvPowerSeries σ R) := rfl

variable (R) in
noncomputable def renameEquiv (e : σ ≃ τ) :
    TateAlgebra σ R ≃ₐ[R] TateAlgebra τ R :=
  AlgEquiv.ofAlgHom (rename R e.toEmbedding) (rename R e.symm.toEmbedding)
    (by
      ext
      simp [rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id])
    (by
      ext
      simp [rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id])

@[simp]
lemma rename_X (e : σ ↪ τ) (s : σ) : rename R e (X s) = X (e s) := by
  ext
  simp [rename]

lemma rename_norm_le (e : σ ↪ τ) (F : TateAlgebra σ R) : ‖rename R e F‖ ≤ ‖F‖ := by
  refine ciSup_le ?_
  intro x
  by_cases hxr : x ∈ Set.range (Finsupp.embDomain e)
  · rcases hxr with ⟨y, rfl⟩
    simpa using coeff_norm_le F y
  · simp [MvPowerSeries.coeff_rename_eq_zero e F.1
      (by simpa [Finsupp.embDomain_eq_mapDomain] using hxr)]

lemma rename_norm_eq (e : σ ≃ τ) (F : TateAlgebra σ R) : ‖rename R e.toEmbedding F‖ = ‖F‖ := by
  apply le_antisymm
  · exact rename_norm_le e.toEmbedding F
  · simpa [renameEquiv, rename, MvPowerSeries.rename_rename, MvPowerSeries.rename_id] using
      rename_norm_le e.symm.toEmbedding (rename R e.toEmbedding F)

lemma exists_coeff_norm_eq_norm (F : TateAlgebra σ R) :
    ∃ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e F.1‖ = ‖F‖ := by
  by_cases hF : F = 0
  · simp [hF]
  let M : ℝ := ‖F‖
  let S : Set (σ →₀ ℕ) := {e | M / 2 ≤ ‖MvPowerSeries.coeff e F.1‖}
  have hMpos : 0 < M := norm_pos_iff.mpr hF
  have hSfin : S.Finite := (isTate_iff F.1).mp F.2 (M / 2) (by positivity)
  have hSne : S.Nonempty := by
    by_contra hSempty
    have : ‖F‖ ≤ M / 2 := by
      refine ciSup_le ?_
      intro e
      have heS : e ∉ S := fun heS ↦ hSempty ⟨e, heS⟩
      exact (lt_of_not_ge heS).le
    linarith
  let s : Finset (σ →₀ ℕ) := hSfin.toFinset
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image s
    (fun e : σ →₀ ℕ ↦ ‖MvPowerSeries.coeff e F.1‖) (hSfin.toFinset_nonempty.mpr hSne)
  have hnorm_le : ‖F‖ ≤ ‖MvPowerSeries.coeff e F.1‖ := by
    refine ciSup_le ?_
    intro d
    by_cases hdS : d ∈ S
    · exact hmax d (hSfin.mem_toFinset.mpr hdS)
    · exact (lt_of_not_ge hdS).le.trans (hSfin.mem_toFinset.mp he)
  refine ⟨e, le_antisymm (coeff_norm_le F e) ?_⟩
  simpa [M] using hnorm_le

lemma exists_lex_min_coeff_norm_eq_norm [LinearOrder σ] (F : TateAlgebra σ R) (hF : F ≠ 0) :
    ∃ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e F.1‖ = ‖F‖ ∧
      ∀ d : σ →₀ ℕ, ‖MvPowerSeries.coeff d F.1‖ = ‖F‖ → (toLex e : Lex (σ →₀ ℕ)) ≤ toLex d := by
  let S : Set (σ →₀ ℕ) := {e | ‖F‖ ≤ ‖MvPowerSeries.coeff e F.1‖}
  have hSfin : S.Finite := (isTate_iff F.1).mp F.2 ‖F‖ (norm_pos_iff.mpr hF)
  obtain ⟨e₀, he₀⟩ := exists_coeff_norm_eq_norm F
  have hSne : S.Nonempty := ⟨e₀, by simp [S, he₀]⟩
  let s : Finset (σ →₀ ℕ) := hSfin.toFinset
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image s
    (fun e : σ →₀ ℕ ↦ (toLex e : Lex (σ →₀ ℕ))) (hSfin.toFinset_nonempty.mpr hSne)
  refine ⟨e, ?_, ?_⟩
  · exact le_antisymm (coeff_norm_le F e) (hSfin.mem_toFinset.mp he)
  · intro d hd
    have hdS : d ∈ S := by simp [S, hd]
    exact hmin d (hSfin.mem_toFinset.mpr hdS)

theorem value_group_subset (F : TateAlgebra σ R) : ∃ x : R, ‖x‖ = ‖F‖ := by
  rcases TateAlgebra.exists_coeff_norm_eq_norm F with ⟨e, he⟩
  exact ⟨MvPowerSeries.coeff e F.1, he⟩

section NormOneClass

variable [NormOneClass R]

instance : NormOneClass (TateAlgebra σ R) where
  norm_one := (TateAlgebra.gaussNorm_C 1).trans (by simp)

instance : Nontrivial (TateAlgebra σ R) := NormOneClass.nontrivial

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
  have hFpos : 0 < ‖F‖ := norm_pos_iff.mpr hF
  have hGpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  obtain ⟨p, hpnorm, hpmin⟩ := exists_lex_min_coeff_norm_eq_norm F hF
  obtain ⟨q, hqnorm, hqmin⟩ := exists_lex_min_coeff_norm_eq_norm G hG
  let i0 : (σ →₀ ℕ) × (σ →₀ ℕ) := (p, q)
  let t : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) := Finset.antidiagonal (p + q)
  let u : ((σ →₀ ℕ) × (σ →₀ ℕ)) → R := fun ij ↦
    MvPowerSeries.coeff ij.1 F.1 * MvPowerSeries.coeff ij.2 G.1
  have hi0 : i0 ∈ t := by simp [i0, t]
  have hi0norm : ‖u i0‖ = ‖F‖ * ‖G‖ := by simp [u, i0, hpnorm, hqnorm, norm_mul]
  have hrestlt (ij : (σ →₀ ℕ) × (σ →₀ ℕ)) (hij : ij ∈ t.erase i0) : ‖u ij‖ < ‖u i0‖ := by
    obtain ⟨hij_ne, hij_mem⟩ := Finset.mem_erase.mp hij
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
      · exact hij_ne (Prod.ext (congrArg ofLex hEq.1) (congrArg ofLex hEq.2))
      · exact hiLt.not_ge hp_le
      · exact hjLt.not_ge hq_le
    have hstrict : ‖MvPowerSeries.coeff ij.1 F.1‖ < ‖F‖ ∨ ‖MvPowerSeries.coeff ij.2 G.1‖ < ‖G‖ := by
      by_cases h1 : ‖MvPowerSeries.coeff ij.1 F.1‖ = ‖F‖
      · exact Or.inr <| lt_of_le_of_ne h2le (fun h2 ↦ hnotboth ⟨h1, h2⟩)
      · exact Or.inl <| lt_of_le_of_ne h1le h1
    rcases hstrict with h1lt | h2lt
    · exact lt_of_le_of_lt (by simpa [u, norm_mul] using
          mul_le_mul_of_nonneg_left h2le (norm_nonneg (MvPowerSeries.coeff ij.1 F.1)))
        (by simpa [hi0norm] using mul_lt_mul_of_pos_right h1lt hGpos)
    · exact lt_of_le_of_lt (by simpa [u, norm_mul] using
          mul_le_mul_of_nonneg_right h1le (norm_nonneg (MvPowerSeries.coeff ij.2 G.1)))
        (by simpa [hi0norm] using mul_lt_mul_of_pos_left h2lt hFpos)
  have hrest : ‖∑ ij ∈ t.erase i0, u ij‖ < ‖u i0‖ := by
    by_cases hrestne : (t.erase i0).Nonempty
    · obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (t.erase i0) (fun ij ↦ ‖u ij‖) hrestne
      have hsumle : ‖∑ ij ∈ t.erase i0, u ij‖ ≤ ‖u j‖ :=
        IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty hrestne hjmax
      exact lt_of_le_of_lt hsumle (hrestlt j hj)
    · have hEq : t.erase i0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrestne
      rw [hEq, Finset.sum_empty, hi0norm]
      simpa using mul_pos hFpos hGpos
  have hcoeff :
      MvPowerSeries.coeff (p + q) ((F * G).1) = u i0 + ∑ ij ∈ t.erase i0, u ij := by
    simpa [t, u, MvPowerSeries.coeff_mul] using (Finset.add_sum_erase t u hi0).symm
  have hcoeffnorm : ‖MvPowerSeries.coeff (p + q) ((F * G).1)‖ = ‖u i0‖ := by
    rw [hcoeff]
    have hne : ‖u i0‖ ≠ ‖∑ ij ∈ t.erase i0, u ij‖ := ne_of_gt hrest
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left_of_lt hrest]
  have hlow : ‖F‖ * ‖G‖ ≤ ‖F * G‖ := by grw [← hi0norm, ← hcoeffnorm, coeff_norm_le]
  exact le_antisymm (gaussNorm_mul_le F G) hlow

instance [Finite σ] : NormMulClass (TateAlgebra σ R) where
  norm_mul F G := by
    let : Fintype σ := Fintype.ofFinite σ
    let τ := Fin (Fintype.card σ)
    let e : σ ≃ τ := Fintype.equivFin σ
    simp [← rename_norm_eq e (F * G), norm_mul_eq_of_ordered, rename_norm_eq, rename_norm_eq]

end NormMulClass

instance [NormOneClass R] [NormMulClass R] [Finite σ] : IsDomain (TateAlgebra σ R) where

end TateAlgebra

section toTate

namespace MvPolynomial

/-- The natural embedding of multivariate polynomials into the Tate algebra. -/
noncomputable def toTate : MvPolynomial σ R →ₐ[R] TateAlgebra σ R :=
  MvPolynomial.aeval TateAlgebra.X

noncomputable instance : Coe (MvPolynomial σ R) (TateAlgebra σ R) := ⟨toTate⟩

lemma toTate_X :  (MvPolynomial.X s).toTate = (TateAlgebra.X s : TateAlgebra σ R) := by
  simp [toTate]

lemma toTate_coe (p : MvPolynomial σ R) : (p.toTate : MvPowerSeries σ R) = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [toTate]
      rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [toTate_X, hp]

variable (σ R) in
lemma toTate_denseRange : DenseRange (toTate : MvPolynomial σ R → TateAlgebra σ R) := by
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
    rw [toTate_coe p, LinearMap.map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc']
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

/-- A function is contractive if it does not increase norms. -/
def IsContractiveHom {A B F : Type*} [Norm A] [Norm B] [FunLike F A B] (f : F) : Prop :=
  ∀ a : A, ‖f a‖ ≤ ‖a‖

lemma IsContractiveHom.comp {A B C : Type*} [SeminormedRing A] [SeminormedRing B] [SeminormedRing C]
    {f : A →+* B} {g : B →+* C} (hf : IsContractiveHom f) (hg : IsContractiveHom g) :
    IsContractiveHom (g.comp f) :=
  fun x ↦ (hg _).trans (hf x)

lemma IsContractiveHom.continuous {A B F : Type*}
    [SeminormedAddCommGroup A] [SeminormedAddCommGroup B] [FunLike F A B] [AddMonoidHomClass F A B]
    {f : F} (hf : IsContractiveHom f) : Continuous f :=
  (AddMonoidHomClass.lipschitz_of_bound f 1 (fun x ↦ by simpa using hf x)).continuous

lemma TateAlgebra.rename_isContractiveHom (e : σ ↪ τ) : IsContractiveHom (rename R e) :=
  rename_norm_le e

/-- A function is admissible if the induced quotient norm on its image is equivalent to the
restricted norm from the target. -/
def IsAdmissibleHom {A B F : Type*} [Norm A] [Norm B] [FunLike F A B] (f : F) : Prop :=
  ∃ C > 0, ∀ x : A, sInf {r : ℝ | ∃ a : A, f a = f x ∧ ‖a‖ = r} ≤ C * ‖f x‖ ∧ ‖f x‖ ≤ C * ‖x‖

section NormField

variable {k : Type*} [NormedField k] [IsUltrametricDist k]

noncomputable instance (σ : Type*) : NormedAlgebra k (TateAlgebra σ k) where
  norm_smul_le r x := by
    grw [Algebra.smul_def, norm_mul_le]
    simp

/-- A strict `k`-affinoid algebra with its spectral seminorm. In fact, in this definition the
spectral seminorm must be a norm and `A` must be reduced due to the admissible assumption. -/
class IsStrictAffinoid (k : Type*) [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (A : Type*) [SeminormedRing A] [NormedAlgebra k A] :
    Prop extends NormOneClass A, CompleteSpace A, IsUltrametricDist A where
  withSpectralNorm (a : A) (n : ℕ) : ‖a ^n‖ = ‖a‖ ^ n
  presentation (k A) : ∃ (σ : Type) (_ : Fintype σ) (φ : TateAlgebra σ k →ₐ[k] A)
    (_ : IsAdmissibleHom φ), Function.Surjective φ

variable [CompleteSpace k] {A : Type*} [SeminormedRing A] [NormedAlgebra k A] [IsStrictAffinoid k A]

namespace IsStrictAffinoid

instance {σ : Type*} [Finite σ] : IsStrictAffinoid k (TateAlgebra σ k) where
  withSpectralNorm := norm_pow
  presentation := by
    let τ : Type := Shrink.{0} σ
    let e : σ ≃ τ := equivShrink.{0} σ
    let E : TateAlgebra τ k ≃ₐ[k] TateAlgebra σ k := TateAlgebra.renameEquiv k e.symm
    let φ : TateAlgebra τ k →ₐ[k] TateAlgebra σ k := TateAlgebra.rename k e.symm.toEmbedding
    let ψ : TateAlgebra σ k →ₐ[k] TateAlgebra τ k := TateAlgebra.rename k e.toEmbedding
    refine ⟨τ, Fintype.ofFinite τ, φ, ?_, ?_⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x
      constructor
      · let Q : Set ℝ := {r : ℝ | ∃ a : TateAlgebra τ k, φ a = φ x ∧ ‖a‖ = r}
        have hQbdd : BddBelow Q := by
          refine ⟨0, ?_⟩
          intro r hr
          rcases hr with ⟨a, -, rfl⟩
          exact norm_nonneg _
        have hxmem : ‖x‖ ∈ Q := ⟨x, rfl, rfl⟩
        refine le_trans (csInf_le hQbdd hxmem) ?_
        have hcontract := TateAlgebra.rename_isContractiveHom e.toEmbedding (φ x)
        conv_lhs => rw [← E.symm_apply_apply x]
        simpa [φ, ψ, E, TateAlgebra.renameEquiv, one_mul] using hcontract
      · simpa [φ, one_mul] using TateAlgebra.rename_isContractiveHom e.symm.toEmbedding x
    · intro y
      exact ⟨ψ y, by simpa [φ, ψ, E, TateAlgebra.renameEquiv] using E.apply_symm_apply y⟩

lemma isContractiveHom_of_admissible {B : Type*} [SeminormedRing B] [NormedAlgebra k B]
    [IsStrictAffinoid k B] {f : A →ₐ[k] B} (ha : IsAdmissibleHom f) :
    IsContractiveHom f := by
  rcases ha with ⟨C, -, hC⟩
  intro x
  by_cases hx0 : ‖x‖ = 0
  · simpa [hx0] using (hC x).2
  · by_contra hfx
    have hlt : ‖x‖ < ‖f x‖ := lt_of_not_ge hfx
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
    let r : ℝ := ‖f x‖ / ‖x‖
    have hr : 1 < r := by
      simpa [r, hxpos.ne'] using div_lt_div_of_pos_right hlt hxpos
    have hpow (n : ℕ) : r ^ n ≤ C := by
      dsimp [r]
      have hmain : ‖f x‖ ^ n ≤ C * ‖x‖ ^ n := by simpa [← withSpectralNorm k] using (hC (x ^ n)).2
      have hxpowpos : 0 < ‖x‖ ^ n := pow_pos hxpos _
      rw [div_pow]
      exact (div_le_iff₀ hxpowpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hr
    exact (not_lt_of_ge (hpow n)) hn

variable (k) (A) in
lemma exists_fin_contractive_presentation :
    ∃ (n : ℕ) (φ : TateAlgebra (Fin n) k →ₐ[k] A) (_ : IsContractiveHom φ),
    Function.Surjective φ := by
  rcases IsStrictAffinoid.presentation k A with ⟨σ, _, φ, hφadm, hφsurj⟩
  let n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let E : TateAlgebra (Fin n) k ≃ₐ[k] TateAlgebra σ k := TateAlgebra.renameEquiv k e.symm
  let ρ : TateAlgebra (Fin n) k →ₐ[k] TateAlgebra σ k := TateAlgebra.rename k e.symm.toEmbedding
  let τ : TateAlgebra σ k →ₐ[k] TateAlgebra (Fin n) k := TateAlgebra.rename k e.toEmbedding
  let ψ : TateAlgebra (Fin n) k →ₐ[k] A := φ.comp ρ
  refine ⟨n, ψ, ?_, ?_⟩
  · intro x
    simpa [ψ, ρ, TateAlgebra.rename_norm_eq] using isContractiveHom_of_admissible hφadm (ρ x)
  · intro y
    rcases hφsurj y with ⟨x, rfl⟩
    exact ⟨τ x, by simpa [ψ, E, TateAlgebra.renameEquiv] using congrArg φ (E.apply_symm_apply x)⟩

end IsStrictAffinoid

end NormField
