import YM.SU5.Selected.Energy
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
local notation "T4"=>SU.group
open Buffered Py Py.Rate LocalLimit Preparation Buffered.Afterglow
open Tower VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal


open TopologicalSpace

/-- Sharp recovery from dyadic bounds for continuous observables on a compact full-support space. -/
lemma lasso {A:Type*} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
 (μ:Measure A) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
 {f:A→ℝ} (h:Continuous f) (h':∀x,0≤f x)
 {C:ℝ} (c:0<C) (he:∀n:ℕ, (∫ x,f x^(2^(n+1):ℕ) ∂μ) ≤ C^(2^(n+1):ℕ))
 (x:A) : f x≤C := by
 by_contra! hv
 obtain ⟨b,k,p⟩:=exists_between hv
 have b0:=lt_trans c k
 let S := {y| b<f y}
 have s:IsOpen S:= isOpen_lt continuous_const h
 have z:0<μ.real S:=ENNReal.toReal_pos (ne_of_gt (s.measure_pos μ ⟨x,p⟩)) (measure_ne_top μ S)
 have i: Tendsto (fun n:ℕ=> (C/b)^(2^(n+1):ℕ)) atTop (𝓝 (0:ℝ)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤C/b by positivity) ((div_lt_one b0).mpr k)).comp
       ((tendsto_pow_atTop_atTop_of_one_lt (by decide: (1:ℕ)<2)).comp
          ((tendsto_atTop_mono (fun n:ℕ=> by dsimp; omega : ∀n:ℕ,id n≤ n+1) tendsto_id)))
 obtain ⟨n,t⟩:=(i.eventually (gt_mem_nhds z)).exists
 let d:=2^(n+1)
 rw [div_pow] at t
 have w : μ.real S * b^d ≤ ∫ x,f x^d ∂μ := by
    let g (x:A):= b^d
    have bq:Integrable g μ:=integrable_const _
    rw [show μ.real S*b^d=(∫ x,S.indicator g x ∂μ) by rw [integral_indicator s.measurableSet,show g=(fun _=> b^d) from rfl,setIntegral_const,smul_eq_mul]]
    refine (integral_mono (bq.indicator s.measurableSet)
       ((h.pow d).integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace _))
       (show S.indicator g ≤ fun x=> f x ^ d from fun y=> ?_))
    · by_cases u:y∈S
      · rw [Set.indicator_of_mem u]
        exact pow_le_pow_left₀ b0.le (show b<f y from u).le _
      · rw [Set.indicator_of_notMem u]
        exact pow_nonneg (h' y) _
 exact ((div_lt_iff₀ (pow_pos b0 d)).mp t).not_ge (w.trans (he n))

variable (P:VacuumSelection.Spine) (j:Axis) (s:ℕ)
local notation "K" => P.calibration
local notation "X" => P.Test

def recoil (v:ℤ) (f:X):X:=P.shifts j v (P.reflectTest j f * f)

lemma chargesUnit (y:P.Spectrum0 j): P.singleState j s y 1=1:=by
 rw [P.single_state,P.reading_unit,map_one]

lemma rips (f:X) {S:Finset Cover} (u:InTest K true S false f.val)
 (h:region j 0 (K).ℓ S)
 (d:ℤ) (y:P.Spectrum0 j) :
 ‖P.singleState j s y f‖^2≤ (P.singleState j s y (recoil P j d f)).re := by
 let U:=unity P.run P.large j 0 false s
 let v := P.positiveVox j s S f u h
 let g := P.stateVox j y s
 let F:=P.singleState j s y
 have he : P.reflectTest j 1 = 1 := Subtype.ext (mirror_unit ..)
 have hp:inner ℂ (g U) (g v)= F f:=by
   have h:=P.gram_at j y s U v
   change inner ℂ (g U) (g v)=F (P.reflectTest j 1 * f) at h
   rwa [he,one_mul] at h
 have hgU: ‖g U‖=1:=by
   have h:=P.gram_at j y s U U
   change inner ℂ (g U) (g U) = P.singleState j s y (P.reflectTest j 1 * 1) at h
   rw [he,mul_one,chargesUnit, inner_self_eq_norm_sq_to_K] at h
   have a : ‖g U‖^2=1:= by apply Complex.ofReal_injective; rw [Complex.ofReal_pow,Complex.ofReal_one]; exact h
   nlinarith [norm_nonneg (g U)]

 have hp₂: (P.singleState j s y (recoil P j d f)).re=‖g v‖^2:=by
   rw [recoil,P.slide_single]
   change (P.singleState j s y (P.reflectTest j (P.voxTest j s v)*P.voxTest j s v)).re= _
   rw [←P.gram_at, inner_self_eq_norm_sq_to_K]
   change (Complex.ofReal ‖g v‖ ^ (2:ℕ)).re = ‖g v‖^2
   rw [← Complex.ofReal_pow, Complex.ofReal_re]
 rw [hp₂]
 apply pow_le_pow_left₀ (norm_nonneg _)
 rw [show P.singleState j s y f=inner ℂ (g U) (g v) from hp.symm]
 simpa [hgU] using norm_inner_le_norm (𝕜:=ℂ) (g U) (g v)

lemma sprouts (W:P.Register) {c:ℝ} (hc:0<c)
 (f:ℕ→X)
 (grow:∀n y,‖P.singleState j s y (f n)‖^2≤(P.singleState j s y (f (n+1))).re)
 (cost:∀n,‖P.E s (f (n+1)).val‖≤ c^(2^(n+1):ℕ)) :
 ∀y, ‖P.singleState j s y (f 0)‖ ≤ c := by
 let m (n:ℕ) (y:P.Spectrum0 j):=P.singleState j s y (f n)
 have t(n): Continuous (m n) := P.chi_joint j (P.reading j s _)
 let g y := ‖m 0 y‖
 have q n y : g y ^ (2^n:ℕ) ≤ ‖m n y‖ := by
   induction n with
   | zero=> rw [pow_zero,pow_one]
   | succ n ih=>
        rw [Nat.pow_succ,pow_mul]
        exact le_trans (pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) ih _) ((grow n y).trans (Complex.re_le_norm _))
 letI := P.pillar_support j W
 have i n : Integrable (m n) (P.pillars j) := (t n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 refine lasso (f:=g) (P.pillars j) ((t 0).norm) (fun _=>norm_nonneg _) hc ?_
 intro n
 have a y : g y ^ (2^(n+1):ℕ) ≤ (m (n+1) y).re:=by
     rw [Nat.pow_succ,pow_mul]
     exact le_trans (pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) (q n y) _) (grow n y)

 have u : Integrable (fun y=>g y ^ (2^(n+1):ℕ)) (P.pillars j):=
    ((t 0).norm.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 refine (integral_mono u (i (n+1)).re a).trans ?_
 rw [integral_re (i _)]
 have e : (∫ y,m (n+1) y ∂(P.pillars j))=P.E s (f (n+1)).val:= (P.recovery j (P.reading j s _)).trans (P.occupied ..)
 rw [e]
 exact (Complex.re_le_norm _).trans (cost _)
