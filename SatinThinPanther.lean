import SatinThinStellar
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
namespace Garland
open Etch
variable {I J:Type*} [Fintype I][Fintype J] {Q:ℝ} (z:PlaqAxes→ℝ) {Υ:MvPolynomial I ℝ}
-- Touring records ALL pose displacements on gauge sites (not yet requiring center nodes). Support checked later.
variable {k b':ℝ} {C':Etch G J} (T:Tour I n)(W:Etch G J)
variable {L:Type*} [Fintype L] (Φ: L→Tour I n) (ρ:ℝ)
/-! # The variance tariff. Translate many copies of the far stencil before the
   joint estimate: resulting polynomial-in-arc *per copy* budget is independent
   of the width. (Still subject, for pricing in s, to fitting these particular
   2-fold products into `BunchData`.) -/
variable (T':L → Tour I n) [Nonempty L]
namespace Tour
noncomputable def addStack (U:Tour J n) : Tour (I⊕J) n:=⟨Sum.elim T.loc U.loc, Sum.elim T.orient U.orient⟩
lemma stacked_reads {U:Type*}[Fintype U](X:Tour U n)(z:Altar G n): (T.addStack X).reading W ρ (q:=q) z=T.reading W ρ (q:=q) z * X.reading W ρ (q:=q) z:=by unfold Tour.reading addStack; rw [Fintype.prod_sum_type]; rfl
end Tour
def sunRank(q:Clip)(W:Etch G J)(d:ℕ):ℝ:=8 * Real.exp ((Real.pi/2)^2/2)*(1+sunstroke d q 2 W^2)
local notation "Θq"=> sunRank q W (Fintype.card I)
-- adapt `Ranging.ensemble_double` proof
include L_
lemma increase_vision (h:Bid.Sworn H n G)(u:|ρ|≤2)(i:Stationed Φ)(j:Stationed T') (f:Copied T Φ)(g:Copied T T'):
   |(∑ i:L,∑ j:L, visionCost B P ((Φ i).addStack (T' j)) W ρ) - ((Fintype.card L)*(visionCost B P T W ρ))^2| ≤ Fintype.card L*Θq:= by
  let H':= stamen B P n; let z:= Fintype.card L * visionCost B P T W ρ; let N:ℝ:= Fintype.card L; let U:= N * W.arc^Fintype.card I
  let F(t:L→ Tour I n)(x:H'):= accountGl W ρ t (q:=q) x.val; let S:= sunstroke (Fintype.card I) q 2 W; let R:= S * Real.sqrt N
  have hx(t:L→Tour I n): ContDiff ℝ 1 (accountGl W ρ t (q:=q)):= ContDiff.sum fun i _=> (t i).smooth_read W ρ
  have ht(t:L→Tour I n)(a:Copied T t): ∫ x:H',F t x ∂stdGaussian H'=z:=by
     have hv:= vision_burst B P L_ T W t ρ h a (t:=1); rw [plumeCost,cloud_turn B P _ (hx t).continuous,one_mul,one_mul] at hv; exact hv
  have he(t:L→Tour I n):ContDiff ℝ 1 (F t):= (hx t).comp H'.subtypeL.contDiff
  have hf' : sunstroke (Fintype.card I) q ρ W ≤ S:= sun_mono W ρ _ (by simpa only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using u)
  have hp(t:L→Tour I n)(a:Stationed t)(x:H'): ‖fderiv ℝ (F t) x‖ ≤ R:=by
    let V:= accountGl W ρ t (q:=q); let e:= fderiv ℝ V x.val; change ‖fderiv ℝ (V ∘ H'.subtypeL) x‖ ≤ R; rw [fderiv_comp x _ H'.subtypeL.differentiableAt]; rw [H'.subtypeL.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Submodule.norm_subtypeL_le H')).trans ((everywhere W t ρ a _).trans (mul_le_mul_of_nonneg_right hf' (Real.sqrt_nonneg _))))
    exact (hx t).differentiable (by norm_num) _
  have hh(t:L→Tour I n)(x:H'): |F t x|≤ U:= beacon_priced ..
  have he' := (squareMaps (F Φ) (F T') (hh Φ) (hh T') (he ..) (he ..) (ht _ f) (ht _ g) (hp _ i) (hp _ j)).2
  have hr(t:Tour (I⊕I) n): Integrable (fun i:H'=> t.reading W ρ (q:=q) i.val) (stdGaussian H'):= Regis.bree _ _ (((t.smooth_read (q:=q) W ρ).continuous.comp continuous_subtype_val).measurable) (fun i=> t.reading_cost W ρ (q:=q) i.val)
  have hQ(x:H'): F Φ x * F T' x= ∑ i,∑ j, ((Φ i).addStack (T' j)).reading W ρ (q:=q) x.val:=by simp_rw [Tour.stacked_reads]; exact Fintype.sum_mul_sum ..
  simp_rw [hQ] at he'; rw [integral_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=> hr _))] at he'; simp_rw [integral_finsetSum _ (fun j _=> hr _)] at he'
  rw [sq]; apply he'.trans; change 8*_*(1+R^2) ≤ N*(8*_*(1+S^2)); unfold R; rw [mul_pow S,Real.sq_sqrt (by unfold N; positivity),←mul_assoc N]; let E:=8 * Real.exp ((Real.pi/2)^2/2); have he:N≥1:=Nat.one_le_cast.mpr Fintype.card_pos; change E*_≤_*E*(1+S^2); linarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ E from mul_nonneg (by norm_num) (Real.exp_pos _|>.le))]
end Garland
end YM.Regis.Head
#print axioms YM.Regis.Head.Garland.increase_vision
