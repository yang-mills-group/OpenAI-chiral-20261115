import SatinFixedContrastNovember4
import YM.SU5.Thin.DoseOp

set_option autoImplicit false
set_option maxHeartbeats 210000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open Sifter PadThin
namespace DoseBill
variable (X:Hilbert)(F:SampleDose)(M:ℝ)
variable (A:Vantage→X.Op)(h:∀ x,Continuous (fun i=>A i x))(p: ∀ i,‖A i‖≤M)
private lemma measures (v:Vantage→X)(h:Continuous v)(x:X) (ε:ℝ)(u:0≤ε)(g:∀ z∈tsupport F.val,dist (v z) x≤ ε)(q:F.Normalized): dist (∫ i:Vantage,(F.val i:ℂ) • v i) x ≤ ε:= by
  let D:=along F; let w(i:Vantage):ℂ:= F.val i
  have hv:(∫ i:Vantage,(w i) • x) = x:= by 
      unfold w; rw [integral_smul_const] -- tune unfolding w
      rw [integral_complex_ofReal,q.2,Complex.ofReal_one,one_smul]
  rw [dist_eq_norm]; refine le_trans (a:= ‖(∫ i:Vantage,w i • v i) - x‖) (le_of_eq (congrArg (fun z:X=> ‖(∫ i:Vantage,w i • v i)-z‖) hv.symm)) ?_
  rw [← integral_sub (weightedMoney F X _ h) (weightedMoney F X _ continuous_const)]; simp_rw [← smul_sub]; apply (norm_integral_le_integral_norm ..).trans
  refine (integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _)) (payment F ε) (ae_of_all _ fun i=>?_)).trans_eq ?_
  · by_cases t:i∈ tsupport F.val
    · simp only [norm_smul,w,Complex.norm_real]; rw [← dist_eq_norm]; exact mul_le_mul_of_nonneg_left (g i t) (norm_nonneg _)
    have he:= image_eq_zero_of_notMem_tsupport t; simp only [w,he,Complex.ofReal_zero,zero_smul,norm_zero,zero_mul,le_refl]
  rw [integral_mul_const,show (∫ i:Vantage, ‖F.val i‖)=1 from normalization F q,one_mul]
lemma trueDistance (x y:X) (ε:ℝ)(u:0≤ε)(g:∀ i∈tsupport F.val, dist (A i x) y≤ε)(q:F.Normalized): dist (issue X F M A h p x) y≤ε := measures X F _ (h x) _ ε u g q
-- adjoint left-bound. Price with real smear; we compare separate positions
-- for opp and sensor. Strong both.
private lemma outgoing₁ (f:Vantage→X)(x:X)(u:Integrable f) : inner ℂ (∫ a,f a) x=∫ a,inner ℂ (f a) x:=by
  rw [←inner_conj_symm,← integral_inner u,←integral_conj]; simp_rw [inner_conj_symm]
lemma issue_adj (f: X) (b:Continuous (fun i=> (A i).adjoint f)) : (issue X F M A h p).adjoint f= ∫ i:Vantage,(F.val i:ℂ) • (A i).adjoint f := by
  apply ext_inner_left ℂ; intro y
  rw [ContinuousLinearMap.adjoint_inner_right, ←integral_inner (weightedMoney F X _ b), accomplish, outgoing₁ X _ _ (weightedMoney F X _ (h y))]
  exact integral_congr_ae (Eventually.of_forall fun i=>by dsimp only; rw [inner_smul_left,inner_smul_right,ContinuousLinearMap.adjoint_inner_right,Complex.conj_ofReal])
lemma oppDistance (x y:X) (ε:ℝ)(u:0≤ε) (b:Continuous (fun i=> (A i).adjoint x))(g:∀ i∈tsupport F.val, dist ((A i).adjoint x) y≤ε)(q:F.Normalized): dist ((issue X F M A h p).adjoint x) y≤ε:=
    (congrArg (fun z:X=>dist z y) (issue_adj X F M A h p x b)).trans_le (measures X F _ b y ε u g q)

/-- Concrete lower bound on the signal using the phase- and closeness-payments
on that *unit* ground ray. No uniformity if asked to repay after centering.
Estimate gives information also about upper nonvacuum contribution on
both field vectors. Keep identities with measured/read arguments expressed
separately (also during limit passages). -/
theorem pairStakes (U V:X.Op) (x:X)(p:‖x‖=1) (α β:ℝ)(a:0<α)(b:0<β) (hu:dist (U.adjoint x) ((α:ℂ) • x) ≤ α/16) (hv:dist (V x) ((β:ℂ) • x) ≤ β/16):
    ‖inner ℂ x (U (V x))-(α:ℂ)*(β:ℂ)‖ < α*β/2 ∧ α*β/2< ‖inner ℂ x (U (V x))‖ := by
  let u:= U.adjoint x - (α:ℂ) • x; let v:= V x - (β:ℂ) • x
  let L:= inner ℂ x (U (V x)); let T:ℂ:= (α:ℂ)*(β:ℂ)
  rw [dist_eq_norm] at hv hu; change ‖u‖ ≤_ at hu; change ‖v‖≤_ at hv; change ‖L-T‖ <_ ∧ _ < ‖L‖
  have ht: L-T= inner ℂ u ((β:ℂ) • x)+inner ℂ ((α:ℂ) • x) v+inner ℂ u v:= by
    unfold L; rw [← ContinuousLinearMap.adjoint_inner_left U, show U.adjoint x = u + (α:ℂ) • x from ((sub_add_cancel ..).symm),show V x=v+(β:ℂ) • x from ((sub_add_cancel ..).symm)]; simp only [inner_add_left,inner_add_right,inner_smul_left,Complex.conj_ofReal,inner_smul_right,inner_self_eq_norm_sq_to_K,p]; push_cast; unfold T; ring
  have hx:(norm ((α:ℂ) • x))=α:=by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg a.le,p,mul_one]
  have hy: ‖(β:ℂ) • x‖=β:=by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg b.le,p,mul_one]
  have f: ‖L-T‖<α*β/2:=by
    rw [ht]; refine lt_of_le_of_lt ((norm_add_le ..).trans ((add_le_add_left (norm_add_le ..) _).trans (add_le_add (add_le_add (b:=α/16*β) ?_ (show _ ≤ α*(β/16) from ?_)) (show _ ≤ (α/16)*(β/16) from ?_)))) ?_
    · exact ((norm_inner_le_norm (𝕜:=ℂ) u ((β:ℂ) • x))).trans (mul_le_mul hu hy.le (norm_nonneg _) (by positivity))
    · exact ((norm_inner_le_norm (𝕜:=ℂ) ((α:ℂ) • x) v)).trans (mul_le_mul hx.le hv (norm_nonneg _) a.le)
    · exact ((norm_inner_le_norm (𝕜:=ℂ) u v)).trans (mul_le_mul hu hv (norm_nonneg _) (by positivity))
    nlinarith only [mul_pos a b]
  have hT:‖T‖=α*β:=by unfold T; rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg a.le,Real.norm_of_nonneg b.le]
  refine ⟨f,?_⟩; have hh:= norm_sub_norm_le T L; rw [hT,norm_sub_rev] at hh; linarith only [f,hh]
end DoseBill
#print axioms DoseBill.pairStakes
#print axioms DoseBill.oppDistance
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
