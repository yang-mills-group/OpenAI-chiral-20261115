import YM.CF.Esti.Hope
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){A B:Stores S}{r v:ℕ}
open CF.Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}{n:ℕ}{K M C D:ℝ}{x:E}{U:E→ Config G f}
lemma gran {v:E→G.El}(p:grantB n v x C):grantB n (fun i=>(v i)⁻¹) x C:=by
 let L: G.Mat ≃L[ℝ] G.Mat:= starL ℝ
 unfold grantB; rw [←one_mul C]; refine (p.linear L.toContinuousLinearMap ?_).germ (Eventually.of_forall fun i=> (G.mat_inv ..).symm)
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro u; change ‖star u‖≤_; rw [norm_star,one_mul]

def fareG (G:Gauge)(x:G.Mat) :ℝ:=1 + Push.Uniform.traceCharge G x
lemma fare_h (G:Gauge)(u:G.El): fareG G (G.mat u)=G.price u:=by unfold Gauge.price fareG Push.Uniform.traceCharge; change 1+(-(G.repDim:ℝ)⁻¹)*(G.mat u).trace.re=_; ring
lemma fare_a {f:E→G.Mat}(p:Allows n f x C):Allows n (fareG G ∘ f) x (Push.Uniform.priceCost G C):=(allows_const x (v:=(1:ℝ)) (show ‖(1:ℝ)‖ ≤ 1 by simp)).add (p.linear (Push.Uniform.traceCharge G) le_rfl) -- tune
open Work.F02
lemma guideM (S:Side)(g:E→ Config G S)(p:∀ i:Bond S,grantB n (fun x=> g x i) x C): Allows n (fun i=> physical (g i)) x C:=allows_pi ((p (Classical.arbitrary _)).nonneg) fun i=> ((p i).pair (gran (p i)))
lemma trekP (S:Side) (h:E → Config G S)(u:∀ i:Bond S,grantB n (fun x=>h x i) x C)(w:Walk)(i:Site S)(k:ℕ)(hx:w.length ≤ k):grantB n (fun x=>travel (h x) i w) x (Push.Uniform.travelCost G n k C):=by
 let f(M:Ambient G S):=stringMat M w i; let r:ℝ:= (1+(k:ℝ))⁻¹; let p:=(fun x=>Work.F02.physical (h x)); let a:=Real.exp 1*‖(1:G.Mat)‖; have hp:0<r:=by unfold r; positivity
 have hb:∀ y∈ball (p x) r,‖f y‖≤a:=by
    intro y t; apply (stringMat_bound _ hp.le _ (ball_subset_closedBall t) _ _).trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
       _ ≤ (Real.exp r)^w.length:=by gcongr; linarith [Real.add_one_le_exp r]
       _ ≤ _:=by rw [← Real.exp_nat_mul]; apply Real.exp_monotone; unfold r; rw [←div_eq_mul_inv]; apply (div_le_one (by positivity)).2; exact (show (w.length:ℝ) ≤ k by exact_mod_cast hx).trans (le_add_of_nonneg_left zero_le_one)
 let b:= a*((1+(2:ℝ)^n*(1+k))^n); have hv: Allows n f (p x) b:=by
    have he:= Push.Uniform.allows_real_of_entire n (stringMat_contDiff w i) hp hb; rw [show (2:ℝ)^n/r=2^n*(1+k) from (by unfold r; rw [div_eq_mul_inv,inv_inv])] at he; exact ⟨he.1.of_le le_top,he.2⟩
 exact (hv.comp (f:=p) (guideM S h u)).germ (Eventually.of_forall fun i=> stringMat_physical ..)
-- χ shutter: pays broad ANY Mats, not using family of U analytic
abbrev testing (q:Chi)(d z:ℝ)(b:Bool):=cliff b q (2/d^2*z)
lemma currencyT(q:Chi)(n:ℕ):∃ F:ℝ,1 ≤ F ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{v:E→ℝ}{x:E}{C:ℝ}(d:ℝ)(b:Bool), Allows n v x C → Allows n (fun w=>testing q d (v w) b) x (Jet.composeCost n F ((2/d^2)*C)) ∧ Zed n (fun w=>testing q d (v w) b) x:=by
 choose c p hc using fun b:Bool=>cost_χ q b n
 let F:=max (c true) (c false); have hh(b:Bool): c b ≤ F:=by cases b; exact le_max_right ..; exact le_max_left ..
 refine ⟨F,(p true).trans (hh true),@fun E _ _ v x C d b hv=>?_⟩; have he:= hv.smul (2/d^2); rw [abs_of_nonneg (by positivity : 0 ≤ 2/d^2)] at he; let t(w):=2/d^2 * v w; exact ⟨(((hc b (t x)).mono (hh b)).comp (f:=t) he),zed q b t he ⟩
lemma chooseF(q:Chi)(U:G.El)(d:ℝ): q.innerShare d (G.chord U)=testing q d (G.price U) true:=by unfold Chi.innerShare testing cliff; rw [div_pow,G.chord_price]; simp only [if_true]; ring_nf
lemma chooseB(q:Chi)(U:G.El)(d:ℝ): 1-q.innerShare d (G.chord U)=testing q d (G.price U) false:=by rw [chooseF]; rfl
end YM.CF.Esti
