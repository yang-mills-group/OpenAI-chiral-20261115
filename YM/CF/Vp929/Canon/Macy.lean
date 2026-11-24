import YM.CF.Vp929.Canon.Compass
import YM.CF.Vp929.Canon.Hammer
import YM.UVNext.COUPLING_RESET.Precision
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
/- With p real input pane parameters. Kinetic Hessian lower via ray limit.
   Proof uses existence of actual second derivative (earned below in final Gauge insertion via mask billing), also accounts for beta-independent path data by unmasked_precision. No smoothness needed individually for all atom summands. -/
set_option quotPrecheck false
open Push Exterior
open scoped Matrix.Norms.Frobenius

variable {n L:Side}{R:PathData SU.group}{c:Clip}{q h σ C Λ:ℝ}
local notation "G"=> SU.group
local notation "V'"=> Skye.Seat n
local notation "DN"=> Exterior.fieldDir SU.group (More n) 1
local notation "Ψ"=> Test.tileX
local notation "E'"=> Anne
local notation "Kp"=> Push.BetaTransport.kinetic
abbrev recollect (x:tangD n):DN:= fun i=> x (i.1,Exterior.axisEquiv.symm i.2)

lemma gather_g (x:tangD n):Exterior.collect G (recollect x)=x:=funext fun e=>congr_arg (fun j=> x (e.1,j)) (Exterior.axisEquiv.left_inv e.2)
lemma representing (x:tangD n)(s:ℝ): AnalyticBridge.VerifiedReset.line x s= Precision.represent (s • recollect x) := by
 unfold Precision.represent AnalyticBridge.VerifiedReset.line; rw [show Exterior.collect G (s • recollect x)=s • (Exterior.collect G (recollect x)) from rfl,gather_g]
def perSup (p:Face (Per (More n))) (x:DN) (R:PathData G)(c:Clip):ℝ:=c.direct* (‖Work.F03.faceCurl p x‖^2/2)+ ‖Work.F03.ellLine R p x‖^2/2
abbrev took (x:DN)(R:PathData G)(c:Clip):=∑ b:Face (Per (More n)),perSup b x R c
variable (z:Face (Per (More n)))
lemma chest (x:DN)(u:R.Bounds c σ C Λ):Tendsto (fun s:ℝ=> Precision.quadratic c R (Precision.represent (s • x))/s^2) (𝓝[≠] 0) (𝓝 (took x R c)):=by
 unfold Precision.quadratic; simp_rw [sum_div]; apply tendsto_finsetSum _; intro i _; let F:= fun t:ℝ=> faceValue (Precision.represent (t • x)) i; have he:F 0=1:=by simp [F,faceValue,travel,square]
 have hp:= ((Work.F03.price_limit he (Work.F03.face_deriv i x)).const_mul c.direct).add (((Work.F03.ell_limit R u i x).norm.pow 2).div_const 2); refine hp.congr' (Eventually.of_forall fun t=>?_); unfold F; rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow]; ring
include z
omit z
lemma homeS (x:tangD n)(P:BudgetPoint) : ∀ᶠ t:ℝ in 𝓝 0, pingS P.threshold univ (AnalyticBridge.VerifiedReset.line x t):=by
 have hab: Tendsto (fun i:ℝ=> i • x) (𝓝 0) (𝓝 0):= by simpa only [zero_smul] using (show Continuous (fun i:ℝ=> i • x) by fun_prop).tendsto 0
 exact hab.eventually (Chaff.wind_p (1:Pane n) (ContinuousLinearMap.id ℝ (tangD n)) (ping_f P _))
lemma homeFlag {v:Pane n}{r:ℝ}(h:pingS r univ v) : flags r v=∅:=by
 have h':= ping_le h; exact Finset.eq_empty_of_forall_notMem (fun x h=>Finset.disjoint_left.mp h' (mem_univ x) h)
def takeB (x:tangD n)(R:PathData G)(c:Clip):= (Fintype.card Signed:ℝ)⁻¹* ∑ s: Signed,took (Bid.pulled (recollect x) s) R c
lemma tide (u:R.Bounds c σ C Λ)(x:tangD n)(P:BudgetPoint): Tendsto (fun s:ℝ=> Kp R c P (AnalyticBridge.VerifiedReset.line x s)/s^2) (𝓝[≠] 0) (𝓝 (takeB x R c)):=by
 have hh (d:DN):Tendsto (fun s:ℝ=> (Precision.quadratic c R (Precision.represent (s • d)) + Precision.uncut R.cubic (Precision.represent (s • d))+Precision.uncut R.quartic (Precision.represent (s • d)))/s^2) (𝓝[≠] 0) (𝓝 (took d R c)) := by
    have hp:= ((chest d u).add (Work.F03.uncut_limit (k:=0) d R.cubic u.width u.three)).add (Work.F03.uncut_limit (k:=1) d R.quartic u.width u.four); simpa only [add_zero,add_div] using hp
 apply ((tendsto_finsetSum univ fun s _=> hh (Bid.pulled (recollect x) s)).const_mul ((Fintype.card Signed:ℝ)⁻¹)).congr'; filter_upwards [(homeS x P).filter_mono nhdsWithin_le_nhds] with s h
 rw [(UVNext.CouplingReset.unmasked_precision R c (homeFlag h)).1, representing]; simp only [Precision.mainTerm,RG.Patch.average,Work.F03.represent_pulled,mul_div_assoc,sum_div]
private lemma reone (x:DN)(u:R.Bounds c σ C Λ) : took x R c=took (Bid.pulled x 1) R c:=by apply tendsto_nhds_unique (chest x u); apply (chest (Bid.pulled x 1) u).congr'; filter_upwards with t; rw [←Work.F03.represent_pulled, pull_id]
lemma took_nonneg (x:DN)(c:Clip): 0≤ took x R c:=by
 have hp:= c.quadratic_pos; exact sum_nonneg fun i _=> show 0≤ perSup i x R c from by unfold perSup; positivity
local notation "xΘ"=> transverse (s:=n) q
local notation "yΘ"=> recollect xΘ
include z
omit z
lemma main_face (o:V') (u:Frequency L n q): Work.F03.faceCurl (o,Ψ) yΘ= (2*Real.sin (q/2)/q*Real.cos (rtape q o+q/2)) • AnalyticBridge.VerifiedReset.spike G:=by
 unfold Work.F03.faceCurl; rw [← Exterior.fundamental,gather_g,AnalyticBridge.VerifiedReset.Square.cochain_square]; simp only [tileX,transverse,↓reduceIte, if_neg (by decide:(0:Axis)≠1),sub_self,sub_zero]; rw [←sub_smul]; exact congrArg (fun z:ℝ=> z • AnalyticBridge.VerifiedReset.spike G) (blade_face u o)
def direct_cost (c:Clip):ℝ:= c.direct/(8*Fintype.card Signed)
lemma posed (c:Clip): 0<direct_cost c:=by unfold direct_cost; have hp:=c.quadratic_pos; have hu:=AnalyticBridge.VerifiedReset.card_pos; positivity
lemma plowed (z:Frequency L n q): c.direct*sites n/16 ≤ took yΘ R c:=by
 let a:=2*Real.sin (q/2)/q; let d:= c.direct; have he:0<d:= c.quadratic_pos
 let F(o:V')(b:Lattice.PlaqAxes):=perSup (o,b) yΘ R c; have ht:= q_sinh z; unfold took; rw [Fintype.sum_prod_type]
 calc
    _ ≤ d * (a^2*(sites n/2))/2 :=by change (1/2:ℝ) ≤ a at ht; have h:=sites_pos n; change d*_/16 ≤_; nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) ht 2) (show d * sites n≥0 from mul_nonneg he.le (by linarith))]
    _ = ∑ i:V',d*(‖Work.F03.faceCurl (i,Ψ) yΘ‖^2/2) :=by
       simp_rw [main_face _ z,norm_smul,Real.norm_eq_abs,AnalyticBridge.VerifiedReset.spike_norm Thera.yet_one,mul_one,sq_abs,mul_pow ((2:ℝ)*_/q)]; rw [←mul_sum,←sum_div,←mul_sum, cosineQ z]; unfold a; ring
    _ ≤ _:=by
       exact sum_le_sum fun i _=> le_trans (b:= F i Ψ) (le_add_of_nonneg_right (by positivity : (0:ℝ)≤ ‖Work.F03.ellLine R (i,Ψ) yΘ‖^2/2)) (single_le_sum (f:=F i) (fun b _=> by unfold F perSup; have h:= c.quadratic_pos; positivity) (mem_univ _))
lemma split_rate (u:R.Bounds c σ C Λ)(z:Frequency L n q): direct_cost c*sites n≤2*takeB xΘ R c:=by
 let n0:ℝ:= Fintype.card Signed; have hp:=AnalyticBridge.VerifiedReset.card_pos; have hs:= (plowed (R:=R) (c:=c) z).trans_eq (reone _ u); let F':= fun s:Signed=> took (Bid.pulled yΘ s) R c
 have hv:= hs.trans (single_le_sum (f:=F') (fun s _=> took_nonneg _ c) (mem_univ _)); change _≤ 2*(n0⁻¹*∑ s,F' s)
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hp.le)) (by norm_num : (0:ℝ) ≤ 2)); unfold n0 direct_cost; apply le_of_eq; field_simp; ring

abbrev kineticC (n:Side) (R:PathData G)(c:Clip)(P:BudgetPoint)(q:ℝ) := (sites n)⁻¹*iteratedDeriv 2 (Kp R c P ∘ AnalyticBridge.VerifiedReset.line (transverse (s:=n) q)) 0
lemma macy (u:R.Bounds c σ C Λ)(H:Frequency L n q)(P:BudgetPoint) (p:ContDiffAt ℝ 2 (Kp R c P ∘ AnalyticBridge.VerifiedReset.line xΘ) 0) : direct_cost c ≤ kineticC n R c P q :=by
 let f:= Kp R c P ∘ AnalyticBridge.VerifiedReset.line xΘ; have hu:Tendsto (fun t:ℝ=> f t/t^2) (𝓝[≠] 0) (𝓝 (takeB xΘ R c)):= tide u _ _; obtain ⟨v,g⟩:= Work.F03.value_slope_of_sq_limit p.continuousAt hu; have e:= tendsto_nhds_unique hu (Work.F03.taylor_limit_two p v g.deriv); let b:=sites n; have ht:=sites_pos n; have h:0<b:=lt_of_lt_of_le zero_lt_one ht; let x:=takeB xΘ R c
 change x=iteratedDeriv 2 f 0/2 at e; change _ ≤ b⁻¹*_; rw [show iteratedDeriv 2 f 0=2*x by linarith]; calc
    _ ≤ b⁻¹*(direct_cost c* b):=by rw [mul_left_comm,inv_mul_cancel₀ h.ne',mul_one];
    _ ≤ _:= mul_le_mul_of_nonneg_left (split_rate u H) (inv_nonneg.mpr h.le)
end Test
end YM.CF.Py.Rate
