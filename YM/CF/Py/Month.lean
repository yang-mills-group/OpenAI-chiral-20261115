import YM.CF.Py.Goals
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
abbrev shiftC(f:ℝ→ℝ)(v:ℝ):ℝ→ℝ:=fun x=> f (x+v)
local notation "y_"=> SectorNext.Remainder.Scales.y SU.group
local notation "g_"=> SectorNext.Remainder.Scales.g SU.group
local notation "p_"=> SectorNext.Remainder.Scales.p SU.group
-- one hop UV calendar.Eβ size projections.Index input f@hat(high)
lemma sweepK(P:Side)(a:ℝ)(u:0≤a)(F:ℝ→ℝ)(t:sizeK P 1 F) :sizeK P 1 (shiftC F a):=by
 let Y:=y_ P; let g:=g_ P; let p:=p_ P; have hx(x:ℝ):Y (x+a)=Y x+a:=by unfold Y SectorNext.Remainder.Scales.y betaF; ring
 have he: Tendsto (fun x:ℝ=>x+a) atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_id
 obtain ⟨H,U⟩:= t
 have hv := Work.E09.temp_ratio a; let f(x):=fiery SU.group x P
 have hu: Tendsto Y atTop atTop:=year SU.group P
 have ht:∀ᶠ x:ℝ in atTop, f (x+a) ≤ 2*f x:=by
    filter_upwards [hu.eventually (hv.eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num))),hu.eventually_gt_atTop 0] with x p t; change temp (Y (x+a)) ≤ _; rw [hx]; exact (div_le_iff₀ (Work.E09.temp_pos t)).mp p
 have hF(x:ℝ):f x=g x*p x:= Scales.fi _ _ _
 refine ⟨H+1,?_⟩; filter_upwards [he.eventually U,ht, (Scales.peak SU.group P).eventually_ge_atTop (4^H), hu.eventually_gt_atTop 0, hu.eventually_ge_atTop a] with x v hq hy hw hz; apply le_trans v; change g (x+a)^1*p (x+a)^H ≤ g x^1*p x^(H+1)
 have hp:Y (x+a) ≤2*Y x:=by rw [hx]; linarith
 have hh:Y x ≤ Y (x+a):= by rw [hx]; linarith
 have hy':=(hw.trans_le hh); have hx1:0<g x:=Scales.gauge _ _ hw; have hx2:0<g (x+a):=Scales.gauge _ _ hy' -- missing proof
 have hV:Y x*g x^2=1:= yg2 _ _ hw; have hg:Y (x+a)*g (x+a)^2=1:=yg2 _ _ hy'
 have h:g (x+a)≤ g x:=by by_contra! w; have ht: g x^2 < g (x+a)^2:= pow_lt_pow_left₀ w hx1.le (by norm_num); nlinarith only [hV,hg,mul_lt_mul_of_pos_left ht hw,mul_le_mul_of_nonneg_right hh (sq_nonneg (g (x+a)))]
 have h0:g x≤2*g (x+a):=by
    by_contra! v; have he:(2*g (x+a))^2<g x^2:=pow_lt_pow_left₀ v (by positivity) (by norm_num)
    nlinarith only [hV,hg,mul_lt_mul_of_pos_left he hw,mul_le_mul_of_nonneg_right hp (sq_nonneg (g (x+a))),mul_nonneg hw.le (sq_nonneg (g (x+a)))]
 rw [hF,hF] at hq; have hm:0 ≤ p x:= (Scales.pos ..).le; have hn:0 ≤ p (x+a):= (Scales.pos ..).le
 have hg': p (x+a) ≤4*p x:=(mul_le_mul_iff_right₀ hx2).mp (show g (x+a)*p (x+a) ≤ g (x+a)*(4*p x) from hq.trans (by nlinarith only [mul_le_mul_of_nonneg_right h0 hm]))
 rw [pow_one,pow_one,pow_succ]; have hx': (4*p x)^H≤ p x^H*p x:=by rw [mul_pow,mul_comm]; exact mul_le_mul_of_nonneg_left hy (pow_nonneg hm _)
 exact mul_le_mul h ((pow_le_pow_left₀ hn hg' _).trans hx') (pow_nonneg hn _) hx1.le
end YM.CF.Py
