import YM.CF.Bloom.Screen
import YM.CF.Paxos.Seed
import YM.CF.Song.Full
import YM.CF.Sere.Ward
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
open Oath
abbrev cone_t(L:Side)(k:ℕ) (x:ℝ):= Scales.g SU.group L x^2* Scales.p SU.group L x^k
lemma fork_u(L:Side)(k:ℕ) : sizeK L 2 (cone_t L k):= ((sizeK.main L).square 2).tint ((sizeK.height L).powC k)
open Next.Scheduling Clock
lemma throatK (L:Side)(k:ℕ): ∀ᶠ x:ℝ in atTop,∀ y:ℝ,x≤y→ cone_t L k y ≤ cone_t L k x:=by
 let Y:= Scales.y SU.group L; let V(i):= - Real.exp i + k*i^2
 have he(x): HasDerivAt V (-Real.exp x+k*(2*x)) x:=by exact HasDerivAt.congr_deriv ((Real.hasDerivAt_exp x).neg.add (((hasDerivAt_id' x).pow 2).const_mul (k:ℝ))) (by push_cast; norm_num)
 have hx:Tendsto (fun x:ℝ=> ((2:ℝ)*k)*(x / Real.exp x)) atTop (𝓝 0):=by simpa only [mul_zero,pow_one,div_eq_mul_inv,Real.exp_neg] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul ((2:ℝ)*k)
 obtain ⟨n,W⟩:= eventually_atTop.mp (hx.eventually (ge_mem_nhds zero_lt_one))
 have hz:AntitoneOn V (Set.Ici n):= antitoneOn_of_deriv_nonpos (convex_Ici n) ((show Continuous V by unfold V; fun_prop).continuousOn) (fun x _=>(he x).differentiableAt.differentiableWithinAt) (fun x p=>by rw [(he x).deriv]; have hh:= W x (interior_subset p); rw [←mul_div_assoc,div_le_one (Real.exp_pos _)] at hh; linarith)
 have hu(x:ℝ)(g:1 < Y x): cone_t L k x= Real.exp (V (Clock.tick (Y x))):=by
    unfold cone_t; rw [Scales.g,Scales.p, Clock.formula g,Clock.watch_two]; unfold V; rw [←Real.exp_nat_mul,←Real.exp_nat_mul, ←Real.exp_add]; norm_num; unfold Y; congr 1; ring
 filter_upwards [(Scales.year SU.group L).eventually_gt_atTop 1, (Clock.clock.comp (year SU.group L)).eventually_ge_atTop n] with x p v u t
 have hv:Y x≤Y u:= add_le_add_left t _; have ht: Clock.tick (Y x) ≤ Clock.tick (Y u):= Real.log_le_log (Real.log_pos p) (Real.log_le_log (zero_lt_one.trans p) hv)
 rw [hu x p,hu u (p.trans_le hv)]; exact Real.exp_monotone (hz (show n ≤ _ from v) (v.trans ht) ht)
lemma govern_K(L:Side)(F:ℝ→ℝ)(h:sizeK L 2 F) : ∃ f:ℝ→ℝ,sizeK L 2 f∧∀ᶠ x:ℝ in atTop, F x≤ f x ∧0 ≤ f x∧∀ y,x≤y→f y≤ f x:=by
 obtain ⟨k,h⟩:=h; exact ⟨_,fork_u L k, (h.and (throatK L k)).mono fun x p=> ⟨(le_abs_self _).trans p.1,(abs_nonneg _).trans p.1, p.2⟩⟩
abbrev grant_B(L:Side)(x:ℝ):ℝ:=Real.sqrt (Scales.y SU.group L x)
lemma gran_x(L:Side)(F:ℝ→ℝ)(h:sizeK L 0 F):∀ᶠ x in atTop,|F x|≤grant_B L x:=by
 let G:= Scales.g SU.group L
 filter_upwards [(sizeK.tint (sizeK.main L) h).spine.abs.eventually (ge_mem_nhds (by norm_num: |(0:ℝ)|<1)),(year SU.group L).eventually_gt_atTop 0] with x p v
 have he:= Scales.gauge SU.group L v; rw [abs_mul,abs_of_pos he] at p; change (grant_B L x)⁻¹ * _ ≤_ at p; rwa [inv_mul_eq_div,div_le_one (Real.sqrt_pos.mpr v)] at p
end YM.CF.Py
