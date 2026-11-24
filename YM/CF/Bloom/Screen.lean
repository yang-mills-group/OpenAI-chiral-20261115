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
variable {c c' S' :Side} (V:Grace K R L)(C A:ℝ)
-- control entire calendar offset against light β capacity. all lengths up to u*log^k. do not extrapolate.
local notation "gL"=> Scales.g SU.group R.L
local notation "βη"=> dleaf R.L
variable (F:ℝ→ℝ)
lemma tenor_Q (h:Litt R 2 F)(u:0<A):∀ᶠ x:ℝ in atTop,F x ≤ A* dleaf R.L x:=by
 let P(x:ℝ):=F x / gL x ^2
 have he:= ((clove_p R).leanB h).spine_a
 filter_upwards [he.eventually (ge_mem_nhds u), spice_R (R:=R),eventually_gt_atTop (0:ℝ)] with i p h t
 have hg:= h.2.2; have hu:=Work.E09.temp_pos t; set a:=gL i; set k:=temp i
 change F i / a^2* (a/k) ≤ A at p; rw [show F i/a^2*(a/k)=F i/(a*k) from ?_] at p; exact (div_le_iff₀ (mul_pos hg hu)).mp p; field_simp -- tune
lemma glimp_T : ∃ i:ℝ,1 ≤ i ∧∀ x:ℝ,i ≤ x→0 < dleaf R.L x ∧0<gL x ∧ ∀ y:ℝ,x ≤ y → dleaf R.L y ≤ dleaf R.L x∧plow x ≤ plow y :=by
 obtain ⟨i,P⟩:= Rue.arrests; obtain ⟨j,W⟩:= eventually_atTop.mp ((Scales.year SU.group R.L).eventually_gt_atTop 0)
 refine ⟨max (max j 1) (i+1),(le_max_right j _).trans (le_max_left ..),fun x t=>?_⟩; have hx0:i < x:=lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) ((le_max_right ..).trans t); have hx:j≤x:= (le_max_left ..).trans ((le_max_left ..).trans t); have hp:1≤x:=(le_max_right ..).trans ((le_max_left ..).trans t); have hr:0<x:=zero_lt_one.trans_le hp; have h:= Scales.gauge SU.group R.L (W _ hx)
 refine ⟨mul_pos h (Work.E09.temp_pos hr),h,fun y u=>?_⟩; rcases u.eq_or_lt with u|u; rw [u]; exact ⟨le_rfl,le_rfl⟩
 refine ⟨mul_le_mul (show gL y ≤ gL x from ?_) (P.antitoneOn hx0 (hx0.trans u) u.le) (Work.E09.temp_pos (hr.trans u)).le h.le,?_⟩
 · exact inv_anti₀ (Real.sqrt_pos.2 (W _ hx)) (Real.sqrt_le_sqrt (add_le_add_left u.le _))
 unfold plow Scales.b radiusB; push_cast; have h:= Real.log_le_log hr u.le; gcongr <;> first|assumption|exact Real.log_nonneg hp -- tune
variable {u0 wα wS u₁ z v:ℝ}{B:Side}{Y:Grasp V.U B d}{W:GivenX V Y}
-- abstract scalable issue funds evergreen
lemma stand_v (K:Patch)(A:ℝ)(h:A/K.L.val ≤1/4)(E G:ℝ→ℝ)(p:Litt K 2 E)(t:Litt K 2 G):∀ᶠ i:ℝ in atTop, A/(K.L.val:ℝ)*dleaf K.L i+E i ≤ dleaf K.L i∧ G i ≤ dleaf K.L i:=by
 filter_upwards [tenor_Q (1/2) E p (by norm_num),tenor_Q 1 G t zero_lt_one, spice_R (R:=K),eventually_gt_atTop (0:ℝ)] with i e t' u v; have hx:0 ≤ dleaf K.L i:= (mul_pos u.2.2 (Work.E09.temp_pos v)).le; refine ⟨?_,by simpa using t'⟩; linarith [mul_le_mul_of_nonneg_right h hx]
variable(q:Chi)
abbrev rendK(k:ℕ)(i:ℝ):= (1/16:ℝ)/(plow i)^k
lemma fuel_s(F:ℝ→ℝ)(h: Chill_v F)(k:ℕ):∀ᶠ x:ℝ in atTop, |F x| ≤ rendK k x:=by
 filter_upwards [(h k).abs.eventually (ge_mem_nhds (show |(0:ℝ)| < 1/16 by norm_num))] with x p; rw [abs_mul] at p; have ht:0<plow x:=lt_of_lt_of_le zero_lt_one (Scales.size x); unfold rendK; apply (le_div_iff₀ (by positivity)).mpr; simpa only [abs_of_pos (pow_pos ht k),mul_comm (|F x|)] using (by rwa [abs_of_pos (pow_pos ht k)] at p : plow x^k*|F x| ≤ 1/16)
-- old coupling trajectory due S_B narrow.
end YM.CF.Py
