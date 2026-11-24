import YM.CF.Vp929.Stage.Escrow
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.LogFunding
import YM.SectorNext.VACUUM_NORMALIZATION.Laplace
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
/-! # Single-step unmarked prefactor pressure in the deployed-hierarchy service

First link log estimate and tree count; no equal-period hypotheses. -/

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
namespace Pannier
section oneLink
variable {G : Gauge} (L:ChartRatio G) (p:LocalRatio L)
-- All dimensions here Lie rep G of the payment. (The Color multiplicity already bought in that system.)
def halfLie (G:Gauge):ℝ := (Module.finrank ℝ G.Color:ℝ)/2
lemma shadowLie (G:Gauge): halfLie G=(Fintype.card G.ColorIndex:ℝ)/2:= by
 simp [halfLie,Gauge.Color]
lemma pen_log_nonneg (G : Gauge):0≤halfLie G:=by unfold halfLie; positivity
open YM.SectorNext.Vacuum

include p
lemma lap (g:KernelChoices) :
   ∃ c> (0:ℝ), ∀ᶠ b:ℝ in atTop, ∀ {m n:Side}(S:StepData m n), S.kernel=g → |Real.log (S.penaltyZ b G)+halfLie G * Real.log b| ≤ c:=by
 let v := narrow L g.penalty
 have hp : 0 < v:= narrow_pos L p _ g.penalty_pos
 let f (t:ℝ):= t^(Module.finrank ℝ G.Color)*linkZ G (g.penalty*t^(2:ℕ))
 have hv : Tendsto f atTop (𝓝 v) := first_asymptotic L p g.penalty g.penalty_pos
 let c:= |Real.log v|+1
 have hc : |Real.log v|<c:=by linarith [show c= _ from rfl]
 refine ⟨c,by unfold c; positivity,?_⟩
 have hh : ∀ᶠ t:ℝ in atTop, |Real.log (f t)|≤c:=(hv.log hp.ne').abs.eventually (ge_mem_nhds hc)
 filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_sqrt_atTop.eventually hh] with b h k
 intro m n S hS
 let t:=Real.sqrt b
 have h0: 0<t:= Real.sqrt_pos.mpr h
 have he : S.penaltyZ b G = linkZ G (g.penalty*b) := by
   unfold StepData.penaltyZ StepData.penaltyWeight linkZ SectorNext.Vacuum.mouth
   rw [hS]; congr 1; ext x; ring_nf
 rw [← Real.sq_sqrt h.le] at he
 change |Real.log (t^ (Module.finrank ℝ G.Color)*linkZ G (g.penalty*t^2))|≤c at k
 rw [show linkZ G (g.penalty*t^2)= S.penaltyZ b G from ?_,Real.log_mul (by positivity : t^ (Module.finrank ℝ G.Color)≠0) (S.penaltyZ_pos ..).ne', Real.log_pow,show Real.log t=_ from Real.log_sqrt h.le] at k
 convert k using 2 <;> first| (unfold halfLie; ring)|congr 1
 · exact he.symm.trans (by rw [Real.sq_sqrt h.le])
-- β of either chosen input can vary.
lemma heatmark (g:KernelChoices) :
   ∃ c> (0:ℝ), ∀ᶠ y:ℝ in atTop,∀ b∈Set.Icc (y/2) (2*y),∀ {m n:Side}(S:StepData m n),S.kernel=g → |Real.log (S.penaltyZ b G)+halfLie G * Real.log y| ≤ c := by
 obtain ⟨c,h,hv⟩:=lap L p g
 obtain ⟨b₀,z⟩:= eventually_atTop.mp hv
 refine ⟨c+halfLie G * Real.log 2,add_pos_of_pos_of_nonneg h (mul_nonneg (pen_log_nonneg G) (Real.log_nonneg (by norm_num))),?_⟩
 filter_upwards [eventually_ge_atTop (2*b₀),eventually_gt_atTop (0:ℝ)] with y e x b t
 intro m n S p
 obtain ⟨j,k⟩:= t
 have hx: 0<b:= lt_of_lt_of_le (half_pos x) j
 have hl := abs_le.mp (z b (show b₀≤b by linarith) S p)
 have hd:= Real.log_le_log (half_pos x) j
 have he:= Real.log_le_log hx k
 rw [Real.log_div x.ne' (by norm_num)] at hd; rw [Real.log_mul (by norm_num) x.ne'] at he
 refine abs_le.mpr ⟨?_,?_⟩ <;> nlinarith only [hl.1,hl.2,mul_le_mul_of_nonneg_left hd (pen_log_nonneg G),mul_le_mul_of_nonneg_left he (pen_log_nonneg G)]

omit p
local notation "Ϝ" => SU.group
lemma flake_cost (L:ChartRatio SU.group) (p:LocalRatio L) : ∃ c> (0:ℝ),∀ y> (0:ℝ),∀ b∈Set.Icc (y/2) (2*y),∀ z:ℝ,1≤z → |Real.log (shotM L z b)+halfLie Ϝ * Real.log y| ≤ c := by
 let d:=halfLie Ϝ * Real.log 2
 have hp:=Appel.point_p (G:=SU.group) zero_lt_one
 let f := point Ϝ
 refine ⟨1+|logFlat L|+d+|Real.log (f 1)|, by unfold d; have := pen_log_nonneg Ϝ; positivity,?_⟩
 intro y hy b ⟨l,r⟩ z hz
 have hx:0<b:= lt_of_lt_of_le (half_pos hy) l
 have hh: f 1≤f z:= ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (closedBall_subset_closedBall hz))
 have he: f z ≤ 1:= (show point Ϝ z ≤ (rice Ϝ Set.univ).toReal from ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq (by simp)
 have h1 : Real.log (f 1)≤Real.log (f z):= Real.log_le_log hp hh
 have hZ:0<f z:=hp.trans_le hh
 have h2 : Real.log (f z)≤0:= by simpa using Real.log_le_log hZ he
 have hd:= Real.log_le_log (half_pos hy) l
 have hf:= Real.log_le_log hx r
 rw [Real.log_div hy.ne' (by norm_num)] at hd; rw [Real.log_mul (by norm_num) hy.ne'] at hf
 rw [shotM, Real.log_mul (spare_pos _ p hx).ne' hZ.ne',spare_formula _ p.scale hx,← shadowLie]
 unfold d
 refine abs_le.mpr ⟨?_,?_⟩ <;> nlinarith only [neg_abs_le (logFlat L),le_abs_self (logFlat L),h1,h2,hZ, neg_abs_le (Real.log (f 1)),abs_nonneg (Real.log (f 1)),mul_le_mul_of_nonneg_left hd (pen_log_nonneg Ϝ), mul_le_mul_of_nonneg_left hf (pen_log_nonneg Ϝ)]
lemma thinWireCount {m f : Side}(G:Ratio m f) (F:Forest G) : (Fintype.card F.Free:ℝ)= (3:ℝ)*(Fintype.card (Site f):ℝ)+ (Fintype.card (Site m):ℝ):=by
 have hp:= FlatTree.count_clear F
 rw [show Fintype.card (Edge (Site f)) = Fintype.card (Site f)*4 from (Fintype.card_prod ..).trans (by rfl)] at hp; exact_mod_cast (show (Fintype.card F.Free:ℕ)=3*Fintype.card (Site f)+Fintype.card (Site m) by omega)
end oneLink
end Pannier
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pannier.flake_cost
#print axioms YM.CF.Py.Rate.Pannier.heatmark
