import YM.SatinExist.Taint
import YM.SatinExist.Polynomial
import YM.SatinExist.Lede
import YM.SatinExist.Stile
import YM.SatinExist.Cameo
import SatinThinBeam
import SatinThinMill
-- Raze sell at finite registration. Toward unpadding on MANY *Operators*.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open TopologicalSpace Germ Alliance
namespace Spine
open Aria Set TopologicalSpace Metric Casting
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j) (D:P.Apron)(n w:ℕ)
local notation "K"=> P.calibration
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> P.VMark
local notation "κ"=> P.laysM
local notation "ψ"=> P.physicalEnergy j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "ω"=> P.colorZero j x
local notation "Φ"=> P.colorSpace j x
local notation "X"=>P.ColorHil j x
local notation "Χ"=>P.ManyF j x
local notation "υ" v:max=>P.voxTest j n v
local notation "φ₀" k:max p:max F:max q:max=>P.colorSpace j x (P.door j n k p F q)
local notation "u₁" v:max=> Apron.time_panel P j v D
local notation "v₁" v:max=> Apron.time_edge P j v D
local notation "W"=> P.cartage j x
local notation "C"=> P.kiosk j x
open SatinTails
local notation "ζ"=> (P.seasons j x)
variable (A:ℕ→P.Apron)(q:ℕ→ ℂ)
local notation "B" v:max t:max=> q v • P.pillar j x (A v) (-t) t 0
local notation "k" r:max=> (A r).realWidth P j
-- representation of growing fields still at positive pads. Allows asymmetric extension through congruence.
structure Mosaic (P:Spine)(j:Axis)(x:P.Spectrum0 j)(a:ℕ→ P.Apron)(q:ℕ→ℂ)(Y:ℝ → (P.ManyF j x).Op):Prop where
 thin: Tendsto (fun i=> (a i).realWidth P j) atTop (𝓝 0)
 paid(t:ℝ)(h:0<t): Brakes (fun i=> q i • P.pillar j x (a i) (-t) t 0) (Y t)
-- analytic reach at unpadded call; NOW on operator. Here one positive datum arbitrary gap. 
variable {Y:ℝ → (P.ManyF j x).Op}(M:Mosaic P j x A q Y)
include M
lemma Mosaic.tariff (t r:ℝ)(p:0<r)(u:r ≤ t): Y t=(ζ).E (t-r).toNNReal * Y r * (ζ).E (t-r).toNNReal:=by
 let E':= (ζ).E ((t-r).toNNReal); let F(i:ℕ):= (B i r)
 let U':Brakes (fun _:ℕ => E') E':= Brakes.by_budget tendsto_const_nhds
 let H:= (U'.weave (M.paid r p)).weave U'
 refine Brakes.uniqueR (M.paid t (p.trans_le u)) (H.sameC ?_ rfl)
 filter_upwards [M.thin.eventually (gt_mem_nhds p)] with i a; change E' * F i * E'= B i t
 have he:(A i).realWidth P j<r:=a
 have ht:=P.bigger_door j x (A i) (-t) t (-r) r 0 (neg_le_neg u) u (show -r ≤ Apron.time_panel P j 0 (A i) from (by unfold Apron.time_panel; rw [Pi.zero_apply]; linarith)) (show Apron.time_edge P j 0 (A i) ≤ r from (by unfold Apron.time_edge; rw [Pi.zero_apply]; linarith))
 rw [show -r - -t = t-r by ring] at ht; rw [ht]; unfold F E'; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
lemma Mosaic.drops {t r:ℝ}(p:0<r)(u:r ≤ t): ‖Y t‖≤‖Y r‖:=by
 let F:= (ζ).E (t-r).toNNReal; have ht:‖F‖≤1:=(ζ).shrinks _
 rw [Mosaic.tariff P j x A q M t r p u]; exact (norm_mul_le ..).trans ( ((mul_le_of_le_one_right (norm_nonneg (F*Y r)) ht).trans (norm_mul_le ..)).trans (mul_le_of_le_one_left (norm_nonneg _) ht)) -- tactic order syntax
omit M
variable (R b:ℝ)
include M
lemma Mosaic.driverM {R:ℝ} (p:0 < R) {C' z:ℝ}(hp:0 ≤ C')(u:1≤z)(h:∀ᶠ n:ℕ in atTop, ‖Y (R*P.macroStep n)‖ ≤ C'*z^n):∃ K'> (0:ℝ),∃ m:ℕ,∀ᶠ t in 𝓝[>] 0, ‖Y t‖ ≤ K'/t^m:=by
 let Z(x:ℝ):= ‖Y (R*x)‖
 obtain ⟨D,v,m,ht⟩:=P.real_timed Z (fun t ht s u=>Mosaic.drops P j x A q M (mul_pos p ht) (mul_le_mul_of_nonneg_left u p.le)) hp u h
 refine ⟨D*R^m,by positivity,m,?_⟩
 have g: Tendsto (fun t:ℝ=>t/R) (𝓝[>] 0) (𝓝[>] 0):=by
    apply tendsto_nhdsWithin_iff.mpr; constructor
    · have h:Tendsto (_root_.id:ℝ→ℝ) (𝓝[>] 0) (𝓝 0):= nhdsWithin_le_nhds
      simpa only [id_eq,zero_div] using h.div_const R
    filter_upwards [self_mem_nhdsWithin] with t a using div_pos a p
 filter_upwards [g.eventually ht,self_mem_nhdsWithin] with t a e; change ‖Y (R*(t/R))‖ ≤ _ at a; rw [mul_div_cancel₀ t p.ne'] at a; apply a.trans_eq; rw [div_pow]; field_simp [ne_of_gt p, ne_of_gt (show 0<t from e)] -- ring division
omit M
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
