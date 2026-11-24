import Preen.StagePiece
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Nc" i:max=> count P.run s i
local notation "Y"=>P.run
local notation "π₀" i:max => P.period (P.projection.rows i)
local notation "ζ₀" i:max => P.cutoff (P.projection.columns i)
abbrev boarding(i:ℕ):ℝ:= berlin Y A s (π₀ i) (ζ₀ i) b (pedestal o (Nc (π₀ i))) (fun _=>1)
local notation "Z"=>hatch A (Yx)
local notation "vT"=>posess SU.group Z
noncomputable abbrev upperZ:ℝ:=((ridges:ℝ)*(Z).cost^2+1)^2
open ProbabilityTheory
open Precision
lemma board_paid (i:ℕ):|boarding P s A o b i|≤upperZ P s A:=by
 unfold boarding berlin _root_.YM.Gleam.Luster.Risa.meal
 dsimp only
 -- lemma on generic n,H.ESO
 exact tariff _ _ _ _ _ _ _
where
 tariff {p:Clip}{Z0: Gauge}{H:Bed}{x z t:ℝ}{M:PathData Z0}{n:Side}(B:M.Bounds p x z t)(L:Attached H M)(Xh:Hike)(y:ℝ)(b:Bool)(w:Bool→Site n)(s:Bool→Signed): -- use N binder bad
  |_root_.YM.Regis.Head.clouds B L (fun t=>raiseZ Z0 p Xh y b t s w)|≤ ((ridges:ℝ)*Xh.cost^2+1)^2:=by
   let k:=((ridges:ℝ)*Xh.cost^2+1)^2
   let T:= Gleam.stamen B L n; let f:=fun x:T=>raiseZ Z0 p Xh y b x.val s w
   change |∫ i,f i∂stdGaussian T| ≤ k; rw [←Real.norm_eq_abs]; refine (norm_integral_le_of_norm_le (g:=fun _=>k) (integrable_const _) (Eventually.of_forall fun i=>?_)).trans_eq ?_; rw [Real.norm_eq_abs]; exact raise_bound Xh y b w s i.val
   simp
/-- For CP8 comparison: pilot.C and t-chord. -/
structure Pilot where
 station:ℕ→ℕ
 trans : StrictMono station
 price:ℝ
 market:Tendsto ((boarding P s A o b) ∘ station) atTop (𝓝 price)
-- eventually.Price guaranteed.After.W. q.
noncomputable def pilot : Pilot P s A o b :=by
 let k:= upperZ P s A
 let f:=boarding P s A o b
 have h: ∃ x∈Metric.closedBall (0:ℝ) k, ∃ φ:ℕ→ℕ, StrictMono φ ∧ Tendsto (f∘φ) atTop (𝓝 x):= (isCompact_closedBall 0 k).isSeqCompact (fun i=> by rw [Metric.mem_closedBall,Real.dist_eq,sub_zero]; exact board_paid P s A o b i)
 exact ⟨h.choose_spec.2.choose,h.choose_spec.2.choose_spec.1,h.choose,h.choose_spec.2.choose_spec.2⟩
lemma pilot_need : let Zk:=pilot P s A o b;∀ᶠ i:ℕ in atTop, |boarding P s A o b (Zk.station i)-Zk.price| *(θ)^A ≤ 1:=by
 intro F; have hx:= ((F.market.sub_const F.price).abs.mul_const ((θ)^A)); -- usage simp.F
 filter_upwards [hx.eventually (ge_mem_nhds (show |F.price-F.price| * (θ)^A <1 from (by simp)))] with x h using h
#check _root_.YM.Regis.Head.clouds
#print axioms pilot_need
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
