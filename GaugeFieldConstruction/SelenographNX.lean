import GaugeFieldConstruction.FanaticLeftVU
import GaugeFieldConstruction.BelcantoTickNX
import GaugeFieldConstruction.ProtestMosaicNX
-- sharp n collar formula.evon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
open Papal FrameP Fock.Flux Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open Lead Designs
variable (P:Spine)(Z:Lead.Clan){n n0:ℕ}
lemma orbitalSpecNX(N:ℕ):P.cFlatstockNX N Z=numeralNX N * ((Window.dimf Z:ℂ)*RomT (direction (N:ℤ)) 0 0):=by unfold cFlatstockNX; rw [show quoteP_NX _ _ =_ from polarityAccNX Z (P.flash N) rfl]
open StressFHeat YM.GaugeFieldConstruction

lemma axisCoinNX: ((Gap.eye ((2:ℝ) • YM.GaugeFieldConstruction.Wick.apex)) (Wick.blend 0 0)) = P20:=by
 rw [Invoice.curvΝ.LeftVU.powered,if_pos rfl, P20_value]
 unfold YM.Maxwell.normal; push_cast; ring -- tune
lemma nectarVN : Tendsto (fun s=> P.cFlatstockNX s Z) atTop (𝓝 (purePrice Z:ℂ)):=by
 let f(i:ℕ):ℝ:= (i:ℝ)⁻¹
 let x(i:ℕ):Cover:= direction (i:ℤ)
 have H:Tendsto f atTop (𝓝 0):= tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
 have v:∀ᶠ i:ℕ in atTop, 0<f i := (eventually_gt_atTop 0).mono fun i h => inv_pos.mpr (by exact_mod_cast h)
 let A:= YM.GaugeFieldConstruction.Wick.apex
 have hp:Tendsto (fun i:ℕ=> f i • ((2:ℝ) • off (x i))) atTop (𝓝 ((2:ℝ) • A)):=by
    refine tendsto_const_nhds.congr' ?_; filter_upwards [eventually_gt_atTop (0:ℕ)] with i g; symm; rw [smul_comm]; congr 1
    ext j
    by_cases p:j=3
    · subst j; simp [f,x,direction,Lattice.step,off,A,YM.GaugeFieldConstruction.Wick.apex]; exact inv_mul_cancel₀ (by exact_mod_cast g.ne')
    simp [f,x,direction,Lattice.step,off,A,YM.GaugeFieldConstruction.Wick.apex,p]
 have he:=gliderRomNX x H v (smul_ne_zero (by norm_num: (2:ℝ)≠0) YM.GaugeFieldConstruction.Wick.exposed) hp 0 0
 rw [show Gap.eye _ _=_ from axisCoinNX] at he
 let D:ℂ:= ↑(Window.dimf Z)/5
 have hk: D*P20=(purePrice Z:ℂ):=by rw [price_as]; change _= ↑(Window.dimf Z)* P20/5; unfold D; ring
 rw [←hk]
 simp_rw [orbitalSpecNX]
 refine (he.const_mul D).congr' ?_; filter_upwards [eventually_gt_atTop (0:ℕ)] with i q; change D*(RomT (x i) 0 0/(f i:ℂ)^3)=numeralNX i*((Window.dimf Z:ℂ)*RomT (x i) 0 0)
 unfold D f numeralNX; push_cast; simp only [div_eq_mul_inv,inv_pow,inv_inv]; ring
#print axioms nectarVN
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
