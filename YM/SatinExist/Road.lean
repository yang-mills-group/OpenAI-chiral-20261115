import YM.SatinExist.ShiftE
import YM.SatinExist.Turret
import YM.SatinExist.Stile
import YM.SatinExist.Shield
import YM.SatinExist.Cameo
import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
import YM.SatinExist.Glacis
import SatinThinSegno

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- specialize now to OP height desk
open Aria Casting MacroGrid
variable (x:P.Spectrum0 3)(s:ℕ)(k:List Axis)
local notation "P₀"=>P.rootSpace f s k
local notation "q" v:max=> (P.basePlay x f v).pivot P k
local notation "X_" v:max=> P.clockPlate s v (P.rootSpace f s k)
local notation "Z"=> (P.turtle j s f k)
noncomputable abbrev fixedStar (j:Axis)(f s:ℕ)(k:List Axis) : Vantage:= fun i=> P.pinTime i f s k
-- traveler. Search orientation precursor possibly different all-axes? rootSpace f s l independent j.
variable (u:f ≤ s)(p:Odd P.par.R.L.val)
include u p x
private lemma shadow_widthII (v:ℕ) : |(( (pivotQ (P.granule (P.megaK f v)) k) j):ℝ)|≤ (P.echoFoot:ℝ):=by
 obtain h|h:= pivot_alone (P.granule (P.megaK f v)) k j <;> rw [h]; swap; · rw [Int.cast_neg, abs_neg]; exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
 exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
lemma safeRad : ∃ z:ℕ → Cover,Tendsto (fun v=> P.laysM (P.vtile v (z v))) atTop (𝓝 (P.fixedStar j f s k)) ∧
    ∀ᶠ v:ℕ in atTop,
    P.chartAll (z v) ((q v).full P v)=P.centeredQ x v (P.clockPlate s v (P.rootSpace f s k)) ∧
    v ≥ s ∧ (q v).s ≤ v ∧
    0 < Apron.time_panel P j (P.laysM (P.vtile v (z v))) (q v) ∧ Apron.time_edge P j (P.laysM (P.vtile v (z v))) (q v)<(Z:ℝ):=by
 choose! z u₁ using fun v (h:s ≤ v)=> P.charge_race f s v u h k p
 let g (v:ℕ):= P.laysM (P.vtile v (z v)); let N':=(P.fixedStar j f s k)
 have he: Tendsto g atTop (𝓝 N'):=by
    apply tendsto_pi_nhds.mpr; intro i
    let f₂(v:ℕ):= (((pivotQ (P.granule (P.megaK f v)) k) i):ℝ)*P.macroStep v/P.sidesPerTick
    have ht:Tendsto (fun v=> (P.echoFoot:ℝ)*P.macroStep v/P.sidesPerTick) atTop (𝓝 0):=by simpa only [mul_zero,zero_div] using ((P.macroStep_zero.const_mul (P.echoFoot:ℝ)).div_const (P.sidesPerTick:ℝ))
    have hp:Tendsto f₂ atTop (𝓝 0):=by
       apply squeeze_zero_norm' _ ht; apply Eventually.of_forall; intro v; rw [Real.norm_eq_abs]; unfold f₂; rw [abs_div, abs_mul, abs_of_pos (P.macroStep_pos _), abs_of_pos (show 0< (P.sidesPerTick:ℝ) from Nat.cast_pos.mpr P.sides_pos)]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (P.shadow_widthII i x s k u p v) (P.macroStep_pos _|>.le)) (Nat.cast_nonneg _)
    have hf:Tendsto (fun v=> N' i - f₂ v) atTop (𝓝 (N' i)):=by simpa only [sub_zero] using tendsto_const_nhds.sub hp
    exact hf.congr' ((eventually_ge_atTop s).mono fun v d=> (P.quote_height i k d (z _) (u₁ _ d)).symm)
 have hm(v:ℕ): (q v).realWidth P j= P.roomy*P.macroStep v:=by rw [Apron.pivot_w,P.play_width]
 have hT:Tendsto (fun v=> (q v).realWidth P j) atTop (𝓝 0):=by simp_rw [hm]; simpa only [mul_zero] using P.macroStep_zero.const_mul (P.roomy:ℝ)
 have Zg:= (tendsto_pi_nhds.mp he) j
 obtain ⟨e₀,e₁⟩:= prime_fit P j s f k
 refine ⟨z,he,?_⟩
 have hk:0 < N' j-0:=by rw [sub_zero]; exact e₀
 have hh: N' j+0 < (Z:ℝ):=by rw [add_zero]; exact e₁
 filter_upwards [(Zg.add hT).eventually (gt_mem_nhds hh), (Zg.sub hT).eventually (lt_mem_nhds hk),eventually_ge_atTop s] with v hv w y
 refine ⟨(P.pivot_Fax x k _).trans ?_,y, ((P.basePlay x f v).pivot_s P k|>.le),w,hv⟩; rw [u₁ v y]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
