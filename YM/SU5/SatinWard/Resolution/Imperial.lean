import YM.SU5.SatinWard.Resolution.MaySong
import YM.SU5.SatinWard.Resolution.RunLens
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal

open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
open Motet SoulField Verdance Mezzo SatinWard.Installment
namespace Imperial
/-! partner due in a smaller-step gauge arithmetic. (Code Fin8 at fixed axis, remainder
 still in the same I' set.) -/
variable (z:ℕ) (q:Cover)(p:ResidualPermit q) (k:Axis)
def color (t:Fin 8): ℤ:= 2*t.val-7
def castY(u:Fin 8)(b:Bool): Fin 8:= if b then u+1 else u-1
local notation "v◀" i:max b:max=> castY i b
def fareQ (b:Bool): ℤ:=if b then 2 else -2
def loadY (i:Fin 8)(b:Bool): ℤ:= (color i +fareQ b-color (castY i b))/16
lemma fare_ar (j:Fin 8)(b:Bool) : color j+ fareQ b=color (castY j b)+16*loadY j b ∧ |loadY j b| ≤1:=by revert b j; decide +kernel
def CLine (j: Fin 8): Cover:= Function.update q k (color j)
local notation "So" t:max=> CLine q k t
include p
lemma lifeC (j:Fin 8): ResidualPermit (So j):=by
 have e(t:Axis)(w:t≠k):(So j) t=q t:= Function.update_of_ne w _ _; have w: (So j) k = color j:= Function.update_self ..; refine ⟨fun t=>?_,fun t=>?_⟩
 · by_cases h:t=k; · subst t; rw [w]; exact ⟨↑j.val-4,by unfold color; omega⟩
   rw [e t h]; exact p.odd t
 by_cases h:t=k; · subst t; rw [w]; unfold color; omega
 rw [e t h]; exact p.cost t
lemma named : ∃ j:Fin 8,CLine q k j=q:=by
 have g:=p.cost k; obtain ⟨i,t⟩:=p.odd k; let j:= (i+4).toNat; let j': Fin 8:= ⟨j, by unfold j; omega⟩; refine ⟨j',?_⟩; funext s; by_cases w:s=k; · subst s; rw [CLine,Function.update_self,t,color]; unfold j' j; simp only; omega
 exact Function.update_of_ne w _ _
omit p
local notation "d₀"=> P.par.block.val
lemma simple3 : d₀ ≤ P.jump128:=by unfold jump128; omega
variable (t:Fin 8)(b:Bool)
local notation "α" => homeTag P (So t)
local notation "A'" b:max=> homeTag P (So (v◀ t b))
-- Need actual soil: this clock uses singleStep macroPeriod/h. equality offsets.
def liner (t:Fin 8)(b:Bool): Cover:=loadY t b • step k
local notation "LL" b:max=> liner k t b
local notation "stepT" b:max=>pmZ P.par.block.val k b
local notation "Vg" v:max=> P.vtile v
lemma geo_tickPay : α+ (2:ℕ) • (stepT b)=A' b+P.sidesPerTick • liner k t b:=by
 funext i; change d₀ • (So t) i + (2:ℕ) • ((stepT b) i)=d₀ • (So (v◀ t b)) i+ P.sidesPerTick • ((LL b) i)
 unfold CLine; rw [sidesTick_eq]
 by_cases h:i=k
 · subst i; simp only [Function.update_self]; have x:= (fare_ar t b).1
   unfold liner pmZ; cases b <;> simp [fareQ, castY, nsmul_eq_mul,zsmul_eq_mul,step] at * <;> nlinarith only [congrArg ((↑(P.par.R.L.val):ℤ)^P.par.b*·) x]
 cases b <;> simp [liner, step, pmZ, h, Ne.symm h]
variable (M:P.par.R.L.val%16=1)
include p
local notation "pin" h:max=> tauprint P M h -- need M first
lemma balance : pin (lifeC q p k t) + pmZ P.par.block.val k b = pin (lifeC q p k (castY t b)) + P.jump128 • LL b:=by
 apply Satin.nodeC_inj; rw [show ∀ x y:Cover,nodeC (x+y)=nodeC x +2 • y from fun x y=>by unfold nodeC; rw [smul_add]; abel,relation_core,show nodeC (pin (lifeC q p k t))=α from (nodeHome P M _ (lifeC q p k t)).choose_spec, show nodeC (pin (lifeC q p k (castY t b)))=A' b from (nodeHome P M _ (lifeC q p k (castY t b))).choose_spec]; exact geo_tickPay P q k t b
omit p

lemma geo_line (v:ℕ)(i:Axis): |P.tock v (liner k t b i)| ≤ P.macroStep v:=by
 unfold liner; have x:= abs_le.mp (fare_ar t b).2
 rw [P.tock_price,abs_mul,abs_of_pos (P.macroStep_pos v)]; apply le_trans (mul_le_mul_of_nonneg_right ?_ (P.macroStep_pos _).le) (one_mul _).le; by_cases e:i=k; · subst i; simpa [step,zsmul_eq_mul] using (show |((loadY t b:ℤ):ℝ)|≤1 from (by exact_mod_cast (fare_ar t b).2))
 simp [step,Ne.symm e]
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
