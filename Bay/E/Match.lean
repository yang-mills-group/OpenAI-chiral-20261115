import Bay.E.Cutting

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted D StressExchange

open Buffered.Afterglow.Tower SlabMark
open Girt
open scoped YM.CF.Buffered

local notation "Ways" => Buffered.Family

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Journey Tower Tapestry VacuumSelection
local notation "VΩ"=>VacuumSelection.Spine
set_option maxRecDepth 5000


variable {w:Berth}{z:Cover}{F:w.First}
def orderMark (N:Side):Stencil N→ₗ[ℂ] Mark N:=⟨⟨toMark,fun _ _=>rfl⟩,fun _ _=>rfl⟩
variable {t d L:ℝ}{b:ℕ}{i j:Axis}
local notation "T"=>sticker w z F b
local notation "K"=>w.P.calibration
local notation "o"=>wrap w.side z

lemma tickle : SlabMark.gaugeT K 1=(tabW w.P:ℤ)∧ SlabMark.gaugeT K (-1)=-(tabW w.P:ℤ):=by
 constructor <;> unfold gaugeT Heat.gaugeShift tabW
 · change _=(↑(8*w.P.calibration.B.val:ℕ):ℤ)
   push_cast;ring
 change _= -(↑(8*w.P.calibration.B.val:ℕ):ℤ)
 push_cast;ring

lemma thickWing (p:Button w F L t d z b):
 instrument w (jest K w.Q T i) = orderMark _ (w.J130 o F i):=by
  rw[jest,Berth.J130,map_smul,map_smul,p.atJ];rfl
lemma thock(p:Button w F L t d z b):
 instrument w (zest K w.Q w.th T)=orderMark _ (w.Z130 o F):=by
  rw[zest,Berth.Z130,map_smul,map_smul,p.atZ];rfl

lemma thickSide(u:ℤ)(p:Button w F L t d z b):
 instrument w (swerve K w.Q T i j u) =
   orderMark _ (w.Jpose o F j (o+wrap _ ((SlabMark.gaugeT K u) • Lattice.step i))):=by
 rw[swerve,relocate,jest,Berth.Jpose, chime_scale,map_smul,map_smul,p.oriented];rfl

lemma matchesWing (p:Button w F L t d z b):
 instrument w (yieldY K w.Q w.th T) = orderMark _ (w.Y128 o F (tabW w.P)):=by
 rw[Berth.splitsY,yieldY,map_add,map_add,thock p,map_smul,map_smul,map_smul,map_sum,map_sum]
 simp_rw[map_sub,thickSide _ p,(tickle (w:=w)).1,(tickle (w:=w)).2, neg_smul,map_neg,map_zsmul,
    wrap_step,natCast_zsmul, gapPlus, sub_eq_add_neg]
end YM.CF.Bay.Silk
