import Velour.Wadding.Lining
import Velour.Organza.Larva
import Velour.Organza.Sprinkles
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

def Apron.knock (Q:P.Apron)(l r:ℝ):(𝓗).Op:=
 P.tableau j x 0 (Q.dye P j x l r)

local notation "⊥₀"=> P.tableau j x 0
variable {P j x}

namespace Veloured
variable {T:ℕ→P.Apron}(h:P.Veloured j x T) {d:ℝ} {a b:ℝ≥0}
lemma icing (p:0<d)(q:d≤ (a:ℝ))(r:d≤ (b:ℝ)):
   (Σ₁).insulate h.adorning a b=⊥₀ ((Σ₀).pad (a-d) (b-d) (h.printOp d)):=by
 let c:=min a b
 change (Σ₁).E (a-c) * _ * _=_
 have x1:c≤a:=min_le_left ..
 have x2:c≤b:=min_le_right ..
 have u:d≤(c:ℝ):=le_min q r
 unfold adorning
 rw [←P.lyre_heat,h.print_wrap p u]

 rw [←(Σ₀).pad_twice (a:=(c:ℝ)-d) (b:=(c:ℝ)-d)
     (sub_nonneg.mpr u) (sub_nonneg.mpr u) (g:=sub_le_sub_right (show (c:ℝ)≤a from x1) d)
     (h:=sub_le_sub_right (show (c:ℝ)≤b from x2) d)]
 rw [sub_sub_sub_cancel_right,sub_sub_sub_cancel_right,pad_val (a:= (a:ℝ)-c),
     ←NNReal.coe_sub x1, ←NNReal.coe_sub x2,Real.toNNReal_coe,Real.toNNReal_coe]

lemma squeeze {L R:ℕ→ℝ}(p:0<a)(q:0<b)
   (g:Tendsto L atTop (𝓝 (a:ℝ))) (w:Tendsto R atTop (𝓝 (b:ℝ))):
 Gleams 𝓗 (fun i=>(T i).knock P j x (L i) (R i)) ((Σ₁).insulate h.adorning a b):=by
 let d:=min (a:ℝ) (b:ℝ)/2
 have he:0 < min (a:ℝ) (b:ℝ):=lt_min p q
 have hd:0<d:=half_pos he
 have r₁:d<a:=(half_lt_self he).trans_le (min_le_left ..)
 have r₂:d<b:=(half_lt_self he).trans_le (min_le_right ..)
 rw [h.icing hd r₁.le r₂.le]
 refine P.lyre_glow j x (((h.printed hd).pad (Σ₀)
     (g.sub_const d) (w.sub_const d)).agree ?_)
 filter_upwards [g.eventually (lt_mem_nhds r₁),w.eventually (lt_mem_nhds r₂),
   h.thin.eventually (gt_mem_nhds hd)] with i l t e
 exact (T i).dye_twice P j x (show (T i).realWidth P j<d from e).le
   (show (T i).realWidth P j<d from e).le (show d<L i from l).le (show d<R i from t).le

def socket:(Σ₁).Detector:= (Σ₁).seated h.cash
lemma delivery : (Σ₁).Instates h.adorning h.socket:= (Σ₁).seated_in _

open Boundary Probe
lemma enlighten {L R:ℕ→ℝ}(p:0<a)(q:0<b)
   (g:Tendsto L atTop (𝓝 (a:ℝ))) (w:Tendsto R atTop (𝓝 (b:ℝ)))
   {u:ℕ→Test4}{f:Test4}(r:Tendsto u atTop (𝓝 f)) :
 (Σ₁).Surges atTop (fun i=>(Σ₁).labelled ((T i).knock P j x (L i) (R i)) (u i))
   ((Σ₁).heatL a*h.socket f*(Σ₁).heatL b):=by
 rw [←h.delivery.either_pad p q f]
 exact (Σ₁).surges_width (h.squeeze p q g w) r

#print axioms enlighten
end Veloured
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

