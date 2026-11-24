import Merino.Cuff.Stroke
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff
-- node = gauge site o
abbrev Axle (N:Side):=Directions group N
abbrev Screw (N:Side):=Edge (Site N)
abbrev Wheel (N:Side):=Axle N →ₗ[ℝ] Axle N →ₗ[ℝ] ℝ
variable {N:Side}
abbrev slope0 {N:Side}(s:Site N→Hue): Axle N:=fun i=>s (i.1+step i.2)-s i.1
abbrev staple {N:Side}(i:Screw N)(v:Hue):Axle N:=Pi.single (M:=fun _=>Hue) i v

def selvage (a:ℝ)(o:Site N)(i:Screw N):=Real.exp (-a/2*↑(separation o i.1))
/-- Link-chart budget for a quadratic stencil. Center may be a mask post
(rather than midpoint of stencil). Axial sums will be taken wrt this center.
Strength is C times product selvage with a fixed a. -/
structure Linked (a C:ℝ)(o:Site N)(k:ℕ)(H:Wheel N):Prop where
  sell:0≤C
  symm(u v): H u v=H v u
  exacts(s:Site N→Hue)(v:Axle N): H (slope0 s) v=0
  van(i:Screw N): k < separation o i.1 → ∀ u v,H (staple i u) v=0
  earns(i j:Screw N)(u v:Hue):‖u‖≤1→‖v‖≤1→
     |H (staple i u) (staple j v)|≤ C*(selvage a o i*selvage a o j)


lemma selv_pos (a:ℝ)(o:Site N)(i:Screw N):0<selvage a o i:=Real.exp_pos _

namespace Linked
variable {o:Site N}{k:ℕ}{α:Type}[Fintype α]{F:α→Wheel N}{l:α→ℝ}{C a:ℝ}
private lemma reline (u v:Axle N): (∑ t,F t) u v=∑ t,F t u v:=by
 simp only [LinearMap.sum_apply]
lemma collate (h:∀ t,Linked a (l t) o k (F t))(v:∑ t,l t≤C):
   Linked a C o k (∑ t,F t):=by
 constructor
 · exact (sum_nonneg fun t _=>(h t).sell).trans v
 · intro u v; simp_rw [reline]; exact sum_congr rfl fun t _=> (h t).symm _ _
 · intro s v; rw [reline]; exact sum_eq_zero fun t _=> (h t).exacts _ _
 · intro i p u w; rw [reline]; exact sum_eq_zero fun t _=> (h t).van i p _ _
 intro i j u w hu hw; rw [reline]
 let L:= selvage a o i*selvage a o j
 have hm:0<L:=mul_pos (selv_pos ..) (selv_pos ..)
 apply (abs_sum_le_sum_abs ..).trans
 apply le_trans _ (mul_le_mul_of_nonneg_right v hm.le)
 rw [sum_mul]
 exact sum_le_sum fun t _=> (h t).earns i j u w hu hw
end Linked
end YM.CF.Merino.Cuff
