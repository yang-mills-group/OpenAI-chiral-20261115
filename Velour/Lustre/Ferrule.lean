import Velour.Wadding.Wick
import Velour.Lustre.Dart
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

local notation "ρ'"=> P.tableau j x 0

def lyreCLM:(ℋ).Op →L[ℂ] (𝓗).Op:=
 ({toFun:=ρ'
   map_add':=by
     intro A B; ext1 z
     rw [P.lyre,_root_.add_apply,map_add,_root_.add_apply,P.lyre,P.lyre]; try rfl --?
   map_smul':= by
     intro c A; ext1 z
     rw [P.lyre,_root_.smul_apply,map_smul,_root_.smul_apply,P.lyre]; try rfl }: (ℋ).Op →ₗ[ℂ] (𝓗).Op).mkContinuous 1
    fun a=> (P.tableau_pay j x _ _).trans (by simp)


local notation "E₀"=> (Σ₀).E
local notation "E₁"=> (Σ₁).E
set_option synthInstance.maxHeartbeats 54000 in
lemma lyre_train (X:(ℋ).Op)(d:ℝ≥0)(p:0<d):
 ρ' ((Σ₀).train d X)=(Σ₁).train d (ρ' X) := by
 let A:= (P.lyreCLM j x).restrictScalars ℝ
 have e : A (deriv (Σ₀).F (d:ℝ) * X * E₀ d)=deriv (Σ₁).F (d:ℝ) * ρ' X * E₁ d:=by
    refine (A.hasFDerivAt.comp_hasDerivAt _ ((((Σ₀).dart _ p).mul_const X).mul_const _)).unique ?_
    refine ((((Σ₁).dart _ p).mul_const _).mul_const _).congr_of_eventuallyEq (Eventually.of_forall ?_)
    intro u; exact P.lyre_heat j x u.toNNReal d X


 have h : A (E₀ d * X * deriv (Σ₀).F (d:ℝ))= E₁ d* ρ' X * deriv (Σ₁).F (d:ℝ):=by
   refine (A.hasFDerivAt.comp_hasDerivAt _ (((Σ₀).dart _ p).const_mul _)).unique ?_
   refine (((Σ₁).dart _ p).const_mul _).congr_of_eventuallyEq (Eventually.of_forall ?_)
   intro u; exact P.lyre_heat j x d u.toNNReal X
 change A (_-_)=_ - _
 rw [map_sub,e,h]


variable {P j x}
open Boundary Probe
namespace Veloured
local notation "C"=> (Σ₁).rasp
variable {T:ℕ→P.Apron}(v:P.Veloured j x T) (c:ℂ)
local notation "Y@" => fun t:ℝ=> c • v.printOp t
local notation "pt" n:max t:max => ((piping (Σ₀))^[n] (Y@)) t

lemma baling (n:ℕ) (t:ℝ)(p:0<t)(f:Test4):
 C (ρ' (pt n t)) f= C (ρ' ((Y@) t)) (bead j n f):=by
 induction n generalizing t f with
 | zero=>rfl
 | succ n ih=>
   let d:=t/4
   let u:=d.toNNReal
   have h:0<d:=by positivity
   have y:0<u:=Real.toNNReal_pos.mpr h
   let r:= t-t/4
   have q:0<r:=by dsimp [r]; linarith
   rw [Function.iterate_succ_apply',
       show piping (Σ₀) (((piping (Σ₀))^[n] (Y@))) t= (Σ₀).train u (pt n r) from by
         unfold OS.Semigroup.train
         rw [show (u:ℝ)=d from Real.coe_toNNReal d h.le];rfl,P.lyre_train _ _ _ _ y,
         (Σ₁).rasp_train _ y,
         (Σ₁).rasp_more_right _ _ (fun b=>(Σ₁).unit_heat b u),
         (Σ₁).rasp_more_left _ _ (fun b=>(Σ₁).unit_heat b u),ih r q]


   have w:E₁ u * (ρ' ((Y@) r)) * E₁ u=ρ' ((Y@) t):=by
     have e:t-r=d:=by dsimp [d,r]; ring
     rw [←P.lyre_heat]
     dsimp only
     conv_rhs=>rw [v.print_wrap q (show r≤t by dsimp [r];linarith),e, pad_val]
     rw [mul_smul_comm,smul_mul_assoc]
   rw [←w,
         (Σ₁).rasp_more_right _ _ (fun b=>(Σ₁).unit_heat b u),
         (Σ₁).rasp_more_left _ _ (fun b=>(Σ₁).unit_heat b u)]
   rfl


lemma fringed_combs (W:Prism)(t:ℝ≥0)(p:0<t)(f:Test4):
 C (ρ' (trims (Σ₀) W (Y@) t)) f=C (v.adorning t) (fringed j W c f):=by
 let L:=P.lyreCLM j x
 change (Σ₁).raspOp f (L (∑ i∈ W.support, W i • (pt (i+1) (t:ℝ))))=_
 rw [map_sum,map_sum,fringed, map_sum]
 refine Finset.sum_congr rfl fun i _=>?_
 rw [map_smul,map_smul,map_smul,mul_comm c, mul_smul]
 change W i • C (ρ' _) f=_
 rw [v.baling c _ t p]
 change W i • C (L (c • _)) _= W i • c • C (L _) _
 rw [map_smul,(Σ₁).rasp_lever];rfl

#print axioms fringed_combs
end Veloured

