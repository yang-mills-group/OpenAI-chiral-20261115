import Gingham.Binding
import YM.SU5.Six.PressSmear
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

open Heat
variable (x : P.Spectrum0 3)
variable {I:Type*} [Finite I]
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Λ"=> P.par
local notation "Q"=> P.history
local notation "M"=> timeMesh P.par
local notation "Θ"=> P.reflectTest 3
local notation "T"=> P.shifts 3
local notation "τ"=> P.singleState 3
open Set Diary

variable (s n t:ℕ) 
lemma grows_bell : Tendsto (fun n:ℕ=>bell M s n) atTop atTop:=
   tendsto_natCast_atTop_atTop.atTop_mul_const (show 0<((mill M s):ℝ) from mill_pos M s)
   -- defeq cast twice
lemma vox_asked (v:P.Vox 3 t): P.asked_at t (P.voxTest 3 t v) {u:Vantage | 0≤u (3:Axis)} :=by
 obtain ⟨h,_⟩ := (purpose_ok ..).1 v.property
 obtain ⟨S,u,p⟩ := (h : ∃ S : Finset Cover, InTest K true S false v.val ∧
    Tower.region 3 (meshface («Λ»:=P.par) 0 t) (K).ℓ S)
 rw [area0] at p
 refine ⟨S,u,?_⟩
 rintro i ⟨z,h,a⟩
 specialize p z h
 specialize a (3:Axis)
 change |(precisionAt Λ t)*(2*i 3)-↑(z 3)|≤ (K).ℓ at a
 have hz:((K).ℓ:ℝ) ≤(z 3:ℝ):=by exact_mod_cast show ((K).ℓ:ℤ) ≤ z 3 from (zero_add _).symm.trans_le p
 have H₂:0<precisionAt Λ t:=positiveScale Λ t
 change 0≤ i 3
 by_contra! H₃
 have h₄:=mul_neg_of_pos_of_neg H₂ (show 2*i 3<0 by linarith)
 linarith [(abs_le.mp a).1]


lemma wheel_budget (R:ℝ)(p:s≤t)(hn:R≤bell M s n)
    (v:P.Vox 3 t): 
   P.asked_at t (chargeB P s n t v) {u:Vantage| R≤u 3}∧
   P.asked_at t (Θ (chargeB P s n t v)) {u:Vantage|u 3 ≤ -R}:=by
 have h:P.asked_at t (chargeB P s n t v) {u:Vantage|R≤u 3}:=by
   obtain ⟨S,h,hS⟩:=vox_asked P t v
   refine ⟨_,P.shifts_support 3 (gapL P s n t) S h,?_⟩
   intro i h
   have a:=hS (P.step_back_pin t S 3 (gapL P s n t) h)
   change 0≤(i 3-Pi.single («M»:=fun _:Axis=>ℝ) 3 (bell M t (castor M s t n)) (3:Axis)) at a
   rw [refineZ M _ _ p,Pi.single_eq_same] at a
   change R ≤ i 3
   linarith
 refine ⟨h,?_⟩
 obtain ⟨S,h,hS⟩:=h
 refine ⟨_,P.canFlip _ _ h,?_⟩
 intro i hi
 have a:= hS (P.mirror_back_pin t S 3 hi)
 change i 3≤ -R
 simpa [mem_setOf_eq,mirrorΩ,le_neg] using a

structure Lodgment (P:Spine)(t:ℕ)(R:ℝ)(u:P.Test) : Prop where
 owner: P.asked_at t u {q:Vantage|R≤q 3}
 reflect: P.asked_at t (P.reflectTest 3 u) {q:Vantage|q 3 ≤ -R}

lemma after_knives (s:ℕ)(F:I→P.Test){U:Set (I→ℂ)} (op:IsOpen U)
    (e:(fun i=>τ s x (F i))∈U)(R:ℝ):
    ∃ (t:ℕ) (_:s≤t) (u:P.Test), Lodgment P t R u ∧
     ∀ᶠ j in atTop, Ferry P.run t (irr P j) (uvv P j) ∧
      rawE P t j (magnet P u 1)≠0 ∧
       (fun i=>coin P s t u (rawE P t j) (F i))∈U :=by
 obtain ⟨n,r,t,p,v,h⟩:= ((grows_bell P s|>.eventually (eventually_ge_atTop R)).and
     (ratio_sharp P x s F op e)).exists
 obtain ⟨a,b⟩:= wheel_budget P s n t R p r v
 exact ⟨t,p,_,⟨a,b⟩,h⟩
