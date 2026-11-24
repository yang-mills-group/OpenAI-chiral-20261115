import SatinPP.Reprise
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
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
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

local notation "H"=> P.ColorHil 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Δ"=> P.truck 3 ξ
local notation "ω"=> P.colorZero 3 ξ
variable (A:P.Apron)(eA : P.birthF 3 A.s A.F)(t:ℕ)

-- Actual width tests re-faced with their own test
def facet(b:Bool)(p:Vantage):=if b then p else opposeR 3 p
def facing(b:Bool)(F:SampleDose):=if b then F else flipDose F 3
lemma face_val(b:Bool)(p:Vantage)(F:SampleDose): (facing b F).val p= F.val (facet b p):= by cases b<;>rfl
lemma facet_y (b:Bool)(p:Vantage)(j:Axis)(h:j≠3)(d:ℝ):
 facet b (p - d • footfall j)=facet b p-d • footfall j:=by
 unfold facet;split;·rfl
 funext k;by_cases t:k=3
 · subst k; simp [opposeR,mirrorΩ,footfall,aglow,Function.update, h.symm]
 simp [opposeR,mirrorΩ,t]
lemma face_bike(b:Bool)(F:SampleDose)(j:Axis)(h:j≠3)(d:ℝ):
 facing b (bike (footfall j) F d)=bike (footfall j) (facing b F) d:=by
 have e(U V':SampleDose)(w:∀p,U.val p=V'.val p):U=V':=by
    cases U;cases V';simp;exact funext w
 apply e; intro p;rw [face_val]
 change nick _ _ _ _=nick _ _ _ _
 unfold nick;rw [face_val,face_val,facet_y b p j h]
def IsPaid(b:Bool)(q:ℝ)(F:SampleDose):Prop:=∀p∈tsupport F.val,q≤ dials b p

lemma IsPaid.front {b q F}(h:IsPaid b q F):forwardSite (facing b F) q:=by
 cases b
 · intro y u
   have p:(poseMirror 3) y∈tsupport F.val:= (show y ∈poseMirror 3 ⁻¹' tsupport F.val from flipBudget .. ▸ u)
   have v:=h _ p; change q ≤ -(opposeR 3 y 3) at v
   rwa [show opposeR 3 y 3= -y 3 from if_pos rfl, neg_neg] at v
 exact h
lemma IsPaid.wheels {b q F}(h:IsPaid b q F)(j:Axis)(p:j≠3)(d:ℝ):
 IsPaid b q (bike (footfall j) F d):= by
 unfold IsPaid
 let V':={p:Vantage| q≤dials b p}
 have hv:IsClosed V':=isClosed_le continuous_const (by cases b; exact (continuous_apply _).neg; exact continuous_apply _)
 suffices support (bike (footfall j) F d).val ⊆ V' from fun _ u => closure_minimal this hv u
 intro y e
 by_cases r:F.val y≠0; · exact h _ (subset_closure r)
 let z:=y-d • footfall j
 have l:F.val z≠0:=by
    intro t;apply e; change nick _ _ _ _=0;unfold nick;rw [r |> not_not.mp,t,sub_self,zero_div] -- tune by_cases autoneg
 have Y:=h _ (subset_closure l)
 have y₀:z 3=y 3:=by simp [z,footfall,aglow,Function.update,p.symm]
 change q≤dials b y;unfold dials at *;rwa [y₀] at Y

variable (b:Bool)(q:ℝ)(F:SampleDose)
def harvest := P.thinGridKet x t A eA (facing b F)
local notation "ν"=>P.harvest x A eA t b
lemma harvest_bike(j:Axis)(h:j≠3)(n:ℤ):
 ν (bike (footfall j) F (P.gradeZ t n)) =
 (P.gradeZ t n)⁻¹ • (ν F - Δ (P.vtile t (wheel j n)) (ν F)):=by
 unfold harvest; rw [face_bike _ _ _ h,P.cycle_grid x A eA _ _ _ h]

lemma harvest_grade {r s τ C:ℝ}(bol:Bolted C)(c:0<C)(h:0<q)
  {a:Vantage}(e:0<r)(U:IsPaid b q (pixel' a r e))
  (j:Axis)(j₀:j≠3)(d:0<s)(v:s≤τ)(u:τ≤r) :
 dist (ν (bike (footfall j) (pixel' a r e) s)) (ν (bike (footfall j) (pixel' a r e) τ)) ≤
 P.humidity t (facing b (coverall a e)) * ((C*(τ/r^2)) * ‖P.cradleH x A eA q‖):= by
 have f:0<τ:=d.trans_le v
 refine P.gridDiff x A eA t _ _ _ h (by positivity)
    (U.wheels j j₀ _).front (U.wheels j j₀ _).front (fun p=>?_ )
 simp_rw [face_val]
 exact bol a e d v u _ _ (footfall_bound j)
#print axioms harvest_grade
#print axioms harvest_bike

