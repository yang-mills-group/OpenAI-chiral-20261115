import YM.SU5.Assay.Kiln
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
local notation "σ"=>P.rawSlot j x
local notation "β"=>P.base j x
local notation "κ"=>P.coffee j x
local notation "𝔤"=>P.Grips j x
local notation "ξ"=>P.prepared
local notation "μ"=>P.singleState j
local notation "⟪" T "⟫"=>inner ℂ Ω ((T:Y) Ω)
/-!
 Vacuum emissions of span prices. No claiming a vector at center;
 in use lag a measured from that center strictly exceeds threshold,
 even though formulas are total.
-/
def pharos (T:Lag)(a:ℝ): B:= T a a Ω
local notation "η"=>P.pharos j x
local notation "τ"=>P.otherLag j x
local notation "ρ"=>P.slot j x
variable {P j x}{T:P.LagOp j x}{a b d e w:ℝ}
lemma other_credits (h:(S).Credits w T): (S).Credits w (τ T):= Credits.dagger h
lemma other_other (P:Spine)(j:Axis)(x:P.Spectrum0 j)(T:P.LagOp j x):P.otherLag j x (P.otherLag j x T)=T:= by
 funext a b;exact star_star _
lemma pharos_right (h:(S).Credits w T)(p:w<a)(q:w<b): T a b Ω=η T a:=by
 have u : ∀r,min a b ≤ r → T a r Ω=T a (min a b) Ω:=by
   intro r t
   rw [h p (lt_min p q) le_rfl t]
   unfold sand; rw [sub_self,wax_zero,one_mul]; change T a _ (ω _ Ω)=_
   unfold wax; rw [P.heaven_hot]
 exact (u _ (min_le_right ..)).trans (u _ (min_le_left ..)).symm
lemma pharos_step (h:(S).Credits w T)(p:w<a)(t:a ≤ d):η T d=ω (d-a) (η T a):=by
 unfold pharos; rw [h p p t t]
 change ω _ (T a a (ω _ Ω))=_;unfold wax;rw [P.heaven_hot]
lemma pharos_wax (h:(S).Credits w T)(p:w<a)(t:0 ≤ d): ω d (η T a)=η T (d+a):=by
 rw [pharos_step h p (le_add_of_nonneg_left t),add_sub_cancel_right]
lemma pharos_pay (h:(S).Credits w T)(p:w<a)(t:a ≤ d): ‖η T d‖ ≤ ‖η T a‖:=by
 rw [pharos_step h p t]
 exact ((ω _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) ((S).wax_pay ..))
lemma pharos_cont (h:(S).Credits w T)(p:w<a):ContinuousAt (η T) a:=
 (Credits.slide h p p tendsto_id tendsto_id).showAt Ω
lemma pharos_pose(y:Vantage)(h:(S).Credits w T)(p:w<y j-a)(t:w<b-y j):ρ T a b y Ω=W y (η T (y j-a)):=by
 unfold slot flown; rw [P.cart_vac,pharos_right h p t]
lemma pharos_star_pose(y:Vantage)(h:(S).Credits w T)(p:w<y j-a)(t:w<b-y j): star (ρ T a b y) Ω=W y (η (τ T) (b-y j)):=by
 unfold slot flown; rw [P.locate_star,P.cart_vac]
 exact congrArg (W y) (pharos_right (other_credits h) t p)

lemma Normal.emits {D:ℕ→P.Apron}(p:P.Normal j x D T)(h:0<a){f:ℕ→ℝ}(v:Tendsto f atTop (𝓝 a)):
 Tendsto (fun s=>η (β (D s)) (f s)) atTop (𝓝 (η T a)):= (p.showOn h h v v).showAt Ω

variable (P j x)
def thrust (T:Lag)(F:SampleDose)(a:ℝ): B:= ∫ y,(F.val y:ℂ)•(W y (η T (y j-a)))
/-- **T here is already earlier-style.** Use reversed emission. -/
def retort (T:Lag)(F:SampleDose)(b:ℝ): B:= ∫ y,(F.val y:ℂ)•(W y (η (τ T) (b-y j)))
local notation "Φ"=>P.thrust j x
local notation "Ψ"=>P.retort j x
lemma retort_coeff (T:Lag)(F:SampleDose)(b:ℝ):Ψ (τ T) F b=∫y,(F.val y:ℂ)•(W y (η T (b-y j))):=by
 unfold retort; rw [P.other_other]
variable {P j x}{F:SampleDose}
private lemma pharos_pan {G L:Vantage→(P.ManyF j x)}(h:∀y∈tsupport F.val,G y=L y):
 (fun y=>(F.val y:ℂ)•G y)=fun y=>(F.val y:ℂ)•L y:=by
 funext y;by_cases u:y∈tsupport F.val; · rw [h _ u]
 rw [image_eq_zero_of_notMem_tsupport u,Complex.ofReal_zero,zero_smul,zero_smul]
lemma thrust_launch (h:(S).Credits w T)(u:Walled j F a b w):
 Integrable (fun y=>(F.val y:ℂ)•(W y (η T (y j-a))))∧ κ T a b F Ω=Φ T F a:=by
 unfold thrust
 rw [←pharos_pan (fun y e => pharos_pose y h (u y e).1 (u y e).2)]
 exact ⟨(u.brew h).drink_int _, (u.brew h).drink _⟩
lemma retort_land (h:(S).Credits w T)(u:Walled j F a b w):
 Integrable (fun y=>(F.val y:ℂ)•(W y (η (τ T) (b-y j))))∧ star (κ T a b F) Ω=Ψ T F b:=by
 unfold retort
 rw [←pharos_pan (fun y e=>pharos_star_pose y h (u y e).1 (u y e).2)]
 exact ⟨(u.brew h).turn_int _,(u.brew h).turn _⟩
lemma thrust_retort (h:(S).Credits w T)(u:Walled j F a b w): Ψ T F b=Φ (τ T) (flipDose F j) (-b):=by
 rw [←(thrust_launch (other_credits h) u.flip).2,←coffee_dagger h u, (retort_land h u).2]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
