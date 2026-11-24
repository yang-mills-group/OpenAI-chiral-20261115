import YM.SU5.Assay.Garden
import YM.SU5.Assay.Espresso
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
open TopologicalSpace
/-! LF operator-valued distributions (real tests) on open lag slabs. The
 limiting fields for **any** Kiln are of this form. Even stage operators
 after fine-grid passage with early width clips are uniformly controlled.
 Not claiming LF continuity of hypothetical prices on coalescing walls. -/
variable {j P x}{T:P.LagOp j x}{Z:Row}{a b d w:ℝ}
local notation "κ"=>P.coffee j x
local notation "β"=>P.base j x
local notation "σ"=>P.slot j x
-- price whole gallery via a chamber cap
lemma gallery {I:Type*}{g:I→P.LagOp j x}
 (h:∀i F,tsupport F.val ⊆ Z→P.Brew j x (g i) a b F)
 (p:∀ Q:Compacts Vantage,(Q:Set Vantage)⊆Z→ ∃C:ℝ,0≤C∧∀i,∀y∈Q,‖σ (g i) a b y‖≤C):
 SeedBook Z (fun i=>κ (g i) a b):= by
 constructor
 · intro i f t l n m e
   rw [←Complex.coe_smul n,←Complex.coe_smul m]
   exact coffee_linear n m (by intro y;change ↑(l y)=((n:ℂ)*(f y)+(m:ℂ)*(t y));rw [e];push_cast;rfl)
       (h _ _ f.tsupport_subset) (h _ _ t.tsupport_subset) (h _ _ l.tsupport_subset)
 · intro Q u; obtain ⟨c,n,v⟩:=p Q u; obtain ⟨y,z,t⟩:=P.dose_price Q
   refine ⟨c*y,mul_nonneg n z,fun i F q M m r=>?_⟩
   refine ((h i F (q.trans u)).charge (fun j t=>v i _ (q t))).trans ?_
   rw [mul_assoc,mul_comm c]; exact mul_le_mul_of_nonneg_right (t _ q _ m r) n
lemma botanical (h:(S).Credits w T) : SeedBook (litRow j a b w) (fun _:Unit=> κ T a b):=by
 refine gallery (fun _ F p=>Walled.brew (fun _ t=>p t) h) ?_
 intro Q u; obtain ⟨y,z,t⟩:=gainRow Q u
 exact ⟨_,norm_nonneg (T y y),fun i p q=>(P.flown_cost ..).trans_le (Credits.pay₂ h z (t q).1.le (t q).2.le)⟩
variable (a b)
def sachet (h:(S).Credits w T):Crop (litRow j a b w) →L[ℝ] Y := (botanical h).per ()
lemma sachet_lf (h:(S).Credits w T)(f:Crop (litRow j a b w)):sachet a b h f=κ T a b (extract f):=rfl
lemma Walled.sachet {F:SampleDose} (q:Walled j F a b w)(h:(S).Credits w T):
 sachet a b h (germinate q.row)=κ T a b F:=rfl

variable {D:ℕ→P.Apron}
-- helper bound including early stage terms
lemma little_book {I:Type*}{f:ℕ→I→ℝ} (a:∀s:ℕ,∃c:ℝ,∀i,f s i≤c) (z:∃c:ℝ,∀ᶠ s in atTop, ∀i,f s i≤c):
 ∃ c:ℝ,0≤c∧∀s i,f s i≤c:=by
 obtain ⟨c,v⟩:=z;obtain ⟨N,h⟩:=eventually_atTop.mp v
 obtain ⟨r,t⟩:=(finite_Iio N).image (fun s=>(a s).choose) |>.bddAbove
 refine ⟨max (max c r) 0,le_max_right ..,fun s i=>le_max_of_le_left ?_⟩
 rcases lt_or_ge s N with u|u
 · exact le_max_of_le_right (((a s).choose_spec i).trans (t (mem_image_of_mem _ u)))
 exact le_max_of_le_left (h _ u i)
lemma Normal.all_stage (h:P.Normal j x D T) : SeedBook (litRow j a b 0) (fun s=>κ (β (D s)) a b):=by
 refine gallery (fun i F _=> P.base_brew ..) ?_
 intro Q u
 obtain ⟨r,k,y⟩:=gainRow Q u
 obtain ⟨c,n,_,v⟩:=h.budget k
 obtain ⟨m,p,t⟩:= little_book (f:=fun (s:ℕ)(y:{y:Vantage//y∈Q})=>‖σ (β (D s)) a b y‖)
    (fun s=>⟨_,fun y=>P.base_slot_pay ..⟩)
    ⟨_,v.mono fun s h i=>(P.flown_cost ..).trans_le (h.2 _ (y i.2).1.le _ (y i.2).2.le)⟩
 exact ⟨m,p,fun s y u=>t s ⟨_,u⟩⟩
-- varying LF input and width
lemma Normal.rotate {I:Type*}{l:Filter I}{u:I→Crop (litRow j a b 0)}{v:Crop (litRow j a b 0)}
 {s:I→ℕ} (h:P.Normal j x D T)(p:Tendsto s l atTop)(t:Tendsto u l (𝓝 v)) :
 BSOT (fun i=>κ (β (D (s i))) a b (extract (u i))) l (κ T a b (extract v)):=
 ((h.pour (extract_walled v)).visit p).squeeze' ((h.all_stage a b).vary t s) (Eventually.of_forall fun _=>le_rfl)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
