import YM.SU5.Assay.Walled
import YM.SU5.Assay.Pan
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
/-! Strong smeared field `coffee` on ManyF in a frame. Definitional junk
 if no integral receipt. Operator star applies the SAME (real) density
 and hermitian-conjugates every slot. -/
local notation "σ"=>P.slot j x
noncomputable def coffee (T:Lag)(a b:ℝ)(F:SampleDose):Y:=mixedCup volume F.val (σ T a b)
structure Brew (T:P.LagOp j x)(a b:ℝ)(F:SampleDose): Prop where
 holds: AtPan F.val (P.slot j x T a b)
 contains: ∃ C:ℝ,0≤C∧PanC F.val (P.slot j x T a b) C
lemma base_brew (D:P.Apron)(a b:ℝ)(F:SampleDose): P.Brew j x (P.base j x D) a b F:=
 ⟨fun y _=> P.base_slot_pin ..,_,norm_nonneg (D.engine P j x),fun _ _=> P.base_slot_pay ..⟩
variable {P j x}{T L:P.LagOp j x}{a b d e w:ℝ}{F:SampleDose}
lemma Walled.cost (h:Walled j F a b d)(p:(S).Credits w T)(q:w<d):PanC F.val (σ T a b) ‖T d d‖:=
 fun _ i=> (P.flown_cost ..).trans_le (Credits.pay₂ p q (h _ i).1.le (h _ i).2.le)
lemma Walled.brew (h:Walled j F a b w)(p:(S).Credits w T):P.Brew j x T a b F:=by
 obtain ⟨d,v,t⟩:=h.more
 exact ⟨fun y i=> slot_limit p (h _ i).1 (h _ i).2 tendsto_const_nhds tendsto_const_nhds tendsto_id,
   _,norm_nonneg _, t.cost p v⟩
local notation "κ"=>P.coffee j x
namespace Brew
variable (p:P.Brew j x T a b F)
include p
lemma booth : SInk volume (Pan F.val (σ T a b)):=
 AtPan.booth F.smooth.continuous F.budget p.holds p.contains.choose_spec.2
lemma drink (u:B): κ T a b F u=∫y,(F.val y:ℂ)•(σ T a b y u):= (p.booth.click u)
lemma turn (u:B): star (κ T a b F) u=∫y,(F.val y:ℂ)•(star (σ T a b y) u):=
 PanC.cupTurn F.smooth.continuous F.budget p.holds p.contains.choose_spec.2 u
lemma drink_int (u:B): Integrable (fun y=>(F.val y:ℂ)•(σ T a b y u)):=p.booth.body u
lemma turn_int (u:B): Integrable (fun y=>(F.val y:ℂ)•(star (σ T a b y) u)):=by
 exact (p.booth.back u).congr (Eventually.of_forall fun _=>congrArg (fun L:Y=>L u) (star_pan _))
lemma charge {C:ℝ}(v:PanC F.val (σ T a b) C):‖κ T a b F‖≤ (∫y, ‖F.val y‖)*C:=
 PanC.cupPrice F.smooth.continuous F.budget p.holds v
lemma nutrition {C:ℝ}(v:PanC F.val (σ T a b) C)(h:F.Normalized): ‖κ T a b F‖≤C:=by
 have he:=p.charge v; simp_rw [Real.norm_of_nonneg (h.1 _)] at he; rwa [h.2,one_mul] at he
end Brew
lemma Walled.pays (h:Walled j F a b d)(p:(S).Credits w T)(q:w<d):‖κ T a b F‖≤(∫y,‖F.val y‖)*‖T d d‖:=
 ((Walled.currency h q.le).brew p).charge (h.cost p q)
lemma Normal.pour {D:ℕ→P.Apron}(p:P.Normal j x D T)(h:Walled j F a b 0):
 BSOT (fun s=>κ (P.base j x (D s)) a b F) atTop (κ T a b F):=by
 obtain ⟨d,v,t⟩:=h.more
 obtain ⟨C,c,_,e⟩:=p.budget v
 refine PanC.cupLimit F.smooth.continuous F.budget (h.brew p.credits).holds ?_ c ?_
 · filter_upwards [e] with s u
   exact ⟨(P.base_brew ..).holds,fun _ i=>(P.flown_cost ..).trans_le (u.2 _ (t _ i).1.le _ (t _ i).2.le)⟩
 intro g i; exact p.posed (h _ i).1 (h _ i).2 tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
