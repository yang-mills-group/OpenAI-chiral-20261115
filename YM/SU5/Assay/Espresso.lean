import YM.SU5.Assay.Coffee
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
/-!
 Compatibility, mirror and displacement of smeared operators. Input a
 lag-funded family; walls must strictly clear supports by more than the
 threshold.
-/
local notation "κ"=> P.coffee j x
local notation "σ"=> P.slot j x
local notation "ℛ"=> P.locate j x
variable {P j x}{F G L:SampleDose}{a b c d w:ℝ}{T:P.LagOp j x}
lemma coffee_linear (u v:ℂ)(e:∀y,(L.val y:ℂ)= u*(F.val y)+v*(G.val y))
  (f:P.Brew j x T a b F)(g:P.Brew j x T a b G)(p:P.Brew j x T a b L):
 κ T a b L=u•κ T a b F+ v•κ T a b G:=by
 ext1 i
 change κ _ _ _ _ _ = u•κ _ _ _ _ _ + v•κ _ _ _ _ _
 rw [f.drink,g.drink,p.drink,← integral_smul,←integral_smul]
 refine Eq.trans ?_ (integral_add ((f.drink_int i).smul u) ((g.drink_int i).smul v))
 refine integral_congr_ae (Eventually.of_forall fun y=>?_)
 dsimp only [Pi.smul_apply]
 rw [e,add_smul, mul_smul,mul_smul]
lemma coffee_cuts (p:(S).Credits w T)(h:Walled j F a b w)(t:c≤a)(v:b≤d):
 κ T c d F= (S).sand (κ T a b F) (a-c) (d-b):=by
 have g:=h.brew p
 ext1 i
 change _ = ω (a-c) (κ T a b F (ω (d-b) i))
 rw [g.drink,((h.outer t v).brew p).drink,←(ω _).integral_comp_comm (g.drink_int _)]
 refine integral_congr_ae (Eventually.of_forall fun y=>?_)
 dsimp only
 by_cases u:y∈tsupport F.val
 · rw [slot_credits y p (h _ u).1 (h _ u).2 t v,map_smul];rfl
 rw [image_eq_zero_of_notMem_tsupport u];simp only [Complex.ofReal_zero,zero_smul,map_zero]
lemma Brew.flip (p:P.Brew j x T a b F)(q:P.Brew j x (P.otherLag j x T) (-b) (-a) (flipDose F j)):
   star (κ T a b F)= κ (P.otherLag j x T) (-b) (-a) (flipDose F j):=by
 ext1 i; rw [p.turn,q.drink]
 have h:MeasurePreserving (poseMirror j).toMeasurableEquiv volume volume:= opposite_money j
 refine Eq.trans (h.integral_comp' _).symm (integral_congr_ae (Eventually.of_forall fun y=>?_))
 change (F.val (opposeR j y):ℂ)•(star (σ T a b (opposeR j y)) i)=_
 rw [P.slot_reflection,reflectPose_twice];rfl
lemma coffee_dagger (p:(S).Credits w T)(h:Walled j F a b w):
   star (κ T a b F)= κ (P.otherLag j x T) (-b) (-a) (flipDose F j):=
 (h.brew p).flip (h.flip.brew (Credits.dagger p))

noncomputable def moveDose (F:SampleDose)(p:Vantage):SampleDose where
 val:=fun y=>F.val (y-p)
 smooth:= F.smooth.comp (contDiff_id.sub contDiff_const)
 budget:= F.budget.comp_homeomorph (Homeomorph.subRight p)
lemma moveforward (F:SampleDose)(p y:Vantage): (moveDose F p).val (p+y)=F.val y:=congrArg F.val (by abel)
lemma move_normalized (p:Vantage)(h:F.Normalized): (moveDose F p).Normalized:=
 ⟨fun _=> h.1 _,(integral_add_right_eq_self F.val (-p)).trans h.2⟩
lemma move_budget (F:SampleDose)(p:Vantage):tsupport (moveDose F p).val=(fun y=>y-p) ⁻¹' tsupport F.val:=
 tsupport_comp_eq_preimage F.val (Homeomorph.subRight p)
lemma Walled.move (h:Walled j F a b w)(p:Vantage): Walled j (moveDose F p) (p j+a) (p j+b) w:=by
 intro y v; rw [move_budget] at v; obtain ⟨t,u⟩:=h (y-p) v
 rw [Pi.sub_apply] at t u;constructor <;> linarith only [t,u]
lemma coffee_moved (p0:Vantage)(p:(S).Credits w T)(h:Walled j F a b w):
 κ T (p0 j+a) (p0 j+b) (moveDose F p0)= ℛ p0 (κ T a b F):=by
 have g:= h.brew p
 ext1 i
 change _ = W p0 (κ T a b F (W (-p0) i))
 rw [g.drink,←(W _).integral_comp_comm (g.drink_int _), ((h.move p0).brew p).drink]
 refine Eq.trans (integral_add_left_eq_self _ p0).symm (integral_congr_ae (Eventually.of_forall fun y=>?_))
 -- maybe change lambda
 dsimp only
 rw [moveforward,P.slot_shift,map_smul]; rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
