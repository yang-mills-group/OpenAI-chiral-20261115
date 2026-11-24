import Mussel.Scope
import Mussel.GleamM
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Broker
namespace FrameZ
variable {P:Spine} {W:Bool} {s:ℕ}(D:FrameZ P W s)(t:ℕ)(F A':SampleDose)
local notation "Ωz"=>P.calibration
private theorem surveyed (S:Finset Cover)(j:Axis):∃ b:ℕ, 0 < b ∧ Between P.calibration j (-(ruler P.par.block*b)) (ruler P.par.block*b) S:=by
 have h(i:Cover):∀ᶠ n:ℕ in atTop,-(ruler P.par.block*(n:ℤ))+(P.calibration.ℓ:ℤ) ≤ i j ∧i j+(P.calibration.ℓ:ℤ)  ≤ ruler P.par.block*(n:ℤ):=by
    filter_upwards [eventually_ge_atTop ((i j).natAbs+ P.calibration.ℓ)] with n u
    have hn:(n:ℤ) ≤  ruler P.par.block*(n:ℤ):= le_mul_of_one_le_left (by positivity) (ruler_gene P.par.block); omega
 exact (( (eventually_gt_atTop (0:ℕ)).and (S.eventually_all.mpr fun i _=> h i)).mono fun i ⟨p,v⟩=> show 0 < i ∧ Between P.calibration j (-(ruler P.par.block*(i:ℤ))) (ruler P.par.block*(i:ℤ)) S from ⟨p,v⟩).exists
/-- For batching helpers only; *not* using these prices for footprint. -/
def placid : P.Apron where
 s:=s
 u j:= (surveyed (P:=P) (D.S0 ∪ D.T0) j).choose
 pos j:= (surveyed (P:=P) (D.S0∪D.T0) j).choose_spec.1
 F:= D.question
 S:=D.S0∪D.T0
 bay:=D.taped
 realM:=D.destinedU
 shelter j:= (by
   rw [neg_mul]
   exact (surveyed (P:=P) (D.S0∪D.T0) j).choose_spec.2)
lemma batch_accrue:D.batch t F=P.prepared t D.placid F:=rfl
variable (p:P.Spectrum0 3)(e:P.Ellis 3 p)(q:P.birthF 3 s D.question)
local notation "V"=>P.otherSpectrum 3 3 p
noncomputable def delivery:= peg p (P.viewF 3 V s q) F
include e q
lemma earned (f:∀ i∈tsupport F.val, 0 ≤ i 3)(a:∀ i∈tsupport A'.val,0 ≤ i 3):
 Tendsto (fun t=> P.singleState 3 t p (D.batch t F)) atTop (𝓝 (inner ℂ (P.heaven 3 V) (D.delivery F p q))) ∧
 Tendsto (fun t=>P.singleState 3 t p (P.reflectTest 3 (D.batch t A') * D.batch t F)) atTop (𝓝 (inner ℂ (D.delivery A' p q) (D.delivery F p q))) := ⟨oneGlimpse p e (A:=D.placid) F f q,twoGlimpse p e (A:=D.placid) (C:=D.placid) A' F a f q q⟩
omit e q
lemma location_leg (o:Cover)(g:s ≤ t){c:Vantage}{r:ℝ}(h:∀ y∈P.pinFoot s (D.S0∪D.T0), ∀ j:Axis, |y j-c j| ≤ r){y:Vantage}(v:y∈ P.pinFoot t (D.swept t o))(j:Axis):|y j-(P.meshPose t o+c) j| ≤ r:=by
 have he:= h _ (D.pin_batch t o _ g v) j; simp only [Pi.sub_apply,Pi.add_apply] at *; rwa [show y j-(P.meshPose t o j+c j)=y j-P.meshPose t o j-c j from by ring]
-- source support; earlier mirror.OK; comparison ONLY earliest gap. E.test.
open PledgeT.MiterT
lemma reading_space (g:s ≤ t)(c:Vantage)(r:ℝ)(h:∀ y∈P.pinFoot s (D.S0∪D.T0), ∀ j:Axis, |y j-c j| ≤ r):
 P.asked_at t (D.batch t (dealt F c)) {y|∃ v∈tsupport F.val,∀ j:Axis,|y j-v j| ≤ r}:=by
 let M:= P.usedGrid t (dealt F c); let Z(i:Cover):= D.swept t i
 refine ⟨M.biUnion Z, Subalgebra.sum_mem _ (fun i p=>tallerBay P.calibration _ _ (subset_biUnion_of_mem Z p) (Subalgebra.smul_mem (bay P.calibration (Z i) true) (D.in_sweep t _) _)),?_⟩
 rintro y ⟨j,w,d⟩; obtain ⟨i,vx,m⟩:= Finset.mem_biUnion.mp (w:j∈M.biUnion Z)
 exact ⟨_,pay_shift F c ((P.usedPose t (dealt F c) i).1 vx),D.location_leg t i g h ⟨_,m,d⟩⟩
lemma solvent (g:s ≤ t)(c:Vantage){r:ℝ}(hr:r ≤ 1)(h:∀ y∈P.pinFoot s (D.S0∪D.T0), ∀ j:Axis, |y j-c j| ≤ r)(f:∀ y∈tsupport F.val,(1:ℝ)<y 3)(b:∀ y∈tsupport A'.val,(1:ℝ)<y 3)(X:P.Test →ₗ[ℂ] ℂ)(x:Factors P.calibration X)(a:MatterWard P.calibration X): X (P.reflectTest 3 (D.batch t (dealt A' c)) * D.batch t (dealt F c))=0 :=by
 apply D.insolvent t g _ _ X x (.inl a); intro i hi j hj
 apply Set.disjoint_left.mpr; intro y u v
 have he:= (abs_le.mp (D.location_leg t i g h v 3)).1; have hh:= (abs_le.mp (D.location_leg t j g h (P.mirror_back_pin t _ 3 u) 3)).1; have ht:=b _ (pay_shift A' c ((P.usedPose t _ j).mp hj)); have hg:=f _ (pay_shift F c ((P.usedPose t _ i).mp hi))
 rw [show mirrorΩ _ y 3= -y 3 from if_pos rfl] at hh; linarith
end FrameZ
end Broker
#print axioms Broker.FrameZ.solvent
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
