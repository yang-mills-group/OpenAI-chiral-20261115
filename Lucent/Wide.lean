import Lucent.Oratorio
import Lucent.Chorus
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration


def Wide (F: Weaver)(S:Finset Cover) : Prop:=InTest P.calibration true S false (Ξ F)
abbrev gateK {F:Weaver}{S:Finset Cover}(h:P.Wide F S) := P.art (Ξ F) (aux_test h)
variable {F:Weaver}{V:Finset Cover}(s k:ℕ)
local notation "pays" => region 3 0 P.calibration.ℓ (onFlight P.par.block V 3 k)
local notation "move" => takeoff (P.par.block) F 3 k
lemma Wide.moved (t:P.Wide F V) : P.Wide move (onFlight P.par.block V 3 k):=by
 let z:= gaugeShift P.par.block k
 have he:= axial _ (3:Axis) z (axial _ 3 0 t); rw [support_translation,sub_zero] at he; exact he
lemma Wide.turn (t:P.Wide F V): P.Wide (fluent 3 0 F) (reflectedBox 3 0 V):=axial _ 3 0 t
lemma wide_note (t:P.Wide F V)(h:pays): P.E s (Ξ (fluent 3 0 move))=star (P.E s (Ξ F))∧P.E s (Ξ move)=P.E s (Ξ F):=by
 have hp:= SWay P.run P.large P.law s 3 k (aux_test t)
 change P.E s (Ξ move)=P.E s (Ξ F) at hp
 refine ⟨?_,hp⟩
 rw [←hp,show Ξ (fluent 3 0 move)=mirror P.calibration 3 (gaugeShift P.par.block 0) (Ξ move) by simp only [gaugeShift,mul_zero]; rfl]

 apply mirror_band P.run P.large P.law s 3 0; exact ⟨_,t.moved P k, by simpa [gaugeShift] using h⟩
lemma wide_credit (t:P.Wide F V)(u:pays) :
 (∫ x, ‖P.singleState 3 s x (P.gateK t)‖^2 ∂ (P.pillars 3)) ≤ ‖P.E s (Ξ (father P.par.block 3 F k))‖:= by
 let T:=P.halfShift 3 k (P.gateK t)
 let z:=P.positiveVox 3 s _ T ((Tapestry.locates ..).mpr (t.moved P k)) u
 simp_rw [P.single_state,← (show P.reading 3 s T=_ from P.halfReads 3 s k (P.gateK t)),P.pillar_]; rw [at_label]
 change ‖(P.compressed 3 s (P.voxTest 3 s z)) φ‖^2≤ ‖P.E s (mirror Kₚ 3 0 z.val * z.val)‖
 rw [←P.seed_pairing,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),P.seed]; exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_orthogonalProjectionOnto_apply_le ..) 2
#check @Shuttle.cform

lemma wide_invoice (b:ℂ) (t:P.Wide F V)(u:pays):
  (∫ x,‖P.singleState 3 s x (P.gateK t)-b‖^2 ∂P.pillars 3)≤
      ‖P.E s (Ξ (father P.par.block 3 F k))-b*star (P.E s (Ξ F))-star b*P.E s (Ξ F)+ star b*b‖:=by
 let g:= Shuttle.changeT F b
 have e:P.Wide g V:= InTest.subOp t (.smul b .one)
 have j:=P.wide_credit s k e u; rw [Shuttle.cform] at j
 let Z:=Ξ move; let Y:=Ξ (fluent 3 0 move); let X:=Y*Z
 have hz:TestFamily Kₚ true Z:= aux_test (t.moved P k)
 have hy:TestFamily Kₚ true Y:= aux_test ((t.moved P k).turn P)
 have hx:TestFamily Kₚ true X:=hy.mul hz
 have sub {x y:Family Kₚ}(f:TestFamily Kₚ true x)(g:TestFamily Kₚ true y) : TestFamily Kₚ true (x-y):=by rw [sub_eq_add_neg,←neg_one_smul ℂ y]; exact f.add (g.scale _)
 have h:=sub hx (hy.scale b)
 have t₁:=sub h (hz.scale (star b))

 obtain ⟨w,v⟩:=P.wide_note s k t u
 have ex: P.E s (X - b • Y - star b • Z+ (star b*b) • 1)=_ := (show _=_ from E_add _ _ P.law s t₁ (TestFamily.oneT.scale _))
 rw [E_sub _ _ P.law s h (hz.scale _),E_sub _ _ P.law s hx (hy.scale _),E_scale _ _ P.law s hy,E_scale _ _ P.law s hz,E_scale _ _ P.law s TestFamily.oneT,E_unit _ _ P.law,mul_one,
    show P.E s Y=_ from w,show P.E s Z=_ from v] at ex
 simp_rw [show P.gateK e=P.gateK t-b • 1 from Subtype.ext rfl,map_sub,map_smul,show ∀ x,P.singleState 3 s x 1 = 1 from fun x=> by simp [single_state],smul_eq_mul,mul_one] at j
 exact j.trans (congrArg norm ex).le
