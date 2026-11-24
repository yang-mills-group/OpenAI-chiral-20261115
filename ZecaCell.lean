import SatinThinQuizSignal
import ZecaLustre
import ZecaVee
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

lemma cradle_price (A:P.Apron)(F:P.birthF 3 A.s A.F)
 {t u:ℝ}(p:A.realWidth P 3≤t):
 P.ruby 3 ξ A 0 t u Ω=P.cradleG x A F t:=by
 let w:=A.realWidth P 3
 rw [P.ruby_price, P.dazzle_zero]
 change E (t-w).toNNReal (P.coffer 3 ξ (A.engine P 3 ξ) (E (u-w).toNNReal Ω))=_
 rw [P.heaven_hot]
 change E (t-w).toNNReal (flashY x A 3)=_
 rw [P.thinCenterEntry x A F]
 exact DFunLike.congr_fun (P.hot_TT 3 ξ (sub_add_cancel ..)
     (sub_nonneg.mpr p) (A.real_width_pos P 3).le) _

lemma cradle_vac(A:P.Apron)(F:P.birthF 3 A.s A.F)(t:ℝ):
 inner ℂ Ω (P.cradleG x A F t)= P.singleState 3 A.s x A.F:=by
 show inner ℂ Ω (E _ (P.wealth 3 ξ _))=_
 rw [←(P.seasons 3 ξ).swing,P.heaven_hot, ← ContinuousLinearMap.adjoint_inner_left (P.wealth 3 ξ),P.bank_star]
 exact (P.view_scalar 3 ξ _ F).trans (P.single_agrees 3 3 x A.s A.F)

variable (D: Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3)))
         (Y:ℕ→P.Apron) (h:∀i,P.birthF 3 (Y i).s (Y i).F)
         (k:P.Bought 3 (P.advocate 3 x 3) D Y)
include k
lemma brood_go (s t:ℝ≥0)(p:0<s)(q:0<t):
  Tendsto (fun i=> P.cradleG x (Y i) (h i) s) atTop
    (𝓝 (D.cost S s t Ω)):=by
 obtain ⟨F,w,y⟩:=k
 rw [← y.translation _ _ p q]
 have ps:0<(s:ℝ):=p
 have pt:0<(t:ℝ):=q
 refine ((w.dyeOne ps pt).app (tendsto_const_nhds (x:=Ω))).congr' ?_
 filter_upwards [w.fit ps pt] with i r
 exact P.cradle_price x _ _ r.1

include h in
lemma brood_zero (t:∀i,P.singleState 3 (Y i).s x (Y i).F=0):
 WitZero S ν D:=by
 apply witZero S ν D (P.prepaid 3 ξ) (P.nova 3 ξ) zero_lt_one zero_lt_one
 exact tendsto_nhds_unique ((tendsto_const_nhds (x:=Ω)).inner
        (P.brood_go x D Y h k 1 1 zero_lt_one zero_lt_one))
   ((tendsto_const_nhds (x:=(0:ℂ))).congr
      (fun i=> ((P.cradle_vac x _ _ 1).trans (t i)).symm))
lemma broodProfile (t:ℝ)(p:0<t):
    Tendsto (fun i=>P.cradleG x (Y i) (h i) t) atTop
          (𝓝 (parabola S D.n t (D.op Ω))):=by
 have e:= P.brood_go x D Y h k t.toNNReal 1 (Real.toNNReal_pos.mpr p) zero_lt_one
 rw [show D.cost S t.toNNReal 1 Ω=parabola S D.n (duration t.toNNReal) (D.op Ω) from coinVac S ν D (P.prepaid 3 ξ) _ _ zero_lt_one] at e
 unfold duration at e
 rwa [Real.coe_toNNReal _ p.le] at e
