import ZecaSilence
import ZecaAureole
import SatinThinQuizMargin
import ZecaSlip
import SatinThinQuizPair
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

open DoseTravel Set

variable (A:ℕ→P.Apron) (c r n:ℕ→ℕ) (w:Lead.Clan→Prism)
 (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
 (T:P.HandleWith x c r A n)(R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)


variable (D:Cilium P x)
 (b:∀i, P.Lustre 3 (P.advocate 3 x 3) (D i) (P.soldTrumpet A c r n w i))

local notation "ℒ"=>Lead.Clan

variable (U W:Doorway)(K:P.Register)(μ:ℝ)(uc:U.upper 3≤ -μ)(wc:μ≤W.lower 3)
 (m:0<μ)


local notation "Q"=> reviewEarlierBox
local notation "L"=> reviewLaterBox

/-- Earlier and later centers, including our aperture footprints,
spacelike if kept in the prescribed "spare" part. -/
lemma vacant (p q:E4)
 (u:backV p∈(Q).spare.invites)(v:backV q∈(L).spare.invites):
   q-p∈Mink.spacelike ∧ Mink.m (q-p) < -1:=by

 have h(i:Axis):8/3 < (q-p) i ∧ (q-p) i < 10/3:=by
    have h:=u i (mem_univ _); have t:=v i (mem_univ _)
    change (2*(-2)+(-1))/3 < p i ∧ p i<((-2)+2*(-1))/3 at h
    change (2*1+2)/3<q i ∧ q i <(1+2*2)/3 at t
    rw [PiLp.sub_apply]
    constructor <;>linarith
 have a:‖(spatial (q-p))‖^2 > 3*(8/3)^2:= by
    rw [←real_inner_self_eq_norm_sq,PiLp.inner_apply, show (3:ℝ)=∑ _:Fin 3,1 by norm_num,Finset.sum_mul]
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
    intro i _
    rw [one_mul]
    simpa [pow_two] using (sq_lt_sq₀ (show 0≤ (8/3:ℝ) by norm_num) (show 0≤(spatial (q-p)) i from le_trans (by norm_num) (h i.castSucc).1.le)).mpr (h i.castSucc).1

 have b:(_root_.YM.time (q-p))^2 <(10/3:ℝ)^2:=
     (sq_lt_sq₀ (le_trans (show (0:ℝ)≤8/3 by norm_num) (h 3).1.le) (by norm_num)).mpr (h 3).2
 have d:Mink.m (q-p)< -1:= by unfold Mink.m; linarith only [a,b]
 exact ⟨d.trans (by norm_num),d⟩
