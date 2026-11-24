import Velour.Palace.Tuple
import Velour.Quilt.Nap
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "C"=> Lead.Clan

lemma Apron.velour_birthRaw (D:P.Apron)(f:P.birthF 3 D.s D.F)(t:ℝ)(y:D.realWidth P 3≤t) :
   D.velour P 3 ξ t ω=P.cradleH x D f t:=by
 let a:=D.realWidth P 3
 let r:=(t-a).toNNReal
 change (σ).E r (D.engine P 3 ξ ((σ).E r ω))=(σ).E t.toNNReal _
 rw [P.sector_hot 3 ξ r,P.thinRawEntry x D f]
 have e:r+(D.realWidth P 3).toNNReal=t.toNNReal:=by
    unfold r a
    rw [← Real.toNNReal_add (sub_nonneg.mpr y) (D.real_width_pos P 3).le, sub_add_cancel]
 rw [←e,(σ).time]
 rfl

variable (K:P.Register)(c r:ℕ→ℕ)(A:ℕ→P.Apron)(n:ℕ→ℕ)(w:Lead.Clan→Prism)
    (X:P.HandleWith x c r A n)(R:P.Ellis 3 x)
local notation "T"=> P.soldTrumpet A c r n w
local notation "D"=> P.gaugeTrumpet A c r n w
variable {P x c r A n}


include X
/-- Both instrument charges with both conjugates. -/
lemma M4Velvet.both (h:M4Velvet P x A c r n)(z:P.Experiment K c r x R)(a:C):
   ∃ (s:P.Veloured 3 ξ (T a))(u:P.Veloured 3 ξ (D a)),
      ∀t:ℝ,0<t→ s.printOp t=u.printOp t:=
  P.combed_night' a x A X h.handle (h.cup 3 []) w z

lemma M4Velvet.thin {K:P.Register}{R:P.Ellis 3 x}(h:M4Velvet P x A c r n)
    (z:P.Experiment K c r x R): P.ThinVelour x A c r n w:= fun a=>(h.both K w X R z a).choose

-- identify even UNprojected origin. This uses minimal condition
variable (V:∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j))
    (g h:ℕ)
variable {w}
lemma ThinVelour.light (y:P.ThinVelour x A c r n w)
    (z:P.ThinArmada x A c r n w X V g h)(a:C){t:ℝ}(p:0<t):
   (y a).printOp t ω=P.profilesH x w a V t ∧ π' ((y a).printOp t ω)=P.profilesZ x V w a t:=by
 have u:=z.heated_points a t p
 have k: Tendsto (fun i=> P.cradleH x (T a i) (P.sold_birth x A c r n w a i X) t)
    atTop (𝓝 ((y a).printOp t ω)):=
    (((y a).printed p).gaze _).congr' (((y a).thin.eventually_le_const p).mono fun i b=> Apron.velour_birthRaw P x _ _ t b)
 refine ⟨tendsto_nhds_unique k u.1, tendsto_nhds_unique ?_ u.2⟩
 simp_rw [P.cradle_bank]; exact ((π').continuous.tendsto _).comp k


#print axioms ThinVelour.light
#print axioms M4Velvet.thin
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
