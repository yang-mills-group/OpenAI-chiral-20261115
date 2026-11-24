import Velour.Wadding.Tiara
import Velour.Gallery.Twinned
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

open YM.Velour


namespace M4Furnish

variable {P:Spine}{K:P.Register}{c r:ℕ→ℕ}{x:P.Spectrum0 3}
local notation "ξ"=> P.advocate 3 x 3
local notation "ω"=> P.colorZero 3 ξ
local notation "σ"=> P.physicalEnergy 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "ℋ"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ℰ"=> P.seasons 3 ξ
local notation "C"=> Lead.Clan
variable {R:P.Ellis 3 x}{i₀:ℕ}{F U:SampleDose}{A:ℕ→P.Apron}{n:ℕ→ℕ}{w:C→Prism}
    {V: ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)}
    {g h : ℕ} {X : P.HandleWith x c r A n}
variable {realY : C → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)}{Z:C→C→Boundary.Distn E4}
local notation "𝓕₄"=> M4Furnish P K c r x R i₀ F U A n w V g h X realY Z
local notation "𝓑"=> P.Bobbin 3 ξ
local notation "D"=> (ℰ).muslin
local notation "Ω"=> P.firstTulle 3 ξ
local notation "θ"=> P.detects 3 ξ
local notation "Q"=> P.bobQuote 3 ξ
local notation "γ"=> P.ThinVelour x A c r n w
local notation "Λ"=> P.profilesZ x V w

variable (u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)(e:P.ThinVelour x A c r n w)
local notation "a₁" k:max => P.RTest k (c i₀) (r i₀)
local notation "a₂" k:max => P.FTest k (c i₀) (r i₀)
local notation "ϖ"=> P.heaven 3 ξ
-- Experimental instrument readings, prior M4. Eu marking:
def chiffon (_u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)
 (i j:C): ℂ :=
 inner ℂ ϖ
   ((P.sleeveEu 3 ξ F (-5) 0 (a₁ i))
    ((P.sleeveEu 3 ξ U 0 5 (a₂ j)) ϖ))
lemma chiffon_corner (i j:C): u.chiffon i j = P.arrayReading x (c i₀) (r i₀) 0 F U i j:=by
 have b:=u.returns
 have a:=b.beforeY i
 have e (p)(h:p∈ tsupport F.val) :
      -5<p 3 - (a₁ i).realWidth P 3 ∧ p 3 + (a₁ i).realWidth P 3 < 0:= by
    have l:-2<p 3:=(u.boxF h 3 (Set.mem_univ _)).1
    exact ⟨by linarith [a p h],a p h⟩


 have d (p)(h:p∈ tsupport U.val) :
      0<p 3 - (a₂ j).realWidth P 3 ∧ p 3 + (a₂ j).realWidth P 3 <5 := by
    have l:p 3<2:=(u.boxU h 3 (Set.mem_univ _)).2
    have hx:0+ (a₂ j).realWidth P 3 < p 3:=b.beyondY j p h
    constructor <;> linarith
 have q:=P.broadPair x R 3 _ _ F U (-5) 0 5 (by norm_num) (by norm_num) e d
 have y:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp b.steady i) j
 change Tendsto _ _ (𝓝 (u.chiffon i j)) at q
 exact tendsto_nhds_unique (q.congr fun n=>P.single_agrees 3 3 x n _) y

-- Keep older instruments *also* as real-clock operators (not asserting
-- point-local; consume extra heat, not the heat used by the width budget itself):
def leftChiffon (_u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z) (i:C):Module.End ℂ D:=
 P.drapes 3 ξ (.inr (a₁ i)) (sachet_LocalFieldBounds F)
def rightChiffon (_u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z) (i:C):Module.End ℂ D:=
 P.drapes 3 ξ (.inr (a₂ i)) (sachet_LocalFieldBounds U)

lemma cares (a:P.Test) (s:ℕ) (b:P.Apron) (e:b.s=s)(d:b.F=a)
 (U:SampleDose)(r:U.Normalized)(h:P.invCrown 3 ξ): 
 inner ℂ ϖ ((P.drapes 3 ξ (.inr b) (sachet_LocalFieldBounds U) Ω).val)
   = P.singleState 3 s x a:=by
 change inner ℂ ϖ ((P.sleeve 3 ξ b (sachet_LocalFieldBounds U) Ω).val)=_
 rw [sleeve_reading _ _ _ _ _ h,e,d,sachet_one U r,one_mul]
 exact P.single_agrees ..

lemma chiffon_one (i:C) :
 inner ℂ ϖ (u.leftChiffon i Ω).val=0 ∧ inner ℂ ϖ (u.rightChiffon i Ω).val=0:=
 ⟨(cares _ _ (a₁ i) rfl rfl _ u.normF u.emperor).trans (P.body_central x (c i₀) (r i₀) i).2,
  (cares _ _ (a₂ i) rfl rfl _ u.normU u.emperor).trans (P.body_central ..).1⟩

include u
/-- Even full Hilbert determination on this character, at cost of
INCLUDING macroscopic "sleeves" (every singlet test in the native state
is enrolled even if it doesn't participate in point pocket). And for any
measurement gridding at fixed resolution, its singlet status suffices to arrive
instantly from such a real meter (applied to an entire composite charge,
not necessarily to a product of real meters). -/
theorem yard_all :
 ((ℰ).nursery (P.drapes 3 ξ) Ω=⊤) ∧
 ∀a∈enclave P.calibration, ∀s:ℕ,
   ∃B:P.Apron, B.s=s ∧ B.F=a ∧
   P.singleState 3 s x a=inner ℂ ϖ
      ((P.drapes 3 ξ (.inr B) (sachet_LocalFieldBounds F) Ω).val):=by
 refine ⟨P.whole_reach _ _ u.emperor,fun a h s=>?_⟩
 obtain ⟨b,r,t⟩:=P.all_aprons s a h
 exact ⟨b,r,t,(cares _ _ b r t _ u.normF u.emperor).symm⟩

#print axioms yard_all
#print axioms chiffon_corner
end M4Furnish
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
