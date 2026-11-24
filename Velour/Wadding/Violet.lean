import Velour.Wadding.Sachets
import Velour.Palace.Porch
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

namespace M4Furnish

lemma emperor (u:𝓕₄): P.invCrown 3 ξ:=u.experiment.ground.1 3

/-- Clan instruments registered in the real-time storage. -/
def violet (u:𝓕₄)(e:γ)(a:C):𝓑 where
  spool:=P.soldTrumpet A c r n w a
  thin:=u.lab.armada.slender a
  ribbon:=e a

lemma pay_origin (u:𝓕₄)(e:γ)(a:C)(d:ℝ≥0)(p:0<d):
 Q (u.violet e a) d (Ω).val=Λ a d:=by
 rw [bobQuote,Veloured.adorning,P.lyre]
 exact (e.light X V g h u.lab.armada a p).2


lemma lofty_val (u:𝓕₄)(e:γ)(a:C)(f:Test4):
 (θ (u.violet e a) f Ω).val=realY a f:=by
 apply tendsto_nhds_unique (((P.satin_storage 3 ξ).1 _).meet _ _)
 have m:Tendsto (fun d:ℝ≥0=>(d:ℝ)) (𝓝[>] 0) (𝓝[>] 0):= by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    exact self_mem_nhdsWithin
 refine ((u.boundary.boundary a f).2.comp m).congr' ?_
 have v:=P.crown_vac 3 ξ u.emperor
 filter_upwards [self_mem_nhdsWithin] with d y
 dsimp only [Function.comp_apply]
 rw [rasp_apply, ←u.pay_origin e a d y]
 unfold dangle
 simp_rw [mul_apply_eq_comp,v]

#print axioms lofty_val

lemma real_pairs (u:𝓕₄)(e:γ)(a b:C)(f k:Test4):
 inner ℂ (Ω).val ((θ (u.violet e a).windBack (bar f) *
      θ (u.violet e b) k) Ω).val=Z a b (tieAt f k):=by
 rw [u.boundary.matchTest, ←u.lofty_val e a f, ←u.lofty_val e b k]
 exact ((u.violet e a).op_star f Ω _).symm

/-- Relative distribution of these charged slabs (even testing in one
relative variable with no request that outer weights factor). This and
`real_pairs` make contact with both sides of the boundary record. -/
lemma real_line (u:𝓕₄)(e:γ)(a b:C)(f:Test4):
 Tendsto (fun t:ℝ=> let d:=(t/2).toNNReal
              ∫ y:E4,f y* inner ℂ (Q (u.violet e a) d (Ω).val)
                ((ℰ).unit.translation y (Q (u.violet e b) d (Ω).val)))
     (𝓝[>] 0) (𝓝 (Z a b f)):=by
 refine (u.boundary.surface a b f).congr' (eventually_mem_nhdsWithin.mono fun t p=>?_)
 have r:=half_pos (show 0<t from p)
 dsimp only
 rw [u.pay_origin e a _ (Real.toNNReal_pos.mpr r),
    u.pay_origin e b _ (Real.toNNReal_pos.mpr r),
    Real.coe_toNNReal _ r.le]
 rfl




/-- Real-time detector corresponding to the named **earlier** (Kiss) instrument -/
def garnet (u:𝓕₄)(e:γ)(a:C): Module.End ℂ D:= (u.violet e a).windBack.serves P 3 ξ F
/-- Real-time detector corresponding to the named **later** instrument -/
def peridot (u:𝓕₄)(e:γ)(a:C): Module.End ℂ D:= (u.violet e a).serves P 3 ξ U

lemma jewels_at (u:𝓕₄)(e:γ)(a:C):
 u.garnet e a ∈ pocket θ (foldSpace ⁻¹' reviewEarlierBox.invites) ∧
 u.peridot e a ∈ pocket θ (foldSpace ⁻¹' reviewLaterBox.invites):=
 ⟨(u.violet e a).windBack.pocketed P 3 ξ F u.boxF,(u.violet e a).pocketed P 3 ξ U u.boxU⟩

/-- Same edge two-point reading at the same smears. Independent of any extension
outside the ordered-price records. No assertion here of reality or
positivity of this number. -/
theorem jewel_boundary (u:𝓕₄)(e:γ)(a b:C):
 inner ℂ (Ω).val ((u.garnet e a * u.peridot e b) Ω).val=
    Z a b (tieAt (sachet_LocalFieldBounds F) (sachet_LocalFieldBounds U)):=by
 have y:=u.real_pairs e a b (sachet_LocalFieldBounds F) (sachet_LocalFieldBounds U)
 rw [sachet_bar] at y; exact y

end M4Furnish

#print axioms M4Furnish.jewel_boundary
#print axioms M4Furnish.real_line
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

