import Velour.Sequins.Glisten
import Velour.Gathers.Jasmine
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
variable (u:M4Furnish P K c r x R i₀ F U A n w V g h X realY Z)(e:P.ThinVelour x A c r n w)
local notation "ς"=> P.heaven 3 ξ
local notation "M"=> (ℰ).unit.translation

include u in
lemma alert (a:C)(f:Test4): inner ℂ ς (realY a f)=0:=by
 apply tendsto_nhds_unique
   (tendsto_const_nhds.inner (u.boundary.boundary a f).2)
 apply tendsto_const_nhds.congr'
 filter_upwards [eventually_mem_nhdsWithin] with d y
 have h:(ℰ).orth (Λ a d)=0:=((u.lab.armada.energy a).2.2 _ y).2.1
 have p:(ℰ).orth ς=ς:=Submodule.starProjection_eq_self_iff.mpr (show ς∈(ℰ).ground by unfold OS.Semigroup.ground; simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe]; exact fun t=>sub_eq_zero.mpr (P.heaven_hot 3 ξ t))
 have t:=collect_int (ℰ) f (Λ a d)
 rw [←integral_inner t]
 suffices w:∀b:E4, inner ℂ ς (f b • M b (Λ a d))=0 from by simp only [w,integral_zero]
 intro b
 rw [inner_smul_right,←ContinuousLinearMap.adjoint_inner_left]
 have e: (M b).adjoint ς =ς:= (congrArg (fun T=> T ς) ((ℰ).unit_star b)).trans (P.crown_vac 3 ξ u.emperor _)
 rw [e,←p,←ContinuousLinearMap.adjoint_inner_right,Spectral.Alps.engaged,h,inner_zero_right,mul_zero]

lemma real_mean (u:𝓕₄)(e:γ)(a:C):
 inner ℂ ς (u.garnet e a Ω).val=0 ∧ inner ℂ ς (u.peridot e a Ω).val=0:=by
 refine ⟨?_,(u.lofty_val e a (sachet_LocalFieldBounds U)) ▸ u.alert a (sachet_LocalFieldBounds U)⟩

 have h:inner ℂ ς (P.detects 3 ξ (u.violet e a) (sachet_LocalFieldBounds F) Ω).val=0:= by
    rw [u.lofty_val,u.alert]
 exact (((u.violet e a).real_Kiss P 3 ξ F Ω Ω).symm).trans
     ((inner_conj_symm ..).symm.trans ((congrArg (starRingEnd ℂ) h).trans (map_zero _)))

def blaze (u:𝓕₄)(e:γ):CrossRead:=
 Matrix.of fun a b=> inner ℂ ς (((u.garnet e a)*(u.peridot e b)) Ω).val

lemma blaze_cash (u:𝓕₄)(e:γ):u.blaze e=paycheck realY F U:=by
 ext1 a b
 exact (u.jewel_boundary e a b).trans (u.boundary.matchTest ..)

def flashBlaze(u:𝓕₄)(e:γ)(p k:ℕ)(l₁ l₂ r₁ r₂:ℝ≥0):CrossRead:=
   Matrix.of fun a b=> inner ℂ ς (((u.violet e a).windBack.visits P 3 ξ p l₁ r₁ (sachet_LocalFieldBounds F) *
    (u.violet e b).visits P 3 ξ k l₂ r₂ (sachet_LocalFieldBounds U)) Ω).val

def HasSpark(u:𝓕₄)(e:γ):Prop:=
  ∃ d:ℝ,0<d∧LoudMargin (u.blaze e) d ∧
   ∀ (p k:ℕ→ℕ) (l₁ l₂ r₁ r₂:ℕ→ℝ≥0), Tendsto p atTop atTop → Tendsto k atTop atTop →
     Tendsto l₁ atTop (𝓝 0)→ Tendsto l₂ atTop (𝓝 0)→ Tendsto r₁ atTop (𝓝 0)→ Tendsto r₂ atTop (𝓝 0)→
      ∀ᶠ i in atTop,LoudMargin (u.flashBlaze e (p i) (k i) (l₁ i) (l₂ i) (r₁ i) (r₂ i)) d

lemma dazzle (u:𝓕₄)(e:γ)
 (d:M4Velvet P x A c r n)(y:TottyCup P x A)(j:ReadsSix (paycheck realY F U)):
 u.HasSpark e:=by
 obtain ⟨c',v,b⟩:=loud_choose _ j
 rw [←u.blaze_cash e] at b
 refine ⟨c',v,b,fun p k l₁ l₂ r₁ r₂ H H' L L' W W'=> ?_⟩
 let f:=fun i=>u.flashBlaze e (p i) (k i) (l₁ i) (l₂ i) (r₁ i) (r₂ i)
 have t:Tendsto f atTop (𝓝 (u.blaze e)):= by
   apply tendsto_pi_nhds.mpr; intro a; apply tendsto_pi_nhds.mpr; intro a'
   change Tendsto _ _ (𝓝 (inner ℂ (Ω).val ((((u.garnet e a)*(u.peridot e a'))) Ω).val))
   rw [u.jewel_boundary]
   exact u.matched_joint e (u.vio_silky e d y a).1 (u.vio_silky e d y a').1 H H' L L' W W'
 exact t.eventually (loud_near _ _ b)

end M4Furnish


theorem satin_pearl :
    ∃ (P:Spine) (K:P.Register) (c r:ℕ→ℕ) (x:P.Spectrum0 3) (R:P.Ellis 3 x)
    (i₀:ℕ)(F U:SampleDose)(A:ℕ→P.Apron)(n:ℕ→ℕ)(w:Lead.Clan→Prism)
    (V:∀ j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j))
    (g h:ℕ)(X:P.HandleWith x c r A n)
    (Y: Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3))
    (Z: Lead.Clan → Lead.Clan → Boundary.Distn E4),
    
     ∃ (u:M4Furnish P K c r x R i₀ F U A n w V g h X Y Z) (e:P.ThinVelour x A c r n w),
       P.Sconces K c r ∧ M4Velvet P x A c r n ∧ TottyCup P x A ∧
       P.FullPrismLab x A c r n w V g h X 1 F U gate1 gate2 (c i₀) (r i₀) K ∧
       u.AtSpindle e ∧ u.Contrasts e ∧
       u.Facets ∧ ReadsSix (paycheck Y F U) ∧ u.HasSpark e:=by
   obtain ⟨p,a,b,t,d,l,j,f,v,m,o,k,I,i,y,r',L,N,u,hx,k',q,r'',loud⟩:=pearlElection
   let e:=k'.thin k r' u.experiment
   exact ⟨p,a,b,t,d,l,j,f,v,m,o,k,I,i,y,r',L,N,u,e,hx,k',q,r'',u.reunion e,u.foil k',u.sees,
    loud,u.dazzle e k' q loud⟩

#print axioms satin_pearl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
