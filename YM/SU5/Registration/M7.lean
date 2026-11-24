import YM.SU5.Registration.Heave.MildStitch
import YM.SU5.Registration.M5

/-!
Next checkpoint: actual registration on the domain of M5. This is still PARTIAL. 
No spatial cone/Vacuum cov proof (except translations as granted in M4,M5). 
See `the construction notes` also on diagnosis. Does not assert full existence.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
variable (K : P.Register) (c r : ℕ→ℕ) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose) (A : ℕ→P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4→L[ℂ] (P.ManyF 3 (P.advocate 3 x 3))) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4)
local notation "Μ" => M4Tuple P K c r x R i₀ F U A n w V g h X Y Z
local notation "Λ" => P.profilesZ x V w
local notation "ρ" => 𝓝[>] (0:ℝ≥0)
local notation "B" => P.pointBill x A c r n w
local notation "W" a:max => P.soldTrumpet A c r n w a
local notation "G₀" a:max => P.gaugeTrumpet A c r n w a
variable (F₀: M4Tuple P K c r x R i₀ F U A n w V g h X Y Z)
-- avoid rebuilding schedules. Obtained from bill α when design. Assert **parameterized** results (below) and
-- with THIS selection prove all hypotheses together. Does not assert chosen by a new
-- update of the kernel top, moving Preparations post-design.
structure Garrison :Prop where
 aircraft : P.Funding x A
 printed : P.Guest x c r A n
 front : P.Heavier c r
variable (a₀:Garrison P x c r A n)
local notation "𝒯"=> Tendsto (fun i=> c (n i)) atTop atTop
include F₀
lemma height_covered : Tendsto (fun i=> c (n i)) atTop atTop:=F₀.lab.then_read.high
lemma paidThin (a:Lead.Clan) : P.ThinHere (P.ClaimedAt c r n A a):=F₀.lab.armada.fusion.thin a
include a₀
lemma grown_bought (a:Lead.Clan): P.Bought3 x (W a):=by
 exact P.fiery_trumpet x c r n A a (paidThin P x K c r R i₀ F U A n w V g h X Y Z F₀ a) X (height_covered P x K c r R i₀ F U A n w V g h X Y Z F₀) w a₀.printed (.funded P x A a₀.aircraft)
lemma lockup_law : CapBacked P x A c r n w:=fun a=> (grown_bought P x K c r R i₀ F U A n w V g h X Y Z F₀ a₀ a).card
-- THE registered interpretation of the pure analogues on this very witness and `SplitShadow`.
-- If buying additional local equations in the physical net, maintain equality on this domain.
-- Any type of predictions purely from these operators (e.g. independent of representative at the limiting field point)
-- cannot recover these raw split prices on the M4 fixed test. Define a class of predictors:
local notation "κ'"=> ∀ a:Lead.Clan,P.CapReady x (P.gaugeTrumpet A c r n w a)
lemma sentinel_retry : ∀ a:Lead.Clan,Bought3 P x (G₀ a):=fun a=> P.mild_trumpet x c r n A a (paidThin P x K c r R i₀ F U A n w V g h X Y Z F₀ a) X (height_covered P x K c r R i₀ F U A n w V g h X Y Z F₀) w (.funded P x A a₀.aircraft)
omit F₀ a₀
local notation "e₀"=> P.CapBacked x A c r n w
variable (e : P.CapBacked x A c r n w)(E:∀ a:Lead.Clan,P.CapReady x (P.gaugeTrumpet A c r n w a))
local notation "xW" a:max => P.registeredField x A c r n w e (positiveLabel a)
local notation "xWX" a:max => P.registeredField x A c r n w e (negativeLabel a)
local notation "xL" a:max => P.pointField x _ (E a)
local notation "xLX" a:max => P.pointField x (fun i=> ((G₀ a) i).kiss P 3) (P.cap_partner x _ (E a))
local notation "Δ!" t:max i:max=> (P.gaugeShadowPrism A c r n w F U i t) (P.thinSplit x t)
local notation "Δ'" t:max i:max=> (P.reportPrism A c r n w F U i t) (P.thinSplit x t)
local notation "c!" i:max=> c (n i)
-- even an arbitrary election-dependent function of BOTH resulting actual operators
-- and their adjoints on the domain can't pay the split predictions for each of these
-- interchangeable TWO stencils when the representation used is not also specified.
-- This doesn't deny other interpretations of the raw detection that specify that recipe.
abbrev PurelyForecast (vΦ: (Test4→ₗ[ℂ] (D →ₗ[ℂ] D)) → (Test4→ₗ[ℂ] (D →ₗ[ℂ] D)) → ℂ) (t:ℕ→ℕ)(a:Lead.Clan):Prop:=
       Tendsto (fun i=> (Δ! (t i) i) a a) atTop (𝓝 (vΦ (xL a) (xLX a))) ∧
       Tendsto (fun i=>(Δ' (t i) i) a a) atTop (𝓝 (vΦ (xW a) (xWX a)))
include e E F₀ a₀
lemma pricing_diagnostic (a:Lead.Clan): xW a= (xL a) ∧ xWX a=(xLX a):=by
 have u:= P.same_fields x c r n A a (paidThin P x K c r R i₀ F U A n w V g h X Y Z F₀ a) X (height_covered P x K c r R i₀ F U A n w V g h X Y Z F₀) w a₀.printed (.funded P x A a₀.aircraft) (E a) (e a) -- `..` syntax not here replace
 exact ⟨u.1.symm,u.2.symm⟩
lemma no_intrinsic_split (a:Lead.Clan)(t:ℕ→ℕ)(h':∀ᶠ i:ℕ in atTop, c (n i) ≤ t i):
   ¬ ∃ vΦ, P.PurelyForecast x c r F U A n w e E vΦ t a:=by
 rintro ⟨vΦ,z,y⟩
 let V':=vΦ (xW a) (xWX a)
 obtain ⟨l,rξ⟩:= pricing_diagnostic P x K c r R i₀ F U A n w V g h X Y Z F₀ a₀ e E a
 apply P.nonmatching_forecast x A c r n w F U X V g h R F₀.lab (F₀.work.choose_spec.2.1) t h' a ⟨V',?_,y⟩ -- shadow r
 unfold V'; rw [l,rξ]; exact z
omit E e
-- convenient values most directly for interaction use, assemble SAME representation
lemma sold_lockup : P.OverM4 x c r F U A n w V Y Z (lockup_law P x K c r R i₀ F U A n w V g h X Y Z F₀ a₀):= sold_cap_registers P x K c r R i₀ F U A n w V g h X Y Z F₀ (lockup_law P x K c r R i₀ F U A n w V g h X Y Z F₀ a₀)
omit F₀ a₀
open Regis.Head Regis.Head.Brecht
/-- No hypothesis: actual gauge & matter cap estimates and point-fields over this very purchase. -/
theorem ribbons_win : ∃ (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    id ≤ r ∧ uniform P K (fun _ _ _ _ _ _ _ _ _ _ _ _ => 0) 1 1 ∧
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ∧ P.Garrison x c r A n ∧ ∃ p:CapBacked P x A c r n w, P.OverM4 x c r F U A n w V Y Z p := by
 -- See M6, using stronger Future generation here.
 let Y:Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G',C,ec,q,H',A,a,season,c,r,h,Θ,b,β,ρ'⟩:= heavier_century (fun _ _ _ _ _ _=>0) Y 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨s,_,t⟩:=ρ'.exists
 obtain ⟨x,R,_,p,v,a',q',S'⟩:=t (fun _=>True) (Eventually.of_forall fun _=>True.intro)
 obtain ⟨X,V,qX,pX,hX,B'⟩:= P.appointed_camera x K R c r _ _ a' v h0 ⟨P.par.R.L.val/2,by omega⟩ ((P.treasury_plot A C H' a).mono fun s p=> p (s+1) (by omega) (s+1) le_rfl) β p q' S'
 obtain ⟨N,f',hW⟩:= P.seam_grant x c r X p.setup (Heavier.loose P Θ); obtain ⟨i₀,w,F,U,Y,Z,z⟩:= (P.packages_rows x K R c r _ _ e p.setup X V qX pX hX N f').exists
 let t':Garrison P x c r X N:=⟨B', hW, Θ⟩; let ht:= P.lockup_law x K c r R i₀ F U X N w V _ _ f' Y Z z t'; have hd:P.OverM4 x c r F U X N w V Y Z ht:=P.sold_lockup x K c r R i₀ F U X N w V _ _ f' Y Z z t'; exact ⟨P,K,c,r,x,R,i₀,F,U,X,N,w,V,P.pointEra s,s,f',Y,Z,h,e,z,t',ht,hd⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.lockup_law
#print axioms Spine.ribbons_win
#print axioms Spine.PurelyForecast
#print axioms Spine.sold_lockup
#print axioms Spine.pricing_diagnostic
#print axioms Spine.no_intrinsic_split
