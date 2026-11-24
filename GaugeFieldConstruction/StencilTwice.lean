import GaugeFieldConstruction.StencilDouble
import GaugeFieldConstruction.StencilPromotion
import YM.SU5.SatinWard.Resolution.HighSea
import GaugeFieldConstruction.StencilStress
/-!
# The signal in reconstructed space. Distinguish signs & estimators. Continues `GaugeFieldConstruction.ContinuumPredictions`.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 7200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
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
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace

namespace ContinuumConstruction
open Discipline
open _root_.YM.SatinWFixed Andesite Carton InkPort
open _root_.YM.Boundary (Test4)
open _root_.YM.SatinRegistration
open NSF.Boundary
namespace GaugeLimitJoint
open _root_.YM.LocalFieldBounds
open Motif (late_at smallCast programme_plus Programme Production)
open _root_.YM.WakeFields
open QuadClock ShapeLab SignSlot
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open SoulField SatinWard.Installment Ione.Clock Moto
open LitCurrent LitCurrent.AuroraX
open _root_.GarnetAct.Cut
open Set MeasureTheory
open CF.LitCurrent.AuroraX
variable {β₀:ℝ} {y:Project β₀} {a:GivenTime y}
local notation "Pr" => y.P
local notation "qv" => a.guest.atx
local notation "dt@" => a.guest -- adjust
variable
  {nLeaf : ℕ}
  {scale : y.P.Register}
  {production : YardμN y.P CostUpVU PolRun PriceArtVU nLeaf}
  {growth : InterR}
  {roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU}
  {axes : Axis → GaugeFieldConstruction.Empire.Across}
  {comparison : Sheds roles.Crew_N axes}
  {approvals : Supplies comparison}
  {stress : Ticket roles.Gamma_N approvals}
  {costAnalysis : y.P.Ellis 3 a.guest.atx}
  {c : ℕ → ℕ}
  {collars : ℕ→ℕ}
  {layers : NSF.Boundary.Waves (roles.RadianceVU stress)}
  {response : NSF.Boundary.Surface (roles.RadianceVU stress)}
  {continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL}
  {model : roles.GlowVU stress a.guest.atx (le_refl _) layers response}
  {screens : y.P.Poll 3}
local notation "lab$" => (roles.RadianceVU stress).Union
local notation "ink" => appointedLibrarySt model
local notation "μ" => y.P.advocate 3 a.guest.atx 3
local notation "ΤΔ" => y.P.seasons 3 (y.P.advocate 3 a.guest.atx 3)
local notation "The" => y.P.ManyF 3 μ


-- All cups on this balancing preparation. `galaxy` & `library` tested at these bills.
local notation "WΞ" => a.a.Wj
local notation "eΞ" => a.a.ed
local notation "zX" => Motif.brow y.P y.ht.tendsto_atTop a.a.ed y.Costs.ledger.rocky.night a.w true 0
local notation "gaΞ" => galaxy y.P rayPost rayP y.M y.ht.tendsto_atTop a.a.Wj a.a.ed y.Costs.ledger.rocky.night a.guest.atx
local notation "voΞ" => a.guest.i
local notation "ζΞ" => a.guest.sig
local notation "chΞ" => choral a.guest.i zX -- local binder tune
local notation "ΣΞ" => priceX y.P y.ht.tendsto_atTop a.a.ed
local notation "ΧΞ" => y.Costs.ledger.rocky.night
local notation "vhΞ" => a.a.V' (zX)
local notation "qX" j:max=> choral j zX
local notation "JΞ" j:max=> (ΣΞ j rayPost y.M (ΧΞ) rayP 3 μ zX)
local notation "A#"=> PaidPadL y.P
open Fame.PSE OS.Semigroup
open _root_.YM.Boundary (Joint)

variable (k:ℕ) (j:Axis)(X:Axis→UV three)
local notation "χV" i:max => roles.DeckLiftVU k (X i)
local notation "BΚ" i:max => (roles.PerD_VU stress (le_refl _)).TinCanL (roles.DeckLiftVU k (X i))
open YM.GaugeFieldConstruction.Phys

local notation "signM" => ((ζΞ):ℂ)
local notation "leadPair" => signM • (JXSt (model:=model) (a:=a) k X a.guest.i)
local notation "lastPair" => KXSt (model:=model) (a:=a) k X
local notation "starryT" => a.guest.first
local notation "leafyT" => a.guest.last
local notation "smT" => Easel.film a.guest.first
local notation "smG" => Easel.film a.guest.last
local notation "sv"=> model.system.operators.omega
local notation "gh"=> (gaΞ).vacuum
local notation "Jℤ"=> (signM • chΞ)
local notation "AOp"=> (gaΞ).operator (signM • qX (dt@).i)
local notation "DOp"=> (gaΞ).operator omegaCorner
local notation "Tx"=> Polaris.Chili.windowχ y.P a.v
local notation "Hx"=> Freeport.feather y.P y.M zX WΞ a.a.V' y.β a.v a.n
local notation "ϰι" => (dt@).mink
local notation "erΖ" => (dt@).eu
local notation "ℱ₀" => Easel.film a.guest.first  -- tune
local notation "ℱ₁" => Easel.film a.guest.last

variable {F:InkWaves ((roles.RadianceVU stress).Union)}{W:WView ((roles.RadianceVU stress).Union)}{t:roles.LeaseVU k} {u:WordSeatSt model}
local notation "J#"=> (leadPair) smT
local notation "K#"=> (lastPair) smG
local notation "Fx"=> gapXSt (model:=model) (a:=a) k X
local notation "Uj"=> AOp smT
local notation "Ug"=> DOp smG
open Motif Easel
local notation "Ψι" => inkTest a.guest.mink (signM • chΞ) omegaCorner starryT leafyT
local notation "WickM"=> vesper a.guest.eu (signM • chΞ) omegaCorner starryT leafyT
    - sighting a.guest.eu (signM • chΞ) starryT * sighting a.guest.eu omegaCorner leafyT
local notation "ζleft"=> (ϰι).expect [(Jℤ,ℱ₀)]
local notation "ζright"=> (ϰι).expect [(omegaCorner,ℱ₁)]
local notation "ζboth"=> (ϰι).expect [(Jℤ,ℱ₀),(omegaCorner,ℱ₁)]

open Discipline Shower Ember.Volumetric Stage Stage.Cell OS.Semigroup -- syntax tune
-- time-three only, but enough. Full projection on every pad. Simpler than the
-- version via any-axis strict-actor, uses word equality & reconstruction's field-not-lost.
section
include u
lemma pledge_at3 (v:UV four)(p:∀ (l:PermWallJ y.P), projectLine y.P 3 a.guest.atx (roles.RoomsVU v 3 l l)=0): v=0:= pledge_at3_st u v p
end
variable (V:ActorsΞSt (model:=model) X k t F W u)(G:Assembled (scale:=scale) (costAnalysis:=costAnalysis) (c:=c) (collars:=collars)
   (continued:=continued) (model:=model) (screens:=screens))
local notation "FΘ" => fun i:Axis=> roles.DeckLiftVU k (X i)
local notation "μ₁"=> (dt@).i
local notation "ℳ"=> (MaskL) -- no (MaskL) macro in here. 
local notation "Uζ"=> (roles.PerD_VU stress (le_refl _))
abbrev MixPriceSt (k:ℕ)(X: Axis→ UV three)(f g:Test4) (r:ℝ):= pairPriceSt _ (X:=model.system) (((r:ℂ) • JXSt (model:=model) k X a.guest.i) f) (KXSt (model:=model) k X g)
local notation "μQ" => MixPriceSt (a:=a) (model:=model) k X
local notation "νQ" => fun x:Axis=> ((↑(a.a.V' (zX)):ℂ)⁻¹)*clockSign x
local notation "ΠΦ" j:max => projectLine y.P j a.guest.atx
include V G
open Imperial.Lighthouse
local notation "PΨ" => production
local notation "FΦ" => roles.DeckLiftVU k
local notation "ΖΦ" => roles.βBunVU three k
local notation "U`" b:max => roles.RoomsVU (FΦ (X b))
local notation "Zx" => trueKey y.P y.ht.tendsto_atTop eΞ ΧΞ
local notation "GΦ" i:max => (Uζ).TinCanL (χV i)
omit V
include u
variable (z₀:Soul) (U:∀ j:Axis, CardVistaSt (roles:=roles) (a:=a) k j X z₀)
include U t
lemma allRigorousLabelSt (p:Cover)(hp:ResidualPermit p)(b:Axis): VistaX 0 (roles.RoomsVU (roles.DeckLiftVU k (X b))) (fun s=> (JpriceApp y.P p y.M hp ((Zx s) z₀) b s).F) ∧ ∀ j (l r:PermWallJ y.P), (ΠΦ j) (roles.RoomsVU (roles.DeckLiftVU k (X b)) j l r)=priceX y.P y.ht.tendsto_atTop eΞ b p y.M ΧΞ hp j (y.P.advocate 3 a.guest.atx j) z₀ (StallJ y.P l) (StallJ y.P r):=by
 -- even offset points may differ by several sites. need alias rigidity using OTHER taxonomy of resolution (LocalFieldBounds funding). hook Council.
 obtain ⟨c',d,t',w',W₀,W₁⟩:= y.rank; obtain ⟨u₀,v,p',Y₀,z⟩:= a.a.sec
 have he(j:Axis)(l r:PermWallJ y.P): (ΠΦ j) ((U` b) j l r)=priceX y.P y.ht.tendsto_atTop eΞ b p y.M ΧΞ hp j (y.P.advocate 3 a.guest.atx j) z₀ (StallJ y.P l) (StallJ y.P r):=(U b j l r).trans ( aliasJ y.P Unit rayPost rayP y.M z₀ b j (y.P.advocate 3 a.guest.atx j) Y₀ ΧΞ y.ht.tendsto_atTop eΞ z WΞ W₀ W₁ 3 qv (y.P.ellisP 3 qv y.U).some y.large.1 a.a.ress l.2 r.2 ⟨p,hp⟩)
 exact ⟨nominate_st roles eΞ ΧΞ y.ht.tendsto_atTop a.guest.atx X k t p hp z₀ b G.extra_births WΞ (pledge_at3 (u:=u)) he,he⟩
-- full normal currency at standard PV widths. Fits even arbitrary reindex vote. Includes obtaining authorized local supports on every chart (independent of the box stencil radius convention).
lemma allJStandardSt (H:ℕ→ℕ)(v:Tendsto H atTop atTop) (p:Cover)(hp:ResidualPermit p)(b:Axis): StandardPV H (fun _ s=>(JpriceApp y.P p y.M hp ((Zx s) z₀) b s).F) (roles.RoomsVU (roles.DeckLiftVU k (X b))):=by
 exact faithClock_st roles b X k p hp (fun i=>Zx i z₀) H v ((allRigorousLabelSt k X (u:=u) G z₀ U (t:=t) p hp b).1)
lemma seenAllSt : _root_.YM.GaugeFieldConstruction.Stage.looksVectorSt X:= promotes_st roles X k t rayPost rayP (fun i=> Zx i z₀) (fun p h b=>(allRigorousLabelSt k X (u:=u) G z₀ U (t:=t) p h b).1)
omit U
include V
lemma rigorousLabelPricesSt (p:Cover)(hp:ResidualPermit p)(b:Axis): VistaX 0 (roles.RoomsVU (roles.DeckLiftVU k (X b))) (fun s=> (JpriceApp y.P p y.M hp ((Zx s) zX) b s).F) ∧ ∀ j (l r:PermWallJ y.P), (ΠΦ j) (roles.RoomsVU (roles.DeckLiftVU k (X b)) j l r)=priceX y.P y.ht.tendsto_atTop eΞ b p y.M ΧΞ hp j (y.P.advocate 3 a.guest.atx j) zX (StallJ y.P l) (StallJ y.P r):= allRigorousLabelSt k X (u:=u) G zX V.card (t:=t) p hp b
lemma forJStandardSt (H:ℕ→ℕ)(v:Tendsto H atTop atTop) (p:Cover)(hp:ResidualPermit p)(b:Axis): StandardPV H (fun _ s=>(JpriceApp y.P p y.M hp ((Zx s) zX) b s).F) (roles.RoomsVU (roles.DeckLiftVU k (X b))):= allJStandardSt k X (u:=u) G zX V.card (t:=t) H v p hp b
lemma seenFullSt : _root_.YM.GaugeFieldConstruction.Stage.looksVectorSt X:= seenAllSt k X (u:=u) G zX V.card (t:=t)
-- Mink price. proper. mark has extra camera sign σ not in intrinsic Spin.
omit V G u t in
abbrev UprightJ_st (j:Axis):= ((Wickγ j):ℂ)⁻¹ • JXSt (model:=model) (a:=a) k X j
local notation "νκ" i:max=> UprightJ_st (model:=model) (a:=a) k X i
omit V G u t in
lemma UprightEq_st (i:Axis)(h:i≠3): UprightJ_st (model:=model) (a:=a) k X i= JXSt (model:=model) (a:=a) k X i:=by unfold UprightJ_st Wickγ; simp [h,timeAxis] -- omit prereq later
lemma singularJ_vectorSt : properCurrentSt stress _ Uζ model.course (fun i=> UprightJ_st (model:=model) (a:=a) k X i):=by
 exact upright_fee_st G k X t (seenFullSt k X V G)
lemma Mink_scalarSt (g:Mink.Poincare)(f:Test4): DragΛL model.system model.course g (KXSt (model:=model) k X f)=KXSt (model:=model) k X (Joint.push g f):=by
 rw [purchaseDescSt k X]; exact Mink_descendantSt G k X t _ (seenFullSt k X V G) g f
#print axioms seenFullSt
#print axioms singularJ_vectorSt
#print axioms Mink_scalarSt
lemma twoTickets (i:Axis)(t:i≠3)(h: a.guest.i≠3)(u:i≠a.guest.i)(f g:Test4)(r:ℝ): MixPriceSt (model:=model) k X f g r= -(MixPriceSt (model:=model) k X (Joint.push (flipLocationSt a.guest.i i h t) f) (Joint.push (flipLocationSt a.guest.i i h t) g) r):=by
 exact directionDouble_st stress _ a.guest.i i (Uζ) model.course (fun i=> UprightJ_st (model:=model) k X i) (KXSt (model:=model) k X) (singularJ_vectorSt k X V G) (Mink_scalarSt k X V G) f g h t (JXSt (model:=model) k X a.guest.i) (UprightEq_st (model:=model) k X _ h) u r
/-!
 Positive in actual current convention. In fact even **for same camera sig** get either sign
 by reposing both supports with simultaneous spatial half turn. Wick margin ONLY delivered in
 camera support prescription. Not claiming a Coast in this lemma (the supports may be *decreasing* in
 some spatial axis to get this sign); positive time gap paid nevertheless.
-/
theorem reorderPaysSt (r:ℝ)(x:r≠0): ∃ (w:a.guest.i≠3), ∃ f g:Test4,
   ((f=smT ∧ g=smG) ∨ ∃ (k:Axis) (z:k≠3), k≠a.guest.i ∧ f=Joint.push (flipLocationSt a.guest.i k w z) smT ∧ g=Joint.push (flipLocationSt a.guest.i k w z) smG ) ∧ SmallDoseSt f ∧ SmallDoseSt g ∧ Apart_st Tx f g ∧ LinearMap.IsSymmetric (((r:ℂ) • JXSt (model:=model) k X a.guest.i) f) ∧ LinearMap.IsSymmetric (KXSt (model:=model) k X g) ∧ (MixPriceSt (model:=model) k X f g r).im=0 ∧ ∃δ:ℝ,0<δ∧δ < (MixPriceSt (model:=model) k X f g r).re:=by
 let F:= smT; let W:=smG; let A:= still_prices k X V; let c(x:ℝ):= μQ F W x; let ε := (Tx); have hp: (μ₁)≠3:= A.signs.2
 refine ⟨hp,?_⟩
 exact directionEither_st stress _ _ Uζ model.course (fun i=> UprightJ_st (model:=model) k X i) (KXSt (model:=model) k X) (singularJ_vectorSt k X V G) (Mink_scalarSt k X V G) hp (JXSt (model:=model) k X a.guest.i) (UprightEq_st (model:=model) k X _ hp) r x F W (A.not_empty F (Or.inl rfl)) (A.not_empty W (Or.inr rfl)) Tx A.region.1 (fun x hx y hy=> (A.region.2 x hx y hy).1) (fun x hx y hy=> (A.region.2 x hx y hy).2.2) _ A.signs.1 (Fx) rfl A.joint_prices_unpadded.2.2.2 A.tape A.joint_prices_unpadded.1 A.joint_prices_unpadded.2.1
#print axioms reorderPaysSt
end GaugeLimitJoint
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
