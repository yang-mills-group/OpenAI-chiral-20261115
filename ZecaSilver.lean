import ZecaTune
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


/-- tied stronger Lustre: minted literally out of ONE clover power price. -/
def foraged:Prop:=
 ∃ F, P.Iguana 3 ξ F A ∧
    ∀z:ℒ, P.Iguana 3 ξ
       (P.trophy ξ (P.spark x z F) (w z)) (P.soldTrumpet A c r n w z) ∧
       P.Truth 3 ξ (P.trophy ξ (P.spark x z F) (w z)) (D z)

lemma mintage (a:P.Aureole x A c r n):
 ∃ D:P.Cilium x,(∀z,P.Lustre 3 ξ (D z) (P.soldTrumpet A c r n w z)) ∧
      P.foraged x A c r n w D:= by
 obtain ⟨_,_,_,F,h,i⟩:=a
 choose d e using fun z:ℒ=> P.gets_lustre 3 ξ ((i z).2 w)
 exact ⟨d,fun z=>(e z).2,F,h,fun z=> ⟨(i z).2 w,(e z).1⟩⟩

local notation "Z"=>P.soldTrumpet A c r n w

variable (F L:SampleDose)

structure Silver :Prop where
 prices: ∀ i:ℒ,P.Lustre 3 (P.advocate 3 x 3) (D i) (P.soldTrumpet A c r n w i)
 found: P.foraged x A c r n w D
 earlier:tsupport F.val ⊆ U.spare.invites
 laterProbe: tsupport L.val ⊆ W.spare.invites
 seats: backwardSite F μ ∧ forwardSite L μ
 under:∀ᶠ i:ℕ in atTop,∀a:ℒ,P.spacePrice ((Z a i).kiss P 3) F ⊆ U.spare.invites∧P.spacePrice (Z a i) L ⊆ W.spare.invites
 profile: ∀z:ℒ,∀t:ℝ,0<t→P.profilesZ x V w z t= parabola S (D z).n t ((D z).op Ω)
 eu:∀p q:Vantage,p 3 < q 3 → P.pointPrism x V w (q-p)=P.euPrice x D p q
 price:P.readPrism x V w μ F L=P.euRead x D F L
 realW:∀i j,P.minkPrice x D F L i j=
    inner ℂ Ω ((D i).dagger.field S (att F)
       ((D j).field S (att L) ν)).val
 centered:∀z:ℒ,WitZero S ν (D z)
 nonzero:∃d>0,LoudMargin (P.euRead x D F L) d ∧ LoudMargin (P.minkPrice x D F L) d
 _realm:P.Realm 3 ξ

lemma softer (M:CrossRead){e d:ℝ}(v:e≤d)(p:LoudMargin M d): LoudMargin M e:=
 ⟨v.trans_lt p.1,fun _=>v.trans_lt (p.2 _)⟩

include R b J uc wc m
lemma yields (ro:P.foraged x A c r n w D)
 (f:tsupport F.val⊆U.spare.invites)(l:tsupport L.val⊆W.spare.invites)
 (y:ReadsSix (P.readPrism x V w μ F L))
 (d:ReadsSix (P.minkPrice x D F L)):
 P.Silver x A c r n w V D U W μ F L:=by
 have y₁:backwardSite F μ:= fun p h=> by
   have k:= (U.sparesDoor (subset_closure (f h)) 3 (mem_univ _)).2
   linarith only [uc,k]
 have y₂:forwardSite L μ:= fun p h=>wc.trans (W.sparesDoor (subset_closure (l h)) 3 (mem_univ _)).1.le
 have e:=P.euLimit x A c r n w V g h T R J D b μ F L m y₁ y₂
 exact
  { prices:=b
    found:=ro
    earlier:=f
    laterProbe:=l
    seats:=⟨y₁,y₂⟩
    under:=eventually_all.mpr fun a=> (P.thin_inside _ (P.invertWidth _ (R.slender a)) _ U.spare.doorOpen _ f).and (P.thin_inside _ (R.slender a) _ W.spare.doorOpen _ l)
    profile:=P.euProfile x A c r n w V g h T R D b
    eu:=P.euPoint x A c r n w V g h T R J D b
    price:=e
    realW:=P.mink_is x D F L
    centered:=P.euVac x A c r n w V g h T R D b
    nonzero:= by
      rw [e] at y
      obtain ⟨d₁,p,t⟩:=loud_choose _ y
      obtain ⟨d₂,q,k⟩:=loud_choose _ d
      exact ⟨_,lt_min p q,softer _ (min_le_left ..) t,softer _ (min_le_right ..) k⟩
    _realm:=P.realm .. }
#check @yields
