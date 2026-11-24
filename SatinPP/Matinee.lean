import SatinPP.Instrument
import SatinPP.Vending
import SatinPP.Meteor
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 300000
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
open YM.SatinJets YM.Quays
variable (P:Spine)(x:P.Spectrum0 3)
variable (D:P.Concert x)(V:∀ j:Axis,List Axis → ℝ→ P.ColorHil j (P.advocate 3 x j))(A:ℕ→ P.Apron)(w: Lead.Clan→ Prism)

local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "π'"=>P.wealth 3 (P.advocate 3 x 3)
local notation "ε"=>P.seasons 3 (P.advocate 3 x 3)
local notation "Ω"=>P.heaven 3 (P.advocate 3 x 3)


/-- The singular stamp used for the *later* stencil in a given clan.
For the earlier stencil, use Turn of this one. -/
def headliner (a: Lead.Clan): Stamp G:=
    surfaces (ε) (w a) ((purePrice a:ℂ) • P.seats 3 x (D 3 []))

structure Matinee : Prop where
 seed:∃ B:ℝ,P.ConcertPlays x A B D ∧ ∀ j:Axis,∀ l:List Axis,
    P.Seated j x V A l (P.seats j x (D j l)) B
 pp(a:Lead.Clan):Sold (ε) (P.headliner x D w a)
 pp'(a:Lead.Clan):Sold (ε) (Turn (P.headliner x D w a))
 vac(a:Lead.Clan)(u v:ℝ)(p:0<u)(q:0<v):
       P.headliner x D w a u v (Ω)=P.profilesZ x V w a u


lemma matinee_exists (g h:ℕ)(R:P.Register)(z:Attested P x g h A)
  (t:P.GalaxyShow x g h A V):
  ∃ D,P.Matinee x D V A w:=by
 obtain ⟨B,q⟩:=attested_price R z
 obtain ⟨D,k⟩:=P.plays x A q
 have y:=k.seated 3 [] t.heat
 let E :=P.seats 3 x (D 3 [])
 let X(a:Lead.Clan):= (purePrice a:ℂ) • E
 have d(a):Sold (ε) (X a):=(show Sold (ε) E from ⟨_,_,y.paid⟩).smul _
 have m(a):Sold (ε) (P.headliner x D w a):= (d a).surfaced _
 refine ⟨D,⟨B,k,fun j l=>k.seated j l t.heat⟩,m,fun a=>(m a).turn,
   fun a u v p e=>surfaced (Ω) (P.route_pos x g h V t a) (d a) ?_ (w a) u v p e⟩
 intro u v p q
 exact congrArg ((purePrice a:ℂ) • ·) (y.vacuum p q)

def SoldOut:Invoice:=fun P _ _ _ x _ _ _ _ A _ w V g h _ =>
    Attested P x g h A ∧ ∃ D,P.Matinee x D V A w


/-- **One unpack** of the specific proof of
 `exists_disclosed_satin_native_contrast`, via instrumentation. In
 `Affirmed SoldOut`, one experiment with an additional predicate
 `SoldOut`. The singular prices of *that witness* are paid, including
 the clan jets. -/
lemma sold_out : Affirmed SoldOut:=by
 obtain ⟨P,K,c,r,x,R,i₀,F,U,beta,e,y,nf,nu,bf,bu,s,t,A,n,w,V,g,h,X,flag,p,b,j,a⟩:=one_manifest
 exact ⟨P,K,c,r,x,R,i₀,F,U,beta,e,y,nf,nu,bf,bu,s,t,A,n,w,V,g,h,X,
      ⟨flag,P.matinee_exists x V A w g h K flag p.armada.cinema⟩,p,b,j,a⟩

#print Affirmed
#print SoldOut
#check sold_out
#print axioms sold_out

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

