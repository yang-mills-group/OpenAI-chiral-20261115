import SatinPP.Tunic
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 320000
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
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)

local notation "ξ"=>P.advocate 3 x 3
local notation "G"=>P.ManyF 3 ξ
local notation "H"=>P.ColorHil 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "E" => (P.physicalEnergy 3 ξ).E
local notation "ε" => P.seasons 3 ξ
local notation "ℜ"=>Lead.Clan
variable (w:Lead.Clan→Prism)
 (V:∀j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j))
 (A:ℕ→P.Apron)(c s n:ℕ→ℕ)
local notation "W"=>P.soldTrumpet A c s n w
local notation "W₁" a:max i:max => ((W a i).kiss P 3)
local notation "st" i:max => c (n i)
variable (F U:SampleDose)
local notation "Φ" a:max t:max i:max=> P.prepared t (W₁ a i) F
local notation "Ψ" b:max t:max i:max=> P.prepared t (W b i) U
variable (l u q t μ:ℝ)
local notation "K₁" a:max i:max r:max => P.gridRun x r (W₁ a i) F l u
local notation "K₂" a:max i:max r:max => P.gridRun x r (W a i) U q t
variable (D:P.Concert x)(Y:Lead.Clan→Silk.Spool (P.ManyF 3 (P.advocate 3 x 3)))
local notation "V₁" a:max => P.leaderW x w D a F l u
local notation "V₂" a:max => P.laterW x w D a U q t

variable (g h:ℕ)(X:P.HandleWith x c s A n)
local notation "χ'"=>P.reportPrism A c s n w F U
open Silk Quays
def Couture:Prop:=
 (∀a, Silken (ε) ((Y a).dual) (puff F) (Turn (P.headliner x D w a)) l u)∧
 (∀a, Silken (ε) (Y a) (puff U) (P.headliner x D w a) q t)

variable {P x w V A c s n F U l u q t μ D Y X}
lemma made (r:P.Played x w V D A Y) (e:Agenda μ F U l u q t):P.Couture x w F U l u q t D Y:= by
 constructor
 · intro a; obtain ⟨_,_,p⟩ := r.m.pp' a; exact silk_dress (Played.back _ _ _ _ _ _ _ r a) p (bandp e.strict)
 · intro a; obtain ⟨_,_,p⟩ := r.m.pp a; exact silk_dress (r.tick a) p (bandp e.widen)
def Palace:Invoice:=fun P K c s x R i F U A n w V f h X =>
  Fanfare P K c s x R i F U A n w V f h X ∧
  ∃ D Y,P.SellPanel x w V A c s n F U (-2) (-1) 1 2 1 D Y X ∧
      P.InteractionW x Y F U ∧ P.Trellis x Y F U ∧
      P.Chandelier x w V Y F U ∧ P.Couture x w F U (-2) (-1) 1 2 D Y
theorem state_dress:Affirmed Palace:=by
 obtain ⟨P,K,c,r,x,J,i,F,U,beta,z,y,nf,nu,bf,bu,m,k,A,n,w,V,g,h,X,s,p,tail⟩:=radiance
 have v:=s
 obtain ⟨⟨_,D,Y,a,b,e,z'⟩,_⟩:=v
 exact ⟨P,K,c,r,x,J,i,F,U,beta,z,y,nf,nu,bf,bu,m,k,A,n,w,V,g,h,X,
   ⟨s,D,Y,a,b,e,z',made a.opened (day p)⟩,p,tail⟩
#print axioms state_dress
#print Palace
#print Couture
#print Silken
#check state_dress
