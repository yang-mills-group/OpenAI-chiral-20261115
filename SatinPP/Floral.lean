import SatinPP.Arch

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ" j:max => P.advocate 3 x j
local notation "K₁" j:max => P.ManyF j (P.advocate 3 x j)
local notation "Π'" j:max=>P.wealth j (P.advocate 3 x j)
local notation "Sh"=>Shrine (P.houses x)
local notation "W"=>P.socials x
local notation "ω"=>P.lights x

open Aria Casting Six
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable {F U:SampleDose}
variable (i:Axis)(n:i≠3)(v:tsupport F.val ⊆ reviewEarlierBox.invites)
   (t:tsupport U.val⊆ reviewLaterBox.invites)
   {d:ℝ}(g:0<d)
include v t n
lemma airy (h:d<1/2):Wing 3 i (puff (puffup F g)) (puff (puffup U g)):=by
 have vf:=pu_strict g (show Strict (-2) (-1) F from fun p hp=>v hp 3 (mem_univ _))
 have vu:=pu_strict g (show Strict 1 2 U from fun p hp=>t hp 3 (mem_univ _))
 have ℓ(p:Vantage)(w:p∈tsupport (puffup U g).val):1<p i∧p i<2:=by
    rw [pu_space] at w;obtain ⟨p,h,rfl⟩:=w;rw [puffup_T,if_neg n,one_mul]
    exact t h i (mem_univ _)
 have k(p:Vantage)(w:p∈tsupport (puffup F g).val):p i< -1:=by
    rw [pu_space] at w;obtain ⟨p,h,rfl⟩:=w;rw [puffup_T,if_neg n,one_mul];exact (v h i (mem_univ _)).2

 have j:0<2-4*d:=by linarith only [h]
 have a:0<4*d:=mul_pos (by norm_num) g
 exact ⟨⟨2,fun p z=>(ℓ _ ((puff_inv _).le z)).2.le⟩,
   ⟨4*d,a.le⟩, ⟨2-4*d,j.le⟩,a,j,fun p l q b=> by
    obtain ⟨u,_⟩:=ℓ _ ((puff_inv _).le b)
    have r:=k _ ((puff_inv _).le l)
    have e:=vf _ ((puff_inv _).le l)
    have f:=vu _ ((puff_inv _).le b)
    change |(roll q) 3-(roll p) 3|<4*d∧4*d+(2-4*d)≤(roll q) i-(roll p) i
    constructor
    · rw [abs_lt];constructor<;>linarith only [e.1,e.2,f.1,f.2]
    · linarith only [r,u]⟩

local notation "ℜ"=>Lead.Clan
variable (Y:ℜ→Silk.Spool (P.ManyF 3 (P.advocate 3 x 3)))
local notation "M"=>P.MinkF x Y (puffup F g)
local notation "N"=>P.MinkU x Y (puffup U g)
variable (F U)
def Spacelit (F U:SampleDose) (i:Axis):Prop:=
   ∃z:ℝ,0<z∧LoudMargin (P.MinkAnswer x Y F U) z∧
   F.Normalized ∧ U.Normalized ∧ Wing 3 i (puff F) (puff U) ∧
   ∀a b:ℜ,(P.MinkF x Y F a).comp (P.MinkU x Y U b)= (P.MinkU x Y U b).comp (P.MinkF x Y F a)

/-- The Wick readout is preserved via literal spacelike prices on any open interval up to 1/2. Original F U. -/
def Trellis(F U:SampleDose): Prop:=
 ∀i:Axis,i≠3→P.DayStar x 3→P.DayStar x i→∀a b:ℝ,0≤a→a<b→b ≤ 1/2→
   ∃d∈ Ioo a b,∃g:0<d,P.Spacelit x Y (puffup F g) (puffup U g) i


omit n 
variable {P x Y F U}
lemma vineW
   {A:ℕ→P.Apron}{V:∀j:Axis,List Axis→ℝ→P.ColorHil j (P.advocate 3 x j)}
   {D:P.Concert x}{w:Lead.Clan→Prism}
   (r:P.Played x w V D A Y)(J:P.Ellis 3 x)
   (p:P.InteractionW x Y F U)(f:F.Normalized)(u:U.Normalized):
   P.Trellis x Y F U:=by
 intro i n y3 yi a b h z k
 obtain ⟨d,s,g,m,h',q⟩:=p.2 _ _ h z
 have e:= airy i n v t g (s.2.trans_le k)
 refine ⟨d,s,g,m,h',q,pu_normal g f,pu_normal g u,e,fun α β=>?_⟩
 exact privacy J (fully_bright r α).2 (fully_bright r β).1 n y3 yi e
#check vineW


omit v t
open Twah Lamour.Bridge.Celeste -- tune
def Parish:Invoice:=fun P _ c s x _ _ F U A n w V f h X =>
   Attested P x f h A ∧ ∃ D Y,
    P.SellPanel x w V A c s n F U (-2) (-1) 1 2 1 D Y X ∧
    P.InteractionW x Y F U ∧ P.Trellis x Y F U
theorem basilica: Affirmed Parish:=by
 obtain ⟨P,K,c,s,x,R,i0,f,u,g,p,t,q,w,b,j,y,h,A,n,v,V,α,β,X,
          ⟨hp,D,Y,H,I⟩,tail⟩:=box_seat
 exact ⟨P,K,c,s,x,R,i0,f,u,g,p,t,q,w,b,j,y,h,A,n,v,V,α,β,X,
       ⟨hp,D,Y,H,I,vineW b j H.opened R I q w⟩,tail⟩

#print axioms basilica
#check fully_bright
#check privacy
#print axioms privacy
#print Parish
#print Trellis

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
