import ZecaFroth
import ZecaQuorum
import ZecaSilver
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000



variable (P:Spine)(x:P.Spectrum0 3)(D:P.Cilium x)
local notation "ℒ"=>Lead.Clan
local notation "ξ"=>P.advocate 3 x 3
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open Hierarchy.Seld.Zeca

variable (F U:SampleDose)(z:ℒ)

abbrev Weigh:= Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3))

def whipped (d:ℕ) (f:Fin d→ℒ) (A:Cellz (Fin d)→Gaia) (V:Fin d→DirSpin): P.Weigh x:=
 P.essence ξ (Twah.witness f (Twah.letters d) A V) (D z)

local notation "ν"=>P.nv 3 (P.advocate 3 x 3)
local notation "ω"=>P.heaven 3 (P.advocate 3 x 3)
local notation "S"=>P.seasons 3 (P.advocate 3 x 3)
def come (E:P.Weigh x):=
    inner ℂ ω ((D z).dagger.field S (att F)
       (E.field S (att U) ν)).val

local notation "b" => P.come x D F U z

local notation "t"=> P.whipped x D z
def sipRatio (d:ℕ):Quorum.Quote d:=
 fun f A V=> b (t d f A V) / b (D z)
lemma readsFlavor (h:b (D z) ≠ 0)(d:ℕ):
 Quorum.Identity d (P.sipRatio x D F U z d):=by
 intro f A V
 let v:=Twah.witness f (Twah.letters d) A V
 unfold sipRatio whipped
 apply (div_eq_iff h).mpr
 unfold come
 rw [essence_op, LinearMap.smul_apply, map_smul]
 change inner ℂ ω (v • _) = _
 rw [inner_smul_right]

variable (c r m:ℕ→ℕ)(h:P.Bean c r m)(Y:ℒ→ℕ→P.Apron)
def foamOps (p:ℕ→ℕ):Prop:=
 ∀(d:ℕ) (f:Fin d→ℒ) (A:Cellz (Fin d)→Gaia) (V:Fin d→DirSpin),
 let W:= espuma d f A V r P c m h (Y z) p
 P.Lustre 3 (P.advocate 3 x 3) (P.whipped x D z d f A V) W ∧
 ∀j,Tendsto (fun i=> (W i).realWidth P j) atTop (𝓝 0)

structure Honey : Prop where
 caps:∀z:ℒ, P.come x D F U z (D z) ≠0∧∀d,Quorum.Identity d (sipRatio P x D F U z d)
 sort:∀z:ℒ,Quorum.GaugeTable (P.sipRatio x D F U z 2) (P.sipRatio x D F U z 3)
 offer: ∃c r m:ℕ→ℕ,∃h:P.Bean c r m,∀z:ℒ,∃p:ℕ→ℕ,
         P.Spoon (P.advocate 3 x 3) c (Y z) p ∧ P.foamOps x D z c r m h Y p

#check @Honey
#check @foamOps
#check @stirB

lemma zecaWhip (g:∃c r m : ℕ→ℕ, P.Bean c r m)
 (o:∀z:ℒ,P.come x D F U z (D z) ≠0)
 (e:∀z:ℒ,∃G, P.Iguana 3 ξ G (Y z) ∧ P.Truth 3 ξ G (D z))
 (u:∀z j,Tendsto (fun i=>(Y z i).realWidth P j) atTop (𝓝 0)):
 P.Honey x D F U Y:=by
 have v:= fun z=> P.readsFlavor x D F U z (o z)
 obtain ⟨l,q,g',L⟩:=g
 refine ⟨fun z=>⟨o z,v z⟩,fun z=>Quorum.table _ _ (v z 2) (v z 3),l,q,g',L,?_⟩
 intro a
 obtain ⟨G,g,y⟩:=e a

 obtain ⟨p,r₀⟩:=P.stirB ξ _ _ _ L (Y a)
 refine ⟨p,r₀,?_⟩
 intro d f A V
 obtain ⟨_,r₁,w⟩:=espuma_buy d f A V q P ξ _ _ _ L (Y a) p r₀ g y
 exact ⟨r₁,fun j=>w j (u ..)⟩
#print axioms zecaWhip
