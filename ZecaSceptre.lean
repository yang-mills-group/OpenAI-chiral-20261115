import ZecaClip
import ZecaGilt
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

local notation "MH"=> Hierarchy.Seld.Zeca.Moment

open Hierarchy.Seld.Poin Hierarchy.Seld.Zeca.Monument
open Boundary
variable {ι:Type}(N:P.Tent x ι)
local notation "wΩ"=>P.nova 3 ξ
local notation "J"=>Grotto S N Ω
local notation "H'"=> chapel S N Ω
local notation "Z"=>springs S N Ω
local notation "qΩ"=> saint S N ν wΩ
local notation "op"=>mast S N ν wΩ
local notation "qv"=>mastV S N ν wΩ
local notation "lens"=>(H').lens Z qΩ


open Hierarchy.Seld.Zeca.Gilt
open Hierarchy.Seld.Poin.Gem Hierarchy.Seld.Poin.Galleon
  Hierarchy.Seld.Leal Hierarchy.Seld.Leal.Breve Hierarchy.Celeritas Land
abbrev Retinue (j:Axis):Hilbert:= P.ManyF j (P.advocate 3 x j)
abbrev Shiver (N:P.Tent x ι):= Tribe (K:=P.Retinue x) N -- N type implicit? name ι auto via previous var
abbrev Centripetal (j:Axis):= P.seasons j (P.advocate 3 x j)
abbrev Sphere (j:Axis):= P.heaven j (P.advocate 3 x j)

variable (A:P.Shiver x N)
structure Regalia (Y:N.Chip→ℕ→P.Apron):Prop where
 buys(j:Axis)(w:N.Chip):P.Bought j (P.advocate 3 x j) (coin (K:=P.Retinue x) N A j w) (Y w)

lemma pose_r (j:Axis) (p:E4):poseSp j p.ofLp = SEP j p:=by
 have h(i:{i:Axis//i≠j}): (SEP j p).val i=p i:=by
    change p i - p j * YM.basis j i = p i
    simp [YM.basis,i.property]
 unfold poseSp
 exact (congrArg (transverse j) (funext h).symm).trans (eyes_toFace ..).symm


def Sched (Y:N.Chip→ℕ→P.Apron){D:Type}(u:D→N.Chip)(k:ℕ):=fun i=>Y (u i) k

variable {P x N A}{Y:N.Chip→ℕ→P.Apron}
 (q:P.Ellis 3 x) (l:P.Regalia x N A Y)
local notation "Wₑ"=> P.Centripetal x
local notation "ωₑ"=> P.Sphere x
variable {n:ℕ}(j:Axis)(p:Points n)(u:Fin n→N.Chip)
abbrev atPosition{n:ℕ}(p:Points n): Fin n→Vantage:=fun i=>(p i).ofLp

include l q
lemma reigning (L L':List (Fin n))(e:L'.Perm L)(v:ℕ→Fin n→Vantage)
    (h:∀i,Tendsto (fun k=>v k i) atTop (𝓝 (atPosition p i)))
    (g:ProofOrder p j L):
 Tendsto (fun k=> P.commonWell 3 x (P.Sched x N Y u k) (v k) L') atTop
     (𝓝 (quoteG (K:=P.Retinue x) Wₑ N A ωₑ j p u L)):=by
 unfold quoteG
 have s := funext fun i=>pose_r j (p i)
 rw [←s]
 exact P.quoteWell j x q _ _ _ _ _ _ e (fun i=>l.buys _ (u i)) h g
#print axioms reigning


lemma diadem (a b:Axis)(L L':List (Fin n))(e:L.Perm L')
   (d:ProofOrder p a L)(f:ProofOrder p b L'):
 quoteG (K:=P.Retinue x) Wₑ N A ωₑ a p u L=
 quoteG (K:=P.Retinue x) Wₑ N A ωₑ b p u L':=
   tendsto_nhds_unique
      (reigning q l a p u L L (.refl _) (fun _=>atPosition p) (fun _=>tendsto_const_nhds) d)
      (reigning q l b p u L' L e (fun _=>atPosition p) (fun _=>tendsto_const_nhds) f)
#print axioms diadem
