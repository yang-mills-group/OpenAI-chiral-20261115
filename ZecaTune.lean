import ZecaFloat
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

include uc wc
lemma ontoSeats (p:Vantage)(q:Vantage)
 (hp:p∈U.spare.invites)(hq:q∈W.spare.invites):
 (μ ≤ -(p 3) ∧ μ≤ q 3):=by
 have h: (p 3) < U.upper 3:= (U.sparesDoor (subset_closure hp) 3 (Set.mem_univ _)).2
 have i:= (W.sparesDoor (subset_closure hq) 3 (Set.mem_univ _)).1
 exact ⟨by linarith only [uc,h],wc.trans i.le⟩

include m R b J
lemma zecaEncore (s k:ℕ)(y:P.calibration.ℓ<k)
 (f:U.upper 3+P.probeWidth s k 3<0)
 (t:0+P.probeWidth s k 3<W.lower 3)
 (A₁:∀j,U.lower j+P.probeWidth s k j<U.spare.lower j∧U.spare.upper j+P.probeWidth s k j<U.upper j)
 (A₂:∀j,W.lower j+P.probeWidth s k j<W.spare.lower j∧W.spare.upper j+P.probeWidth s k j<W.upper j)
 (p a:Vantage)(h₁:p∈U.spare.invites)(h₂:a∈W.spare.invites)
 (xa:ReadsSix (P.pointMatrix x s k (a-p)))
 (wa:ReadsSix (P.pointPrism x V w (a-p))):

 ∃ (F L:SampleDose),
 P.OnceHere x V w μ s k F L K U W ∧
 ReadsSix (P.minkPrice x D F L) ∧
 tsupport F.val ⊆ U.spare.invites ∧
 tsupport L.val ⊆ W.spare.invites:= by
 have xq(z)(p':z∈W.spare.invites):
   P.pointPrism x V w (z-p)=matchRoles G
      (fun j=>P.earlierProfile x V w μ j p)
      (fun j=>P.laterProfile x V w μ j z):=by
    obtain ⟨m₁,m₂⟩:= ontoSeats U W μ uc wc p z h₁ p'
    exact P.prism_between x g h V w μ R.cinema m p z m₁ m₂
 have b₁: p ∈ closure U.invites:=subset_closure (U.sparesDoor (subset_closure h₁))
 have b₂(z)(h:z∈W.spare.invites):z∈closure W.invites:=
    subset_closure (W.sparesDoor (subset_closure h))
 obtain ⟨q,qgo,hm⟩:= minkSequence a (fun i t=>ReadsSix (P.minkPrice x D (skate p i) (skate t i))) (P.mink_buy x A c r n w V g h T R D b p a (by
   obtain ⟨k,l⟩:=ontoSeats U W μ uc wc p a h₁ h₂;linarith) wa)

 rw [xq a h₂] at wa
 let v:=P.profile_solid x g h V w μ R.cinema m
 have j:=bothSix a q qgo p G (P.earlierProfile x V w μ) (P.laterProfile x V w μ)
       (fun i=>(v i).1) (fun i=>(v i).2) wa

 let Z:=fun i=>P.backwardRay x i s k 0
 let N:=fun i=> P.forwardRay x i s k 0
 rw [P.array_at_point x s k 0 U W J f t p a b₁ (b₂ a h₂)] at xa
 have y':=bothSix a q qgo p G Z N (fun i=>P.cold_cont ..) (fun i=>P.hot_cont ..) xa
 obtain ⟨i,⟨⟨j₁,j₂⟩,o₁,o₂⟩,m₃,l,g',ℓ⟩:=
   ((j.and y').and (hm.and ((concentrates _ _ (U.spare.doorOpen.mem_nhds h₁)).and
         (floats a q qgo _ (W.spare.doorOpen.mem_nhds h₂))))).exists
 let F:=skate p i
 let L:=skate (q i) i
 have pF:tsupport F.val ⊆ U.invites:=l.trans (subset_trans subset_closure U.sparesDoor)
 have pL:tsupport L.val ⊆ W.invites:= ℓ.trans (subset_trans subset_closure W.sparesDoor)
 have e:ReadsSix (P.pointPrism x V w (q i-p)):=xq (q i) g' ▸ j₂ -- motive?
 have e':ReadsSix (P.pointMatrix x s k (q i-p)):=by
     rw [P.array_at_point x s k 0 U W J f t p (q i) b₁ (b₂ _ g')]; exact o₂
 have hT:= P.paidReturn x s k 0 F L
      (fun z=>P.beforeTest s k 0 U f F z (pF.trans subset_closure))
      (fun z=>P.afterTest s k 0 W t L z (pL.trans subset_closure)) J
           (show ReadsSix (P.arrayReading x s k 0 F L) from o₁) y

 exact ⟨F,L,⟨m,pF,pL,⟨prescribed ..,prescribed ..⟩,⟨hT,P.reviewWardContrast K x _ _ 0 _ _ hT⟩,
     (fun z=>⟨bounded_within (P.RTest z s k) F l A₁,bounded_within (P.FTest z s k) L ℓ A₂⟩),
     j₁,p,U.sparesDoor (subset_closure h₁),q i,W.sparesDoor (subset_closure g'),i,rfl,rfl,e,e'⟩,m₃,l,ℓ⟩
#print axioms zecaEncore

#check @zecaEncore
