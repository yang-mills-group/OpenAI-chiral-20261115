import YM.SU5.Six.PointSpot
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 190000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Preen
variable (P:Spine)(x:P.Spectrum0 3)(s:ℕ)
-- center from O reduced, orientation. Width function can use abs node_i.W.B positive F0.
variable(o:Cover)
local notation "X"=> ruler P.par.block
abbrev beamU(P:Spine)(o:Cover)(i:Axis):ℕ:= (nodeC o i).natAbs+ P.calibration.ℓ+22+1
lemma suited(i:Axis) : Between P.calibration i (-ruler P.par.block * beamU P o i) (X* beamU P o i) (Calico.bands o 22):=by
 intro y h
 obtain ⟨l,r⟩:=Calico.bands_spec o h i
 change _ ≤ y i-nodeC o i at l; change y i-nodeC o i≤_ at r
 let v:=beamU P o i; have hx: (v:ℤ)≤ X*v:=le_mul_of_one_le_left (by positivity --tune
    ) (ruler_gene P.par.block)
 rw [neg_mul]
 obtain p|p:= Int.natAbs_eq (nodeC o i)
 · unfold v beamU at hx; unfold beamU; constructor <;> omega
 · unfold v beamU at hx; unfold beamU; constructor <;> omega
noncomputable def fitting: P.Apron:=⟨s,beamU P o,fun i=> Nat.zero_lt_succ _,wp P s o,(Calico.bands o 22),lining_test ..,color_wp P s o,suited P o⟩
abbrev heatU:= whenly (timeMesh P.par) s (beamU P o 3)
lemma heatU_correct:(heatU P s o:ℝ)=(fitting P s o).realWidth P 3:=(natural_time ..).symm
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "W"=>P.ManyF 3 ξ
local notation "S"=>P.seasons 3 ξ
local notation "B"=>P.wealth 3 ξ
local notation "Λ"=> fitting P s o
variable (h:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o (3:Axis))
abbrev palmY(P:Spine)(x:P.Spectrum0 3)(s:ℕ)(o:Cover)(h:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o (3:Axis)):P.ManyF 3 (P.otherSpectrum 3 3 x):=P.wealth 3 _ (P.viewF 3 _ s (birthWP P o h))
lemma rentT : flashY x (fitting P s o) 3=(S).E (heatU P s o) (palmY P x s o h):=by
 let g:=P.passesLater 3 s (beamU P o 3) (birthWP P o h)
 have hz:= Eq.trans (P.engine_view 3 (ξ) (Λ)) ((P.identical_F 3 ξ s _ g ((Λ).card_price P 3)).trans (P.releasedLater 3 ξ s _ (birthWP P o h)))
 exact (congrArg (P.wealth 3 ξ) hz).trans (P.bankHeat ..)
#check flashY
variable {d f:Cover}
private lemma housing (t: ∀ i:Axis, (↑(beamU P o i):ℤ)+(↑(beamU P o i):ℤ) < f i-d i):
 let A:=usher ((Λ).kiss P 3) (Λ); let B':= P.gridSpot s ∘ usher d f; let L:=[false,true]; P.Turnstile 3 A L B' ∧ P.Plenum A L B':=by
 intro A B' L; have g(i:Axis):P.Turnstile i A L B':= by
    refine List.pairwise_pair.mpr ?_
    change P.gridSpot s d i + (Λ).realWidth P i < P.gridSpot s f i - (Λ).realWidth P i
    rw [P.gridSpot_mul,P.gridSpot_mul]; let k:=P.spotMesh s
    have hk:=P.spotMesh_pos s; let w:=beamU P o i
    have he : ((w:ℤ):ℝ)+((w:ℤ):ℝ) < (f i:ℝ)-(d i:ℝ):=by exact_mod_cast t i
    have hw:(Λ).realWidth P i=((w:ℤ):ℝ)*k:=rfl
    rw [hw]; unfold k; exact (by nlinarith)
 exact ⟨g 3,⟨fun i=>⟨_,List.Perm.refl _,g i⟩⟩⟩
private lemma portalBasic (N:P.Apron)(L:P.Apron)(rJ:L=N.kiss P 3)(J:P.Ellis 3 x)(t:P.Turnstile 3 (usher L N) [false,true] (P.gridSpot N.s ∘ usher d f))(e:P.Plenum (usher L N) [false,true] (P.gridSpot N.s ∘ usher d f)):P.singleState 3 N.s x ((P.chartAll d L.F)*(P.chartAll f N.F))=P.bodyPair x L N (P.gridSpot N.s d) (P.gridSpot N.s f):=by
 subst L; let A:=usher (N.kiss P 3) N
 have ht(a:P.Apron) : a.full P a.s=a.F:=by change P.conveying a.s (a.s-a.s) _=_; rw [Nat.sub_self]; rfl
 have hv:P.fullScroll N.s A (usher d f) [false,true] = P.chartAll d (N.kiss P 3).F*P.chartAll f N.F:=by
    change P.chartAll d ((N.kiss P 3).full P (N.kiss P 3).s)*(P.chartAll f (N.full P N.s)*1)=_
    rw [mul_one,ht,ht]
 have hp:∀i∈[false,true], (A i).s ≤ N.s:=by rintro (_|_) _<;>exact le_rfl
 -- use composition, not rw
 let hh:=P.spot_full x A _ _ J N.s hp t e
 exact (congrArg (P.singleState 3 N.s x) hv.symm).trans (hh.trans (congrArg (fun z:Bool→Vantage=> P.commonWell 3 x A z [false,true]) (show (P.gridSpot N.s ∘ usher d f)=usher (P.gridSpot N.s d) (P.gridSpot N.s f) from (by funext i; cases i<;> rfl))))
lemma portalK (L N:P.Apron)(rJ:N=L.kiss P 3)(J:P.Ellis 3 x)(t:P.Turnstile 3 (usher N L) [false,true] (P.gridSpot L.s ∘ usher d f))(e:P.Plenum (usher N L) [false,true] (P.gridSpot L.s ∘ usher d f))(Q:W)(h:flashY x L 3=Q):
 let r:=P.gridSpot L.s f-P.gridSpot L.s d
 P.singleState 3 L.s x ((P.chartAll d N.F)*(P.chartAll f L.F))=inner ℂ Q ((S).E (Real.toNNReal (r 3-((L.realWidth P 3)+(L.realWidth P 3)))) ((P.cartage 3 ξ r) Q)):=by
 subst N; intro r; let p:=P.gridSpot L.s d; let q:=P.gridSpot L.s f; let K':P.Apron:= L.kiss P 3
 have hz:=List.pairwise_pair.mp t
 have hF:q-p ∈ P.forwardPair K' L 3:=by
    change p 3+L.realWidth P 3<q 3-L.realWidth P 3 at hz
    change L.realWidth P 3+L.realWidth P 3< q 3-p 3; linarith only [hz]
 have hB:=P.bodyPair_fwd x K' L 3 p q J hF
 let F':=fun (a b:W)=>inner ℂ a ((S).E (Real.toNNReal (r 3-((K'.realWidth P 3)+(L.realWidth P 3)))) ((P.cartage 3 ξ r) b))
 exact (portalBasic P x L _ rfl J t e).trans (hB.trans (congrArg₂ F' ((flashY_glare x L 3).trans h) h))
lemma portal_price(J:P.Ellis 3 x)(t:∀ i:Axis, ↑(beamU P o i)+ (↑(beamU P o i):ℤ) < f i-d i):
 let d':=P.gridSpot s d; let r:=P.gridSpot s f-d'; let K:=(Λ); let v:W:= (S).E (heatU P s o) (palmY P x s o h)
 P.singleState 3 s x ((P.chartAll d (K.kiss P 3).F)*(P.chartAll f K.F))=inner ℂ v ((S).E (Real.toNNReal (r 3-((K.realWidth P 3)+(K.realWidth P 3)))) ((P.cartage 3 ξ r) v)):=by
 have ht:=housing P s o t
 exact portalK P x (Λ) _ rfl J ht.1 ht.2 _ (rentT P x s o h)

#print axioms portal_price
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
