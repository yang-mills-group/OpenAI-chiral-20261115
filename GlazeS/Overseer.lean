import GlazeS.CastLight
import GlazeS.Locations
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
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
variable (P:Spine) (F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(s t:ℕ)(A:SampleDose)
local notation "c"=>central P F s
local notation "M"=>dealt A c
-- enrolled mark at s; no vacuum subtraction yet. Only local gauge, singlet.
abbrev callix (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(s:ℕ):P.Test:= ((basket P.par.R.L C D F s:ℝ):ℂ) • etui P s s (cellar P F s)
lemma enroll:P.birthF 3 s (callix P F C D s):= P.birthScale _ _ (certificate P F s s)
lemma round_r :P.viewF 3 x s (enroll P F C D s)= recoup P F C D x s s:=P.sixWard_view_scale x s ((basket P.par.R.L C D F s:ℝ):ℂ) (certificate P F s s)
def wageRoll(s t:ℕ)(W:P.Test)(a:SampleDose):P.Test:= ∑ i∈ P.usedGrid t a,P.activation t a i • gibbert P s t W i
def athlete:=wageRoll P s t (callix P F C D s) (dealt A (central P F s))
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "H"=>P.ColorHil 3 ξ
local notation "u"=>P.meshPose t
local notation "Ψ"=>P.physicalEnergy 3 ξ
local notation "G₀"=>recoup P F C D (ξ) s s
-- orientation kernel after casting.Occupied.U positivity from M support.
noncomputable def arts(P:Spine)(x:P.Spectrum0 3)(s t:ℕ)(g:P.ColorHil 3 (P.otherSpectrum 3 3 x))(a:SampleDose):P.ColorHil 3 (P.otherSpectrum 3 3 x):=∑ i∈P.usedGrid t a, P.activation t a i • (P.truck 3 (P.otherSpectrum 3 3 x) (P.vtile t i)) ((P.physicalEnergy 3 (P.otherSpectrum 3 3 x)).E ((P.meshPose t i 3).toNNReal) g)
lemma wagesponsor (p:s ≤ t)(v:∀ y∈tsupport A.val,tidal P F s ≤ y 3)(i:Cover)(h:i ∈ P.usedGrid t (dealt A (central P F s))):0 ≤ i 3:=by
 apply (bell_le (timeMesh P.par) t 0 _).mp
 specialize v _ (pay_shift A (c) ((P.usedPose t (M) i).mp h)); rw [Pi.add_apply,center3] at v
 rw [show bell (timeMesh P.par) t 0=0 from by simp [bell]]; change tidal P F s ≤ bell (timeMesh P.par) t (i 3)+ tidal P F s at v; linarith
lemma paidtravel (p:s≤t)(v:∀ y∈tsupport A.val,tidal P F s ≤ y 3) (i:Cover)(h:i ∈ P.usedGrid t (dealt A (central P F s))):
 ∃ q:P.birthF 3 t ((P.activation t (dealt A (central P F s)) i) • gibbert P s t (callix P F C D s) i), P.viewF 3 (P.otherSpectrum 3 3 x) t q=(P.activation t (dealt A (central P F s)) i) • (P.truck 3 (P.otherSpectrum 3 3 x) (P.vtile t i)) ((P.physicalEnergy 3 (P.otherSpectrum 3 3 x)).E ((P.meshPose t i 3).toNNReal) (G₀)):=by
 let e0:=enroll P F C D s; let q:=fill_gossip P s t (P.otherSpectrum 3 3 x) e0 p i (wagesponsor P F s t A p v i h); let z:=q.choose; let e:=q.choose_spec
 refine ⟨P.birthScale _ _ z,(P.sixWard_view_scale _ t _ z).trans (congrArg (fun a:P.ColorHil 3 ξ=> P.activation t (M) i • a) (e.trans (congrArg (fun w:P.ColorHil 3 ξ=> P.truck 3 (ξ) (P.vtile t i) ((Ψ).E ((u i 3).toNNReal) w)) (round_r P F C D (P.otherSpectrum 3 3 x) s)))) ⟩
lemma gland (p:s≤t)(v:∀ y∈tsupport A.val,tidal P F s ≤ y 3):∃ h:P.birthF 3 t (athlete P F C D s t A),P.viewF 3 (P.otherSpectrum 3 3 x) t h=arts P x s t (G₀) (M):=by
 exact P.birthSum (P.otherSpectrum 3 3 x) _ _ _ _ (paidtravel P F C D x s t A p v)
-- att defs had params x section? #check
#check athlete
#check fill_gossip
#print axioms gland
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
