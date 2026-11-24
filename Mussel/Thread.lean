import Mussel.Harvest
import Mussel.Wear
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
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
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Sentry
variable {s:ℕ}{f:P.Test}
/-- unrestricted purchase last card -/
def catchV(h:P.birthF 3 s f):Sentry P s f:=by
 let k:= P.emmigrant 3 s h; let z:= P.fits 3 s k.val
 let F:=z.choose_spec.2.choose
 have e:F.val=k.val:=z.choose_spec.2.choose_spec
 let ei:=congrArg (P.voxTest 3 s) e
 exact ⟨z.choose,z.choose_spec.1,F,ei.trans (P.documented 3 s h), (congrArg (fun p:P.Test=>p∈enclave P.calibration) ei).mpr k.property⟩
end Sentry
-- join at later regulator t=c i. cast W fixed. future at spatial chart z. gap W.
noncomputable def collar (Z:Lead.Clan)(P:Spine)(t n w:ℕ)(z:Cover):P.Test:=
 P.luggage 3 (look 3) (fun i=> z i.val) (P.shifts 3 w (P.defaultR Z n))
variable (t n w:ℕ)(z:Cover)
lemma birthT : P.birthF 3 t (collar Z P t n w z):=
 P.certify 3 t (look 3) _ (P.passesLater 3 t w (brightR P Z t n)) -- .. syntax
local notation "E"=>(P.physicalEnergy 3 ξ).E
lemma collarPV :P.viewF 3 ξ t (birthT (P:=P) Z t n w z)=P.truck 3 ξ (P.vtile t z) (E (whenly (timeMesh P.par) t w) ((purity Z)⁻¹ • P.shard x Z t n)) :=by
 let K':=P.defaultR Z n; let M:= P.truck 3 ξ (P.vtile t z)
 let J':=brightR P Z t n; have h:P.birthF 3 t K':=J'
 let D:= P.passesLater 3 t w h
 let T':= E (whenly (timeMesh P.par) t w)
 exact (P.ship_ideal 3 ξ t (look 3) (fun i=>z i.val) D).trans (congrArg (fun a:G=>M a) ((P.releasedLater 3 ξ t w h).trans (congrArg (fun a:G=>T' a) (shine P Z t n x))))
-- ability to fuse w extra gap at Ww.
variable (s:ℕ){f:P.Test}(Kpp:Sentry P s f)
abbrev thickStep(P:Spine)(s t w:ℕ):ℕ:=P.par.R.L.val^(t-s)*w
lemma step_when(v:s ≤ t): whenly (timeMesh P.par) t (thickStep P s t w)=whenly (timeMesh P.par) s w:=by
 let T' := timeMesh P.par
 ext
 refine (natural_time T' t (thickStep P s t w)).symm.trans ((?_:bell T' t ↑(thickStep P s t w)=bell T' s (w:ℤ)).trans (natural_time T' s w))
 unfold thickStep; push_cast; exact refineZ T' s t v (w:ℤ)

/-- clocked composite formula. Armor.w paid earlier, collar extra ticks at same physical width.
Delivered at i chosen arbitrarily large depending on s. -/
def ribbon := P.conveying s (t-s) f * P.shifts 3 ((thickStep P s t Kpp.w):ℕ) (collar Z P t n (thickStep P s t Kpp.w) z)
#check ribbon
abbrev playClock(v:s ≤ t): Sentry P t (ribbon Z t n z s Kpp):= (Kpp.grows t v).joined (Sentry.catchV (birthT ..))
lemma receipt_transfer (v:s ≤ t):
    P.viewF 3 ξ t (playClock (P:=P) Z t n z s Kpp v).born=
    (Kpp.beam ξ) (P.truck 3 ξ (P.vtile t z) (E (whenly (timeMesh P.par) s Kpp.w) ((purity Z)⁻¹ • P.shard x Z t n))):=by
 let w:=thickStep P s t Kpp.w; let X:=P.ColorHil 3 ξ
 let p:= birthT (P:=P) Z t n w z
 let Y:=P.viewF 3 ξ t p
 let M:=P.truck 3 ξ (P.vtile t z)
 let a:= ((purity Z)⁻¹ • P.shard x Z t n:X)
 have k1: Y=M (E (whenly (timeMesh P.par) t w) a):= collarPV ..
 have k2:= congrArg (fun b:ℝ≥0=>M (E b a)) (step_when (P:=P) t Kpp.w s v) -- arg order
 exact ((Kpp.grows t v).joint_future ξ (Sentry.catchV p) p).symm.trans (congrArg₂ (fun (F:X.Op)(x:X)=>F x) (Kpp.beams_kept ξ t v) (k1.trans k2))

end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
