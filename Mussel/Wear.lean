import SatinFixedContrastNovember4
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
variable(P:Spine)(x':P.Spectrum0 3)(s t:ℕ)
local notation "K₀"=>P.calibration
local notation "V"=>P.ColorHil 3 x'
local notation "κ"=>P.colorSpace 3 x'
local notation "ω'"=>P.colorZero 3 x'
local notation "U" n:max=>P.shifts 3 n
/-- A post-clock certificate at exactly its native purchase. -/
structure Sentry (P:Spine)(s:ℕ)(f:P.Test) where
 w:ℕ
 ok:0<w
 pin:P.Card 3 s w
 val:P.voxTest 3 s pin.val=f
 care:P.voxTest 3 s pin.val∈ enclave P.calibration

namespace Sentry
variable {P s}{f g:P.Test}
def blockR (F:Sentry P s f):P.Physical 3:= P.door 3 s F.w F.ok F.pin F.care
def beam(F:Sentry P s f): (P.ColorHil 3 x').Op:= P.colorSpace 3 x' (F.blockR)
variable (F:Sentry P s f)(D:Sentry P s g)
protected theorem born(F:Sentry P s f): P.birthF 3 s f:= ⟨⟨F.pin.val,F.care⟩, F.val⟩
lemma pays(q:P.birthF 3 s f):F.beam x' (P.colorZero 3 x')=P.viewF 3 x' s q:=
 (P.awake 3 x' s F.w F.ok F.pin F.care).trans (P.holdsF 3 x' s q ⟨F.pin.val,F.care⟩ F.val).symm
lemma grows_pay {v:s≤t}: let r:=P.conveying s (t-s)
    let K':=furnished P.run P.large s P.history 3 false _ F.pin t v
    P.voxTest 3 t K'.val=r f:=by
 intro r K'
 exact (P.convey_vox 3 F.pin v).symm.trans (congrArg r F.val)
def grows(v:s ≤t): Sentry P t (P.conveying s (t-s) f) where
 w:=P.par.R.L.val^(t-s)*F.w
 ok:=Nat.mul_pos (pow_pos P.par.R.L.property _) F.ok
 pin:=furnished P.run P.large s P.history 3 false _ F.pin t v
 val:=F.grows_pay t
 care:= P.refine_keeps s _ F.care (t-s)
lemma kept(v:s ≤ t):(F.grows t v).blockR=F.blockR:=Subtype.ext ((P.upper_tab 3 _ _ F.ok F.pin t v).symm)
lemma beams_kept(v:s ≤ t):(F.grows t v).beam x'=F.beam x':=congrArg κ (F.kept t v)
/-- multiplication up time-axis. -/
def joined:Sentry P s (f* P.shifts 3 (F.w:ℤ) g) where
 w:=F.w+D.w
 ok:=add_pos F.ok D.ok
 pin:=edit P.run P.large s 3 false _ _ F.pin D.pin
 val:=by
    exact Eq.trans (Subtype.ext (editor ..) : P.voxTest 3 s _=P.voxTest 3 s F.pin.val * P.shifts 3 (F.w:ℤ) (P.voxTest 3 s D.pin.val)) (congrArg₂ (·*·:P.Test→P.Test→P.Test) F.val (congrArg (P.shifts 3 (F.w:ℤ)) D.val))
 care:=by
    refine (Eq.mpr (congrArg (fun y:P.Test=>y∈enclave K₀) (show P.voxTest 3 s _=P.voxTest 3 s F.pin.val*P.shifts 3 (F.w:ℤ) (P.voxTest 3 s D.pin.val) from Subtype.ext (editor ..))) ?_)
    exact Subalgebra.mul_mem _ F.care (P.shifts_keep 3 _ D.care)
lemma joined_buy : F.blockR*D.blockR=(F.joined D).blockR:=Subtype.ext (P.concat ..)
lemma joined_pays: F.beam x' (D.beam x' ω')=P.viewF 3 x' s (F.joined D).born :=by
 let W :P.Physical 3:=F.blockR
 let X:=D.blockR
 have ht:(κ W)*(κ X)= (F.joined D).beam x' := (map_mul κ W X).symm.trans (congrArg κ (F.joined_buy D))
 exact (congrArg (fun a:(P.ColorHil 3 x').Op=> a (P.colorZero 3 x')) ht).trans ((F.joined D).pays x' _)
lemma joint_future (b:P.birthF 3 s g): F.beam x' (P.viewF 3 x' s b)=P.viewF 3 x' s (F.joined D).born:=
 (congrArg (fun y:(P.ColorHil 3 x').space=> F.beam x' y) (D.pays x' b).symm).trans (F.joined_pays x' D)
end Sentry
#print axioms Sentry.joint_future
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
