import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
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
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
open Py.Rate.Pitching.Focus (Morn)
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "Ξ" s:max=> agent P d C D s B Z
local notation "v"=> PledgeT.wp -- unused
local notation "k" s:max=> offer_update P d C D s B Z
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "zQ" s:max=> MiterT.central P d s
variable (s t:ℕ)(Q:Cover)
noncomputable def schema(n:ℕ)(F:SampleDose):P.Test:= Nat.rec (motive:=fun _=> SampleDose→P.Test) (fun A=>chunk B Z d C D s t A) (fun _ g A=> (φ s)⁻¹ • (g (shuf A (P.macroStep s))-g A)) n F
noncomputable def works(n:ℕ)(F:SampleDose):H:= Nat.rec (motive:=fun _=> SampleDose→(H).space) (fun A=>vistaH B Z d C D s A) (fun _ g A=> (φ s)⁻¹ • (g (shuf A (P.macroStep s))-g A)) n F
lemma rSchema (n:ℕ)(F:SampleDose): schema B Z d C D s t (n+1) F=(φ s)⁻¹ • (schema B Z d C D s t n (shuf F (P.macroStep s))-schema B Z d C D s t n F):=rfl
noncomputable def macroZ(n:ℕ)(i:Cover):P.Test:=Nat.rec (motive:=fun _=>Cover→P.Test) (fun i=>Broker.pilot P (offer_update P d C D s B Z) t i (Ξ s).question) (fun _ f i=> (φ s)⁻¹ • (f (i+cursor P s t)-f i)) n i
local notation "μ" n:max i:max=>macroZ B Z d C D s t n i
#check Broker.pilot
lemma face_in (h:s ≤ t)(n:ℕ)(F:SampleDose): schema B Z d C D s t n F= ∑ i∈P.usedGrid t (dealt F (zQ s)), P.activation t (dealt F (zQ s)) i • (μ n i):=by
 induction n generalizing F with
 | zero=>rfl
 | succ n ih=>
    rw [rSchema,ih,ih]
    rw [fore P F s t h,Finset.sum_map]
    -- change.Sums
    let R':=zQ s
    change (φ s)⁻¹ • ((∑ i∈P.usedGrid t (dealt F R'),P.activation t (dealt (shuf F _) R') (i+cursor P s t) • (μ n (i+cursor P s t)))-_)=_
    simp_rw [beams P F s t h]; rw [← Finset.sum_sub_distrib,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_
    rw [← smul_sub,smul_comm]; rfl
-- supports center.Y.Shift wobble.Power n
noncomputable def oval(n:ℕ)(i:Cover):Finset Cover:=Nat.rec (motive:=fun _=> Cover→Finset Cover) (fun i=> (Ξ s).swept t i) (fun _ f i=>f (i+cursor P s t)∪f i) n i
local notation "τ" n:max i:max=>oval B Z d C D s t n i
lemma ameter(n:ℕ)(i:Cover): μ n i∈ bay P.calibration (τ n i) true∧(μ n i)∈enclave P.calibration:=by
 induction n generalizing i with
 | zero=> exact ⟨(Ξ s).in_sweep t _,(Ξ s).in_charge t _⟩
 | succ n ih=>
    let A(i:Cover):= μ n i
    let TA(i:Cover):=τ n i
    let z:=i+cursor P s t; let B:= bay P.calibration (TA z∪TA i) true; let E:=enclave P.calibration
    exact ⟨B.smul_mem (B.sub_mem (tallerBay P.calibration _ _ subset_union_left (ih z).1) (tallerBay P.calibration _ _ subset_union_right (ih i).1)) _,E.smul_mem (E.sub_mem (ih z).2 (ih i).2) _⟩
noncomputable abbrev tiny(n:ℕ):ℝ:= 4*Hemlock.radius P d s +(n:ℝ)*P.macroStep s
variable (u:s ≤ t)(h0:offer_update P d C D s B Z ≤ t)
include u h0
lemma legs(n:ℕ)(i:Cover){y:Vantage}(hq:y ∈ P.pinFoot t (τ n i))(j:Axis): |y j - (P.meshPose t i+zQ s) j| ≤ tiny (P:=P) d s n:=by
 induction n generalizing i y with
 | zero=>simpa only [tiny,Nat.cast_zero,zero_mul,add_zero] using (Ξ s).location_leg t i h0 (deputized P d C D s B Z).coordinates hq j
 | succ n hi=>
    let x:=i+cursor P s t
    change y ∈ P.pinFoot t ((τ n x)∪τ n i) at hq
    rw [P.pin_union] at hq; let e:=tiny (P:=P) d s n
    have ht:tiny (P:=P) d s (n+1)=e+P.macroStep s:=by unfold e tiny; push_cast; ring
    rw [ht]; rcases hq with H1|H2
    · have h':=hi x H1; unfold x at h'; rw [verse P s t u] at h'
      let z:Vantage:=aislePt 3 (P.macroStep s)
      let a:=P.meshPose t i+ zQ s
      change |y j-a j|≤_; rw [show y j-a j=y j- ((P.meshPose t i+z+zQ s) j)+z j from ?_]; swap; · unfold a; simp only [Pi.add_apply]; ring
      exact (abs_add_le ..).trans (add_le_add h' (location_h _ (P.macroStep_pos _|>.le) _))
    exact (hi i H2).trans (le_add_of_nonneg_right (P.macroStep_pos _|>.le))
noncomputable abbrev veil(U:SampleDose): Finset Cover:=P.usedGrid t (dealt U (zQ s))
lemma commissioned (U:SampleDose)(n:ℕ) (i:Cover)(hi:i∈ veil (P:=P) d s t U): ∃ y∈ tsupport U.val,
 P.asked_at t (μ n i) {z|∀ j:Axis, |z j-y j| ≤ tiny (P:=P) d s n} ∧ (μ n i)∈enclave P.calibration:=by
 refine ⟨P.meshPose t i+zQ s, pay_shift U (zQ s) ((P.usedPose ..).mp hi), ⟨τ n i,(ameter B Z d C D s t n i).1, fun _ h j=> legs B Z d C D s t u h0 n i h j⟩,(ameter B Z d C D s t n i).2⟩
#check @face_in
#print axioms commissioned
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
