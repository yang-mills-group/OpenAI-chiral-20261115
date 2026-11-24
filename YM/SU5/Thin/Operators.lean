import SatinFixedContrastNovember4
import YM.SU5.Thin.GroundChannel
import YM.SU5.Thin.HardLight
import YM.SU5.Thin.VantagePoint

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
/-!
# Milestone B. Actual separated interaction on a thin-*operator*-limit cost

See writeup for statement including the locality and centering qualifications.
Statistic is the discrepancy of the total ACTUAL and total FACTORIZED predictions
on two independently positionable Euclidean smears of these mixed marks. (It is
NOT a claim of a positive transmission in a CENTERED/TRUNCATED reading between
the two spacetime boxes.) Includes costs for all six measures at once,
same n value as the **fixed-contrast** experiment, not promising to retain
full rank, the nonzero-energy result, etc., in width removal. Readers use fields
with resolution prescription, not just limiting operators on the vacuum. Do
not replace an estimated answer for them by using e.g. an equation in the
quotient/core of another observer. Keep that normalization on the genuine
history (see `Elected.lean` & ground costs).
-/
open DoseBill VoucherOp Theatre StrongStamp PadThin
namespace Theatre
section
variable {P:Spine}(x:P.Spectrum0 3){J:P.Ellis 3 x}{I:Type*}{n:ℕ}{b:ℕ→ℕ} (Z:I→Lead.Clan) (D:∀ i:I,P.VoucherOp x (Z i) n b)(w:I→Bool)(s:I→ℕ) (f:I→ SampleDose)(lo hi:I→ℝ)(L:List I)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H"=> P.ManyF 3 ξ
local notation "κ"=> P.enter 3 ξ
local notation "η" => P.colorZero 3 ξ
/-- Euclidean costs on any ordered list of these probes; smears before/after
in particular use these measures. `continuum` includes the joint read on the
same operator space. Not pricing all-orientation Mink properties. Always
use substantial qualification even after the width investments.
-/
structure PlayPrice : Prop where
  order : Ordered L lo hi
  interior (i:I)(_p:i∈ L) : ReadyThin (f i) (lo i) (hi i)
  footQualified (s:I→ℕ)(T:SureFoot x Z D w s f lo hi L) : (∀ᶠ t:ℕ in atTop,qualifiedLevel x Z D s L t) ∧
    (∀ (t:ℕ),qualifiedLevel x Z D s L t → P.singleState 3 t x (word (fun i=>(D i).markField (w i) (s i) t (f i)) L) = markVoice (P.ColorHil 3 (P.otherSpectrum 3 3 x)) (P.colorZero 3 (P.otherSpectrum 3 3 x)) (poseGrid x Z D w s f lo hi L t)) ∧
    Tendsto (measuredPrice x Z D w s f L) atTop (𝓝 (tentativePrice x Z D w s f lo hi L)) ∧
    ∀ (y:P.ManyF 3 (P.otherSpectrum 3 3 x)), Tendsto (fun t:ℕ=> poseGrid x Z D w s f lo hi L t (κ y)) atTop (𝓝 (κ (finished0 x Z D w s f lo hi L y)))
  passage (v:ℕ→I→ℕ)(t:∀ i∈L, Tendsto (fun n=>v n i) atTop atTop) :
    (∀ᶠ i in atTop,SureFoot x Z D w (v i) f lo hi L) ∧
    Tendsto (fun t=> tentativePrice x Z D w (v t) f lo hi L) atTop (𝓝 (answer x Z D w f lo hi L)) ∧
    ∀ y:P.ManyF 3 (P.otherSpectrum 3 3 x), Tendsto (fun i=> finished0 x Z D w (v i) f lo hi L y) atTop (𝓝 (finished x Z D w f lo hi L y))
  compare (v:L≠[]) (s:I→ℕ)(u:SureFoot x Z D w s f lo hi L)(t:ℕ)(h:qualifiedLevel x Z D s L t)(Y:P.Test→ₗ[ℂ]ℂ)(X:P.SameRawProduct t x Y) :
     Y (word (fun i=> (D i).markField (w i) (s i) t (f i)) L)=0
-- joint proof; head optional; production ∀ such experiments estimated on P
lemma pays (J:P.Ellis 3 x)(p: Ordered L lo hi)(h:∀ i∈ L,ReadyThin (f i) (lo i) (hi i))(u:P.calibration.ℓ<n): PlayPrice x Z D w f lo hi L:= by
  refine ⟨p,h,fun s T=>?_, fun v t=> ⟨ safetyPlan x Z D w f lo hi L v t h, atFinal x Z D w f lo hi L v t h,widthInvest x Z D w f lo hi L v t h⟩, fun v s z t g Y q=> losesPrediction x Z D w s f lo hi L p t g z q.marginal.factors (.inl q.matter) v u⟩
  exact ⟨apricot x Z D s L,fun t g=> live x Z D w s f lo hi L p t g T,
    gridInvest x J Z D w s f lo hi L p T,authority x J Z D w s f lo hi L T⟩
end
end Theatre
variable (P:Spine)(K:P.Register)(x:P.Spectrum0 3) (c r:ℕ→ℕ)(i:ℕ)(a:ℝ)(F G:SampleDose)(b:ℕ→ℕ) (Z W:Lead.Clan)
local notation "N"=> r i
variable (D:∀ Z:Lead.Clan, P.VoucherOp x Z (r i) b)
abbrev wedding : List Bool:= [false,true]
abbrev flagsFor (A B:Lead.Clan) (i:Bool):Lead.Clan:= if i then B else A
abbrev smearsFor (A B:SampleDose)(i:Bool):SampleDose:= if i then B else A
abbrev lEdge (i:Bool):ℝ:= if i then 0 else stopEarly
abbrev rEdge (i:Bool):ℝ:= if i then stopLate else 0
def weddingCost (L:List Bool): Prop:= PlayPrice x (flagsFor Z W) (fun i=>D (flagsFor Z W i)) id (smearsFor F G) lEdge rEdge L
def jointPrice :ℂ:= answer x (flagsFor Z W) (fun i=> D (flagsFor Z W i)) id (smearsFor F G) lEdge rEdge wedding
-- expose readings at every ruler & both singles explicitly as receipts in the book
structure OrderedCost : Prop where
  earlier : weddingCost P x r i F G b Z W D [false]
  later   : weddingCost P x r i F G b Z W D [true]
  pair    : weddingCost P x r i F G b Z W D wedding
  approx : ‖jointPrice P x r i F G b Z W D-(purePrice Z:ℂ)*(purePrice W:ℂ)‖<purePrice Z*purePrice W/2
  interaction : purePrice Z*purePrice W/2<‖jointPrice P x r i F G b Z W D‖
  margin : 0 < purePrice Z*purePrice W/2
local notation "U"=>reviewEarlierBox
local notation "V"=>reviewLaterBox
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "ℍ"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "ω"=> P.heaven 3 (P.otherSpectrum 3 3 x)
local notation "ν"=> P.seasons 3 (P.otherSpectrum 3 3 x)
-- existential P data with all the pay hypotheses & qualifications
def SeeStatic (f:Bool) : Prop:=∀ ε>0,∀ᶠ s in atTop, ∀ t:ℕ,(D Z).eligible s t→ P.asked_at t ((D Z).markField f s t (smearsFor F G f)) (if f then reviewLaterBox.invites else reviewEarlierBox.invites) ∧ ∀ k:Cover, P.asked_at t ((D Z).formMark f s t k) (Metric.ball (P.meshPose t k) ε) ∧ (D Z).formMark f s t k ∈enclave P.calibration
def SeeRoot : Prop := ((ν).ℚmeasure.diagonal ((P.tableau 3 (P.otherSpectrum 3 3 x) 0 ((D Z).operator true)) ω)) YM.Six.night ≠ 0
structure GetsThin : Prop where
 oldData : F.Normalized ∧ G.Normalized ∧ tsupport F.val ⊆ (U).invites∧ tsupport G.val ⊆ (V).invites
 retest : P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G
 oldPositions (Z:Lead.Clan) : P.spacePrice (P.RTest Z (c i) (r i)) F ⊆ (U).invites ∧ P.spacePrice (P.FTest Z (c i) (r i)) G⊆ (V).invites
 purchased : P.calibration.ℓ < r i ∧ StrictMono b
 guard : Weather P x latch downDue (r i) b
 comp (t:ℕ) : ∃! X:P.Test→ₗ[ℂ]ℂ,P.SameRawProduct t x X
 visible (Z:Lead.Clan)(f:Bool) : SeeStatic P x r i F G b Z D f
 channel (Z W:Lead.Clan) : OrderedCost P x r i F G b Z W D
 night (Z:Lead.Clan) : SeeRoot P x r i b Z D
#print axioms GetsThin
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
