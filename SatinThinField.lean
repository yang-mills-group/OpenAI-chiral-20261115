import SatinFixedContrastNovember4
import SatinThinLoss

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 28000
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
open Aria Casting Six MacroGrid
/-!
## An intrinsic thin trial on the elected regulator

Keep the short string minus its (positive-time) translate as the local neutral
composite; test thinner and thinner such differences. Take also a
first-derivative renormalization in physical time units (in addition to the
`Lead.sing` normalization already in the string). The two half projections of
the CAR source, gauge factor on the path and Fock ordering per string are given
e.g. by `front_read`; see also the `Elected.input_formula` style formulas
(i.e. `Spine.input_formula`) and `Spine.six_families, Spine.bare_chiral`.
The difference counterterm gives exact centering on the elected state (also
after promotion as used here); no additional mean subtraction. No padding-only
change, no change of sea, transfer, normalization of Schwinger readings or
character. 

Result: negative. Even with this growing renormalization the actual readings
(all six) converge to *zero*, at fixed strictly separated time supports. In
particular the fine-grid limit and subsequent width limit here do NOT produce
the desired discrepancy. Failures are on the same x at the very same smears
where the width-retaining experiment worked. The `SatinThinLoss` file prices
also moving smears and normalization and gives strong convergence (to zero)
of the continuous-sector vectors even there.
-/

open Set
variable (P:Spine)(s n t:ℕ)(Z W:Lead.Clan)(F G:SampleDose)

/-- Inverse physical offset of the subtraction in `experimentBody`. -/
def thinAmp : ℂ := (↑(P.increment s n):ℂ)⁻¹

def sheetMinus : P.Test :=
    star (P.thinAmp s n) • P.prepared t (P.RTest Z s n) F

def sheetPlus : P.Test :=
    P.thinAmp s n • P.prepared t (P.FTest W s n) G -- uses W G? Z unused argument order

private lemma dual_afford (c r:ℕ→ℕ) : P.UpToTick c r (fun i=> P.thinAmp (c i) (r i)) := by
  refine ⟨1,Eventually.of_forall fun i=>?_⟩
  let z:ℂ:=↑(P.increment (c i) (r i))
  change ‖z⁻¹*z‖≤1
  by_cases H:z=0 <;> simp [H]

variable (x:P.Spectrum0 3)
/-- The asserted endpoints use the ACTUAL elected insertion `singleState` at t
(not taking an unelected period-vacuum proxy). Strong smearing endpoints in its
actor spaces are included as well; Chronological pairing version only. -/
def thinArray : CrossRead := Matrix.of fun Z W => P.singleState 3 t x
     ((P.sheetMinus s n t Z F) * P.sheetPlus s n t W G)

def costArray (a:ℝ) : CrossRead := Matrix.of fun Z W=> star (P.thinAmp s n) * P.thinAmp s n *
  P.arrayReading x s n a F G Z W


private theorem cross_smul {X:Type} [Ring X][Algebra ℂ X] (l:X→ₗ[ℂ]ℂ) (a b:ℂ)(y z:X):
    l ((a • y)*(b • z))=a*b*l (y*z):=by
  rw [smul_mul_assoc,mul_smul_comm,map_smul,map_smul]; simp only [smul_eq_mul,mul_assoc]

private lemma six_scaling (Y:ℕ→CrossRead)(y:CrossRead)(w:ℂ)(p:Tendsto Y atTop (𝓝 y)) :
    Tendsto (fun t=> Matrix.of fun i j=> w * Y t i j) atTop (𝓝 (Matrix.of fun i j=> w*y i j)):=
  tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>
    (((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp p i) j)).const_mul w)

theorem thin_at (x:P.Spectrum0 3) : P.thinArray s n t F G x Z W=
    star (P.thinAmp s n)*P.thinAmp s n* P.arrayFine x s n t F G Z W :=
  cross_smul (P.singleState 3 t x) _ _ (P.prepared t (P.RTest Z s n) F) (P.prepared t (P.FTest W s n) G)

theorem gridThin (a:ℝ)(h:Tendsto (fun t=>P.arrayFine x s n t F G) atTop (𝓝 (P.arrayReading x s n a F G))) :
    Tendsto (fun t=> P.thinArray s n t F G x) atTop (𝓝 (P.costArray s n F G x a)) :=
  (six_scaling _ _ (star (P.thinAmp s n) * P.thinAmp s n) h).congr fun t=> funext₂ fun i j=>
    (P.thin_at ..).symm

private theorem lin_zero {X:Type} [AddCommGroup X][Module ℂ X](l:X→ₗ[ℂ]ℂ)(a:ℂ)(y:X)(h:l y=0):l (a • y)=0:=by rw [map_smul,h,smul_zero]

open Six
/-- At every width and grid height where the chronology is met, including
canonical comparison at that very height. -/
structure TickRecording (Kkk:P.Register)(a:ℝ) : Prop where
  negative : ∀ Z:Lead.Clan,P.WallBefore (P.RTest Z s n) F a
  positive : ∀ Z:Lead.Clan,P.WallAfter (P.FTest Z s n) G a
  posed Z W: Disjoint (P.spacePrice (P.RTest Z s n) F) (P.spacePrice (P.FTest W s n) G)
  realPrice Z W: (P.thinArray s n t F G x Z W)=
    (P.spirits Kkk 3 x (P.slotHole t (P.sheetMinus s n t Z F * P.sheetPlus s n t W G)))
  center Z: P.singleState 3 t x (P.sheetMinus s n t Z F)=0 ∧ P.singleState 3 t x (P.sheetPlus s n t Z G)=0
  forecast Z W (X:P.Test→ₗ[ℂ]ℂ): Factors P.calibration X→ MatterWard P.calibration X ∨ GaugeWard P.calibration X →
    X (P.sheetMinus s n t Z F * P.sheetPlus s n t W G)=0
  trueComparison : ∃ X:P.Test→ₗ[ℂ]ℂ, Comparison P.calibration (P.singleState 3 t x) X ∧ X 1=1 ∧ GaugeWard P.calibration X ∧ MatterWard P.calibration X ∧
    ∀ Z W:Lead.Clan,X ((P.sheetMinus s n t Z F)*(P.sheetPlus s n t W G))=0

theorem recording (Kkk:P.Register)(a:ℝ)(u:∀ Z:Lead.Clan,P.WallBefore (P.RTest Z s n) F a)(v:∀ Z:Lead.Clan,P.WallAfter (P.FTest Z s n) G a)(h:P.calibration.ℓ<n)(p:s≤t):
    P.TickRecording s n t F G x Kkk a := by
  have he (Z W:Lead.Clan)(X:P.Test→ₗ[ℂ]ℂ)(b:Factors P.calibration X)(q:MatterWard P.calibration X ∨ GaugeWard P.calibration X) : X ((P.sheetMinus s n t Z F)*(P.sheetPlus s n t W G))=0:= by
    have hx:X (P.prepared t (P.RTest Z s n) F * P.prepared t (P.FTest W s n) G)=0:=
      congrArg (fun A:CrossRead=> A Z W) (P.forecast s n t h p F G a u v X b q)
    exact (cross_smul X (star (P.thinAmp s n)) (P.thinAmp s n) (P.prepared t (P.RTest Z s n) F) (P.prepared t (P.FTest W s n) G)).trans ((congrArg ((star (P.thinAmp s n)*P.thinAmp s n)*·) hx).trans (mul_zero _))
  refine ⟨u,v,fun Z W=> P.test_apart _ _ a _ _ (u Z) (v W),fun Z W=>(P.oneCup Kkk 3 x _ _).symm,fun Z=>?_, he,?_⟩
  · exact ⟨lin_zero (P.singleState 3 t x) (star (P.thinAmp s n)) _ (P.Dose_zero t _ F x (P.body_central x s n Z).2 p),lin_zero (P.singleState 3 t x) (P.thinAmp s n) _ (P.Dose_zero t _ G x (P.body_central x s n Z).1 p)⟩
  let H := P.comparator t x
  let X := H.choose
  exact ⟨X,H.choose_spec.1,H.choose_spec.2.1,H.choose_spec.2.2.1,H.choose_spec.2.2.2,fun Z W=>he Z W X H.choose_spec.1.factors (.inl H.choose_spec.2.2.2)⟩

structure Walls (a:ℝ) : Prop where
  beforeQ : ∀ Z, P.WallBefore (P.RTest Z s n) F a
  afterQ : ∀ Z,P.WallAfter (P.FTest Z s n) G a

private lemma open_wall (v:Vantage)(p':v∈reviewEarlierBox.invites): v 3<(-1:ℝ):=(p' (3:Axis) (Set.mem_univ _)).2
private lemma open_wall_pos (v:Vantage)(p':v∈reviewLaterBox.invites): (1:ℝ)<v 3:=(p' (3:Axis) (Set.mem_univ _)).1

variable {F G}
theorem windowWall (h:P.probeWidth s n 3<1)(a:tsupport F.val⊆ reviewEarlierBox.invites)(b:tsupport G.val⊆reviewLaterBox.invites) : P.Walls s n F G 0:= by
  constructor
  · intro Z v hv; change v 3+P.probeWidth s n 3<(0:ℝ)
    linarith [open_wall v (a hv)]
  intro Z v hv; change 0+P.probeWidth s n 3<v 3
  linarith [open_wall_pos v (b hv)]

/-- Per placement, including support of the implementing mark at the finer t. -/
structure Spent_LocalFieldBounds (A:P.Apron)(v:Cover):Prop where
  gauge: P.issuing t A v∈ enclave P.calibration
  paid: P.issuing t A v∈ bay P.calibration (P.plotSet t A v) true
  stays: P.pinFoot t (P.plotSet t A v) ⊆ P.Aperture A (P.meshPose t v)

theorem spentThin (A:P.Apron)(v:Cover)(e:A.s≤t) : P.Spent_LocalFieldBounds t A v :=
  ⟨P.issuing_color t v A,P.issuing_support t v A,P.inside_now t v A e⟩

private lemma asksScale (Y:P.Test)(z:ℂ)(J:Set Vantage)(b:P.asked_at t Y J) : P.asked_at t (z • Y) J:=
  b.imp fun _ p=>⟨Subalgebra.smul_mem _ p.1 _,p.2⟩

structure LocalTick : Prop where
 gaugeLeft:P.sheetMinus s n t Z F∈enclave P.calibration
 gaugeRight:P.sheetPlus s n t W G∈enclave P.calibration
 regionLeft:P.asked_at t (P.sheetMinus s n t Z F) (P.spacePrice (P.RTest Z s n) F)
 regionRight:P.asked_at t (P.sheetPlus s n t W G) (P.spacePrice (P.FTest W s n) G)
 posesLeft(v:Cover):P.Spent_LocalFieldBounds t (P.RTest Z s n) v
 posesRight(v:Cover):P.Spent_LocalFieldBounds t (P.FTest W s n) v

lemma localTick (p:s≤t) : P.LocalTick s n t Z W (F:=F) (G:=G):= by
 refine { gaugeLeft:= Subalgebra.smul_mem (enclave _) (P.prepared_color t _ F) _
          gaugeRight:=Subalgebra.smul_mem (enclave _) (P.prepared_color t _ G) _
          regionLeft:=P.asksScale t _ _ _ (P.prepared_at t _ F p)
          regionRight:=P.asksScale t _ _ _ (P.prepared_at t _ G p)
          posesLeft:=fun i=>P.spentThin t _ i p
          posesRight:=fun i=>P.spentThin t _ i p }

variable (F G)
private lemma boxed (a:tsupport F.val⊆reviewEarlierBox.invites) (b:tsupport G.val⊆reviewLaterBox.invites)(h:F.Normalized)(p:G.Normalized):
    StaysBack (fun _=>F) (fun _=>G) (fun _=>0) (1/2):= by
  refine ⟨by norm_num,.of_forall fun _=>h,.of_forall fun _=>p,?_,?_⟩
  · apply Eventually.of_forall; intro i v t; push_cast
    linarith [open_wall v (a t)]
  apply Eventually.of_forall; intro i v t; push_cast
  linarith [open_wall_pos v (b t)]

variable (c r:ℕ→ℕ)
local notation3 "ξ" => P.otherSpectrum 3 3 x
local notation "H" => P.ColorHil 3 ξ
local notation "β" => P.enter 3 ξ

structure Crossing : Prop where
  pinEach : P.thinArray s n t F G x Z W=
    inner ℂ ((P.thinAmp s n) • (P.preVector x s t n Z F 0)) ((P.thinAmp s n) • (P.postVector x s t n W G 0))
  limitLeft : Tendsto (fun t=> P.thinAmp s n • P.preVector x s t n Z F 0) atTop
    (𝓝 (β (P.thinAmp s n • P.landingCost x s n Z F 0)))
  limitRight : Tendsto (fun t=> P.thinAmp s n • P.postVector x s t n W G 0) atTop
    (𝓝 (β (P.thinAmp s n • P.launchCost x s n W G 0)))
  innerReal : P.costArray s n F G x 0 Z W =
    inner ℂ (β (P.thinAmp s n • P.landingCost x s n Z F 0))
      (β (P.thinAmp s n • P.launchCost x s n W G 0))
  rightSeed: ∃ h:P.birthF 3 t (P.sheetPlus s n t W G), P.viewF 3 ξ t h=
    P.thinAmp s n • P.postVector x s t n W G 0

private lemma scalah {Q:Hilbert}(a b:ℂ)(v w:Q.space):
    star a*b* inner ℂ v w = inner ℂ (a • v) (b • w) := by
  rw [inner_smul_left,inner_smul_right,mul_assoc]; rfl

private lemma sendLanding {Q R:Hilbert}(L:Q.space →ₗᵢ[ℂ] R.space)(u:ℕ→R)(v:Q)(q:Tendsto u atTop (𝓝 (L v)))(a:ℂ):
    Tendsto (fun i=>a • u i) atTop (𝓝 (L (a • v))):=by
  rw [map_smul]; exact Tendsto.smul tendsto_const_nhds q

theorem crossing (J:P.Ellis 3 x)(p:P.Walls s n F G 0)(q:s≤t) :
    P.Crossing s n t Z W F G x:={
      pinEach:=(P.thin_at ..).trans ((congrArg (fun w=>star (P.thinAmp s n)*P.thinAmp s n*w) (P.pinPricing x s t n Z W F G 0 (p.beforeQ Z) (p.afterQ W) q)).trans (scalah (Q:=H) ..))
      limitLeft:=sendLanding (Q:=P.ManyF 3 ξ) (R:=H) β _ _ (P.toLand x s n Z F 0 J) _
      limitRight:=sendLanding (Q:=P.ManyF 3 ξ) (R:=H) β _ _ (P.toLaunch x s n W G 0 J) _
      innerReal:=(scalah (Q:=P.ManyF 3 ξ) _ _ (P.landingCost x s n Z F 0) (P.launchCost x s n W G 0)).trans ((β).inner_map_map ..).symm
      rightSeed:= (P.positive_exposure x s t n W G (p.afterQ _) q).elim (fun h hp=>⟨P.birthScale t _ h,(P.sixWard_view_scale ..).trans (congrArg ((P.thinAmp s n) • ·) hp)⟩) }


/-- The left question also gets identification as a positive seed (use reflection
through the measurement wall at zero; we only need equality with the Crossing
vector in the independent fine-position *limit*). -/
private lemma flipback(U:SampleDose): flipDose (flipDose U 3) 3=U:=by
  cases U with | mk v h q=>
    unfold flipDose; congr 1
    funext x; exact congrArg v (reflectPose_twice 3 x)
private lemma flipped (v:P.Walls s n F G 0): P.WallAfter (P.FTest Z s n) (flipDose F 3) 0:= by
  intro y h; rw [flipBudget] at h
  let a:=poseMirror 3 y
  have he:= (v.beforeQ Z) a h
  change opposeR 3 y 3+P.probeWidth s n 3<0 at he; change 0+P.probeWidth s n 3<y 3
  rw [show opposeR 3 y 3= -y 3 from if_pos rfl] at he
  linarith only [he]

set_option linter.unusedSectionVars false
structure LeftSeed : Prop where
  exactSeed: ∃ h:P.birthF 3 t (P.reflectTest 3 (P.sheetMinus s n t Z F)), P.viewF 3 ξ t h=P.thinAmp s n • P.postVector x s t n Z (flipDose F 3) 0
  mirrorLimit : Tendsto (fun t=>P.thinAmp s n • P.postVector x s t n Z (flipDose F 3) 0) atTop
    (𝓝 (β (P.thinAmp s n • P.landingCost x s n Z F 0)))

theorem reflectedSeed (J:P.Ellis 3 x)(v:P.Walls s n F G 0)(q:s≤t):
    P.LeftSeed s n t Z F x:= by
  let Y:=P.prepared t (P.RTest Z s n) F
  let V:=P.prepared t (P.FTest Z s n) (flipDose F 3)
  have hu: Y=P.reflectTest 3 V:=
    (congrArg (P.prepared t (P.RTest ..)) (flipback F).symm).trans (P.prepared_opposition t _ _ 3)
  let amp:= P.thinAmp s n
  have he:P.reflectTest 3 (P.sheetMinus s n t Z F) = amp • V:=
    ((map_smulₛₗ (P.reflectTest 3) (star amp) Y).trans (congrArg₂ (· • · : ℂ→P.Test→P.Test) (star_star amp) ((congrArg (P.reflectTest 3) hu).trans (aureoleTwice ..))))
  let l:= P.positive_exposure x s t n Z (flipDose F 3) (P.flipped s n Z F G v) q
  refine { exactSeed := ?_
           mirrorLimit := ?_ }
  · exact (congrArg (fun v:P.Test=> ∃ h:P.birthF 3 t v,P.viewF 3 ξ t h=amp • P.postVector x s t n Z (flipDose F 3) 0) he).mpr (l.elim fun h hp=> ⟨P.birthScale t amp h,(P.sixWard_view_scale ..).trans (congrArg (amp • ·) hp)⟩ :
      ∃ h:P.birthF 3 t (amp • V),P.viewF 3 ξ t h=amp • P.postVector x s t n Z (flipDose F 3) 0)
  have hl:P.landingCost x s n Z F 0=P.launchCost x s n Z (flipDose F 3) 0:=
    (congrArg (fun U:SampleDose=>P.landingCost x s n Z U 0) (flipback F).symm).trans (P.poseFlipCost x s n Z (flipDose F 3))
  -- avoid rewriting
  exact (congrArg (fun y : (P.ManyF 3 ξ).space=> Tendsto (fun t=> amp • P.postVector x s t n Z (flipDose F 3) 0) atTop (𝓝 (β (amp • y)))) hl).mpr
    (sendLanding (Q:=P.ManyF 3 ξ) (R:=(P.ColorHil 3 ξ)) β _ _ (P.toLaunch x s n Z (flipDose F 3) 0 J) amp)

private lemma enrolled_zero {E R:Hilbert}(u:ℕ→E)(p:Tendsto u atTop (𝓝 0))(f:E.space →ₗᵢ[ℂ] R.space):
    Tendsto (fun i=> f (u i)) atTop (𝓝 0):= by
  have ht : Tendsto f (𝓝 0) (𝓝 0):= by simpa using f.continuous.continuousAt.tendsto (x:=0)
  exact ht.comp p

/-- The intrinsic localization check (not just chronological gaps). -/
def FitsAll (eps:ℝ) : Prop :=
  ∀ i:Lead.Clan, ∀ y:Vantage,
    P.Aperture (P.FTest i s n) y ⊆ {u:Vantage | ∀ a:Axis, |u a-y a|<eps} ∧
    P.Aperture (P.RTest i s n) y ⊆ {u:Vantage | ∀ a:Axis, |u a-y a|<eps}

private lemma fitso (z:ℝ)(v:∀ a,P.probeWidth s n a<z) : P.FitsAll s n z:=
  fun i y=> ⟨fun _ u a=> (u a).trans_lt (v a),fun _ u a=> (u a).trans_lt (v a)⟩

/-- Grid cost and ordered vector limits at single trial-width height. -/
structure WidthStation (K0:P.Register): Prop where
  small : P.probeWidth s n 3<1
  nlarge : P.calibration.ℓ<n
  allGrids (t:ℕ)(p:s≤t): P.TickRecording s n t F G x K0 0 ∧ ∀ i j:Lead.Clan,
    P.LocalTick s n t i j (F:=F) (G:=G) ∧ P.Crossing s n t i j F G x ∧ P.LeftSeed s n t i F x
  positionLimit : Tendsto (fun t=> P.thinArray s n t F G x) atTop (𝓝 (P.costArray s n F G x 0))

private lemma narrowEnough (K0:P.Register)(J:P.Ellis 3 x)(w:P.probeWidth s n 3<1)(e:P.calibration.ℓ<n)(Y:P.Walls s n F G 0) : P.WidthStation s n F G x K0:=
 { small:=w
   nlarge:=e
   allGrids t v:=⟨P.recording s n t F G x K0 0 Y.beforeQ Y.afterQ e v,fun i j=>⟨P.localTick s n t i j v,P.crossing s n t i j F G x J Y v,P.reflectedSeed s n t i F G x J Y v⟩⟩
   positionLimit:= P.gridThin s n F G x 0 (P.answersTogether x _ _ _ J F G Y.beforeQ Y.afterQ) }

/-- Purchased estimates through the two limits for the explicit intrinsic shrink
attempt. It's NOT a thin-field interaction result; the second limit loses it (even
on exactly these bodies and smears, through the physical-resolution limit first).
The fields in the setback OS spaces converge, but to zero. -/
structure OnTheseWindows (K0:P.Register) : Prop where
  holds : ∀ᶠ i:ℕ in atTop, P.WidthStation (c i) (r i) F G x K0
  thin (eps:ℝ)(he:0<eps) : ∀ᶠ i:ℕ in atTop,P.FitsAll (c i) (r i) eps
  collapsesLeft (Z:Lead.Clan) :
    Tendsto (fun i=> β (P.thinAmp (c i) (r i) • P.landingCost x (c i) (r i) Z F 0)) atTop (𝓝 0)
  collapsesRight (Z:Lead.Clan) :
    Tendsto (fun i=> β (P.thinAmp (c i) (r i) • P.launchCost x (c i) (r i) Z G 0)) atTop (𝓝 0)
  costsShrink : Tendsto (fun i=>P.costArray (c i) (r i) F G x 0) atTop (𝓝 (0:CrossRead))
  evenChanging (Fₜ Gₜ :ℕ→SampleDose)(a:ℕ→ℝ)(b:ℝ≥0) (R: StaysBack Fₜ Gₜ a b)
    (z y:ℕ→Lead.Clan→ℂ) (u:∀ i,P.UpToTick c r (fun k=>z k i))(v:∀ i,P.UpToTick c r (fun k=>y k i)) :
    Tendsto (fun k=> Matrix.of fun i j:Lead.Clan=> star (z k i)*y k j*P.arrayReading x (c k) (r k) (a k) (Fₜ k) (Gₜ k) i j)
      atTop (𝓝 (0:CrossRead))

variable {P x c r F G} {K0:P.Register}{J:P.Ellis 3 x}
theorem onTheseWindows (B:P.Experiment K0 c r x J)
    (a:tsupport F.val⊆reviewEarlierBox.invites)(b:tsupport G.val⊆reviewLaterBox.invites)
    (h:F.Normalized)(p:G.Normalized) : P.OnTheseWindows F G x c r K0:=by
  let Q:=boxed F G a b h p
  let A(i):=P.thinAmp (c i) (r i)
  let l (i:Lead.Clan):= filterPrice_back B Q i A (P.dual_afford ..)
  let w (i:Lead.Clan):= filterPrice B Q i A (P.dual_afford ..)
  let T':= trans6 B
  refine { holds:=?_
           thin:=?_
           collapsesLeft:= fun i=> enrolled_zero (E:=P.ManyF 3 ξ) (R:=P.ColorHil 3 ξ) _ (l i) β
           collapsesRight:=fun i=> enrolled_zero (E:=P.ManyF 3 ξ) (R:=P.ColorHil 3 ξ) _ (w i) β
           costsShrink:= limitSixLoss B Q (fun i _=> A i) (fun i _=> A i) (fun _=> P.dual_afford ..) (fun _=> P.dual_afford ..)
           evenChanging:= fun _ _ _ _ R'=> limitSixLoss B R' }
  · exact (((T'.widths 3).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).and (B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ))).mono fun i t=>
      P.narrowEnough (c i) (r i) F G x K0 J t.1 t.2 (P.windowWall _ _ t.1 a b)
  intro e he
  exact (eventually_all.mpr (fun i=>(T'.widths i).eventually (gt_mem_nhds he))).mono fun i v=> P.fitso _ _ e v

/-- Bought mismatch estimate. On any one purchased fixed experiment, with these
actual x and smears, the second limit of this trial gives the whole discrepancy back
as *error* (instead of preserving even some of it as a thin-field contrast). -/
theorem paidButLoses (X:P.OnTheseWindows F G x c r K0){s n:ℕ}{a:ℝ}(R:P.ReturnsSix x s n a F G)(i:Lead.Clan):
    let w:= P.arrayReading x s n a F G i i
    w≠0 ∧ Tendsto (fun j=> ‖w-P.costArray (c j) (r j) F G x 0 i i‖) atTop (𝓝 ‖w‖) :=by
  intro w
  have h:Tendsto (fun j=> P.costArray (c j) (r j) F G x 0 i i) atTop (𝓝 0):= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp X.costsShrink i) i
  have he:= ((tendsto_const_nhds (x:=w)).sub h).norm
  rw [sub_zero] at he
  exact ⟨R.poles.2 i,he⟩

/-- Problem is unconditional even including the request. Take constant zero here. -/
def thinRequest_LocalFieldBounds : Supplier:=fun _ _ _ _ _ _ _ _ _ _ _ _ => 0

def SameTestTrial (P:Spine)(K:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3)(i:ℕ)(a:ℝ)(F G:SampleDose) : Prop:=
 uniform P K thinRequest_LocalFieldBounds 1 1 ∧
 (∃ J:P.Ellis 3 x,P.Experiment K c r x J) ∧
 F.Normalized∧ G.Normalized∧ tsupport F.val⊆ reviewEarlierBox.invites ∧ tsupport G.val⊆ reviewLaterBox.invites ∧
 (∀ Z:Lead.Clan,P.spacePrice (P.RTest Z (c i) (r i)) F⊆reviewEarlierBox.invites)∧
 (∀ Z:Lead.Clan,P.spacePrice (P.FTest Z (c i) (r i)) G⊆reviewLaterBox.invites)∧
 P.ReturnsSix x (c i) (r i) a F G∧ P.FixedSatinReadings K x (c i) (r i) a F G∧
 -- both sizes of tests can also use the wall at zero (though review earlier used a)
 P.WidthStation (c i) (r i) F G x K ∧ P.OnTheseWindows F G x c r K ∧
 ∀ q:Lead.Clan, let w:= P.arrayReading x (c i) (r i) a F G q q
                w≠0 ∧ Tendsto (fun j=> ‖w-P.costArray (c j) (r j) F G x 0 q q‖) atTop (𝓝 ‖w‖)

/-- Public partial application. On one physically elected P, K, x and one
experiment holding its body widths and smears fixed in the verified sense,
attempt the inverse-increment thin variant through the widths. (See
`OnTheseWindows` and `SatinThinLoss.limitSixLoss` (namespace `Spine`), and
`WidthStation` for the intrinsic poses, grid and comparison tests this buys.)
This estimate of the thin variant has all quantifiers back on the chosen theory
(in particular with no Spectrum grant left as a hypothesis or conditional
request on growth of movement). It's an obstruction to obtaining the margin by
such a limit.

No successful nonzero *thin-field* interaction theorem asserted here;
spacelike locality of the old width-retaining bodies, or removal of their
Lorentz retest obstruction in a successful limit with new normalization,
isn't inferred either. -/
theorem electedInverseTrial :
   ∃ (P:Spine)(K:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3)(i:ℕ)(a:ℝ)(F G:SampleDose), SameTestTrial P K c r x i a F G :=by
  obtain ⟨P,K,h,c,r,x,e,J,B,L⟩:= macroscopicSatin thinRequest_LocalFieldBounds 1 1 zero_lt_one id
  let U:=reviewEarlierBox
  let V:=reviewLaterBox
  let orders:Orders:= ⟨fun _=>true,rfl⟩
  have sep:U.Later V orders 0:=by intro j; norm_num [U,V,Doorway.Later,reviewEarlierBox,reviewLaterBox,orders]
  let b:Fin 3→Bool:= fun _=>false
  obtain ⟨p,x',v,_,w⟩:= authorize b
  obtain ⟨i,⟨_,a,F,G,hF,hG,M,m,q,d,t⟩,narrow,y⟩:=
    ((packs_within_rectangles L (Metric.ball p x') b w U V orders sep).and (((L.widths 3).eventually (gt_mem_nhds zero_lt_one)).and (B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)))).exists
  let Hp:=onTheseWindows B m q hF hG
  exact ⟨P,K,c,r,x,i,a,F,G,h,⟨J,B⟩,hF,hG,m,q,d,t,M,
    P.reviewWardContrast K x _ _ _ _ _ M,P.narrowEnough _ _ F G x K J narrow y (P.windowWall _ _ narrow m q),Hp,fun q'=> paidButLoses Hp M q'⟩

end Spine
#print axioms Spine.electedInverseTrial
#print axioms Spine.paidButLoses
#print axioms Spine.onTheseWindows
#print axioms Spine.recording
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
