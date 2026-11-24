import SatinFixedContrastNovember4
import YM.SU5.Thin.Smoothed

/-!
# The pair and component readings, with a lower bound

Declare the **two-field** Schwinger and marginal tests of these thin fields.
Always keep the normalization and split qualification (factorization of the
field law tested in the *original* gauge & matter variables). To compute that
prediction apply the SAME JointPair inputs at t to the (unique)
`SameRawProduct t`, NOT interpreting the split as multiplying limiting scalars,
or factoring on functions on the selected spectrum, nor only estimating a joint
answer far away from contact and the split somehow *at* contact. These tests also
work for fully independent choices of string length for each box along this
one career. No Minkowski hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
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

/-- Readings in one regulator test. Use with `P.singleState 3 t x` for true,
with `SameRawProduct t x` for the canonical comparator. Both price the
same three Marks. -/
def pairSurvey (P:Spine) (X:P.Test→ₗ[ℂ] ℂ)(f g:P.Test) : ℂ × ℂ × ℂ :=
  (X (f*g), X f, X g)

/-- Opposed Euclidean pairing on a seam in the chosen Hilbert room. -/
def wallPairing (H:Hilbert) (Ω f g:H) : ℂ × ℂ × ℂ :=
  (inner ℂ f g, star (inner ℂ Ω f), inner ℂ Ω g)

section estimates
variable (X:Hilbert)(Ω:X)(u v:X)
private lemma reading_replace (Ω' x' y':X) (c d e:ℂ)(q:c=inner ℂ x' y' ∧ d=star (inner ℂ Ω' x') ∧ e=inner ℂ Ω' y') :
    (c, d, e)=wallPairing X Ω' x' y' := Prod.ext q.1 (Prod.ext q.2.1 q.2.2)
lemma wall_limit_rays {I:Type*}{p:Filter I}{X' Y:I → X} (h:Tendsto X' p (𝓝 u)) (w:Tendsto Y p (𝓝 v)) :
    Tendsto (fun i=> wallPairing X Ω (X' i) (Y i)) p (𝓝 (wallPairing X Ω u v)) :=
  (h.inner w).prodMk_nhds (((tendsto_const_nhds (x:=Ω)).inner h).star.prodMk_nhds
    ((tendsto_const_nhds (x:=Ω)).inner w))

lemma wall_read_limits_vac (z w:ℝ)(n:‖Ω‖=1)(p:u=(z:ℂ) • Ω)(q:v=(w:ℂ) • Ω) :
    wallPairing X Ω u v=((z:ℂ)*(w:ℂ),(z:ℂ),(w:ℂ)) := by
  rw [p,q,wallPairing]
  simp only [inner_smul_left,inner_smul_right,inner_self_eq_norm_sq_to_K,n, one_pow,RCLike.ofReal_one, Complex.conj_ofReal, mul_one]
  simp; ring
end estimates

section computation
variable (P:Spine) (x:P.Spectrum0 3) (Z W:Lead.Clan) (A B:SampleDose) (s n s' n' t:ℕ)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "H" => P.ColorHil 3 ξ
local notation "μ" => P.singleState 3 t x
local notation "ω" => P.colorZero 3 ξ
-- forwards price

def thinSamples (t:ℕ)(m:P.Test →ₗ[ℂ] ℂ) : ℂ × ℂ × ℂ:=
  P.pairSurvey m (P.thinIncoming Z s n t A) (P.thinOutgoing W s' n' t B)
def thinPairing (α β:P.ColorHil 3 (P.otherSpectrum 3 3 x)) := wallPairing H ω α β

def sampledWall : ℂ × ℂ × ℂ:=
  P.thinPairing x
    (P.wallSignal x t (flipDose A 3) (P.shard x Z s n)) (P.wallSignal x t B (P.shard x W s' n'))
def integratedWall : ℂ × ℂ × ℂ:=
  P.thinPairing x
    (P.wallContinuum x (flipDose A 3) (P.shard x Z s n)) (P.wallContinuum x B (P.shard x W s' n'))
/-- The limits we use. No seam fit asserted by defining them; pay it below. -/
def finalPairing : ℂ × ℂ × ℂ:= P.thinPairing x (P.thinField x Z A) (P.thinField x W B)

local notation "G" => P.thinSamples Z W A B
local notation "uStr" => P.thinString Z
local notation "vStr" => P.thinString W
local notation "Λ₁" => P.finalPairing x Z W A B

def StringBefore : Prop := P.WallBefore ((P.thinString Z s n).kiss P 3) A 0
def StringAfter : Prop := P.WallAfter (P.thinString Z s n) A 0

lemma rawSurvey (v:P.StringBefore Z A s n)(u:P.StringAfter W B s' n') (e:s≤t)(p:s'≤t):
    G s n s' n' t (P.singleState 3 t x)=P.sampledWall x Z W A B s n s' n' t :=
  reading_replace H _ _ _ _ _ _
    (P.seam_gram x A B (P.thinString Z s n) (P.thinString W s' n') t
      (P.thinString_birth Z s n) (P.thinString_birth W s' n') e p v u)

lemma surveyInAlgebra (R:P.Register) :
    let α:=P.slotHole t (P.thinIncoming Z s n t A)
    let β:=P.slotHole t (P.thinOutgoing W s' n' t B)
    let χ:=P.spirits R 3 x
    P.thinSamples Z W A B s n s' n' t (P.singleState 3 t x)=(χ (α*β),χ α,χ β):= by
  intro α β χ
  have he : α * β=P.slotHole t (P.thinIncoming Z s n t A * P.thinOutgoing W s' n' t B):=(map_mul (P.slotHole t) _ _).symm
  have hx(a:P.Test): χ (P.slotHole t a)= P.singleState 3 t x a:= P.oneCup R 3 x t a
  exact Prod.ext (((congrArg χ he).trans (hx _)).symm) (Prod.ext (hx _).symm (hx _).symm)

lemma away (v:P.StringBefore Z A s n)(u:P.StringAfter W B s' n') :
    Disjoint (P.spacePrice ((uStr s n).kiss P 3) A) (P.spacePrice (vStr s' n') B) :=
  P.test_apart _ _ 0 _ _ v u

lemma splitSurvey (f:P.StringBefore Z A s n)(g:P.StringAfter W B s' n') (e:s≤t)(h:s'≤t)
    (p:n>P.calibration.ℓ)(q:n'>P.calibration.ℓ)
    (X:P.Test→ₗ[ℂ]ℂ)(v:Factors P.calibration X)(u:MatterWard P.calibration X ∨ GaugeWard P.calibration X):
    G s n s' n' t X = 0 :=
  let r:= P.thin_factor_pays Z W s n t A B s' n' e h p q (P.away Z W A B s n s' n' f g) X v u
  Prod.ext r.2.2 (Prod.ext r.1 r.2.1)

lemma splitSurvey_marginals (f:P.StringBefore Z A s n)(g:P.StringAfter W B s' n') (e:s≤t)(h:s'≤t)
    (p:n>P.calibration.ℓ)(q:n'>P.calibration.ℓ)
    (X:P.Test→ₗ[ℂ]ℂ)(x':P.SameRawProduct t x X) : G s n s' n' t X = 0 :=
  P.splitSurvey Z W A B s n s' n' t f g e h p q X x'.marginal.factors (.inl x'.matter)

variable {P x} {c r : ℕ → ℕ} {K:P.Register} {J:P.Ellis 3 x}
local notation "X₀" i:max=> P.StringBefore Z A (c i) (r i)
local notation "Y₀" i:max=> P.StringAfter W B (c i) (r i)

lemma eventually_after (H':P.Transmission x c r) (h:MatureAfter A) : ∀ᶠ i:ℕ in atTop,
    P.StringAfter Z A (c i) (r i):=
   MatureAfter.eventually A (fun i=> uStr (c i) (r i)) (H'.widths 3) h

lemma eventually_before (H':P.Transmission x c r) (h:MatureAfter (flipDose A 3)) :
    ∀ᶠ i:ℕ in atTop,X₀ i:= ((MatureAfter.eventually (flipDose A 3) (fun i=> uStr (c i) (r i)) (H'.widths 3) h)).mono
      (q:=fun i=> P.StringBefore Z A (c i) (r i)) (fun i v=> mirrorFitsBefore A (P.thinString Z (c i) (r i)) v)

include J in
lemma survey_axis (v:P.StringBefore Z A s n)(u:P.StringAfter W B s' n') :
    Tendsto (fun t=> G s n s' n' t (P.singleState 3 t x)) atTop (𝓝 (P.integratedWall x Z W A B s n s' n')):=
  (wall_limit_rays H ω _ _ (P.at_seam x (flipDose A 3) J (P.shard x Z s n)) (P.at_seam x B J (P.shard x W s' n'))).congr'
    (((eventually_ge_atTop s).and (eventually_ge_atTop s')).mono (fun t h=> (P.rawSurvey x Z W A B s n s' n' t v u h.1 h.2).symm))

-- Full width stability and interpretation
variable (Y:P.Experiment K c r x J) (f:MatureAfter (flipDose A 3))(h:MatureAfter B)
variable {I:Type*}(D:Filter I)(F R T:I→ℕ)(v:Tendsto F D atTop)(u:Tendsto R D atTop)
variable (e: ∀ᶠ i in D,c (F i)≤ T i)(p: ∀ᶠ i in D,c (R i) ≤ T i)
local notation "α" i:max=> P.wallContinuum x (flipDose A 3) (P.shard x Z (c (F i)) (r (F i)))
local notation "β" i:max=> P.wallContinuum x B (P.shard x W (c (R i)) (r (R i)))
local notation "singleLevelSurvey"=> P.sampledWall x Z W A B
local notation "g" i:max=> P.thinSamples Z W A B (c (F i)) (r (F i)) (c (R i)) (r (R i)) (T i)

include v u Y f h
private lemma quals_all : ∀ᶠ i in D, X₀ (F i) ∧ Y₀ (R i) ∧ r (F i)>P.calibration.ℓ ∧ r (R i)>P.calibration.ℓ :=
  let η:=trans6 Y
  let y:=Y.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)
  (v.eventually (eventually_before Z A η f)).and ((u.eventually (eventually_after W B η h)).and
    ((v.eventually y).and (u.eventually y)))

/-- Whether the integration is performed before narrowing (as intended) -/
lemma independentWidths : Tendsto (fun i=> P.integratedWall x Z W A B
    (c (F i)) (r (F i)) (c (R i)) (r (R i))) D (𝓝 (Λ₁)):=
  let K := P.thinField x Z (flipDose A 3)
  let y := P.thinField x W B
  Eq.mp (congrArg (fun z:H=> Tendsto (fun i=> P.thinPairing x (α i) (β i)) D (𝓝 (P.thinPairing x z y)))
      (P.sameMass x Z A))
    (wall_limit_rays H ω K y ((afterField Z (flipDose A 3) Y f).comp v) ((afterField W B Y h).comp u))

include e p
private lemma past_receipts : ∀ᶠ i in D,
    (g i) (P.singleState 3 (T i) x)= singleLevelSurvey (c (F i)) (r (F i)) (c (R i)) (r (R i)) (T i) ∧
    ∀ X:P.Test→ₗ[ℂ]ℂ, Factors P.calibration X →
    MatterWard P.calibration X ∨ GaugeWard P.calibration X → (g i) X = 0 :=
  (((quals_all Z W A B Y f h D F R v u).and e).and p).mono
    (fun i a=>
      let s:=c (F i); let n:=r (F i); let t:=T i
      let s':=c (R i); let n':=r (R i); let z:= a.1.1
      let b:=a.1.2
      ⟨P.rawSurvey x Z W A B s n s' n' t z.1 z.2.1 b a.2,
       P.splitSurvey Z W A B s n s' n' t z.1 z.2.1 b a.2 z.2.2.1 z.2.2.2⟩)

/-- or using the height-t samples synchronously, at arbitrary `t≥s` per i. Also
shows convergence of predicted singles and pair on ANY Ward-factorized oracle. -/
lemma survey_read (X:I→ P.Test→ₗ[ℂ]ℂ)(k:∀ i,Factors P.calibration (X i))
    (y:∀ i,MatterWard P.calibration (X i) ∨ GaugeWard P.calibration (X i)) :
    Tendsto (fun i=>(g i) (P.singleState 3 (T i) x)) D (𝓝 (Λ₁)) ∧
    Tendsto (fun i=>(g i) (X i)) D (𝓝 0) :=
  let ψ₀:= P.thinField x Z (flipDose A 3)
  let ψ:= P.thinField x W B
  let d := tendsto_atTop_mono' D (f₁:=c∘F) e (Y.launch.smaller.tendsto_atTop.comp v)
  let y':= past_receipts Z W A B Y f h D F R T v u e p
  ⟨Eq.mp (congrArg (fun z:H=> Tendsto (fun i=>(g i) (P.singleState 3 (T i) x)) D (𝓝 (P.thinPairing x z ψ))) (P.sameMass x Z A))
    ((wall_limit_rays H ω ψ₀ ψ (widthSignal Z (flipDose A 3) Y D f F T v d) (widthSignal W B Y D h R T u d)).congr'
      (y'.mono fun _ a => a.1.symm)),
    tendsto_const_nhds.congr' (f₂:=fun i=>(g i) (X i)) (y'.mono fun i a=> (a.2 (X i) (k i) (y i)).symm)⟩

omit f h v u e p Y
lemma thinSurvey_value (x:P.Spectrum0 3)(y:A.Normalized)(w:B.Normalized) :
    P.finalPairing x Z W A B=((purePrice Z:ℂ)*(purePrice W:ℂ),(purePrice Z:ℂ),(purePrice W:ℂ)):=
  wall_read_limits_vac (P.ColorHil 3 (P.otherSpectrum 3 3 x)) _ _ _ _ _
    (P.norms_color 3 _) (P.thinMassOne x Z A y) (P.thinMassOne x W B w)
include f h Y v u e p
/-- Lower bound against the canonical product oracle, in all six channels.
The limit matrix is **not** asserted positive definite; the computed signal is
carried on the vacuum line. It detects gauge--matter interaction by strict
discrepancy from the raw product comparison, NOT by a nonzero connected
correlator between separated cells. -/
lemma survey_below (a:A.Normalized)(b:B.Normalized) (X:I→ P.Test→ₗ[ℂ]ℂ)(y:∀ i,P.SameRawProduct (T i) x (X i)) :
    0 < purePrice Z*purePrice W/2 ∧
    ∀ᶠ i in D, purePrice Z*purePrice W/2 <
      ‖((g i) (P.singleState 3 (T i) x)).1 - ((g i) (X i)).1‖ := by
  have hw:= survey_read Z W A B Y f h D F R T v u e p X (fun i=> (y i).marginal.factors)
    (fun i=> .inl (y i).matter)
  have hp:= (((continuous_fst.tendsto _).comp hw.1).sub ((continuous_fst.tendsto _).comp hw.2)).norm
  have H' x : ‖(P.finalPairing x Z W A B).1-((0:ℂ× ℂ× ℂ).1)‖=purePrice Z*purePrice W := by
    rw [thinSurvey_value Z W A B x a b]
    change ‖(↑(purePrice Z):ℂ)* (purePrice W:ℂ)-0‖=_
    rw [sub_zero,norm_mul]
    simp only [Complex.norm_real,Real.norm_of_nonneg (purePrice_p Z).le,Real.norm_of_nonneg (purePrice_p W).le]
  rw [H'] at hp
  exact ⟨half_pos (mul_pos (purePrice_p Z) (purePrice_p W)), hp.eventually (lt_mem_nhds
    (half_lt_self (mul_pos (purePrice_p Z) (purePrice_p W))))⟩

#print axioms rawSurvey
#print axioms surveyInAlgebra
#print axioms splitSurvey_marginals
#print axioms survey_axis
#print axioms independentWidths
#print axioms survey_read
#print axioms thinSurvey_value
#print axioms survey_below
end computation
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
