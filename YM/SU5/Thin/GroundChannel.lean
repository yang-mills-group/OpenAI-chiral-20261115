import SatinFixedContrastNovember4
import YM.SU5.Thin.WhatLimit

/-!
# Milestone -- an actual discrepancy for two thin, BI-POCKET fields

This reads `raw-factorization` (see `YM.SU5.Six.RawWard` in the imported fixed-six experiment).
It is a total actual-vs-split price. NO further meaning as connected momentum
transmission: our solution obtains a ground-channel interaction receipt, with no
need for that stronger interpretation, and also calculates the limiting **actual**
connected correlation for the two cells, which is zero. We think the distinction
is important both for interpreting the interaction test as posed, and for the
other reconstruction steps which remain open. See the writeup.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
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

variable (P:Spine)(K:P.Register)(x:P.Spectrum0 3) (Z W:Lead.Clan)(F G:SampleDose)(c r:ℕ→ℕ)
local notation "X"=> reviewEarlierBox
local notation "Y"=> reviewLaterBox
local notation "χ"=> P.otherSpectrum 3 3 x

/-- All physical lengths in matter-spacing-at-zero units. -/
lemma thinCells (a b:Vantage)(u:a∈ reviewEarlierBox.invites)(w:b∈ reviewLaterBox.invites) :
    ∀ j:Axis, 2 < b j-a j := by
  intro j
  have hx:b j > 1 := (w j (Set.mem_univ _)).1
  have h:a j < -1 := (u j (Set.mem_univ _)).2
  linarith only [h,hx]

/-- Includes the genuine t-level formulae for probes and interpretation on every
eligible resolution. (Thin births used only for n>ℓ and in regions indicated.)
F, G are the TWO order-oriented independent tests, at EVERY height. -/
structure PaidPair (s n:ℕ) : Prop where
  early : P.StringBefore Z F s n
  late : P.StringAfter W G s n
  lenses : P.spacePrice ((P.thinString Z s n).kiss P 3) F ⊆ reviewEarlierBox.invites ∧
            P.spacePrice (P.thinString W s n) G ⊆ reviewLaterBox.invites
  registry (t:ℕ) (g:s ≤ t) :
    P.asked_at t (P.thinIncoming Z s n t F) (P.spacePrice ((P.thinString Z s n).kiss P 3) F) ∧
    P.asked_at t (P.thinOutgoing W s n t G) (P.spacePrice (P.thinString W s n) G) ∧
    P.thinIncoming Z s n t F ∈ enclave P.calibration ∧
    P.thinOutgoing W s n t G ∈ enclave P.calibration
  fields (t:ℕ) (g:s ≤ t) :
    let a := P.thinIncoming Z s n t F; let d:= P.thinOutgoing W s n t G
    -- first bill uses reflected copy across the seam, including its dressing.
    let b:= P.thinOutgoing Z s n t (flipDose F 3)
    (∃ i:P.birthF 3 t b, a=P.reflectTest 3 b ∧ P.viewF 3 χ t i=P.wallSignal x t (flipDose F 3) (P.shard x Z s n)) ∧
    (∃ i:P.birthF 3 t d, P.viewF 3 χ t i=P.wallSignal x t G (P.shard x W s n))
  prices (t:ℕ)(h:s≤t) :
    P.thinSamples Z W F G s n s n t (P.singleState 3 t x)=P.sampledWall x Z W F G s n s n t ∧
    ∀ E:P.Test→ₗ[ℂ]ℂ, Comparison P.calibration (P.singleState 3 t x) E →
      P.thinSamples Z W F G s n s n t E=0
  smearing :
    Tendsto (fun t=>P.wallSignal x t (flipDose F 3) (P.shard x Z s n)) atTop (𝓝 (P.wallContinuum x (flipDose F 3) (P.shard x Z s n))) ∧
    Tendsto (fun t=>P.wallSignal x t G (P.shard x W s n)) atTop (𝓝 (P.wallContinuum x G (P.shard x W s n))) ∧
    Tendsto (fun t=>P.thinSamples Z W F G s n s n t (P.singleState 3 t x)) atTop
      (𝓝 (P.integratedWall x Z W F G s n s n))

/-- Exact at one character. Splits from `P.singleState` on same state of SAME
experiment. More general results in companion files; note all-vector convergence
results are FIELD-ON-VACUUM, in the full-space strong topology (see `fields`,
`observe`, and `widthSignal`). This is intended for Euclidean one-point and
ordered two-point questions, not all products. `predicted` value is at the RAW
labels/field resolution; do not pass to a Hilbert-space quotient to define it. -/
structure GroundChannel : Prop where
  predict_at (t:ℕ) : ∃! M:P.Test →ₗ[ℂ] ℂ, P.SameRawProduct t x M
  shrink : ∀ ε>0, ∀ᶠ i:ℕ in atTop, ∀ Z:Lead.Clan,
    P.ThinIntrinsic (P.thinString Z (c i) (r i)) ε ∧ P.ThinIntrinsic ((P.thinString Z (c i) (r i)).kiss P 3) ε
  survey : ∀ᶠ i in atTop, r i > P.calibration.ℓ ∧ ∀ Z W:Lead.Clan,P.PaidPair x Z W F G (c i) (r i)
  narrow (Z W:Lead.Clan) :
    Tendsto (fun i=> P.integratedWall x Z W F G (c i) (r i) (c i) (r i)) atTop (𝓝 (P.finalPairing x Z W F G)) ∧
    Tendsto (fun i=>P.wallContinuum x (flipDose F 3) (P.shard x Z (c i) (r i))) atTop (𝓝 (P.thinField x Z F)) ∧
    Tendsto (fun i=>P.wallContinuum x G (P.shard x W (c i) (r i))) atTop (𝓝 (P.thinField x W G))
  vectorLimit (Z W:Lead.Clan) : P.finalPairing x Z W F G=
    ((purePrice Z:ℂ)*(purePrice W:ℂ),(purePrice Z:ℂ),(purePrice W:ℂ))
  contrast (Z W:Lead.Clan) (T:ℕ→ℕ) (h:c≤T)
      (M:ℕ→ P.Test →ₗ[ℂ] ℂ) (f:∀ i,P.SameRawProduct (T i) x (M i)) :
    0 < purePrice Z*purePrice W/2 ∧ ∀ᶠ i:ℕ in atTop, purePrice Z*purePrice W/2 <
      ‖(P.thinSamples Z W F G (c i) (r i) (c i) (r i) (T i) (P.singleState 3 (T i) x)).1 -
        (P.thinSamples Z W F G (c i) (r i) (c i) (r i) (T i) (M i)).1‖
  predecessor (T:ℕ→ℕ)(h:c≤T) :
    Tendsto (fun i=> P.arrayFine x (c i) (r i) (T i) F G) atTop (𝓝 (0:CrossRead))
  noUndamped (Z:Lead.Clan) : ¬ Tendsto (fun i=> P.shard x Z (c i) (r i)) atTop (𝓝 ((purePrice Z:ℂ) • P.colorZero 3 (P.otherSpectrum 3 3 x)))

variable {P K x c r}{J:P.Ellis 3 x}(R:P.Experiment K c r x J)
variable (p:tsupport F.val ⊆ reviewEarlierBox.spare.invites)
         (u:tsupport G.val ⊆ reviewLaterBox.spare.invites)
include p u
private lemma boxes : (tsupport F.val ⊆ (X).invites) ∧ tsupport G.val ⊆ (Y).invites :=
  ⟨p.trans (Set.Subset.trans subset_closure (X).sparesDoor), u.trans (Set.Subset.trans subset_closure (Y).sparesDoor)⟩ -- include

include R
private lemma funded (f:MatureAfter (flipDose F 3))(g:MatureAfter G) :
    ∀ᶠ i in atTop, (r i) > P.calibration.ℓ ∧ P.PaidPair x Z W F G (c i) (r i):= by
 let C:=trans6 R
 filter_upwards [eventually_before Z F C f,eventually_after W G C g, thin_inside_boxes F G C p u,
     (R.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ))] with i a b ht w
 let s:=c i; let n:=r i; let F':=(flipDose F 3)
 let U:=P.thinString Z s n; let U':=U.kiss P 3; let V:=P.thinString W s n
 refine ⟨w,⟨a,b,⟨(ht Z).1,(ht W).2⟩,fun t h=>⟨P.prepared_at t U' F h,P.prepared_at t V G h,
    (P.thinGaugeInvariant Z s n t F).2,(P.thinGaugeInvariant W s n t G).1⟩,
   fun t h=> ?_,fun t h=> ⟨P.rawSurvey x Z W F G s n s n t a b h h,
    fun M p'=>P.splitSurvey_marginals x Z W F G s n s n t a b h h w w M ((P.SameRawProduct_iff t x M).2 p')⟩,
   P.at_seam x F' J (P.shard x Z s n), P.at_seam x G J (P.shard x W s n), survey_axis Z W F G s n s n (J:=J) a b⟩⟩ -- smearing nested ∧
 let W₀:= P.seam_signal_birth x U (P.thinString_birth Z s n) t F' (P.mirrorFits F U a) h
 exact ⟨⟨W₀.choose,P.mirrorPayment F U t,W₀.choose_spec⟩, P.seam_signal_birth x V (P.thinString_birth W s n) t G b h⟩

lemma observe (h:F.Normalized)(q:G.Normalized) : P.GroundChannel x F G c r:= by
  let C:=trans6 R
  have hx:= boxes F G p u
  have he:= mirror_strict F 1 zero_lt_one (fun i y=> ( (show i∈ (X).invites from hx.1 y) 3 (Set.mem_univ _)).2.le)
  have hu:= seam_strict G 1 zero_lt_one (fun i y=> ( (show i∈ (Y).invites from hx.2 y) 3 (Set.mem_univ _)).1.le)
  refine { predict_at:= fun i=> P.thin_comparator i x
           survey:=?_
           shrink:= thin_widths C
           narrow:= fun Z W=> ⟨independentWidths Z W F G R he hu atTop id id tendsto_id tendsto_id,
             Eq.mp (congrArg (fun z: P.ColorHil 3 χ=> Tendsto (fun i=>P.wallContinuum x (flipDose F 3) (P.shard x Z (c i) (r i))) atTop (𝓝 z)) (P.sameMass x Z F)) (afterField Z (flipDose F 3) R he),
             afterField W G R hu⟩
           vectorLimit:= fun Z W=> thinSurvey_value Z W F G x h q
           contrast:= fun Z W T y M f=> survey_below Z W F G R he hu atTop id id T tendsto_id tendsto_id (Eventually.of_forall y) (Eventually.of_forall y) h q M f
           predecessor:= fun T y=> losesOld F G R ℕ atTop id T tendsto_id (Eventually.of_forall y) he hu
           noUndamped:= fun Z=> thin_damping_needed Z R }
  exact (R.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and
    (eventually_all.mpr (fun Z => eventually_all.mpr fun W=> (funded Z W F G R p u he hu).mono (fun _ w=> w.2)))
omit R p u

variable (P K x c r)
/-- Use the SAME data as for `ReturnsSix` and `FixedSatinReadings`. We can call
`reviewWardContrast` itself here, therefore deliver both fixed and thin purchases
(includes the TRUE vacuum vector identification for the latter). `the construction notes`
for exact scope. -/

structure TwoPayments (s n:ℕ)(b:ℝ) : Prop where
  normF : F.Normalized
  normG : G.Normalized
  insideF : tsupport F.val ⊆ reviewEarlierBox.invites
  insideG : tsupport G.val ⊆ reviewLaterBox.invites
  oldFixedSix : P.ReturnsSix x s n b F G ∧ P.FixedSatinReadings K x s n b F G
  oldPositions : (∀ Z:Lead.Clan, P.spacePrice (P.RTest Z s n) F ⊆ reviewEarlierBox.invites) ∧
                 ∀ Z:Lead.Clan, P.spacePrice (P.FTest Z s n) G ⊆ reviewLaterBox.invites
  thin : P.GroundChannel x F G c r
variable {P K x c r}
include R

lemma both_observations : ∀ᶠ i in atTop, ∃ (F G : SampleDose)(b:ℝ),
    P.TwoPayments K x F G c r (c i) (r i) b := by
  let B:Fin 3→Bool:= fun _=>false
  obtain ⟨p₀,e,v₀,hp,q⟩:=authorize B
  let o:Orders:=⟨fun _=>true,rfl⟩
  have e': (X).Later Y o 0:= by intro j; norm_num [Doorway.Later, reviewEarlierBox, reviewLaterBox,o]
  have L:=packs_within_rectangles (trans6 R) (Metric.ball p₀ e) B q (X).spare (Y).spare o ((X).spareLater e')
  filter_upwards [L] with i H
  obtain ⟨b,F,G,u',v',w,x₀,y,h,k⟩:= H.2
  have hx:=boxes F G x₀ y
  exact ⟨F,G,b,u',v',hx.1,hx.2, ⟨w,P.reviewWardContrast K x _ _ b F G w⟩,
    ⟨fun i=> (h i).trans (Set.Subset.trans subset_closure (X).sparesDoor),fun i=> (k i).trans (Set.Subset.trans subset_closure (Y).sparesDoor)⟩,
    observe F G R x₀ y u' v'⟩
omit R
/-- Final picker, at an arbitrary supplier request. -/
theorem satinThinVacuum (H:Supplier)(L M:ℝ)(e:0<M)(z:ℕ→ℕ) :
   ∃ (P:Spine)(K:P.Register), uniform P K H L M ∧ ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3)(J:P.Ellis 3 x),
   z≤r ∧ P.Experiment K c r x J ∧ ∃ (i:ℕ) (F G:SampleDose) (a:ℝ), P.TwoPayments K x F G c r (c i) (r i) a := by
  obtain ⟨P,K,v₁,c,r,x,h,J,B,R⟩:= macroscopicSatin H L M e z
  exact ⟨P,K,v₁,c,r,x,J,h,B, (both_observations B).exists⟩

def thinRequest : Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
/-- Unconditional application to physical Satin (three LH SU(5) generations).
Uses the coupling fixed by that `P` (see `terminalBeta`, pinned to `P.par.x`). -/
theorem satinThinOnPhysical :
    ∃ (P:Spine)(K:P.Register), uniform P K thinRequest 1 1 ∧
      ∃ (c r : ℕ→ℕ)(x:P.Spectrum0 3)(J:P.Ellis 3 x), (fun i=> i) ≤ r ∧ P.Experiment K c r x J ∧
      ∃ (i:ℕ) (F G:SampleDose) (a:ℝ), P.TwoPayments K x F G c r (c i) (r i) a :=
    satinThinVacuum thinRequest 1 1 (by norm_num) (fun i=>i)

#check @satinThinVacuum
#check @satinThinOnPhysical
#print axioms satinThinVacuum
#print axioms satinThinOnPhysical
#print axioms observe
#print axioms thinCells
#print axioms widthSignal
#print axioms thin_inside_boxes
#print axioms thinString_eval
#print axioms relation_to_thick
#print axioms thinSurvey_value
#print axioms survey_below
#print axioms surveyInAlgebra
#print axioms thin_factor_pays
#print axioms thin_widths
#print axioms thin_uniform_heat
#print axioms survey_read
#print axioms independentWidths
#print axioms seam_signal_birth
#print axioms losesOld
#print axioms actualDisconnected
#print axioms obstruction_test
#print axioms thin_damping_needed
#print axioms common_reading
#print axioms input_formula
#print axioms input_order
#print axioms input_paid
#print axioms bare_density
#print axioms bare_chiral
#print axioms six_families
#print axioms terminalBeta
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
