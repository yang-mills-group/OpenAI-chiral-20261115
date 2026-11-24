import SatinFixedContrastNovember4
import YM.SU5.Thin.Pair

/-!
# Test the new field; what the discrepancy is and is not

See local references `the construction notes` and `the construction notes`
on fixed-width and positive-energy center-Wick-test obstruction. This file does not
claim reconstruction as local Minkowski fields or attempt to prove those written
results. Rather, test some relevant *criteria* on these fields, on this very x.

* Even with fully shrinking width, the undamped point insertion in this test is
not granted a strong limit (failure of convergence to the vacuum-price one,
`StringLimit.thin_damping_needed`). Removing the **external** positive-time
requirement doesn't follow from our estimates. And the **limiting ordered
price** and width costs do not license putting ANY of the actual fixed-height
bodies in the completed theory as sharp-time operators.
* The thin field-on-vacuum really lies in the vacuum line. Adding further heat
OR using the reconstructed **time** group therefore has no effect on *it*. So
it doesn't meet the positive-energy (strict >0), hence nonvacuum propagation
test, which is used importantly in the obstruction via the oriented two-point
function. Don't infer the obstruction for this LIMITING pairing from analyticity
from positive width of some earlier body. Nor any locality: we don't have the
price for commutator tests from such field-vector convergence.
* Indeed the earlier experiment bodies themselves, used instead as the varied-width
insertions along this Experiment and held on the fixed smears in a pair of such
separated regions, have ZERO limit. We prove that whole comparison too (calculation
of the actual price, not just the competitor prices). The time *duration* between
the two supports in their countermove in the stencil is itself going to zero.
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
private lemma vac_extend (X:Hilbert)(S:OS.Semigroup X (3:Axis))(z v:X) (c d:ℂ) (h:z=c • d • v) (g:∀ t,S.E t v=v) :
    (∀ t,S.E t z=z) ∧ (∀ t,S.edge t z=z) :=
  let p : ∀ t,S.E t z=z:= fun t=> by rw [h,map_smul,map_smul,g]
  ⟨p,(heat_iff_edge (3:Axis) S z).mp p⟩

section costs
variable (P:Spine)(x:P.Spectrum0 3)(Z W:Lead.Clan)(F G:SampleDose)(s n t:ℕ)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "H" => P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "ω" => P.colorZero 3 ξ
local notation "S" => P.physicalEnergy 3 ξ
local notation "λ'" => P.singleState 3 t x
local notation "v₀" => P.thinField x Z F

lemma obstruction_test : (∀ t,(S).E t v₀=v₀) ∧ (∀ t,(S).edge t v₀=v₀) :=
  vac_extend H (S) (v₀) ω (↑(doseMass F)) (↑(purePrice Z)) rfl (P.sector_hot 3 ξ)
lemma actualDisconnected (p:F.Normalized)(u:G.Normalized) :
    let z:=P.finalPairing x Z W F G; z.1=z.2.1*z.2.2 := by rw [thinSurvey_value Z W F G x p u]
-- Old width-varying experiment: VECTORS →0 even for the same smears.
variable {P x} {c r:ℕ→ℕ}{K:P.Register}{J:P.Ellis 3 x}
variable (R:P.Experiment K c r x J)
local notation "Δ" i:max=> P.increment (c i) (r i)

include R
lemma shift_duration : Tendsto (fun i:ℕ=> (↑(Δ i) : ℝ)) atTop (𝓝 0) := by
  let a(i:ℕ):= P.dew (c i) (r i)
  have h: Tendsto (fun i=> (↑(Δ i):ℝ)/a i) atTop (𝓝 (1/2)) := increment_ratio R.launch
  have he := h.mul (P.proper_dew c r R.launch)
  rw [mul_zero] at he
  exact he.congr fun i=> div_mul_cancel₀ _ (P.dew_pos (c i) (R.launch.unitSize i)).ne'

omit R
-- Shift price
private lemma afterShift_heat (X:Hilbert)(S':OS.Semigroup X (3:Axis))(v:X)(f h:ℕ→X)(w:ℕ→ℝ≥0)(b:ℝ≥0)
    (p:Tendsto (fun i=> S'.E b (h i)) atTop (𝓝 v))(e:∀ t,S'.E t v=v)
    (u:∀ i,f i=h i-S'.E (w i) (h i)) :
    Tendsto (fun i=> S'.E b (f i)) atTop (𝓝 ((0:ℂ) • v)) := by
  let Y(i):=S'.E b (h i); let X'(i):= S'.E b (S'.E (w i) (h i))
  have he(i:ℕ): X' i = S'.E (w i) (Y i):= by unfold X' Y; rw [← ContinuousLinearMap.comp_apply,← S'.time,add_comm, S'.time]; rfl
  have hy : Tendsto X' atTop (𝓝 v) := by
    apply Metric.tendsto_nhds.mpr
    intro ε o; filter_upwards [Metric.tendsto_nhds.mp p ε o] with i f
    rw [he]; exact lt_of_le_of_lt ((congrArg (fun x=> dist (S'.E (w i) (Y i)) x) (e (w i))).symm.le.trans
      (heat_nonexpanding X S' (w i) (Y i) v)) f
  have ht:= p.sub hy; rw [sub_self] at ht; rw [zero_smul]
  exact ht.congr fun i=>by unfold X'; rw [u,map_sub]

variable (Y:Type*)(D:Filter Y)(A T:Y→ℕ)(v:Tendsto A D atTop)(p:∀ᶠ i in D,c (A i)≤ T i)
local notation "V" i:max=> P.shard x Z (c i) (r i)
local notation "V'" i:max=> P.filterVector x (c i) (r i) Z
private lemma zeros (X:Hilbert)(v z:X) : (0:ℂ) • v = (0:ℂ) • z:= (zero_smul ..).trans (zero_smul (ℂ) z).symm
include R v p
lemma old_cost (h:MatureAfter F) :
    Tendsto (fun i=> P.wallSignal x (T i) F (V' (A i))) D (𝓝 0) :=
  let L:= h.choose
  let f:=purePrice Z
  let w:=(f:ℂ) • ω
  let S':= S
  let u : Tendsto (fun i=> S'.E L (V' i)) atTop (𝓝 ((0:ℂ) • ω)) :=
    Eq.mp (congrArg (fun y:H=> Tendsto (fun i=> S'.E L (V' i)) atTop (𝓝 y)) (zeros H w ω))
      (afterShift_heat H S' w _ _ (fun i=> Δ i) L (thin_cost Z R L h.choose_spec.1)
        (fun t=> (map_smul (S'.E t) (f:ℂ) ω).trans (congrArg (fun z:H=>(f:ℂ) • z) (P.sector_hot 3 ξ t)))
        (fun i=> P.filter_born x (c i) (r i) Z))
  Eq.mp (congrArg (fun y:H=> Tendsto (fun i=> P.wallSignal x (T i) F (V' (A i))) D (𝓝 y))
      ((congrArg (fun z:H=> (↑(doseMass F):ℂ) • z) (zero_smul ℂ ω)).trans (smul_zero (↑(doseMass F):ℂ))))
    (P.smearEstimate x F _ 0 L h.choose_spec.2 u D A T v (tendsto_atTop_mono' D (f₁:=c∘A) p (R.launch.smaller.tendsto_atTop.comp v)))

-- Test width contraction on the older pair, using its given shift with its duration.
omit R v p
lemma incumbentBefore (a:P.StringBefore Z F s n) : P.WallBefore (P.RTest Z s n) F 0 := by
  intro i hi; have h:i 3+P.probeWidth s n 3<0 := a i hi; change _+bell _ _ (P.probeClock n 3)<0; exact h
lemma incumbentAfter (a:P.StringAfter Z F s n) : P.WallAfter (P.FTest Z s n) F 0 := by
  change P.WallAfter (P.thinString Z s n) F 0 at a
  intro i hi; exact a i hi
private lemma oldVector : P.viewF 3 ξ s (P.body_birth Z s n)=P.filterVector x s n Z := rfl
private lemma oldIncomingRay : P.rayEarlier x F t (P.FTest Z s n) (P.body_birth Z s n) = P.wallSignal x t (flipDose F 3) (P.filterVector x s n Z) := rfl
private lemma oldFutureRay : P.rayLater x F t (P.FTest Z s n) (P.body_birth Z s n) = P.wallSignal x t F (P.filterVector x s n Z) := rfl
lemma relation_to_old (a:P.StringBefore Z F s n)(g:P.StringAfter W G s n)(r:s≤t) : P.arrayFine x s n t F G Z W=
    inner ℂ (P.wallSignal x t (flipDose F 3) (P.filterVector x s n Z))
      (P.wallSignal x t G (P.filterVector x s n W)) := by
  change P.singleState 3 t x (P.prepared t (P.RTest Z s n) F * P.prepared t (P.FTest W s n) G) = _
  let F':= P.seam_gram x F G (P.FTest Z s n) (P.FTest W s n) t (P.body_birth Z s n) (P.body_birth W s n) r r (incumbentBefore Z F s n a) (incumbentAfter W G s n g)
  exact F'.1.trans (congrArg₂ (inner ℂ) (oldIncomingRay (P:=P) (x:=x) Z F s n t)
    (oldFutureRay (P:=P) (x:=x) W G s n t))

private lemma no_read {I:Type*}{D:Filter I} (X:Hilbert)(a b:I→ X)(g:I→ℂ)
    (v:Tendsto a D (𝓝 0))(u:Tendsto b D (𝓝 0))(e:∀ᶠ i in D,g i=inner ℂ (a i) (b i)): Tendsto g D (𝓝 0) := by
  have h:= v.inner (𝕜:=ℂ) u
  rw [inner_zero_right] at h; exact h.congr' (e.mono fun _ w=>w.symm)
include R v p
lemma losesOld (h: MatureAfter (flipDose F 3))(u: MatureAfter G) :
    Tendsto (fun i=> P.arrayFine x (c (A i)) (r (A i)) (T i) F G) D (𝓝 (0:CrossRead)) :=
  tendsto_pi_nhds.mpr (fun Z => tendsto_pi_nhds.mpr (fun W =>
    no_read H _ _ _ (old_cost Z (flipDose F 3) R Y D A T v p h) (old_cost W G R Y D A T v p u)
      (((v.eventually (eventually_before Z F (trans6 R) h)).and ((v.eventually (eventually_after W G (trans6 R) u)).and p)).mono
        (fun i w=> relation_to_old Z W F G (c (A i)) (r (A i)) (T i) (x:=x) w.1 w.2.1 w.2.2))))

end costs
#print axioms obstruction_test
#print axioms actualDisconnected
#print axioms losesOld
#print axioms shift_duration
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
