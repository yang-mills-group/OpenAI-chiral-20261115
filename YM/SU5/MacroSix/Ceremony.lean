import YM.SU5.MacroSix.Arrivals
import YM.SU5.MacroSix.Decimal
import YM.SU5.MacroSix.Sunshine

/-! # The purchases together at the same resolution and fixed physical geometry

All observations using these f, g (left after sign/origin, right canonical), with
full time gap, are on the same `Consult` and receive at a fixed character. No claim
of point price off all-axes being continuous in the ambient H', and no claim of
PSD on the rectangular variant. Includes also eventual positive discrepancy of
actual consulted heights t (component normalization) against every split predictor
with marginal Ward. Small perturbation stability asserted in a precise L¹ test
sense *keeping strict order*. This allows independent perturbation of pose supports
(as incorporated in the tests), no fixed compact for the perturbative part;
`C^k` density of the new rectangular tests in their supports from `Credited`.
On the reflection test this stability actually keeps a uniform lower gram-ray
cost for the HERMITIAN part through those movements. Requiring also that its
real diagonal deviations or singular transport stay close is implied by
ordinary closeness costs (here all entries converge as the perturbation goes
to zero; just for the same order prices). Our perturbative statement below uses
`ReFloor`, in particular giving a strictly positive real lower on every diag.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Aria Pockets
open _root_.YM.MacroSix _root_.YM.MacroSix.ClockTest
namespace Spine
variable (P : Spine) (R : P.Register) (s n t : ℕ) (x : P.Spectrum0 3)
    (Q : P.Ellis 3 x) (f g : Vantage→ℝ)
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "U"=> Window.Family
local notation "Γ"=> P.otherSpectrum 3 3 x
local notation "Π"=> (P.seasons 3 Γ).ℚmeasure
local notation "A"=>P.measureField s n f g x
local notation "B" t:max => P.measureAt s n t f g x
local notation "Y"=>P.measureField s n (f ∘ mirrorΩ 3) f x
local notation "Z" t:max => P.measureAt s n t (f ∘ mirrorΩ 3) f x
local notation "ν" r:max=> P.darkSmear s n r f 0 x true

variable {T : Type*}
structure Through (L : Filter T)(a b : T → Vantage→ℝ) : Prop where
  valid : ∀ᶠ i in L, SmoothDensity (a i) ∧ SmoothDensity (b i) ∧ ∃ c : ℝ, P.OnFrame s n (a i) (b i) c
  left : Tendsto (fun i ↦ discrepancy (a i) f) L (𝓝 0)
  right : Tendsto (fun i ↦ discrepancy (b i) g) L (𝓝 0)

structure Questions : Prop where
  fden : SmoothDensity f
  gden : SmoothDensity g
  looking : ∃ c : ℝ, P.AddressPrice s n f g c

structure Realized : Prop where
  asks : P.Questions s n f g
  success : Success (P.measureField s n f g x)
  consultation(t:ℕ): s≤ t → P.Consult R s t n f g x
  integrates (z w: Window.Family) : Integrable (weightKernel (fun y z' ↦ P.fieldKernel s n x y z' z w) f g)
  limits : Tendsto (fun t ↦ P.measureAt s n t f g x) atTop (𝓝 (P.measureField s n f g x))
  finer : ∀ᶠ t in atTop, Success (P.measureAt s n t f g x) ∧
    ∀ M : P.Test →ₗ[ℂ] ℂ, PaintedSplit P.par t M →
      Success (P.measureAt s n t f g x-P.respond s t n f g M)

include Q in
lemma realize (p : P.StockClear n) (q : P.Questions s n f g) (e : Success (P.measureField s n f g x)) :
    P.Realized R s n x f g := by
  obtain ⟨c,u⟩:= q.looking
  let α i j:= P.consult_limit s n i j f g x Q q.fden q.gden u.funds
  let χ t (v:s ≤ t) := P.obeys_consult R s t n f g x q.fden.compact q.gden.compact u.funds p v
  refine ⟨q,e,χ,fun i j ↦ (α i j).1,entry_tendsto _ _ _ (fun i j ↦ (α i j).2),?_⟩
  filter_upwards [eventually_success atTop (fun t ↦ B t) (P.measureField s n f g x) (fun i j ↦ (α i j).2) e,
    eventually_ge_atTop s] with t u v
  exact ⟨u,fun M h ↦ by rw [(χ t v).opponent M h,sub_zero]; exact u⟩

variable (V : Set E4)
-- projection window (set scaled before i; inside given Octant confidence calibration).
-- PSD purchase & gram identity & actual positive-side H' vectors.
local notation "pV"=> Cheer.press (P.dew s n) V
structure Forever : Prop where
  orientation : P.ReflectedGrant s n f x V
  price (t:ℕ) (h:s≤ t): Z t = Matrix.gram ℂ (fun z:Window.Family ↦ P.weighLight s n t z f 0 x true)
  view (z:Window.Family) (t:ℕ) (h:s ≤ t):
    P.inFuture t x (P.smearField t f (P.sixBody s n z)) (P.weighLight s n t z f 0 x true)
  represents(z:Window.Family): Tendsto (fun t ↦ P.weighLight s n t z f 0 x true)
    atTop (𝓝 (P.enter 3 Γ (ν z)))
  real_measure : P.Realized R s n x (f ∘ mirrorΩ 3) f
  lower : ∃ d:ℝ,0<d ∧ (d:ℂ) • (1 : Matrix Window.Family _ ℂ) ≤
      Matrix.gram ℂ (fun z:Window.Family ↦ (Π).region pV (ν z)) ∧
    (d:ℂ) • (1 : Matrix Window.Family _ ℂ) ≤ P.measureField s n (f ∘ mirrorΩ 3) f x ∧
    ∀ d':ℝ, d'<d → ∀ᶠ t in atTop, (d':ℂ) • 1 ≤ P.measureAt s n t (f ∘ mirrorΩ 3) f x

lemma Forever.perturb_floor {d : ℝ}
    (p : P.Forever R s n x f V) (q : (d:ℂ) • 1 ≤ P.measureField s n (f ∘ mirrorΩ 3) f x)
    (L : Filter T)(a b : T → Vantage→ℝ)(v : P.Through s n (f∘mirrorΩ 3) f L a b)
    (h : P.Ellis 3 x) {d':ℝ} (e : d'<d) :
    ∀ᶠ i in L, ReFloor (P.measureField s n (a i) (b i) x) d' := by
  have he: ReFloor (Y) d:= by
    unfold ReFloor
    rw [sunrise_herm]; exact q
    exact p.orientation.answer.symm ▸ Matrix.isHermitian_gram ℂ (fun z:Window.Family ↦ ν z)
  exact ReFloor.retain e he L _ (fun i j ↦ P.variation_limit x s n i j (f∘mirrorΩ 3) f
    h L a b p.orientation.reflected p.orientation.smooth ⟨_,p.orientation.frame⟩ v.valid v.left v.right)

private lemma psiView (p : P.ReflectedGrant s n f x V) : ∀ (z:Window.Family)(i:ℕ) (_ : s ≤ i),
    P.inFuture i x (P.smearField i f (P.sixBody s n z)) (P.weighLight s n i z f 0 x true) :=
  fun z i e ↦ P.smoothFutures s n i z x f (fun i h ↦ ((sub_pos.mp (p.frame.after i h))).le) p.smooth.compact e
lemma ray_real (p : P.ReflectedGrant s n f x V) (v : s≤ t) :
    (Z t)=Matrix.gram ℂ (fun z : Window.Family ↦ P.weighLight s n t z f 0 x true) := by
    let G := p.smooth; let ψ:=psiView P s n x f V p
    ext1 i j
    let x₀:= P.smearField t f (P.sixBody s n i)
    let y₀:= P.smearField t f (P.sixBody s n j)
    obtain ⟨a,ha⟩:= ψ i t v; obtain ⟨b,hb⟩:= ψ j t v
    let A':= P.singleState 3 t x
    have hu := P.single_agrees 3 3 x t (P.reflectTest 3 x₀*y₀)
    refine (congrArg (fun r ↦ A' (r*y₀)) (P.reflect_smearField t f (P.sixBody s n i) 3 G.compact).symm).trans
      (hu.symm.trans ((P.released_gram 3 Γ t a b).symm.trans (congrArg₂ (inner ℂ) ha hb)))
private lemma lateRays (p : P.ReflectedGrant s n f x V) {d:ℝ} (k : (d:ℂ) • 1 ≤ Y) :
    ∀ d':ℝ,d'<d→ ∀ᶠ t in atTop,(d':ℂ) • 1 ≤ Z t := by
  have he := fun t (w:s≤ t) ↦ ray_real P s n t x f V p w
  let x' t := Z t
  have hp : ReFloor (Y) d:= by
    unfold ReFloor
    rw [sunrise_herm]; exact k
    exact p.answer.symm ▸ Matrix.isHermitian_gram ℂ (fun z : Window.Family ↦ ν z)
  intro d' w
  filter_upwards [ReFloor.retain w hp atTop x' p.raw_price,eventually_ge_atTop s] with t b c
  unfold ReFloor x' at b
  rw [sunrise_herm] at b; exact b
  exact (he t c).symm ▸ Matrix.isHermitian_gram ℂ (fun z : Window.Family ↦ P.weighLight s n t z f 0 x true)
include Q in
lemma believe (p : P.ReflectedGrant s n f x V) (u:P.StockClear n) :
    P.Forever R s n x f V := by
  have k := p.price.choose_spec
  exact ⟨p,(fun t h => ray_real P s n t x f V p h), psiView P s n x f V p,
    (fun z ↦ P.frameLight_limit s n z f 0 x p.smooth.smooth.continuous p.smooth.compact true Q),
    P.realize R s n x Q (f∘mirrorΩ 3) f u ⟨p.reflected,p.smooth,0,OnFrame.coverPrice p.frame p.reflected.compact p.smooth.compact⟩ p.survives,
    p.price.choose,k.1,k.2.1,k.2.2,lateRays P s n x f V p k.2.2⟩

lemma birthsAvail : ∃ (u : ClockTest.Space → ℝ) (g : ℝ → ℝ), SmoothDensity u ∧ TimeDensity g ∧ P.TimeFare s n g := by
  obtain ⟨g,p,w⟩:= prepare_time (Set.Ioi ((P.sixWidth s n 3):ℝ)) Set.nonempty_Ioi isOpen_Ioi
  obtain ⟨u,e,-⟩:= densityRoom (Set.univ:Set ClockTest.Space) Set.univ_nonempty isOpen_univ
  exact ⟨u,g,e,p,w⟩

lemma Realized.difference (p:P.Realized R s n x f g) {M: P.Test→ₗ[ℂ]ℂ} (h:Comparison M) (e : s≤ t) :
    P.respond s t n f g M=0 ∧ Success (P.measureField s n f g x-P.respond s t n f g M):= by
  have ht:=(p.consultation t e).opponent M (paintedSplit_of_ordinary Λ t h)
  rw [ht, sub_zero]; exact ⟨rfl,p.success⟩

include Q
lemma Realized.perturb (p : P.Realized R s n x f g) (h : P.StockClear n)
    (L : Filter T)(a b : T → Vantage→ℝ)(v : P.Through s n f g L a b) :
    Tendsto (fun i ↦ P.measureField s n (a i) (b i) x) L (𝓝 (P.measureField s n f g x)) ∧
      ∀ᶠ i in L, P.Realized R s n x (a i) (b i) := by
  let q:=p.asks
  obtain ⟨c,u⟩:= q.looking
  have he(i j:Window.Family):=(P.variation_limit x s n i j f g Q L a b q.fden q.gden ⟨c,u.funds⟩
    v.valid v.left v.right)
  refine ⟨entry_tendsto L _ _ he,?_⟩
  filter_upwards [eventually_success L _ _ he p.success, v.valid] with i t q'
  obtain ⟨f,hb,u,h'⟩:= q'; exact realize P R s n x Q _ _ h ⟨f,hb,u,h'.coverPrice f.compact hb.compact⟩ t

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms realize
#print axioms believe
#print axioms Forever.perturb_floor
#print axioms Realized.perturb
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
