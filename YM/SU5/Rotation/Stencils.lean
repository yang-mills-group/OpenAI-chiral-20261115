import YM.SU5.Rotation.Noise
import YM.SU5.FiniteGaugeData.Tapestry.Baldachin
-- Raiment for threshold/beta names
import YM.SU5.FiniteGaugeData.Tapestry.Raiment

/-!
# Actual coarse stencil and ascent of scalar tests
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 350000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tapestry.RotationGap
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
open SU5Rotation

/-- The observable is put in slot 0 below, but the stencil can be used at any slot.
Keep both endpoints of the links all the way, take *first Pane*. -/
def sites (p : Face ℤ) : Finset Cover := (visits p.1 (square p.2.val.1 p.2.val.2)).toFinset

def traceFamily (K : Calibration) (p : Face ℤ) : Family K :=
  scalar K (fun V => (traceTest (faceValue V.1 p) : ℂ))

theorem traceFamily_test (K : Calibration) (p : Face ℤ) :
    InTest K false (sites p) false (traceFamily K p) := by
  let F (V : LinksC) := (traceTest (faceValue V p) : ℂ)
  have H : Continuous F := Complex.continuous_ofReal.comp
    (continuous_traceTest.comp (continuous_travel _ _))
  refine InTest.seed (Coeff.fromC _ (sites p) H (fun U V h => ?_))
  have he : faceValue U p = faceValue V p := by
    apply travel_local _ _ U V
    exact fun k h₁ h₂ => h k (List.mem_toFinset.mpr h₁) (List.mem_toFinset.mpr h₂)
  unfold F; rw [he]

/-- Face at the actual period and gauge size. -/
def perFace (n : Side) (p : Face ℤ) : Face (Per (More n)) := (wrap (More n) p.1,p.2)

theorem traceFamily_eval (K : Calibration) (p : Face ℤ) (m : Side) (V : Fields (K.c m)) :
    traceFamily K p m V = (torusTrace (perFace (K.c m) p) V.1 : ℂ) • 1 := by
  have he : faceValue (onC (K.c m) V.1) p = faceValue V.1 (perFace (K.c m) p) := by
    unfold onC faceValue perFace; rw [travel_at]; simp
  change (traceTest (faceValue (onC (K.c m) V.1) p) : ℂ) • _ = _
  rw [he]; rfl

theorem traceFamily_neutral (K : Calibration) (p : Face ℤ) : Neutral K (traceFamily K p) := by
  intro m g x
  rw [traceFamily_eval, traceFamily_eval, twist_scalar, map_one]
  unfold torusTrace
  rw [show (simultaneous g x).1 = gauge g x.1 from rfl, face_gauge, traceTest_conj]

def plaque (K : Calibration) (p : Face ℤ) : Dome K :=
  ⟨traceFamily K p,broadCompile K (sites p) (traceFamily_test K p).widen⟩

lemma plaque_bay (K : Calibration) (p : Face ℤ) (wide : Bool) :
    plaque K p ∈ bay K (sites p) wide := by
  cases wide; exact traceFamily_test K p; exact (traceFamily_test K p).widen

lemma plaque_enclave (K : Calibration) (p : Face ℤ) : plaque K p ∈ enclave K :=
  traceFamily_neutral K p

/-- Scalar test on just the first torus Pane. -/
def pureMark (n : Side) (F : Pane n → ℂ) : Mark n := fun x => F x.1 • 1

lemma pureMark_mul (n : Side) (F H : Pane n → ℂ) :
    pureMark n F * pureMark n H = pureMark n (F*H) := by
  funext x; change (_ • (1 : FC (Single n))) * (H x.1 • 1) = (F x.1 * H x.1) • 1
  rw [Algebra.smul_mul_assoc, one_mul, mul_smul]

open Push.GridApprox

section step
variable {N P : Side} (G : Ratio N P) (A : StepData (More N) (More P)) (j : ℕ)
    (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)

lemma gathered_scalar (W : Fields P) (V : Fields N) (F : Pane N → ℂ) :
    gathered G j Q M ho q d (pureMark N F) W V = F V.1 • (1:FC _) := by
  have h : gathered G j Q M ho q d (pureMark N F) W V =
      gathered G j Q M ho q d (F V.1 • (1:Mark N)) W V := by
    unfold gathered avgF Advance.before; rfl
  rw [h, collectScale, collectUnit]

lemma assembled_scalar (W : Fields P) (V : Pane N) (F : Pane N → ℂ) :
    assembled G j Q M ho q d l (pureMark N F) W V = F V • (1 : FC _) := by
  unfold Advance.assembled; simp_rw [gathered_scalar]
  change (∫ _ : Ids N, F V • (1 : FC (Single P)) ∂depot N) = _
  simp only [integral_const,probReal_univ,one_smul]

-- A formula of the defined integrals; used with actual integrability below.
lemma push_scalar (F : Pane N → ℂ) :
    pushMark G A j Q M ho q d β l (pureMark N F) = pureMark P (back A β F) := by
  funext W
  have hx (V : Pane N) : A.density β W.1 V • (F V • (1 : FC (Single P))) =
      ((A.density β W.1 V : ℂ) * F V) • 1 := by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; rfl
  unfold pushMark linkLaw; simp_rw [assembled_scalar, hx]
  unfold pureMark back; exact integral_smul_const (𝕜 := ℂ) _ _
end step

section course
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
    (H:Real.exp 1 ≤ Λ.x) (s i k:ℕ)
local notation "K" => tent Y H
local notation "N" => Journey.side Y i s
local notation "P" => Journey.side Y i (s+1)
local notation "β" => patternβ Y s i k
local notation "A" => patternA Y s i k

lemma ascender_scalar_eq (F : Pane N → ℂ) :
    ascender Y s i k (pureMark N F) = pureMark P (back A β F) := by
  unfold ascender nextMark; apply push_scalar

lemma pattern_kernel : (patternA Y s i k).IsKernel (patternβ Y s i k) SU.group :=
  (A).isKernel (Y.pilot_steps s i k).2.2 β

/-- Scalar kernel formula for the actual ascent. Bounded Borel input;
apply at any `PairIdx`. Includes that the formula uses ordinary integrals and
again gives bounded Borel output. (Even holds without PairIdx, as a statement
about these defined operations alone.) -/
theorem ascender_scalar {F : Pane N → ℂ} (p : Envelope F) :
    Envelope (Push.GridApprox.back (G:=SU.group) A β F) ∧
    ∀ W : Fields P,
      Integrable (fun V => ((A).density β W.1 V : ℂ) * F V) (prior SU.group (More N)) ∧
      ascender Y s i k (pureMark N F) W =
        (∫ V, ((A).density β W.1 V : ℂ) * F V ∂prior SU.group (More N)) • 1 :=
  ⟨back_env (pattern_kernel Y s i k) p, fun W =>
    ⟨Env.integrableX (back_slice (pattern_kernel Y s i k) p W.1) _,
      congrFun (ascender_scalar_eq Y s i k F) W⟩⟩

/-- `Noise`'s real average is exactly that used in the scalar advance. -/
lemma ascender_real (W : Fields P) (F : Pane N → ℝ) :
    ascender Y s i k (pureMark N (fun x => (F x : ℂ))) W =
      (SU5Rotation.average A β W.1 F : ℂ) • 1 := by
  let h : back A β (fun x => (F x : ℂ)) W.1 = (SU5Rotation.average A β W.1 F : ℂ) := by
    have h (x) : ((A).density β W.1 x : ℂ) * (F x : ℂ) = ((F x * (A).density β W.1 x : ℝ):ℂ) := by
      rw [Complex.ofReal_mul,mul_comm]
    unfold back; simp_rw [h]
    exact integral_ofReal (𝕜:=ℂ) (f := fun x => F x * (A).density β W.1 x)
  rw [ascender_scalar_eq, pureMark, h]

lemma pattern_real_paid {F : Pane N → ℝ} (p : Envelope F) (W : Pane P) :
    Integrable (fun V => F V * (A).density β W V) (prior SU.group (More N)) :=
  (p.mul (slice_env A β (Y.pilot_steps s i k).2.2 W)).integrable _

/-- Period rendering of this supported stencil. -/
lemma exhibit_plaque (p : Face ℤ) :
    exhibit Y H s i (plaque K p).val = pureMark N (fun x => (torusTrace (perFace N p) x : ℂ)) :=
  sendTrace (tent Y H) p (momentm Y i s) (Journey.side Y i s) (terrain Y H (Y.ir i) s)
where
  sendTrace (K' : Calibration) (p : Face ℤ) (m O : Side) (h : K'.c m = O) :
      arrange _ _ h ((traceFamily K' p) m) =
        pureMark O (fun x => (torusTrace (perFace O p) x : ℂ)) := by
    subst O; exact funext (traceFamily_eval K' p m)

lemma exhibit_plaque_sq (p : Face ℤ) :
    exhibit Y H s i ((plaque K p)^2).val =
      pureMark N (fun x => ((torusTrace (perFace N p) x^2 : ℝ) : ℂ)) := by
  rw [pow_two]; change exhibit Y H s i ((plaque K p).val * (plaque K p).val) = _
  rw [actual_product, exhibit_plaque, pureMark_mul]; congr 1; ext1 x
  simp only [Pi.mul_apply, pow_two, Complex.ofReal_mul]

/-- Floor for the course, fixed before choosing volume index or cutoff. -/
def varianceFloor (Λ : Preparation) (s : ℕ) : ℝ :=
  noiseFloor (Course.ceiling Λ s) Λ.K.bind.penalty * haarVariance

theorem varianceFloor_pos (Λ : Preparation) (s : ℕ) : 0 < varianceFloor Λ s :=
  varianceBound_pos ..

def moment₁ (p : Face ℤ) (W : Pane (Journey.side Y i (s+1))) :=
  SU5Rotation.average (patternA Y s i k) (patternβ Y s i k) W (torusTrace (perFace N p))

def moment₂ (p : Face ℤ) (W : Pane (Journey.side Y i (s+1))) :=
  SU5Rotation.average A β W (fun x => torusTrace (perFace N p) x ^ 2)

theorem ascend_plaque (p : Face ℤ) (W : Fields P) :
    ascender Y s i k (exhibit Y H s i (plaque K p).val) W =
      (moment₁ Y s i k p W.1 : ℂ) • 1 := by
  rw [exhibit_plaque]; exact ascender_real ..

theorem ascend_plaque_sq (p : Face ℤ) (W : Fields P) :
    ascender Y s i k (exhibit Y H s i ((plaque K p)^2).val) W =
      (moment₂ Y s i k p W.1 : ℂ) • 1 := by
  rw [exhibit_plaque_sq]; exact ascender_real ..

lemma moments_integrable (p : Face ℤ) (W : Pane P) :
    Integrable (fun x => torusTrace (perFace N p) x * (A).density β W x) (prior SU.group (More N)) ∧
    Integrable (fun x => torusTrace (perFace N p) x ^ 2 * (A).density β W x) (prior SU.group (More N)) :=
  ⟨pattern_real_paid Y s i k (Env.compact (continuous_torusTrace (perFace N p))) W,
    pattern_real_paid Y s i k (Env.compact ((continuous_torusTrace (perFace N p)).pow 2)) W⟩

/-- Every pair paying for the sharp step. More-side at least two so even the
independent-link argument needs no further hypothesis on volume. -/
theorem moments_gap (p : Face ℤ) (h : Satin.PairIdx Y s i k) (W : Pane P) :
    varianceFloor Λ s ≤ moment₂ Y s i k p W - moment₁ Y s i k p W^2 := by
  have hp : (A).kernel.penalty = Λ.K.bind.penalty := by rw [alignedMarks]
  have hβ : |patternβ Y s i k| ≤ Course.ceiling Λ s := abs_le.mpr (Y.seated s i k h.2)
  have hc : 1 < (More (Journey.side Y i s)).val := by
    exact lt_of_lt_of_le one_lt_two (Nat.le_mul_of_pos_left 2 (Journey.side Y i s).property)
  unfold varianceFloor; rw [←hp]
  exact cutoff_variance A β (Course.ceiling Λ s) hβ (Y.pilot_steps s i k).2.2 hc (perFace N p) W

end course
end YM.CF.Buffered.Afterglow.Tapestry.RotationGap

#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.plaque_enclave
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.ascender_scalar
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.ascend_plaque
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.ascend_plaque_sq
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.moments_gap
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.moments_integrable
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.varianceFloor_pos
