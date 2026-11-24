import YM.SU5.Obstruction.Noise
import YM.SU5.FiniteGaugeData.Tapestry.Raiment
import YM.Lattice.Foliation

/-!
# The real plaquette test on the actual course — finite steps
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open Buffered
open Buffered.Afterglow Tapestry
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Buffered.Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Buffered.Afterglow Satin Tapestry
attribute [local instance] opCStarAlgebra

/-- scalar Mark, first-Pane. -/
def scalarMark {N : Side} (g : Pane N → ℂ) : Mark N := fun W => g W.1 • 1

lemma scalarMark_mul {N : Side} (g h : Pane N → ℂ) :
    scalarMark g * scalarMark h = scalarMark (fun v => g v * h v) := by
  funext W
  simp only [Pi.mul_apply, scalarMark, Algebra.smul_mul_assoc, one_mul, smul_smul]

section Push

variable {N P : Side} (G : Ratio N P) (A : StepData (More N) (More P))
  (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)
  (g : Pane N → ℂ) (X : Fields P)

lemma gather_scalar (Y : Fields N) :
    gathered G j Q M ho q d (scalarMark g) X Y = g Y.1 • 1 := by
  calc
    _ = gathered G j Q M ho q d (g Y.1 • (1 : Mark N)) X Y := rfl
    _ = _ := by rw [collectScale, collectUnit]

-- The formal equality works directly. For actual use always take
-- integrable coefficients; see scalar_kernel_integrable.
private lemma push_scalar :
    pushMark G A j Q M ho q d β l (scalarMark g) X =
      (∫ v, (A.density β X.1 v : ℂ) * g v ∂prior SU.group (More N)) • (1 : FC (Single P)) := by
  unfold pushMark linkLaw Advance.assembled
  simp_rw [gather_scalar, drawn]
  simp only [integral_const, probReal_univ, one_smul]
  simp_rw [← smul_assoc, Complex.real_smul]
  rw [integral_smul_const]

lemma scalar_kernel_integrable (h : A.patch.Branches A.kernel SU.group) (hg : Envelope g) :
    Integrable (fun v => (A.density β X.1 v : ℂ) * g v) (prior SU.group (More N)) := by
  have hv (v) : (A.density β X.1 v : ℂ) * g v = A.density β X.1 v • g v := by
    simp only [Complex.real_smul]
  simp_rw [hv]
  exact Env.integrableX (Env.scale (slice_env A β h X.1) hg) _

/-- Well-definedness also for the integrals on the Mark side of the computation. -/
lemma scalar_push_integrable (h : A.patch.Branches A.kernel SU.group) (hg : Envelope g) :
    Integrable (fun v : Pane N => A.density β X.1 v •
      Advance.assembled G j Q M ho q d l (scalarMark g) X v) (prior SU.group (More N)) ∧
    ∀ v : Pane N, Integrable (fun i =>
      gathered G j Q M ho q d (scalarMark g) X (drawn l (v,i))) (depot N) := by
  unfold Advance.assembled
  simp_rw [gather_scalar, drawn]
  simp only [integral_const, probReal_univ, one_smul]
  simp_rw [← smul_assoc, Complex.real_smul]
  exact ⟨(scalar_kernel_integrable A β g X h hg).smul_const _, fun v => integrable_const _⟩

end Push

section Course
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (s i k : ℕ)
local notation "σ" => side Y i s
local notation "β" => patternβ Y s i k
local notation "A" => patternA Y s i k

lemma patternBranches : (patternA Y s i k).patch.Branches (patternA Y s i k).kernel SU.group :=
  (Y.pilot_steps s i k).2.2

lemma ascend_kernelIsProb : (patternA Y s i k).IsKernel β SU.group :=
  (A).isKernel (patternBranches ..) β

lemma ascend_scalar_integrable {g : Pane σ → ℂ} (hg : Envelope g) (x : Fields (side Y i (s+1))) :
    Integrable (fun v => ((A).density β x.1 v : ℂ) * g v) (prior SU.group (More σ)) :=
  scalar_kernel_integrable A β _ x (patternBranches ..) hg

/-- For the indicated inputs there is no integrability caveat to the formula.
The identity used with the numerical integrals is at the real paid step of this course. -/
lemma ascend_scalar (_ : PairIdx Y s i k) {g : Pane σ → ℂ}
    (_ : Envelope g) :
    ascender Y s i k (scalarMark g) =
      scalarMark (fun u => ∫ v, ((A).density β u v : ℂ) * g v ∂prior SU.group (More σ)) :=
  funext fun x => push_scalar (Vale.apt (Y.ir i) Λ.block Λ.R.L s) A Λ.K.j (patternQ Y s i k).val
    _ Λ.R.odd_side Chi.canonical Λ.J.d β ((Y.voyage i).CapeT s) g x

def advanceCoeff (g : Pane σ → ℝ) (u : Pane (side Y i (s+1))) : ℝ :=
  ∫ v, (A).density β u v * g v ∂prior SU.group (More σ)

lemma advanceCoeff_defined {g : Pane σ → ℝ} (e : Envelope g) (u : Pane (side Y i (s+1))) :
    Integrable (fun v => (A).density β u v * g v) (prior SU.group (More σ)) :=
  ((slice_env A β (patternBranches ..) u).mul e).integrable _

lemma envelope_ofReal {T : Type*} [MeasurableSpace T] {f : T → ℝ} (h : Envelope f) :
    Envelope (fun v => (f v : ℂ)) := Girt.pole_w f Complex.ofReal Complex.continuous_ofReal h

lemma ascend_real (h : PairIdx Y s i k) {g : Pane σ → ℝ} (e : Envelope g) :
    ascender Y s i k (scalarMark fun v => (g v : ℂ)) =
      scalarMark fun u => (advanceCoeff Y s i k g u : ℂ) := by
  rw [ascend_scalar Y s i k h (envelope_ofReal e)]
  unfold advanceCoeff
  simp_rw [← Complex.ofReal_mul, integral_complex_ofReal]

end Course

section Stencil

variable (K : Calibration) (p : Lattice.Face ℤ)

def faceSites : Finset Cover := (visits p.1 (Lattice.square p.2.val.1 p.2.val.2)).toFinset

lemma faceSites_list : faceSites p = [p.1,p.1 + step p.2.val.1,
    p.1 + step p.2.val.1 + step p.2.val.2,p.1 + step p.2.val.2,p.1].toFinset :=
  congrArg List.toFinset (square_corners ..)

/-- The real normalized trace of exactly the defining holonomy around the plaquette. -/
def coverPlaquette (V : Lifted.LinksC) : ℝ := normalizedTrace (faceValue V p)

lemma coverPlaquette_cont : Continuous (coverPlaquette p) :=
  normalizedTrace_cont.comp (show Continuous fun V : Lifted.LinksC => faceValue V p from continuous_travel _ _)

lemma coverPlaquette_local : LocalOn (faceSites p) (coverPlaquette p) := by
  intro U V h
  apply congrArg normalizedTrace
  apply travel_local p.1 (Lattice.square p.2.val.1 p.2.val.2) U V
  exact fun e u v => h e (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)

variable (N : Side)

def wrapFace : Lattice.Face (Per (More N)) := (wrap (More N) p.1, p.2)

lemma wrapFace_admits (h : Hosp (faceSites p) N) :
    (wrapFace p N).1 + step (wrapFace p N).2.val.2 ≠ (wrapFace p N).1 := by
  let j := p.2.val.2
  intro he
  change wrap (More N) p.1 + step j = wrap (More N) p.1 at he
  have hv : wrap (More N) (p.1 + step j) = wrap (More N) p.1 := by
    rw [map_add, wrap_step, he]
  have h1 : p.1 ∈ faceSites p := by rw [faceSites_list]; simp
  have h2 : p.1 + step j ∈ faceSites p := by rw [faceSites_list]; simp [j]
  have heq := congrFun (h.seat_ h2 h1 hv) j
  simp at heq

def paneTrace (V : Pane N) := normalizedTrace (faceValue V (wrapFace p N))

lemma paneTrace_env : Envelope (paneTrace p N) := Env.compact
  (normalizedTrace_cont.comp
    (show Continuous fun V : Pane N => faceValue V (wrapFace p N) from continuous_travel _ _))

lemma coverPlaquette_on (V : Pane N) : coverPlaquette p (onC N V) = paneTrace p N V := by
  unfold coverPlaquette paneTrace faceValue wrapFace onC
  simp only [travel_at, add_zero]

/-- Our level's test in the native test grammar. -/
def faceFamily : Buffered.Family K := Buffered.scalar K fun v => ((coverPlaquette p v.1 : ℝ) : ℂ)

lemma faceFamily_test (b : Bool) : InTest K b (faceSites p) false (faceFamily K p) :=
  .seed (Coeff.fromC b _ (f:=fun x : LinksC => (coverPlaquette p x : ℂ))
    (Complex.continuous_ofReal.comp (coverPlaquette_cont p)) fun x y h =>
    congrArg Complex.ofReal (coverPlaquette_local p x y h))

lemma faceFamily_val (m : Side) :
    faceFamily K p m = scalarMark fun v => (paneTrace p (K.c m) v : ℂ) := by
  funext x
  simp only [faceFamily, scalar, scalarMark, coverPlaquette_on]

lemma faceFamily_gauge (m : Side) : covariant (faceFamily K p m) := by
  rw [faceFamily_val]
  intro g x
  simp only [scalarMark, simultaneous, Prod.map, paneTrace, normalizedTrace, face_gauge, Gauge.price_conj,
    twist_scalar, map_one]

end Stencil

section Course
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
  (s i k : ℕ)
local notation "σ" => side Y i s
local notation "A" => patternA Y s i k
local notation "K" => tent Y H

variable (p : Lattice.Face ℤ)

lemma exhibit_face : exhibit Y H s i (faceFamily K p) =
    scalarMark fun v => (paneTrace p σ v : ℂ) := by
  change arrange _ _ _ (faceFamily K p _) = _
  rw [faceFamily_val]; exact carry _
where
  carry {m n : Side} (h : m = n) : arrange m n h
      (scalarMark (fun v => (paneTrace p m v : ℂ))) =
      scalarMark fun v => (paneTrace p n v : ℂ) := by subst n; rfl

def faceStep := advanceCoeff Y s i k (paneTrace p σ)
def faceStepTwo := advanceCoeff Y s i k fun v => (paneTrace p σ v)^2

lemma ascend_face (h : PairIdx Y s i k) :
    ascender Y s i k (exhibit Y H s i (faceFamily K p)) =
    scalarMark fun u => (faceStep Y s i k p u : ℂ) := by
  rw [exhibit_face]
  exact ascend_real Y s i k h (paneTrace_env ..)

lemma ascend_face_two (h : PairIdx Y s i k) :
    ascender Y s i k (exhibit Y H s i ((faceFamily K p) * (faceFamily K p))) =
    scalarMark fun u => (faceStepTwo Y s i k p u : ℂ) := by
  rw [actual_product, exhibit_face, scalarMark_mul]
  unfold faceStepTwo
  simp_rw [pow_two, ← Complex.ofReal_mul]
  exact ascend_real Y s i k h ((paneTrace_env p σ).mul (paneTrace_env ..))

def unitBudget (Λ : Preparation) (s : ℕ) :=
  noiseFloor (Course.ceiling Λ s) Λ.K.bind.penalty * faceHaarVariance

theorem unitBudget_pos (Λ : Preparation) (s : ℕ) : 0 < unitBudget Λ s :=
  mul_pos (noiseFloor_pos ..) faceHaarVariance_pos

/-- Uniform in period and cutoff at the hosted paid step, with no premise on configuration. -/
theorem advance_variance_bound (h : PairIdx Y s i k) (hp : Hosp (faceSites p) σ)
    (V : Pane (side Y i (s+1))) :
    unitBudget Λ s ≤ faceStepTwo Y s i k p V - (faceStep Y s i k p V)^2 := by
  have hc := conditional_variance_face A (wrapFace p σ) (wrapFace_admits p σ hp)
    (show |patternβ Y s i k| ≤ Course.ceiling Λ s from abs_le.mpr (Y.seated s i k h.2))
    (patternBranches ..) V
  unfold unitBudget
  rw [← show (patternA Y s i k).kernel = Λ.K.bind from (Y.pilot_steps s i k).2.1]
  exact hc

end Course
end YM.CF.SatinRotation

#print axioms YM.CF.SatinRotation.ascend_face
#print axioms YM.CF.SatinRotation.advance_variance_bound
#print axioms YM.CF.SatinRotation.faceFamily_gauge
