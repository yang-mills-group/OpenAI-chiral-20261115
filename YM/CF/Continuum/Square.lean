import YM.CF.Continuum.TagMirror
import YM.CF.Scree.Locus

/-! # Normalized state and Gram evaluation on FiniteGaugeData stencils

A primary useful probe readout is complex **linear** in the ket. To
estimate Hermiticity it is particularly important not to overlook the phase of
the normalizing factor. `Square` refers to the depth-native reflected matrix,
computed on one chosen lattice below; not an assertion about differing levels'
spacing. The flip `theta (fullTurn m B i)` on even stencils extends to a
product (including the conjugation in `flipTime`); no exchange sign in this
even-only `localObs`/`nonnegativeTime` net. -/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function MeasureTheory Lattice Finset RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade
open scoped Topology InnerProductSpace BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {L m B N : Side} 
local notation "Λ" => CSide m B

def readLinear (F : Evaluation N) (x : Orbit N) : Phys N→L[ℂ]ℂ := (innerSL ℂ (mateK N)).comp (acts (F x.1))
def moment (W : Orbit N→ Phys N) (F : Evaluation N) : ℂ := ∫ x, readLinear F x (W x) ∂city N

section algebra
variable {W : Orbit N→ Phys N}
private lemma apply_integrable {I U P : Type*} [MeasurableSpace U] [NormedAddCommGroup P] [NormedSpace ℂ P]
    [TopologicalSpace I][CompactSpace I][Nonempty I][MeasurableSpace I][OpensMeasurableSpace I] [SecondCountableTopology I] [SecondCountableTopology (P→L[ℂ]ℂ)]
    {m : Measure U} {f:U→P} {j:U→I}(w : Integrable f m)(t : Measurable j)(X:I → (P→L[ℂ]ℂ))(h : Continuous X) : Integrable (fun u=>X (j u) (f u)) m := by
  have hc : Continuous (fun p : (P→L[ℂ]ℂ) × P=>p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have he : StronglyMeasurable (X ∘ j) := h.stronglyMeasurable.comp_measurable t
  obtain ⟨u,v,hu⟩:= isCompact_univ.exists_isMaxOn Set.univ_nonempty h.norm.continuousOn
  apply Integrable.mono' (w.norm.const_mul ‖X u‖) (hc.comp_aestronglyMeasurable (he.aestronglyMeasurable.prodMk w.aestronglyMeasurable)); exact Eventually.of_forall fun x=> ((X (j x)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hu (Set.mem_univ (j x))) (norm_nonneg _))
lemma integrable_read (t : Integrable W (city N)) (F : Evaluation N) (hF : Continuous F) : Integrable (fun x=>readLinear F x (W x)) (city N) := by
  let V(u : Pane N): Phys N→L[ℂ]ℂ:= (innerSL ℂ (mateK N)).comp (acts (F u))
  have h : Continuous V := Continuous.clm_comp continuous_const (acts_cont.comp hF)
  exact apply_integrable t (show Measurable (fun v: Orbit N=>v.1) from measurable_fst) V h
lemma moment_add (t : Integrable W (city N)) {F G : Evaluation N} (p : F∈allObs N) (q : G∈allObs N) : moment W (F+G)=moment W F+moment W G := by
  unfold moment; simp_rw [show ∀ x, readLinear (F+G) x (W x)= readLinear F x (W x)+readLinear G x (W x) from fun x=> (by change inner ℂ _ (acts (F x.1+G x.1) (W x))= _; rw [act_add,inner_add_right]; rfl)]; exact integral_add (integrable_read t F ((mem_allObs F).mp p).1) (integrable_read t G ((mem_allObs G).mp q).1)
lemma moment_scalar (F : Evaluation N) (a : ℂ) : moment W (a•F)=a*moment W F :=by
  unfold moment; rw [←integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_ ; dsimp only; change inner ℂ _ (acts (a • _) (W i))=_; rw [act_smul,inner_smul_right]; rfl

def momentForm (W : Orbit N→ Phys N) (t : Integrable W (city N)) : (allObs N) →ₗ[ℂ] ℂ where
  toFun F:=moment W F.val
  map_add' X Y:= moment_add t X.property Y.property
  map_smul' a X:=by change moment W ((a•X:allObs N).val)=a*moment W X.val; rw [Subalgebra.coe_smul]; exact moment_scalar X.val a

lemma read_ket_scalar (F : Evaluation N)(a : ℂ) : moment (fun i=> a • W i) F=a*moment W F :=by unfold moment; simp_rw [map_smul]; exact integral_const_mul a _
lemma read_beam (T : Orbit N→ Phys N) : moment T 1=∫ i, beamZ N (T i) ∂city N :=by unfold moment; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_ ; change inner ℂ _ (acts 1 (T i)) = _; rw [act_one]
end algebra
section normalize
variable {j : ℕ}{o : Odd L.val}{d : ℝ}(Yγ : Pricing j L o (Thread j))(Pγ : Grasp Yγ B d) (Xβ : GramM (CSide m B))(Kβ : Loom (CSide m B))
local notation "U" => partitionZ Xβ Pγ Kβ

def finiteForm (F : Evaluation Λ) : ℂ := moment (fun x=>U⁻¹ • denZ Xβ Pγ Kβ x) F
lemma by_denominator (F : Evaluation Λ) : finiteForm Yγ Pγ Xβ Kβ F = moment (denZ Xβ Pγ Kβ) F / U :=by unfold finiteForm; rw [read_ket_scalar,div_eq_mul_inv,mul_comm]
lemma reads_mass (e : U≠0) : finiteForm Yγ Pγ Xβ Kβ (1:Evaluation Λ)=1 :=by rw [by_denominator, read_beam]; exact div_self e
lemma relative (F : Evaluation Λ) : finiteForm Yγ Pγ Xβ Kβ F=moment (fun x=>Complex.exp (-Xβ.v) • denZ Xβ Pγ Kβ x) F/(Complex.exp (-Xβ.v)*U):= by rw [by_denominator, read_ket_scalar, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
end normalize
section reflection
variable (i : Axis) (Fβ : Orbit (CSide m B)→ Phys (CSide m B))
local notation "xR" => orbitFlip m B i
def expectationsMirror (m B : Side)(i : Axis)(v : Evaluation (CSide m B)→ℂ) := ∀ {G}, G∈allObs (CSide m B)→ v (flipTime m B i G)=star (v G)

theorem by_density (h : ∀ᵐ x∂city Λ, arum (fullTurn m B i) false true (mateK _) (Fβ x)=Fβ (xR x)) : expectationsMirror m B i (moment Fβ) := by
  intro G _; unfold moment
  rw [Complex.star_def,←integral_conj, ← (show MeasurePreserving xR (city Λ) (city Λ) from keepsVolume i).integral_comp' (fun x=> readLinear (flipTime m B i G) x (Fβ x))]; apply integral_congr_ae
  filter_upwards [h] with x p
  rw [←p]; change inner ℂ _ (acts (theta (fullTurn m B i) (G (mirrorPane m B i (xR x).1))) (_))=_
  rw [orbitFlip_gauge, mirror_invol i, ←fullTurn_physical i, ← arum_act]; exact (by nth_rw 1 [←vacuum_turn (m:=m) (B:=B) i]; exact inner_turn ..)

def crossForm (m B:Side)(i:Axis)(v: Evaluation (CSide m B)→ℂ) (A B' : Evaluation (CSide m B)) := v (flipTime m B i A*B')
def reflectionForm {S:Type*}(v : Evaluation Λ→ℂ) (A : S→ Evaluation Λ) := Matrix.of (fun j k=> crossForm m B i v (A j) (A k))
theorem matrix_mirror {v : Evaluation Λ→ℂ} (p : expectationsMirror m B i v) {S:Type*} (A : S→ Evaluation Λ) (h : ∀ s, A s∈ allObs Λ) : (reflectionForm i v A).IsHermitian :=by
  ext j k; change star (v _) = v _; rw [← p, flipTime_order i (flipTime_all _ (h _)) (h _),flipTime_invol i (h _)]; apply Subalgebra.mul_mem _ (flipTime_all i (h _)) (h _)

-- reflection closure properties, no claim positivity for all functions
theorem passes_mirror {v : ℕ→ Evaluation Λ→ℂ}{u : Evaluation Λ→ℂ} (p : ∀ᶠ t in atTop, expectationsMirror m B i (v t)) (h : ∀ x ∈ allObs Λ,Tendsto (fun t=>v t x) atTop (𝓝 (u x))) : expectationsMirror m B i u := by
  intro x e; exact tendsto_nhds_unique_of_eventuallyEq (h _ (flipTime_all i e)) ((h x e).star) (p.mono fun i h=> h e)
end reflection
end YM.CF.Window
