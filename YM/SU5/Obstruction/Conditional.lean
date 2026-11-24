import YM.SU5.Obstruction.Finite
import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme

/-!
# Strictly positive conditional variance, at fixed support in the limit charts

Real, first-argument Borel stencils inside the wide, even observable system.
Pointwise, not a.e. No continuum motion or transformation law is assumed.
We read back the scalar evaluations at upper torus hosts using the given
`eyes_native`, throughout the actual cone limit, and thus capture the
`liftD` of that Exhibition.
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
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Buffered.Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

section ScalarChart

variable (K : Calibration) (S : Finset Cover)

def scalarTag : Evens S := ⟨∅, by simp [tagWord, Sound.treble]⟩

lemma spool_scalar (n : Side) : spool n (tagWord S (scalarTag S).val) = 1 := by
  simp [scalarTag,tagWord,spool]

def constantCanvas : Swatch S := Pi.single (scalarTag S) (pigment S (g:=fun _ => 1)
  { narrow := fun _ => by contradiction
    env := Env.compact (show Continuous (fun _ : PairsC => (1:ℂ)) from continuous_const)
    locus := fun _ _ _ _ => rfl })

lemma constantCanvas_tag (x : PairsC) : daub S (constantCanvas S (scalarTag S)) x = 1 := by
  simp [constantCanvas]

lemma constantCanvas_other {i : Evens S} (h : i ≠ scalarTag S) (x : PairsC) :
    daub S (constantCanvas S i) x = 0 := by
  unfold constantCanvas
  rw [Pi.single_eq_of_ne h]; rfl

lemma render_constant : render S K (constantCanvas S) = 1 := by
  funext n W
  rw [appearRender, appearSpool, Finset.sum_eq_single (scalarTag S)]
  · rw [constantCanvas_tag, spool_scalar, one_smul]; rfl
  · intro i _ hi
    rw [constantCanvas_other S hi, zero_smul]
  simp

/-- Candidate first-Pane coefficient (defined on the **cover**) of a real scalar output. -/
def scalarPart (f : Swatch S) (v : LinksC) := (daub S (f (scalarTag S)) (v,1)).re

lemma scalarPart_locus (f : Swatch S) : LocalOn S (scalarPart S f) :=
  fun x y h => congrArg Complex.re ((authentic S _).locus (x,1) (y,1) h (fun _ _ _ => rfl))

lemma scalarPart_env (f : Swatch S) : Envelope (scalarPart S f) := Env.along (g:=fun x : LinksC => (x,(1:LinksC)))
  (Girt.pole_w _ Complex.re Complex.continuous_re (authentic S (f (scalarTag S))).env)
  (measurable_id.prodMk measurable_const)

def RealFirst (f : Swatch S) : Prop :=
  (∀ x : PairsC, daub S (f (scalarTag S)) x = (scalarPart S f x.1 : ℂ)) ∧
    ∀ x (j : Evens S), j ≠ scalarTag S → daub S (f j) x = 0

lemma render_real {f : Swatch S} (h : RealFirst S f) :
    render S K f = Buffered.scalar K fun x => (scalarPart S f x.1 : ℂ) := by
  funext m W
  rw [appearRender, appearSpool, Finset.sum_eq_single (scalarTag S)]
  · rw [h.1 _, spool_scalar]; rfl
  · intro j _ hj
    rw [h.2 _ j hj, zero_smul]
  simp

-- evaluation from Swatch topology
lemma tendsto_daub {α : Type*} {q : Filter α} {f : α → Swatch S} {w : Swatch S}
    (p : Tendsto f q (𝓝 w)) (j : Evens S) (x : PairsC) :
    Tendsto (fun i => daub S (f i j) x) q (𝓝 (daub S (w j) x)) := by
  have ht : Continuous (fun v : Pigment S => daub S v x) :=
    (lp.lipschitzWith_one_eval ∞ x).continuous.comp continuous_subtype_val
  exact ht.continuousAt.tendsto.comp ((continuous_apply j).continuousAt.tendsto.comp p)

open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
    (H : Real.exp 1 ≤ Λ.x)

lemma scalar_at_host (n i : ℕ) (h : Hosp S (side Y i n))
    (f : Swatch S) (g : Pane (side Y i n) → ℝ)
    (p : present Y H n i S f = scalarMark fun x => (g x : ℂ))
    (x : PairsC) :
    daub S (f (scalarTag S)) x = (g (graft S _ x.1) : ℂ) ∧
      ∀ j : Evens S, j ≠ scalarTag S → daub S (f j) x = 0 := by
  obtain ⟨m, hm⟩ := eyes_native Y H n i S h
  have he (j : Evens S) : daub S (f j) x = (g (graft S _ x.1) : ℂ) • m j 1 := by
    rw [(hm f x j).2, p, scalarMark, map_smul]; rfl
  have h1 (j : Evens S) : daub S (constantCanvas S j) x = m j 1 := by
    rw [(hm (constantCanvas S) x j).2, present_exhibit, render_constant, actual_one]; rfl
  constructor
  · rw [he, ← h1, constantCanvas_tag, smul_eq_mul, mul_one]
  intro j hj
  rw [he, ← h1, constantCanvas_other S hj, smul_zero]

/-- Pass from (potentially varying) upper host information to pointwise real
and first-argument information on the entire chart. -/
lemma scalar_limit {α : Type*} {q : Filter α} [q.NeBot] {f : α → Swatch S} {w : Swatch S}
    (p : Tendsto f q (𝓝 w)) {n : ℕ} {r : α → ℕ} {g : ∀ i : α, Pane (side Y (r i) n) → ℝ}
    (h : ∀ᶠ i in q, Hosp S (side Y (r i) n) ∧
      present Y H n (r i) S (f i) = scalarMark fun x => (g i x : ℂ)) :
    RealFirst S w ∧
      ∀ x : LinksC, Tendsto (fun i => g i (graft S _ x)) q (𝓝 (scalarPart S w x)) := by
  have hv (x : PairsC) : Tendsto (fun i => (g i (graft S _ x.1) : ℂ)) q
      (𝓝 (daub S (w (scalarTag S)) x)) :=
    (tendsto_daub S p (scalarTag S) x).congr' (h.mono fun i hi =>
      (scalar_at_host S Y H n (r i) hi.1 (f i) (g i) hi.2 x).1)
  have ht (x : LinksC) : Tendsto (fun i => g i (graft S _ x)) q (𝓝 (scalarPart S w x)) := by
    unfold scalarPart
    exact (Complex.continuous_re.continuousAt.tendsto.comp (hv (x,1)))
  refine ⟨⟨?_,?_⟩, ht⟩
  · intro x
    exact tendsto_nhds_unique (hv x) (Complex.continuous_ofReal.continuousAt.tendsto.comp (ht x.1))
  intro x j hj
  exact tendsto_nhds_unique_of_eventuallyEq (tendsto_daub S p j x) tendsto_const_nhds (h.mono fun i hi =>
    (scalar_at_host S Y H n (r i) hi.1 (f i) (g i) hi.2 x).2 j hj)

end ScalarChart

section Limit
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
  {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Buffered.Family (tent Y H) → ℂ}
  {L : Rack Λ l} {B : Clay Λ l} (D : Exhibition Y H a b I E L B)
  (n : ℕ) (p : Lattice.Face ℤ)
local notation "K" => tent Y H
local notation "i₀" t:max => a (WedgeStage.vol t)
local notation "k₀" t:max => b (WedgeStage.uv t)
local notation "T" => followBox (Λ:=Λ) (l:=l) (faceSites p)

def faceDome : Dome (tent Y H) := ⟨faceFamily K p, broadCompile K _ (faceFamily_test K p true)⟩

lemma faceDome_bay (w : Bool) : faceDome Y H p ∈ bay K (faceSites p) w := faceFamily_test K p w
lemma faceDome_enclave : faceDome Y H p ∈ enclave K := (enclave_spec K).mpr (faceFamily_gauge K p)

def inputFabric := trophy K (faceDome Y H p) (faceDome_bay Y H p true)
def inputFabricTwo := trophy K (faceDome Y H p * faceDome Y H p)
  ((bay K (faceSites p) true).mul_mem (faceDome_bay Y H p true) (faceDome_bay Y H p true))
lemma badge_face : badge K (faceSites p) (inputFabric Y H p) = faceDome Y H p := trophy_at ..
lemma badge_face_two : badge K (faceSites p) (inputFabricTwo Y H p) =
    faceDome Y H p * faceDome Y H p := trophy_at ..

def limitFace (B : Clay Λ l) := B (faceSites p) n (inputFabric Y H p)
def limitFaceTwo (B : Clay Λ l) := B (faceSites p) n (inputFabricTwo Y H p)

lemma rise_face : D.liftD Y H n (faceDome Y H p) = badge K T (limitFace Y H n p B) := by
  rw [← badge_face]; exact D.fromLocal Y H n _ _

lemma rise_face_two : D.liftD Y H n (faceDome Y H p * faceDome Y H p) =
    badge K T (limitFaceTwo Y H n p B) := by
  rw [← badge_face_two]; exact D.fromLocal Y H n _ _

include D
lemma real_face :
    RealFirst T (limitFace Y H n p B) ∧
      ∀ x : LinksC, Tendsto
        (fun t : WedgeStage => faceStep Y n (i₀ t) (k₀ t) p (graft T _ x))
        followStage (𝓝 (scalarPart T (limitFace Y H n p B) x)) := by
  let S := faceSites p
  let f := inputFabric Y H p
  apply scalar_limit T Y H (D.buoy Y H S n f) (n:=n+1) (r:=fun t => i₀ t) (g:=fun t => faceStep Y n (i₀ t) (k₀ t) p)
  have h : render S K f = faceFamily K p := congrArg Subtype.val (badge_face Y H p)
  filter_upwards [D.uniformRoad Y H S n] with t ht
  refine ⟨Roomy.seats ht.2.2,?_⟩
  change present Y H (n+1) _ (followBox (Λ:=Λ) (l:=l) S) (coupon Y H S n (i₀ t) (k₀ t) f) = _
  rw [onSpanned _ _ _ _ _ _ ht,present_exhibit,h]; exact ascend_face Y H n _ _ p ht.1

lemma real_face_two :
    RealFirst T (limitFaceTwo Y H n p B) ∧
      ∀ x : LinksC, Tendsto
        (fun t : WedgeStage => faceStepTwo Y n (i₀ t) (k₀ t) p (graft T _ x))
        followStage (𝓝 (scalarPart T (limitFaceTwo Y H n p B) x)) := by
  let S := faceSites p
  let f := inputFabricTwo Y H p
  apply scalar_limit T Y H (D.buoy Y H S n f) (n:=n+1) (r:=fun t => i₀ t) (g:=fun t => faceStepTwo Y n (i₀ t) (k₀ t) p)
  have h : render S K f = faceFamily K p * faceFamily K p := congrArg Subtype.val (badge_face_two Y H p)
  filter_upwards [D.uniformRoad Y H S n] with t ht
  refine ⟨Roomy.seats ht.2.2,?_⟩
  change present Y H (n+1) _ (followBox (Λ:=Λ) (l:=l) S) (coupon Y H S n (i₀ t) (k₀ t) f) = _
  rw [onSpanned _ _ _ _ _ _ ht,present_exhibit,h]; exact ascend_face_two Y H n _ _ p ht.1

lemma advance_face_val : (D.liftD Y H n (faceDome Y H p)).val = Buffered.scalar K
    fun x => (scalarPart T (limitFace Y H n p B) x.1 : ℂ) := by
  rw [rise_face, domTag]; exact render_real K T (real_face Y H D n p).1
lemma advance_two_val : (D.liftD Y H n (faceDome Y H p * faceDome Y H p)).val = Buffered.scalar K
    fun x => (scalarPart T (limitFaceTwo Y H n p B) x.1 : ℂ) := by
  rw [rise_face_two, domTag]; exact render_real K T (real_face_two Y H D n p).1

omit D
-- `D.liftD Y H` is the existing selected-course map, with its actual
-- fixed-support norm-limit provision above. Don't replace it by a new
-- averaging and in particular don't upgrade to an algebra hom.
def faceVariance : Dome K :=
  D.liftD Y H n (faceDome Y H p * faceDome Y H p) -
    D.liftD Y H n (faceDome Y H p) * D.liftD Y H n (faceDome Y H p)

def varianceCoeff (B : Clay Λ l) (x : LinksC) : ℝ :=
  scalarPart T (limitFaceTwo Y H n p B) x - (scalarPart T (limitFace Y H n p B) x)^2

include D
lemma faceVariance_val : (faceVariance Y H D n p).val =
    Buffered.scalar K fun x => (varianceCoeff Y H n p B x.1 : ℂ) := by
  let Y₁ := D.liftD Y H n (faceDome Y H p)
  let Y₂ := D.liftD Y H n (faceDome Y H p * faceDome Y H p)
  change Y₂.val - (Y₁.val * Y₁.val) = _
  unfold Y₂ Y₁; rw [advance_two_val, advance_face_val]
  funext m x
  simp only [Pi.sub_apply, Pi.mul_apply, scalar, varianceCoeff, Complex.ofReal_sub, pow_two,
    Complex.ofReal_mul, sub_smul, Algebra.smul_mul_assoc, one_mul, smul_smul]

lemma variance_bay : faceVariance Y H D n p ∈ bay K T true := by
  let X := faceDome Y H p
  let h : X ∈ bay K (faceSites p) true := faceDome_bay ..
  let h1 := D.risePay Y H n _ h
  exact (bay K T true).sub_mem (D.risePay Y H n (faceSites p)
    ((bay K (faceSites p) true).mul_mem h h)) ((bay K T true).mul_mem h1 h1)
lemma variance_enclave : faceVariance Y H D n p ∈ enclave K := by
  let h := faceDome_enclave Y H p
  let h1 := D.riseGauge Y H n h
  exact (enclave K).sub_mem (D.riseGauge Y H n ((enclave K).mul_mem h h))
    ((enclave K).mul_mem h1 h1)

omit D
lemma varianceCoeff_locus (B : Clay Λ l) : LocalOn T (varianceCoeff Y H n p B) :=
  fun x y h => by unfold varianceCoeff; rw [scalarPart_locus T _ x y h,scalarPart_locus T _ x y h]
lemma varianceCoeff_env (B : Clay Λ l) : Envelope (varianceCoeff Y H n p B) := by
  let u := scalarPart T (limitFace Y H n p B)
  let v := scalarPart T (limitFaceTwo Y H n p B)
  change Envelope (fun x => v x - u x ^ 2)
  have hu : Envelope u := scalarPart_env T _
  have hv : Envelope v := scalarPart_env T _
  simp_rw [pow_two,sub_eq_add_neg]
  exact hv.add (hu.mul hu).neg

include D in
lemma variance_bound (x : LinksC) : unitBudget Λ n ≤ varianceCoeff Y H n p B x := by
  apply ge_of_tendsto ((real_face_two Y H D n p).2 x |>.sub (((real_face Y H D n p).2 x).pow 2))
  filter_upwards [D.uniformRoad Y H (faceSites p) n, D.uniformRoom Y H (faceSites p) n] with t ht hr
  exact advance_variance_bound Y n _ _ p ht.1 (Roomy.seats hr) _

def inverseCoeff (B : Clay Λ l) (x : LinksC) := (varianceCoeff Y H n p B x)⁻¹
lemma inverse_locus (B : Clay Λ l) : LocalOn T (inverseCoeff Y H n p B) :=
  fun x y h => congrArg Inv.inv (varianceCoeff_locus Y H n p B x y h)
lemma inverse_meas (B : Clay Λ l) : Measurable (inverseCoeff Y H n p B) :=
  (varianceCoeff_env Y H n p B).meas.inv
include D
lemma inverse_bound (x : LinksC) : ‖inverseCoeff Y H n p B x‖ ≤ (unitBudget Λ n)⁻¹ := by
  have hp := variance_bound Y H D n p x
  have hu := unitBudget_pos Λ n
  unfold inverseCoeff
  rw [Real.norm_of_nonneg (inv_pos.mpr (hu.trans_le hp)).le]
  exact inv_anti₀ hu hp
lemma inverse_env : Envelope (inverseCoeff Y H n p B) :=
  ⟨inverse_meas Y H n p B, _, inverse_bound Y H D n p⟩

lemma inverse_test : InTest K true T false (Buffered.scalar K
    (fun x => (inverseCoeff Y H n p B x.1 : ℂ))) :=
  .seed ⟨fun _ => by contradiction, Env.along (envelope_ofReal (inverse_env Y H D n p)) measurable_fst,
    fun x y h _ => congrArg Complex.ofReal (inverse_locus Y H n p B x.1 y.1 h)⟩

def faceInverse : Dome K :=
  ⟨Buffered.scalar K (fun x => (inverseCoeff Y H n p B x.1 : ℂ)),
    broadCompile K T (inverse_test Y H D n p)⟩

lemma inverse_bay : faceInverse Y H D n p ∈ bay K T true := inverse_test Y H D n p
lemma inverse_identity : faceVariance Y H D n p * faceInverse Y H D n p = 1 := by
  apply Subtype.ext
  change (faceVariance Y H D n p).val *
      Buffered.scalar K (fun x => (inverseCoeff Y H n p B x.1 : ℂ)) = 1
  rw [faceVariance_val]
  funext m x
  simp only [scalar, inverseCoeff, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul,
    smul_smul, ← Complex.ofReal_mul, Pi.one_apply]
  rw [mul_inv_cancel₀ ((unitBudget_pos Λ n).trans_le (variance_bound Y H D n p _)).ne',
    Complex.ofReal_one, one_smul]
lemma inverse_enclave : faceInverse Y H D n p ∈ enclave K := by
  apply (colorFixed K).mpr
  intro R
  let u := pennant K R
  let V := faceVariance Y H D n p
  let W := faceInverse Y H D n p
  have ht : V * W = 1 := inverse_identity ..
  have hk : u V = V := (colorFixed K).mp (variance_enclave Y H D n p) R
  have hp : V * u W = 1 := calc
    _ = u V * u W := by rw [hk]
    _ = _ := by rw [← map_mul, ht, map_one]
  change u W = W
  calc
    _ = (W * V) * (u W) := by rw [mul_comm W, ht, one_mul]
    _ = _ := by rw [mul_assoc,hp,mul_one]

end Limit
end YM.CF.SatinRotation

#print axioms YM.CF.SatinRotation.variance_bound
#print axioms YM.CF.SatinRotation.inverse_identity
#print axioms YM.CF.SatinRotation.inverse_enclave
