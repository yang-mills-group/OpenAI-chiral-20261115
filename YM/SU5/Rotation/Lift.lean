import YM.SU5.Rotation.Stencils
import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme

/-!
# Variance floor in the fixed physical charts, and the inverse

Read at paying period/cutoff, realize on upper pairs via replants and `eyes_native`,
pass to the limit on the same exhibition, with its full qualifying cone.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tapestry.RotationGap
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
open SU5Rotation Exhibition

section chart
variable {S : Finset Cover}

def emptyMon (S : Finset Cover) : Evens S :=
  ⟨∅, by simp [tagWord, Sound.treble]⟩

def chartStd (S : Finset Cover) : Pigment S := pigment S (g:=fun _=>1)
  (show Coeff true S (fun _ => 1) from ⟨by simp, Env.compact continuous_const, fun _ _ _ _=> rfl⟩)

lemma readChartStd (x : PairsC) (t : Evens S) :
    daub S (nuance S (emptyMon S) (chartStd S) t) x = if t=emptyMon S then 1 else 0 := by
  split_ifs with h
  · rw [h, nuance, Pi.single_eq_same]; rfl
  rw [nuance, Pi.single_eq_of_ne h]; rfl

def coefficient {S : Finset Cover} (t : Evens S) (x : PairsC) : Swatch S →L[ℂ] ℂ :=
  let L : Swatch S →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp ((daubL S).comp (LinearMap.proj t))
  L.mkContinuous 1 (by
    intro v
    rw [one_mul]
    change ‖daub S (v t) x‖ ≤ ‖v‖
    exact (daubLe S (v t) x).trans (norm_le_pi_norm ..))

lemma renderScalar {F : Swatch S} {c : PairsC → ℝ} (K : Calibration)
    (h : ∀ (x : PairsC) t, coefficient t x F = if t=emptyMon S then (c x : ℂ) else 0) :
    render S K F = scalar K (fun x => (c x : ℂ)) := by
  funext m u
  rw [appearRender, appearSpool, sum_eq_single (emptyMon S)]
  · change coefficient (emptyMon S) _ F • _ = _
    rw [h, if_pos rfl, show tagWord S (emptyMon S).val = [] by simp [emptyMon, tagWord]]
    rfl
  · intro b _ hb
    rw [show daub S (F b) _ = 0 from (h _ b).trans (if_neg hb), zero_smul]
  simp
end chart

variable {Λ:Preparation} {l:ℕ}
    (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x) (s:ℕ)

local notation "K" => tent Y H
local notation "P" i:max => Journey.side Y i (s+1)
local notation "S↑" S:max => followBox (Λ:=Λ) (l:=l) S

/-- Host extraction on a scalar pure-Mark output. No a.e. arguments; in particular
what is read on an input cover pair may be compared directly, including with another
cover pair with the same first Pane. -/
theorem recover_scalar {S : Finset Cover} {i : ℕ} (e : Hosp S (Journey.side Y i s))
    {F : Swatch S} {c : Pane (Journey.side Y i s) → ℝ}
    (h : ∀ u, present Y H s i S F u = (c u.1 : ℂ) • 1) (x : PairsC) (t : Evens S) :
    coefficient t x F = if t=emptyMon S then ((c (graft S (Journey.side Y i s) x.1)) : ℂ) else 0 := by
  let I := nuance S (emptyMon S) (chartStd S)
  have hu : present Y H s i S I=1 := by
    rw [show I=nuance S (emptyMon S) (chartStd S) from rfl, show_note]
    funext z; unfold Satin.knot; change (1:ℂ) • _ = 1; simp [emptyMon,tagWord,spool]
  obtain ⟨m,w⟩ := eyes_native Y H s i S e
  have hr : m t 1 = if t=emptyMon S then 1 else 0 := by
    have he := (w I x t).2
    rw [hu, Pi.one_apply] at he
    exact he.symm.trans (readChartStd ..)
  change daub S (F t) x = _
  rw [(w F x t).2,h,map_smul,hr]; unfold replant; split_ifs <;> simp

section lift
variable {a b : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
    {L : Rack Λ l} {B : Clay Λ l} (D : Exhibition Y H a b I E L B)

local notation "A" => liftD Y H s D
local notation "i₀" t:max => a (WedgeStage.vol t)
local notation "k₀" t:max => b (WedgeStage.uv t)

-- General lemma for passing real scalars across varying period hosts.

/-- Candidate scalar coefficient in real/first-link cover variables of the lifted test.
(This extracts ONLY the real part of ONLY the empty-tag coefficient, using second-Pane
input equal to 1. We prove below when this suffices.) -/
def readLift {S : Finset Cover} (F : Dome (tent Y H))
    (p : F∈bay (tent Y H) S true) (x : LinksC) : ℝ :=
  -- let it depend on D (and its Clay B)
  (coefficient (emptyMon (S↑ S)) (x,1)
    (trophy (tent Y H) ((A) F) (D.risePay Y H s S p))).re

theorem toLobby {S : Finset Cover} (F : Dome (tent Y H)) (p : F∈bay (tent Y H) S true) :
    trophy (tent Y H) (liftD Y H s D F) (D.risePay Y H s S p) = B S s (trophy K F p) := by
  apply badge_inj (tent Y H)
  rw [trophy_at, ←fromLocal Y H s S D, trophy_at]

lemma scalarLift {S : Finset Cover} (F : Dome K) (p : F∈bay K S true)
    (u : (i k:ℕ) → Pane (Journey.side Y i (s+1)) → ℝ)
    (h : ∀ i k, Spanned Y S s i k →
      ∀ w, ascender Y s i k (exhibit Y H s i F.val) w=(u i k w.1 : ℂ) • 1) (x : PairsC) :
    Tendsto (fun t => u (i₀ t) (k₀ t) (graft (S↑ S) (P (i₀ t)) x.1)) followStage
      (𝓝 (readLift Y H s D F p x.1)) ∧
    ∀ t, coefficient t x (B S s (trophy K F p)) =
      if t=emptyMon (S↑ S) then ((readLift Y H s D F p x.1) : ℂ) else 0 := by
  let g := trophy K F p
  let c i k := coupon Y H S s i k g
  let M (z : WedgeStage) := u (i₀ z) (k₀ z) (graft (S↑ S) (P (i₀ z)) x.1)
  let Q := emptyMon (S↑ S)
  have hc (y : PairsC) (t : Evens (S↑ S)) :
      Tendsto (fun z => coefficient t y (c (i₀ z) (k₀ z))) followStage (𝓝 (coefficient t y (B S s g))) :=
    (coefficient t y).continuous.continuousAt.tendsto.comp (D.buoy Y H S s g)
  have he (y : PairsC) (hy : y.1=x.1) (t : Evens (S↑ S)) : ∀ᶠ z in followStage,
      coefficient t y (c (i₀ z) (k₀ z)) = if t=Q then (M z : ℂ) else 0 := by
    filter_upwards [D.uniformRoad Y H S s] with z hz
    unfold M
    rw [←hy]; apply recover_scalar Y H (s+1) (Roomy.seats hz.2.2)
    intro v; unfold c; rw [onSpanned Y H S s _ _ hz, present_exhibit, ←domTag, show badge K S g=F from trophy_at ..]
    exact h _ _ hz v
  have hk : Tendsto M followStage (𝓝 (readLift Y H s D F p x.1)) := by
    rw [readLift,toLobby Y H s D F p]
    apply (Complex.continuous_re.continuousAt.tendsto.comp (hc (x.1,1) Q)).congr'
    filter_upwards [he (x.1,1) rfl Q] with z hz
    change (coefficient Q _ _).re = M z
    rw [hz,if_pos rfl,Complex.ofReal_re]
  refine ⟨hk,fun t => tendsto_nhds_unique_of_eventuallyEq (hc x t) ?_ (he x rfl t)⟩
  change Tendsto (fun z => if t=Q then (M z : ℂ) else 0) followStage (𝓝 (if t=Q then (readLift Y H s D F p x.1:ℂ) else 0))
  by_cases ht : t=Q
  · simp_rw [if_pos ht]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp hk
  simp_rw [if_neg ht]; exact tendsto_const_nhds

private lemma lift_repr {S : Finset Cover} (F : Dome K) (p : F∈bay K S true)
    (h : ∀ x t, coefficient t x (B S s (trophy K F p)) =
      if t=emptyMon (S↑ S) then (readLift Y H s D F p x.1 : ℂ) else 0) :
    ((A) F).val = scalar K (fun x => (readLift Y H s D F p x.1 : ℂ)) ∧
      Coeff true (S↑ S) (fun x => (readLift Y H s D F p x.1 : ℂ)) := by
  let g := trophy K F p; let W := B S s g
  constructor
  · refine Eq.trans (congrArg Subtype.val (show (A) F = badge K (S↑ S) W from ?_))
      (renderScalar (tent Y H) (c:=fun x => readLift Y H s D F p x.1) h)
    rw [show W=B S s g from rfl, ←fromLocal Y H s S D, show badge K S g=F from trophy_at ..]
  rw [show (fun x : PairsC => (readLift Y H s D F p x.1 : ℂ)) = daub (S↑ S) (W (emptyMon (S↑ S))) from funext fun x =>
    ((h x (emptyMon _)).trans (if_pos rfl)).symm]
  exact authentic ..

variable (p : Face ℤ)
local notation "W" => plaque (tent Y H) p
local notation "S" => sites p

private theorem pow_in : (plaque (tent Y H) p)^2 ∈ bay (tent Y H) (sites p) true :=
  (bay ..).pow_mem (plaque_bay (tent Y H) p true) _

def liftMean := readLift Y H s D W (plaque_bay (tent Y H) p true)
def liftSecond := readLift Y H s D (W^2) (pow_in Y H p)

/-- This proves `liftD`'s Mark outputs *are* these everywhere scalar, first-field-only
stencils, with bounded and measurable cover coefficients and the closed-extent charge. -/
theorem liftMean_fields :
    ((A) W).val = scalar K (fun x => ((liftMean Y H s D p x.1):ℂ)) ∧
    Coeff true (S↑ S) (fun x => ((liftMean Y H s D p x.1):ℂ)) :=
  lift_repr Y H s D W (plaque_bay (tent Y H) p true)
    (fun x => (scalarLift Y H s D W (plaque_bay (tent Y H) p true)
      (fun i k => moment₁ Y s i k p) (fun _ _ _ _=> ascend_plaque ..) x).2)

theorem liftSecond_fields :
    ((A) (W^2)).val = scalar K (fun x => ((liftSecond Y H s D p x.1):ℂ)) ∧
    Coeff true (S↑ S) (fun x => ((liftSecond Y H s D p x.1):ℂ)) :=
  lift_repr Y H s D (W^2) (pow_in Y H p)
    (fun x => (scalarLift Y H s D (W^2) (pow_in Y H p)
      (fun i k => moment₂ Y s i k p) (fun _ _ _ _=> ascend_plaque_sq ..) x).2)

theorem liftMean_lim (x : LinksC) : Tendsto (fun t =>
    moment₁ Y s (i₀ t) (k₀ t) p (graft (S↑ S) (P (i₀ t)) x)) followStage
    (𝓝 (liftMean Y H s D p x)) :=
  (scalarLift Y H s D W (plaque_bay (tent Y H) p true)
    (fun i k => moment₁ Y s i k p) (fun _ _ _ _ => ascend_plaque ..) (x,1)).1

theorem liftSecond_lim (x : LinksC) : Tendsto (fun t =>
    moment₂ Y s (i₀ t) (k₀ t) p (graft (S↑ S) (P (i₀ t)) x)) followStage
    (𝓝 (liftSecond Y H s D p x)) :=
  (scalarLift Y H s D (W^2) (pow_in Y H p)
    (fun i k => moment₂ Y s i k p) (fun _ _ _ _ => ascend_plaque_sq ..) (x,1)).1

def valueV (x : LinksC) := liftSecond Y H s D p x - liftMean Y H s D p x ^ 2

theorem lift_floor (x : LinksC) : varianceFloor Λ s ≤ valueV Y H s D p x := by
  apply ge_of_tendsto ((liftSecond_lim Y H s D p x).sub ((liftMean_lim Y H s D p x).pow 2))
  filter_upwards [D.uniformRoad Y H S s] with t ht
  exact moments_gap Y s _ _ p ht.1 _

def varianceD : Dome (tent Y H) := (A) (W^2) - ((A) W)^2

lemma scalarFamily_mul (K' : Calibration) (f g : PairsC → ℂ) :
    scalar K' f * scalar K' g = scalar K' (f*g) := by
  funext i x; simp only [Pi.mul_apply, scalar, Algebra.smul_mul_assoc, one_mul, mul_smul]

lemma scalarFamily_sub (K' : Calibration) (f g : PairsC → ℂ) :
    scalar K' f - scalar K' g = scalar K' (f-g) := by
  funext i x; simp only [Pi.sub_apply, scalar, sub_smul]

lemma variance_fields : (varianceD Y H s D p).val = scalar K
    (fun x => ((valueV Y H s D p x.1):ℂ)) := by
  change ((A) (W^2)).val - ((A) W).val^2 = _
  rw [(liftSecond_fields Y H s D p).1,(liftMean_fields Y H s D p).1, pow_two, scalarFamily_mul,
    scalarFamily_sub]
  apply congrArg; ext1 x
  simp only [valueV, Pi.mul_apply, Pi.sub_apply, pow_two, Complex.ofReal_mul, Complex.ofReal_sub]

lemma valueV_coeff : Coeff true (S↑ S) (fun x => ((valueV Y H s D p x.1):ℂ)) := by
  let U (x : PairsC) := (liftMean Y H s D p x.1 : ℂ)
  let V (x : PairsC) := (liftSecond Y H s D p x.1 : ℂ)
  have eq (x : PairsC) : (valueV Y H s D p x.1:ℂ) = V x - U x * U x := by
    unfold valueV U V; rw [pow_two, Complex.ofReal_sub,Complex.ofReal_mul]
  simp_rw [eq]
  have hu : Coeff true (S↑ S) U := (liftMean_fields Y H s D p).2
  have hv : Coeff true (S↑ S) V := (liftSecond_fields Y H s D p).2
  refine ⟨by simp, Girt.kitE _ _ (fun (i j:ℂ) => i-j) (by fun_prop) hv.env (env_mult hu.env hu.env), ?_⟩
  intro x y h t; rw [hu.locus _ _ h t, hv.locus _ _ h t]

lemma varianceD_bay : varianceD Y H s D p ∈ bay K (S↑ S) true := by
  apply (locates ..).mpr; rw [variance_fields]; exact InTest.seed (valueV_coeff ..)

lemma varianceD_enclave : varianceD Y H s D p ∈ enclave K :=
  let E := enclave (tent Y H)
  E.sub_mem (D.riseGauge Y H s (E.pow_mem (plaque_enclave (tent Y H) p) 2))
    (E.pow_mem (D.riseGauge Y H s (plaque_enclave (tent Y H) p)) 2)

local notation "v" => valueV Y H s D p

def inverseValue (x : LinksC) : ℂ := (((valueV Y H s D p x:ℝ):ℂ))⁻¹

lemma inverse_bound (x : LinksC) : ‖inverseValue Y H s D p x‖ ≤ (varianceFloor Λ s)⁻¹ := by
  have h := (varianceFloor_pos Λ s).trans_le (lift_floor Y H s D p x)
  unfold inverseValue
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h.le]
  exact inv_anti₀ (varianceFloor_pos Λ s) (lift_floor Y H s D p x)

lemma inverse_coeff : Coeff true (S↑ S) (fun x => inverseValue Y H s D p x.1) :=
  let c := valueV_coeff Y H s D p
  ⟨by simp, ⟨c.env.meas.inv,_,fun x=>inverse_bound Y H s D p x.1⟩,
    fun x y h t=> congrArg (·⁻¹) (c.locus x y h t)⟩

def reciprocalD : Dome (tent Y H) :=
  ⟨scalar K (fun x => inverseValue Y H s D p x.1),
    broadCompile K (S↑ S) (InTest.seed (inverse_coeff ..))⟩

theorem reciprocalD_inv : varianceD Y H s D p * reciprocalD Y H s D p = 1 := by
  apply Subtype.ext; change (varianceD Y H s D p).val * scalar K _ = 1
  rw [variance_fields,scalarFamily_mul]
  funext m u
  change (((v (onC ((K).c m) u.1) : ℂ) * (v (onC ((K).c m) u.1) : ℂ)⁻¹) • (1:FC _)) = 1
  have he : (v (onC ((K).c m) u.1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((varianceFloor_pos Λ s).trans_le (lift_floor Y H s D p _)).ne'
  rw [mul_inv_cancel₀ he, one_smul]

lemma reciprocalD_bay : reciprocalD Y H s D p ∈ bay K (S↑ S) true :=
  (locates ..).mpr (InTest.seed (inverse_coeff ..))

theorem reciprocalD_enclave : reciprocalD Y H s D p ∈ enclave K := by
  let X := varianceD Y H s D p
  let Z := reciprocalD Y H s D p
  rw [colorFixed]
  intro R; change pennant K R Z = Z
  have h : X*Z=1 := reciprocalD_inv ..
  have he : X*pennant K R Z = 1 := by
    calc
      X*pennant K R Z = pennant K R X * pennant K R Z := by
        rw [show pennant K R X = X from (colorFixed K).1 (varianceD_enclave Y H s D p) R]
      _ = _ := by rw [← map_mul,h,map_one]
  exact left_inv_eq_right_inv ((mul_comm _ _).trans he) h


lemma inverse_measurable : Measurable (inverseValue Y H s D p) := by
  have h := (inverse_coeff Y H s D p).env.meas.comp
    (show Measurable (fun x : LinksC => (x,(1:LinksC))) from measurable_id.prodMk measurable_const)
  simpa only [Function.comp_def] using h

private theorem onCover (K' : Calibration) (U : Finset Cover) (f : LinksC → ℂ)
    (p : Coeff true U (fun x => f x.1)) (q : Neutral K' (scalar K' (fun x => f x.1)))
    (g : Cover → SU.E) (x : LinksC) : f (Lattice.gauge g x) = f x := by
  obtain ⟨m,t⟩ := (separates K' U).exists
  have ht : Hosp U (K'.c m) := ⟨t⟩
  obtain ⟨k,e⟩ := scoreTrace g ht
  let y := Satin.graft U (K'.c m) x
  have hd (a b : LinksC) (hx : Agrees U a b) : f a=f b :=
    p.locus (a,1) (b,1) hx (fun _ _ _=>rfl)
  have hz : Agrees U (onC _ y) x := tacked U _ ht x
  have hv : Agrees U (onC (K'.c m) (Lattice.gauge k y)) (Lattice.gauge g x) := by
    intro i hi hj; refine (gauge_trace g e y i hi hj).trans ?_
    unfold Lattice.gauge; rw [hz i hi hj]
  have hg := q m k (y,y)
  -- Make simultaneous change of both field arguments, coefficient only reads first.
  unfold scalar at hg
  simp only at hg -- tune
  change f (onC _ (Lattice.gauge k y)) • (1:FC (Single (K'.c m))) =
    twist (quantU (tradew (K'.c m) k)) (f (onC _ y) • 1) at hg
  rw [twist_scalar,map_one,hd _ _ hz, hd _ _ hv] at hg
  exact smul_left_injective ℂ (one_ne_zero (α:=FC (Single (K'.c m)))) hg

/-- The all-arguments cover formula is also gauge invariant as a classical function. -/
theorem inverse_gauge (g : Cover→SU.E) (x : LinksC) :
    inverseValue Y H s D p (Lattice.gauge g x) = inverseValue Y H s D p x :=
  onCover (tent Y H) (S↑ S) (inverseValue Y H s D p) (inverse_coeff Y H s D p)
    (show Neutral K (reciprocalD Y H s D p).val from reciprocalD_enclave Y H s D p) g x

end lift
end YM.CF.Buffered.Afterglow.Tapestry.RotationGap

#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.variance_fields
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.lift_floor
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.valueV_coeff
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.reciprocalD_bay
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.reciprocalD_inv
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.reciprocalD_enclave

#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.inverse_measurable
#print axioms YM.CF.Buffered.Afterglow.Tapestry.RotationGap.inverse_gauge
