import SatinFixedContrastNovember4

set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open Aria Set Cheer OS
open OS.Semigroup.Balloon
variable {P:Spine}{x:P.Spectrum0 3}{s t n:ℕ}{Z W:Lead.Clan}
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H"=>P.ManyF 3 ξ
local notation "S"=>P.seasons 3 ξ
local notation "Ω"=>P.heaven 3 ξ
variable {K:P.Register}{c r:ℕ→ℕ}{J:P.Ellis 3 x}(T:Experiment P K c r x J)
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "v" i:max => P.birthCloud x Z (c i) (r i)
lemma thinPlum_zero (t : ℝ) (ht : t ≠ 0) :
    plum 0 (t:ℂ) = (((Real.pi ^ 2)⁻¹ * (t⁻¹)^3 : ℝ) : ℂ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold plum cab Cheer.wind
  rw [norm_zero, show (0:Space3) (2:SpaceAxis) = (0:ℝ) from rfl]
  push_cast
  field_simp; ring


private lemma thinHeat_identity {V : Hilbert} (Q : OS.Semigroup V timeAxis)
    (y:V) (a b:ℝ≥0):
    (FLap (outlay Q y (b:ℝ)) 0 (↑((a+a:ℝ≥0):ℝ):ℂ)).re = ‖Q.E (b*a) y‖^2 := by
  have hx := Cheer.back Q y b (a+a) (0:Space3)
  have hx2 : (shore 0) = 0 := by apply Subtype.ext; exact (show position _ _ = 0 from by simpa using position_eta (0:E4))
  rw [hx,hx2, smul_zero, Q.uZero,ContinuousLinearMap.id_apply,mul_add, Q.time,ContinuousLinearMap.comp_apply, ← Semigroup.swing] -- <-!

  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

include T
/-- Explicit squared norms in the zoom heat test. This Lemma uses that this very
experiment co-elected the stronger data; it's not inferring this from the fixed-width
matrix limit for F,G. -/
lemma thinHeat_zoom (a : ℝ≥0) :
    Tendsto (fun i : ℕ => ‖((S).E (Real.toNNReal (ρ i) * a) (v i))‖^2) atTop
      (𝓝 (Complex.re (pairedLight Z (↑((a+a:ℝ≥0):ℝ):ℂ) 0))) := by
  let g i := Cheer.outlay S (v i) (ρ i)
  have hp (i:ℕ) := P.dew_pos (c i) (T.launch.unitSize i)
  let a' := a+a
  let w : ℂ := ↑((a':ℝ≥0):ℝ)
  have hlim : Tendsto (fun i=> FLap (g i) 0 w) atTop (𝓝 (pairedLight Z w 0)) :=
    priceStream Z (x:=x) T.launch T.ready keyV_go (T.ground.2.1.accepted 3) 0 w
      (show 0 ≤ w.re from a'.property)
  refine (Complex.continuous_re.continuousAt.tendsto.comp hlim).congr fun i=>?_
  let b := Real.toNNReal (ρ i)
  have hb : ρ i = (b:ℝ):=(Real.coe_toNNReal _ (hp i).le).symm
  exact (congrArg (fun κ:ℝ=> (FLap (outlay S (v i) κ) 0 w).re) hb).trans
    (thinHeat_identity S (v i) a b)
omit T
lemma thinHeat_tail (Z:Lead.Clan):
    Tendsto (fun a:ℝ => (pairedLight Z (↑(a+a):ℂ) 0).re) atTop (𝓝 0):=by
  have ha (b:ℝ) : Tendsto (fun a:ℝ=> a+a+b) atTop atTop := tendsto_atTop_add_const_right _ b (tendsto_id.atTop_add_atTop tendsto_id)
  have he (b:ℝ) : Tendsto (fun a:ℝ=>plum 0 (↑(a+a) + ↑b)) atTop (𝓝 0) := by
    simp_rw [← Complex.ofReal_add]
    refine Tendsto.congr' (l₁:=atTop) (f₁:=fun a:ℝ=>(( (Real.pi^2)⁻¹ * ((a+a+b)⁻¹)^3:ℝ):ℂ)) ?_ ?_
    · filter_upwards [(ha b).eventually_gt_atTop 0] with a hb using (thinPlum_zero _ hb.ne').symm
    have ht:=Complex.continuous_ofReal.continuousAt.tendsto.comp (((tendsto_inv_atTop_zero.comp (ha b)).pow 3).const_mul ((Real.pi^2)⁻¹))
    simpa [Function.comp_def] using ht
  have h:= Complex.continuous_re.continuousAt.tendsto.comp (((he 2).mul (he 4)).const_mul (numberX Z / 25))
  simpa [Function.comp_def,pairedLight] using h

section
variable {V:Hilbert}{a:Axis}
lemma thinKill (Q : OS.Semigroup V a) (scale : ℕ → ℝ≥0) (w:ℕ→V)
    (h : Tendsto (fun i=> (scale i:ℝ)) atTop (𝓝 0))
    (z : ℝ → ℝ) (tail : Tendsto z atTop (𝓝 0))
    (scaled : ∀ t:ℝ≥0,Tendsto (fun i=> ‖Q.E (scale i * t) (w i)‖^2) atTop (𝓝 (z (t:ℝ))))
    (e : ℝ≥0) (pos : 0<e):
    Tendsto (fun i=> Q.E e (w i)) atTop (𝓝 0):=by
  refine Metric.tendsto_nhds.mpr fun ε hε=>?_
  obtain ⟨b,hb,g⟩:= ((tail.eventually (gt_mem_nhds (show (0:ℝ)< ε^2 from pow_pos hε 2))).and (eventually_gt_atTop 0)).exists
  let y : ℝ≥0 := ⟨b,g.le⟩
  have he:= h.mul_const b
  rw [zero_mul] at he
  filter_upwards [(scaled y).eventually (gt_mem_nhds (show z (y:ℝ)< ε^2 from hb)), he.eventually (gt_mem_nhds (show (0:ℝ)< (e:ℝ) from pos))] with i hz hv
  have hw:= Q.norm_decrease (w i) (show scale i * y≤ e from (show ((scale i*y:ℝ≥0):ℝ) < (e:ℝ) from hv).le)
  change ‖Q.E e (w i)‖ ≤ ‖Q.E (scale i*y) (w i)‖ at hw
  rw [dist_zero_right]; exact hw.trans_lt ((sq_lt_sq₀ (norm_nonneg _) hε.le).mp hz)
end
include T
lemma thinHeat_loss (e:ℝ≥0)(he:0<e): Tendsto (fun i=> (S).E e (v i)) atTop (𝓝 0):=by
  have hp (i:ℕ) := P.dew_pos (c i) (T.launch.unitSize i)
  let y (i:ℕ) := Real.toNNReal (ρ i)
  have hy : Tendsto (fun i=>(y i:ℝ)) atTop (𝓝 0) := (P.proper_dew c r T.launch).congr (fun i=> (Real.coe_toNNReal _ (hp i).le).symm)
  exact thinKill S y (fun i=> v i) hy _ (thinHeat_tail Z) (fun t=> thinHeat_zoom T t) e he
section
variable {V:Hilbert}{a:Axis}
omit T
/-- Reweighted time finite difference, arbitrarily small step δ. -/
lemma heatSmallDiff (Q:OS.Semigroup V a) (w:V) (d b e:ℝ≥0) (he:0<e)(h: e+e ≤ b)(hd:0<d):
    ‖Q.E b (((d:ℝ)⁻¹:ℝ) • (w - Q.E d w))‖ ≤ (e:ℝ)⁻¹ * ‖Q.E e w‖:=by
  obtain ⟨g,rfl⟩:= exists_add_of_le h
  let A:=Q.E e w
  have add (b d:ℝ≥0)(w:V): Q.E (b+d) w = Q.E b (Q.E d w):=by rw [Q.time]; rfl
  have hun (x:V)(t:ℝ): Q.E ((e+e)+g) (t • x) = t • Q.E ((e+e)+g) x:= map_real_smul _ (Q.E _).continuous ..
  have hx: e+e+g + d=e+g+d+e:=by abel
  have hy: e+e+g=(e+g)+e:=by abel
  rw [hun, map_sub, ←add, hx, add (e+g+d) e, hy, add (e+g) e]
  have ht:= shrinking Q (e+g) (e+g+d) A (e:ℝ) he (by simp) (by rw [NNReal.coe_add,NNReal.coe_add]; exact (le_add_of_nonneg_right g.property).trans (le_add_of_nonneg_right d.property))
  have dp : (0:ℝ)< (d:ℝ):=hd
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc (d:ℝ)⁻¹ * _ ≤ (d:ℝ)⁻¹ * (|((e+g:ℝ≥0):ℝ)-↑(e+g+d)|/(e:ℝ)*‖A‖):= by gcongr
       _ = _:= by rw [NNReal.coe_add (e+g), sub_add_eq_sub_sub,sub_self,zero_sub, abs_neg,abs_of_pos dp]; field_simp; rfl

end
-- outside helper restored include T
omit T
section
variable (P:Spine) (s n:ℕ)
def slopePrice : ℝ := ((P.increment s n:ℝ≥0) : ℝ)⁻¹
lemma slope_cancel (x:P.Spectrum0 3) (Z:Lead.Clan) {b e:ℝ≥0}
    (hd:0<n) (g: e+e ≤ b)(positive:0<e) :
    ‖(P.slopePrice s n:ℂ) • ((P.seasons 3 (P.otherSpectrum 3 3 x)).E b (P.sixWard_macroVector x s n Z))‖ ≤
      (e:ℝ)⁻¹ * ‖((P.seasons 3 (P.otherSpectrum 3 3 x)).E e (P.birthCloud x Z s n))‖:=by
  let N:=P.ManyF 3 (P.otherSpectrum 3 3 x)
  let Q:=P.seasons 3 (P.otherSpectrum 3 3 x)
  let d:=P.increment s n
  let w:N:=P.birthCloud x Z s n
  let a:N:=w - Q.E d w
  let f:ℝ:=(d:ℝ)⁻¹
  have he:P.sixWard_macroVector x s n Z=a:=P.filtered_explicit x s n Z
  -- avoid complex timeouts
  have hx:(↑f:ℂ) • Q.E b (P.sixWard_macroVector x s n Z) = Q.E b ((↑f:ℂ) • a) := (congrArg (fun y:N=> (↑f:ℂ) • Q.E b y) he).trans (map_smul _ _ _).symm
  have ht: Q.E b ((f:ℂ) • a) = Q.E b (f • a) := congrArg (Q.E b) (Complex.coe_smul ..)
  exact (congrArg (fun y:N=>‖y‖) (hx.trans ht)).le.trans (heatSmallDiff Q w d b e positive g (P.increment_pos s n hd))
lemma slope_ray_bound (x:P.Spectrum0 3) (Z:Lead.Clan) (b : Vantage → ℝ≥0) (A:Set Vantage) (e:ℝ≥0)
    (g: ∀ p∈A,e+e ≤ b p)(positive:0<e)(hd:0<n):
    ∀ p∈A, ‖(P.slopePrice s n:ℂ) • ((P.cartage 3 (P.advocate 3 x 3) p)
      ((P.seasons 3 (P.otherSpectrum 3 3 x)).E (b p) (P.sixWard_macroVector x s n Z)))‖ ≤
      (e:ℝ)⁻¹ * ‖((P.seasons 3 (P.otherSpectrum 3 3 x)).E e (P.birthCloud x Z s n))‖:=by
  intro p hp
  let U := P.cartage 3 (P.advocate 3 x 3) p
  let y := (P.seasons 3 (P.otherSpectrum 3 3 x)).E (b p) (P.sixWard_macroVector x s n Z)
  exact le_trans ((congrArg (fun z:P.ManyF 3 (P.advocate 3 x 3)=> ‖z‖) ((map_smul U (↑(P.slopePrice s n):ℂ) y).symm)).trans (P.cart_norm ..)).le (P.slope_cancel s n x Z hd (g p hp) positive)
end
lemma thinSmear_bound (V:Hilbert)(a:ℂ)(X:Vantage→ V)(G:SampleDose)(h:G.Normalized)(κ:ℝ)
    (p:∀ z∈tsupport G.val, ‖a • X z‖ ≤ κ) :
    ‖a • (∫ z:Vantage, (G.val z:ℂ) • X z)‖ ≤ κ:=by
  rw [←integral_smul]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hg:Integrable (fun z=> G.val z * κ):=(G.smooth.continuous.integrable_of_hasCompactSupport G.budget).mul_const _
  refine (integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) hg
    (ae_of_all _ fun z=>?_)).trans_eq ?_
  · have he: ‖(G.val z:ℂ)‖=G.val z := Complex.norm_real _ |>.trans (Real.norm_of_nonneg (h.1 z))
    change ‖a • (G.val z:ℂ) • X z‖ ≤ G.val z * κ
    rw [smul_comm,norm_smul,he]
    by_cases t: G.val z=0
    · rw [t,zero_mul,zero_mul]
    exact mul_le_mul_of_nonneg_left (p z (subset_closure t)) (h.1 z)
  rw [integral_mul_const,h.2,one_mul]

lemma smearedSlopes (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(d:ℝ)(F G:SampleDose)
    (hF:F.Normalized)(hG:G.Normalized)(e:ℝ≥0)(positive:0<e)
    (first:∀ p∈tsupport F.val,e+e≤d-p 3)(second:∀ p∈tsupport G.val,e+e≤p 3-d)(hd:0<n):
    let κ:=(e:ℝ)⁻¹ * ‖((P.seasons 3 (P.otherSpectrum 3 3 x)).E e (P.birthCloud x Z s n))‖
    ‖(P.slopePrice s n:ℂ) • (P.landingCost x s n Z F d)‖ ≤ κ ∧
    ‖(P.slopePrice s n:ℂ) • (P.launchCost x s n Z G d)‖ ≤ κ := by
  let Q:=P.ManyF 3 (P.otherSpectrum 3 3 x)
  have h' (y:ℝ)(t:(e:ℝ)+(e:ℝ)≤y): e+e≤Real.toNNReal y := (Real.le_toNNReal_iff_coe_le (by linarith only [t,positive] : 0 ≤ y)).mpr (show ((e+e:ℝ≥0):ℝ)≤y from t)
  constructor
  · exact thinSmear_bound Q _ _ F hF _ (P.slope_ray_bound s n x Z (fun p => (d-p 3).toNNReal) (tsupport F.val) e (fun p v'=> h' _ (first p v')) positive hd)
  exact thinSmear_bound Q _ _ G hG _ (P.slope_ray_bound s n x Z (fun p => (p 3-d).toNNReal) (tsupport G.val) e (fun p v'=> h' _ (second p v')) positive hd)

include T
lemma slopesDisappear {d:ℝ}{e:ℝ≥0}(positive:0<e)(F G:ℕ→SampleDose)
    (hF:∀ i,(F i).Normalized)(hG:∀ i,(G i).Normalized)
    (first:∀ i p,p∈tsupport (F i).val→(e:ℝ)+(e:ℝ)≤d-p (3:Axis))
    (second:∀ i p,p∈tsupport (G i).val→(e:ℝ)+(e:ℝ)≤p (3:Axis)-d) :
    Tendsto (fun i=> (P.slopePrice (c i) (r i):ℂ) • P.landingCost x (c i) (r i) Z (F i) d) atTop (𝓝 0) ∧
      Tendsto (fun i=> (P.slopePrice (c i) (r i):ℂ) • P.launchCost x (c i) (r i) Z (G i) d) atTop (𝓝 0):=by
  have h:= (thinHeat_loss (Z:=Z) T e positive).norm.const_mul ((e:ℝ)⁻¹)
  have h1 : Tendsto (fun i : ℕ=> (e:ℝ)⁻¹ * ‖(S).E e (v i)‖) atTop (𝓝 0) := Eq.mp (congrArg (fun z:ℝ=> Tendsto (fun i:ℕ=> (e:ℝ)⁻¹ * ‖(S).E e (v i)‖) atTop (𝓝 z)) (show (e:ℝ)⁻¹ * ‖(0:(P.ManyF 3 (P.otherSpectrum 3 3 x)))‖ = 0 from congrArg (fun z:ℝ => (e:ℝ)⁻¹*z) (norm_zero) |>.trans (mul_zero _))) h
  have hp(i:ℕ):=P.smearedSlopes x Z (c i) (r i) d (F i) (G i) (hF i) (hG i) e positive (first i) (second i) (T.launch.unitSize i)
  exact ⟨tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=> norm_nonneg _) (fun i=> (hp i).1) h1), tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=>norm_nonneg _) (fun i=> (hp i).2) h1)⟩
omit T
variable (P:Spine)
/-- A genuinely width-varying trial family, with a first-difference renormalization
(and zero one-letter vacuum counterterm). Tested here for *loss*, not as our
claimed signal. Every level uses the very same bare theory. Its stencil formula
is the gauge-parallel transported polar pair `front_read` minus its indicated
time-translate (`backMat`), times the *inverse physical time step*; the
opposite box uses the reflection of this mark. (`increment` and hence the
last coefficient always physical after the fixed calibration.) -/
def slopeStencil (Z:Lead.Clan)(s n:ℕ) : P.Test :=
  (P.slopePrice s n:ℂ) • (P.FTest Z s n).F
/-- Implementing grid t, physical preparation of the two stencils independently on the original smears. -/
def slopeSample (Z:Lead.Clan)(s n:ℕ)(side:Bool)(F:SampleDose)(t:ℕ) : P.Test :=
  (P.slopePrice s n:ℂ) • P.prepared t (if side then (P.FTest Z s n) else P.RTest Z s n) F
def slopePair (Z W:Lead.Clan)(s n:ℕ)(F G:SampleDose)(t:ℕ) : P.Test :=
  P.slopeSample Z s n false F t * P.slopeSample W s n true G t
def slopeFine (x:P.Spectrum0 3)(s n:ℕ)(F G:SampleDose)(t:ℕ):CrossRead:= Matrix.of fun Z W:Lead.Clan=>P.singleState 3 t x (P.slopePair Z W s n F G t)
def slopeReading (x:P.Spectrum0 3)(s n:ℕ)(d:ℝ)(F G:SampleDose):CrossRead:= Matrix.of fun Z W:Lead.Clan=> inner ℂ ((P.slopePrice s n:ℂ) • (P.landingCost x s n Z F d)) ((P.slopePrice s n:ℂ) • (P.launchCost x s n W G d))
lemma thinTrial_formula (Z:Lead.Clan)(s n:ℕ)(m:Side)(X:Fields (P.calibration.c m)) :
    (P.slopeStencil Z s n).val m X =(P.slopePrice s n:ℂ) •
      ((Lead.sing n false • ∑ i∈Window.colors Z,∑ j∈Window.colors Z, (Lamour.Bridge.Celeste.coilFlag (P.flash n) i j (onC _ X.1)) •
        (Fock.remove (basisC (P.calibration.c m) (P.flash n).death 2 j)*create (basisC (P.calibration.c m) (P.flash n).birth 0 i))) - (P.shifts 3 (P.laterPulse n) (P.stockS Z (P.flash n))).val m X) :=rfl
lemma thinTrial_pair (Z W:Lead.Clan)(s n:ℕ)(F G:SampleDose)(t:ℕ) :
    P.slopePair Z W s n F G t = ((P.slopePrice s n:ℂ) * (P.slopePrice s n:ℂ)) •
      (P.prepared t (P.RTest Z s n) F * P.prepared t (P.FTest W s n) G) := by
  change ((P.slopePrice s n:ℂ) • _) * ((P.slopePrice s n:ℂ) • _) = _
  rw [smul_mul_assoc,mul_smul_comm,smul_smul]
  simp only [Bool.false_eq_true,↓reduceIte]
lemma thinTrial_born (s n:ℕ)(Z:Lead.Clan) :
    ∃ p:P.birthF 3 s (P.slopeStencil Z s n), ∀ x:P.Spectrum0 3,
    P.wealth 3 (P.otherSpectrum 3 3 x) (P.viewF 3 (P.otherSpectrum 3 3 x) s p)= (P.slopePrice s n:ℂ) • P.sixWard_macroVector x s n Z := by
  let z:ℂ:=↑(P.slopePrice s n)
  let p:=P.body_birth Z s n
  refine ⟨P.birthScale s z p,fun x=>?_⟩
  let x':=(P.otherSpectrum 3 3 x); let B:= P.ColorHil 3 x';
  exact (congrArg (fun y:B=>P.wealth 3 x' y) (P.sixWard_view_scale x' s z p)).trans (map_smul ..)
lemma thinTrial_provision (s n:ℕ)(F:SampleDose)(Z:Lead.Clan)(side:Bool)(t:ℕ)(p:s≤t):
    let A:=if side then P.FTest Z s n else P.RTest Z s n
    (P.slopePrice s n:ℂ) • A.F ∈ bay P.calibration A.S true ∧
    (P.slopePrice s n:ℂ) • A.F ∈ enclave P.calibration ∧
    P.slopeSample Z s n side F t ∈ enclave P.calibration ∧
    P.asked_at t (P.slopeSample Z s n side F t) (P.spacePrice A F) ∧
    ∀ q:Cover, (P.slopePrice s n:ℂ) • P.issuing t A q ∈ bay P.calibration (P.plotSet t A q) true ∧
      P.pinFoot t (P.plotSet t A q) ⊆ P.Aperture A (P.meshPose t q):=by
  intro A
  have ha:A.s=s:=by unfold A; split_ifs <;>rfl
  let a:ℂ:=↑(P.slopePrice s n)
  obtain ⟨Q,h,e⟩:=P.prepared_at t A F (ha.trans_le p)
  exact ⟨Subalgebra.smul_mem _ A.bay a,Subalgebra.smul_mem _ A.realM a, Subalgebra.smul_mem _ (P.prepared_color t A F) a, ⟨Q,Subalgebra.smul_mem _ h a,e⟩,fun q=>⟨Subalgebra.smul_mem _ (P.issuing_support t q A) a, P.inside_now t q A (ha.trans_le p)⟩⟩
section
private lemma sameHill_inner (V:Hilbert)(x y:V)(t:ℝ) : ((t:ℂ)*(t:ℂ)) • inner ℂ x y=inner ℂ ((t:ℂ) • x) ((t:ℂ) • y):=by rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal, smul_eq_mul,mul_assoc]
private lemma sameHill_enter {V W:Hilbert} (e:V.space →ₗᵢ[ℂ] W.space) (f:ℕ→W)(x:V)(h:Tendsto f atTop (𝓝 (e x)))(a:ℝ): Tendsto (fun i=> (a:ℂ) • f i) atTop (𝓝 (e ((a:ℂ) • x))) := by rw [map_smul]; exact h.const_smul _
variable {P}{x:P.Spectrum0 3}(Z W:Lead.Clan)(s n:ℕ)(d:ℝ)(F G:SampleDose)
variable (a: P.WallBefore (P.RTest Z s n) F d)(b:P.WallAfter (P.FTest W s n) G d)
variable (t:ℕ)(p:s≤t)
include a b p
private lemma thinTrial_bill :
    P.singleState 3 t x (P.slopePair Z W s n F G t) = inner ℂ
      ((P.slopePrice s n:ℂ) • P.preVector x s t n Z F d) ((P.slopePrice s n:ℂ) • P.postVector x s t n W G d) := by
  let l:ℂ:= P.slopePrice s n
  refine ((congrArg (P.singleState 3 t x) (P.thinTrial_pair Z W s n F G t)).trans ((map_smul _ _ _).trans (congrArg ((l*l) • ·) (P.pinPricing x s t n Z W F G d a b p)))).trans ?_
  exact sameHill_inner (P.ColorHil 3 (P.otherSpectrum 3 3 x)) _ _ _
omit a b p
lemma thinTrial_read (J:P.Ellis 3 x) :
    Tendsto (fun t=> (P.slopePrice s n:ℂ) • P.preVector x s t n Z F d) atTop
      (𝓝 (P.enter 3 (P.otherSpectrum 3 3 x) ((P.slopePrice s n:ℂ) • P.landingCost x s n Z F d))) ∧
    Tendsto (fun t=> (P.slopePrice s n:ℂ) • P.postVector x s t n Z F d) atTop
      (𝓝 (P.enter 3 (P.otherSpectrum 3 3 x) ((P.slopePrice s n:ℂ) • P.launchCost x s n Z F d))) := by
  let l:ℂ:= P.slopePrice s n
  let e:= P.enter 3 (P.otherSpectrum 3 3 x)
  exact ⟨sameHill_enter (V:=P.ManyF 3 (P.otherSpectrum 3 3 x)) (W:=P.ColorHil 3 (P.otherSpectrum 3 3 x)) e _ _ (P.toLand x s n Z F d J) _,sameHill_enter (V:=P.ManyF 3 (P.otherSpectrum 3 3 x)) (W:=P.ColorHil 3 (P.otherSpectrum 3 3 x)) e _ _ (P.toLaunch x s n Z F d J) _⟩
include a b
lemma thinTrial_joint (J:P.Ellis 3 x) :
    Tendsto (fun t=> P.slopeFine x s n F G t Z W) atTop
      (𝓝 (P.slopeReading x s n d F G Z W)):= by
  let h:= (thinTrial_read Z s n d F J).1; let g:=(thinTrial_read W s n d G J).2
  let l:ℂ:=P.slopePrice s n; let S':=l • P.landingCost x s n Z F d; let T':=l • P.launchCost x s n W G d
  let f t:=inner ℂ (l • P.preVector x s t n Z F d) (l • P.postVector x s t n W G d)
  let e:= P.enter 3 (P.otherSpectrum 3 3 x)
  have ht:Tendsto f atTop (𝓝 (inner ℂ S' T')) := Eq.mp (congrArg (fun z:ℂ=> Tendsto f atTop (𝓝 z)) (e.inner_map_map S' T')) (h.inner g)
  exact ht.congr' ((eventually_ge_atTop s).mono fun t p=> Eq.symm (thinTrial_bill Z W s n d F G a b t p))
omit a b
open Six
lemma thinTrial_split (a: ∀ i:Lead.Clan,P.WallBefore (P.FTest i s n) F d) (b: ∀ i:Lead.Clan,P.WallAfter (P.FTest i s n) G d) (g:n>P.calibration.ℓ)
    (t:ℕ) (p:s≤t)(X:P.Test→ₗ[ℂ]ℂ)(m:Factors P.calibration X)(w:MatterWard P.calibration X∨GaugeWard P.calibration X):
    X (P.slopePair Z W s n F G t)=0 := by
  let l:ℂ:= P.slopePrice s n
  have h:=P.forecast s n t g p F G d a b X m w
  have hg:X (P.prepared t (P.RTest Z s n) F * P.prepared t (P.FTest W s n) G) = 0:= congrArg (fun Y:CrossRead=>Y Z W) h
  exact (congrArg X (P.thinTrial_pair Z W s n F G t)).trans ((map_smul X _ _).trans ((congrArg ((l*l) • ·) hg).trans (smul_zero _)))
lemma thinTrial_centered (t:ℕ) (p:s≤t): P.singleState 3 t x (P.slopeSample Z s n false F t)=0 ∧ P.singleState 3 t x (P.slopeSample Z s n true F t)=0:=by
  let h(j:Bool):= P.slopeSample Z s n j F t
  let M:=P.singleState 3 t x; let a:ℂ:=P.slopePrice s n; let z(j:Bool):=if j then P.FTest Z s n else P.RTest Z s n
  have he(j:Bool)(u:P.singleState 3 s x (z j).F=0)(ht:(z j).s=s): M (h j)=0 := (map_smul M a (P.prepared t (z j) F)).trans ((congrArg ((a) • ·) (P.Dose_zero t (z j) F x (show P.singleState 3 (z j).s x (z j).F=0 from ht.symm ▸ u) (ht.trans_le p))).trans (smul_zero _)) -- ht.symm ▸ u problematic z j occurs s
  have hg:= P.body_central x s n Z
  exact ⟨he false hg.2 (by dsimp [z]; rfl),he true hg.1 (by dsimp [z]; rfl)⟩
end

-- physical boxes example, election and loss. First acquire fixed experiment but
-- also its wall clearance and predictions. Can simply use AllOpen at that election.
section experiment
set_option maxHeartbeats 300000
variable {P} {x:P.Spectrum0 3} {K:P.Register}{J:P.Ellis 3 x}(B:Experiment P K c r x J) (Z W:Lead.Clan)
local notation "BoxL"=>reviewEarlierBox
local notation "BoxR"=>reviewLaterBox
private def thinDoor : Orders:= ⟨fun _=>true,rfl⟩
private lemma atBoxes : reviewEarlierBox.Later BoxR thinDoor 0:=by intro j; norm_num [thinDoor,reviewEarlierBox,reviewLaterBox,Doorway.Later]
lemma thinTrial_wall (F G:SampleDose)
    (a:tsupport F.val ⊆ reviewEarlierBox.invites) (b:tsupport G.val ⊆ reviewLaterBox.invites) :
    (∀ p,p∈tsupport F.val→(1:ℝ) ≤ (0:ℝ)-p (3:Axis)) ∧ (∀ p,p∈tsupport G.val→(1:ℝ) ≤ p (3:Axis)-0) :=by
  constructor
  · intro p hp
    have h:= (a hp)
    have hh : p 3 < (-1:ℝ):= ((h (3:Axis) (Set.mem_univ (3:Axis)))).2; linarith
  intro p hp
  have h:=b hp
  have hh : (1:ℝ) < p 3 := ((h (3:Axis) (Set.mem_univ (3:Axis)))).1; linarith
structure SlopeDocket (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(F G:SampleDose) : Prop where
  spaces(Z W:Lead.Clan) : Disjoint (P.spacePrice (P.RTest Z s n) F) (P.spacePrice (P.FTest W s n) G)
  joint : Tendsto (P.slopeFine x s n F G) atTop (𝓝 (P.slopeReading x s n 0 F G))
  centered : ∀ t:ℕ,s≤t→∀ Z:Lead.Clan,P.singleState 3 t x (P.slopeSample Z s n false F t)=0 ∧ P.singleState 3 t x (P.slopeSample Z s n true G t)=0
  split_failure : ∀ t,s≤t → ∀ X:P.Test→ₗ[ℂ]ℂ, Six.Factors P.calibration X → Six.MatterWard P.calibration X ∨ Six.GaugeWard P.calibration X → ∀ Z W:Lead.Clan, X (P.slopePair Z W s n F G t)=0

include B
lemma ledgerSlope (F G:SampleDose)(a:tsupport F.val⊆reviewEarlierBox.invites) (b:tsupport G.val⊆reviewLaterBox.invites) :
    ∀ᶠ i:ℕ in atTop,P.SlopeDocket x (c i) (r i) F G := by
  let Q i := P.probeWidth (c i) (r i)
  have he:= thinTrial_wall F G a b
  filter_upwards [(limit_width B.launch (3:Axis)).eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1)),B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i hi pi
  change Q i 3 <1 at hi
  have hg(Z:Lead.Clan): P.WallBefore (P.RTest Z (c i) (r i)) F 0:= by
    intro p hp; change p 3 + Q i 3 < 0; linarith only [hi, he.1 p hp]
  have hv(Z:Lead.Clan): P.WallAfter (P.FTest Z (c i) (r i)) G 0:= by
    intro p hp; change 0 + Q i 3 < p 3; linarith only [hi, he.2 p hp]
  refine ⟨fun Z W=>P.test_apart (P.RTest ..) F 0 (P.FTest ..) G (hg Z) (hv W),
    tendsto_pi_nhds.mpr (fun Z=> tendsto_pi_nhds.mpr (fun W=> thinTrial_joint Z W (c i) (r i) 0 F G (hg Z) (hv W) J)),
    fun t p Z=> ⟨(thinTrial_centered Z (c i) (r i) F t p (x:=x)).1,(thinTrial_centered Z (c i) (r i) G t p (x:=x)).2⟩, fun t p X m w Z W=> thinTrial_split Z W (c i) (r i) 0 F G hg hv pi t p X m w⟩
lemma plateauSlope (F G:SampleDose)(a:tsupport F.val⊆reviewEarlierBox.invites) (b:tsupport G.val⊆reviewLaterBox.invites)
    (p:F.Normalized)(q:G.Normalized) : Tendsto (fun i:ℕ=> P.slopeReading x (c i) (r i) 0 F G) atTop (𝓝 (0:CrossRead)):=by
  refine tendsto_pi_nhds.mpr fun Z=> tendsto_pi_nhds.mpr fun W=> ?_
  have hv:=thinTrial_wall F G a b
  let e:ℝ≥0:= ⟨1/2,by norm_num⟩
  have he:(e:ℝ)+(e:ℝ)≤1:=by change (1/2:ℝ)+(1/2) ≤ 1; norm_num
  have h(Y:Lead.Clan):=slopesDisappear (Z:=Y) B (d:=0) (show 0 < e from by change (0:ℝ)<1/2; norm_num) (fun _=>F) (fun _=>G) (fun _=>p) (fun _=>q) (fun _ z u=> he.trans (hv.1 z u)) (fun _ z u=>he.trans (hv.2 z u))
  let N:=P.ManyF 3 (P.otherSpectrum 3 3 x)
  have h0:inner ℂ (0:N) 0=0:=inner_zero_left _
  let f i:= P.slopeReading x (c i) (r i) 0 F G Z W
  exact Eq.mp (congrArg (fun z:ℂ=> Tendsto f atTop (𝓝 z)) h0) ((h Z).1.inner (h W).2)

lemma shrinkingTrial (b:Bool)(Z:Lead.Clan): ∀ ε:ℝ,0<ε →
    ∀ᶠ i in atTop,∀ t:ℕ,c i ≤ t →
      let A:=if b then P.FTest Z (c i) (r i) else P.RTest Z (c i) (r i)
      ∀ k:Cover,P.pinFoot t (P.plotSet t A k) ⊆ Metric.ball (P.meshPose t k) ε := by
  intro ε e
  let A(i:ℕ):=if b then P.FTest Z (c i) (r i) else P.RTest Z (c i) (r i)
  have ha(i:ℕ): (A i).s=c i := by unfold A; split_ifs <;> rfl
  have hw(i:ℕ)(j:Axis): (A i).realWidth P j=P.probeWidth (c i) (r i) j:= by unfold A; split_ifs<;> rfl
  have hall:∀ᶠ i in atTop, ∀ j:Axis,P.probeWidth (c i) (r i) j < ε:= Filter.eventually_all.mpr (fun j=> (limit_width B.launch j).eventually (gt_mem_nhds e))
  filter_upwards [hall] with i hi t f
  change ∀ k:Cover,P.pinFoot t (P.plotSet t (A i) k) ⊆ Metric.ball (P.meshPose t k) ε
  intro k v' u
  rw [Metric.mem_ball]
  exact (dist_pi_lt_iff e).mpr (fun j=> (Real.dist_eq _ _).trans_lt (((P.inside_now t k (A i) ((ha i).trans_le f) u j).trans_eq (hw i j)).trans_lt (hi j)))
omit B
end experiment
/-- Public review. A substantive *loss* estimate in the actual six chiral
channels, not a proof of direct nonzero thin-field separation. Even charging
the inverse physical transition length in amplitude cannot keep any of this
trial matrix above the split prediction at the same two tests. Includes the
purchased fixed-width contrast, the split calibrated to exactly this x at every
grid, and takes the trial on that very data with both limits. Companion lemmas
`thinTrial_formula`, `thinTrial_provision`, `shrinkingTrial`, `thinTrial_read`,
`slopesDisappear` tie this to supports, coupling and vectors. -/
theorem reviewSlopesAgainstFixedContrast (Y : Supplier) (L M : ℝ) (hM : 0<M) (z:ℕ→ℕ) :
    ∃ (P : Spine) (K : P.Register), uniform P K Y L M ∧
    ∃ (c r : ℕ → ℕ) (x : P.Spectrum0 3), z ≤ r ∧ ∃ J : P.Ellis 3 x,
    Experiment P K c r x J ∧
    ∃ (m:ℕ) (a:ℝ)(F G:SampleDose),
      F.Normalized ∧ G.Normalized ∧ tsupport F.val⊆reviewEarlierBox.invites ∧ tsupport G.val⊆reviewLaterBox.invites ∧
      P.ReturnsSix x (c m) (r m) a F G ∧ P.FixedSatinReadings K x (c m) (r m) a F G ∧
      (∀ t:ℕ,∃ X, Six.Comparison P.calibration (P.singleState 3 t x) X ∧ Six.Factors P.calibration X ∧ Six.MatterWard P.calibration X) ∧
      (∀ j:Axis,Tendsto (fun i=> P.probeWidth (c i) (r i) j) atTop (𝓝 0)) ∧
      (∀ᶠ i:ℕ in atTop,P.SlopeDocket x (c i) (r i) F G) ∧
      Tendsto (fun i:ℕ=> P.slopeReading x (c i) (r i) 0 F G) atTop (𝓝 (0:CrossRead)):=by
  obtain ⟨P,K,T,c,r,x,hz,J,H',B⟩ := macroscopicSatin Y L M hM z
  let b: Fin 3→Bool:= fun _=>false
  obtain ⟨p,e,a,t,u⟩:= authorize b
  obtain ⟨m,h⟩:=(packs_within_rectangles B (Metric.ball p e) b u _ _ thinDoor atBoxes).exists
  obtain ⟨g, F,G,x',p',v',u,e,_⟩:= h.2
  refine ⟨P,K,T,c,r,x,hz,J,H',m,g,F,G,x',p',u,e,v',P.reviewWardContrast K x (c m) (r m) g F G v',fun t=>?_,limit_width H'.launch,ledgerSlope H' F G u e,plateauSlope H' F G u e x' p'⟩
  obtain ⟨X,p,_,_,e⟩:= P.comparator t x
  exact ⟨X,p,p.factors,e⟩

#check @reviewSlopesAgainstFixedContrast
#print axioms reviewSlopesAgainstFixedContrast
#print axioms thinTrial_formula
#print axioms thinTrial_provision
#print axioms shrinkingTrial
#print axioms thinTrial_read
#print axioms thinTrial_born
#print axioms slopesDisappear
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
