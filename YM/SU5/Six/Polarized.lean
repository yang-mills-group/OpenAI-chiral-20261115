import YM.SU5.Six.Ball
import YM.SU5.Six.MovingTest
import YM.SU5.Six.FrameBound
set_option maxHeartbeats 250000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Cheer
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(c r:ℕ→ℕ)(z:SixCoefficients)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)

open scoped BoundedContinuousFunction
/-- Polarization of a matrix measure. All complex cross-measure integration is
 phrased in terms of integration against *finite positive* measures. -/
def polar (D:SixCoefficients→ℂ)(Z W:Lead.Clan): ℂ:=
  let a:SixCoefficients:=Pi.single Z 1
  let b:SixCoefficients:=Pi.single W 1
  (D (a+b) - D (a-b) - Complex.I * D (a + Complex.I • b) + Complex.I * D (a - Complex.I • b))/4

private lemma polar_gram (G:Hilbert) (v:Lead.Clan→G)(Z W:Lead.Clan) :
    polar (fun z:SixCoefficients=> ((‖FrameBound.combination _ G v z‖^2:ℝ):ℂ)) Z W = inner ℂ (v Z) (v W):= by
  let a:SixCoefficients:=Pi.single Z 1
  let b:SixCoefficients:=Pi.single W 1
  let M:=FrameBound.combination _ G v
  have one (Z:Lead.Clan): M (Pi.single Z 1)=v Z:= by simp [M,FrameBound.combination] -- tune
  have plus(x y:SixCoefficients): M (x+y)=M x+M y:= by simp only [M,FrameBound.combination,Pi.add_apply,add_smul,sum_add_distrib]
  have minus(x y:SixCoefficients):M (x-y)=M x-M y:= by simp only [M,FrameBound.combination,Pi.sub_apply,sub_smul,sum_sub_distrib]
  have hi(x:SixCoefficients): M (Complex.I • x)=Complex.I • M x:= by simp only [M,FrameBound.combination,Pi.smul_apply,smul_sum,smul_smul,smul_eq_mul]
  have hx:M a=v Z:=one Z; have hy:M b=v W:=one W
  unfold polar
  change ( ((↑(‖M (a+b)‖^2):ℂ) - ↑(‖M (a-b)‖^2) - Complex.I * ↑(‖M (a+ Complex.I • b)‖^2) + Complex.I * ↑(‖M (a- Complex.I • b)‖^2))/4) = _
  rw [plus,minus,plus,minus,hi,hx,hy]
  have he:= inner_map_polarization' (LinearMap.id (R:=ℂ) (M:=G.space)) (v Z) (v W)
  simp only [LinearMap.id_coe,id_eq,inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] at he ⊢; exact he.symm

lemma cross_borel (V:Set E4)(h:MeasurableSet V)(Z W:Lead.Clan) :
    polar (fun z:SixCoefficients=> ((((P.zoomMatrix x s n z):Measure E4).real V):ℂ)) Z W =
      inner ℂ (P.spectralRoster x s n V Z) (P.spectralRoster x s n V W):= by
  let v:=P.spectralRoster x s n V
  exact (congrArg (fun f=>polar f Z W) (funext (g:=fun z=> (↑(‖FrameBound.combination _ H v z‖^2):ℂ)) (fun z=> congrArg Complex.ofReal (P.zoom_matrix_event x s n z V h)))).trans (polar_gram H v Z W)

def crossTest (M:SixCoefficients→Narrow)(f:E4→ᵇℂ)(Z W:Lead.Clan) :=
  polar (fun z=>∫ w, f w ∂(M z:Measure E4)) Z W
private lemma polar_sum_norm (F:Lead.Clan→ℂ)(Z W:Lead.Clan) :
    polar (fun z=> ∑ i:Lead.Clan, (↑(‖z i‖^2):ℂ)*F i) Z W = if Z=W then F Z else 0 := by
  let a:SixCoefficients:=Pi.single Z 1; let b:SixCoefficients:=Pi.single W 1
  let H' (i:Lead.Clan)(c:SixCoefficients):= (↑(‖c i‖^2):ℂ)*F i
  let G(i:Lead.Clan):= polar (fun z=> H' i z) Z W
  calc _ = ∑ i:Lead.Clan,G i := by simp only [G,H',polar,mul_sum,sum_div,← sum_add_distrib,← sum_sub_distrib]
       _ = G Z:=by
         apply sum_eq_single
         · intro i _ v
           have hx:(Pi.single Z (1:ℂ):SixCoefficients) i=0:= by simp [v]
           simp [G,H',polar,hx]
         · simp
       _ = _ := by
         split_ifs with p
         · subst W
           simp only [G,H',polar, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
             smul_eq_mul, Pi.single_eq_same,mul_one,sub_self]
           simp_rw [Complex.sq_norm, Complex.normSq_apply]
           simp
           ring
         have hb:(Pi.single W (1:ℂ):SixCoefficients) Z=0:=by simp [p]
         simp [G,H',polar,hb]
lemma diagonal_only (f:E4→ᵇℂ)(Z W:Lead.Clan) :
    crossTest diagonalLimit f Z W = if Z=W then ∫ w, f w ∂(promenade Z:Measure E4) else 0 := by
  have hx(c:SixCoefficients): (∫ w, f w ∂(diagonalLimit c:Measure E4))=
      ∑ i:Lead.Clan,(↑(‖c i‖^2):ℂ)*(∫ w,f w ∂(promenade i:Measure E4)):= by
    unfold diagonalLimit
    rw [FiniteMeasure.toMeasure_sum,integral_finsetSum_measure (fun i _=>f.integrable _)]
    refine sum_congr rfl fun i _=>?_
    rw [FiniteMeasure.toMeasure_smul,integral_smul_nnreal_measure, NNReal.smul_def,NNReal.coe_pow,coe_nnnorm,Complex.real_smul]
  unfold crossTest
  simp_rw [hx]; exact polar_sum_norm ..

-- spectrum halfspace. Allow all bounded continuous functions there; extension
-- is just to simplify types of the integrations, irrelevant since the measures
-- are Brilliant.
def TimeHalf:= {x:E4| 0≤YM.time x} -- type Set E4?
def clampTime : ContinuousMap E4 ↥TimeHalf where
  toFun x:= ⟨position (YM.spatial x) (max 0 (YM.time x)),by change 0≤ YM.time _; rw [time_position]; exact le_max_left ..⟩
  continuous_toFun := Continuous.subtype_mk (Mink.divide.symm.continuous.comp (Mink.rest_cont.prodMk (continuous_const.max Mink.clock_cont))) (fun x=>by change 0≤YM.time (position _ _); rw [time_position]; exact le_max_left ..)
lemma clamped (v: ↥TimeHalf): clampTime v=v:=Subtype.ext ((congrArg (position (YM.spatial v)) (max_eq_right (show 0≤YM.time v from v.property))).trans (position_eta _))
def onHalf (f:↥TimeHalf→ᵇ ℂ):E4→ᵇ ℂ:= f.compContinuous clampTime
variable {P x c r} {q:ℕ→ℝ}
  (A:Launch P c r)(Y:readyUV P c r x q)(hq:Tendsto q atTop (𝓝 0))(u:P.lodestarHere 3 (P.otherSpectrum 3 3 x))

private lemma polar_limit (Z W:Lead.Clan)(U:ℕ→SixCoefficients→ℂ)(V:SixCoefficients→ℂ)
    (L:∀ z, Tendsto (fun i=> U i z) atTop (𝓝 (V z))): Tendsto (fun i=> polar (U i) Z W) atTop (𝓝 (polar V Z W)):=
  ((((L _|>.sub (L _)).sub ((L _).const_mul _)).add ((L _).const_mul _)).div_const 4)
include A Y hq u
lemma cross_march (Z W:Lead.Clan)(f:ℕ→↥TimeHalf→ᵇ ℂ)(g:↥TimeHalf→ᵇ ℂ)(M:ℝ)
    (p:∀ i,‖f i‖≤ M)(e:∀ T:Set ↥TimeHalf, IsCompact T→TendstoUniformlyOn (fun i=>f i) g atTop T) :
    Tendsto (fun i=>crossTest (P.zoomMatrix x (c i) (r i)) (onHalf (f i)) Z W) atTop
      (𝓝 (if Z=W then ∫ w,onHalf g w ∂(promenade Z:Measure E4) else 0)) := by
  have he(S': Set E4)(t:IsCompact S') : TendstoUniformlyOn (fun i=>(onHalf (f i))) (onHalf g) atTop S':= by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ w
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (e _ (t.image clampTime.continuous)) δ w] with n h
    intro x y; exact h _ ⟨_,y,rfl⟩
  let V(z):=∫ w,onHalf g w ∂(diagonalLimit z: Measure E4)
  let U(i:ℕ)(z:SixCoefficients):= ∫ w,onHalf (f i) w ∂(P.zoomMatrix x (c i) (r i) z: Measure E4)
  have L := polar_limit Z W U V fun z=>
    FiniteMeasure.integral_moving_test (zoomMatrix_limit z A Y hq u) _ _ M
      (fun i=> ((f i).norm_compContinuous_le clampTime).trans (p i)) he
  rw [← diagonal_only]
  exact L
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
