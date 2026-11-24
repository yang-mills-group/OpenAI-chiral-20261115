import Ridgetop.Hess
import YM.SU5.Regis.Curators
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
namespace Ridgetop
variable (q)
local notation "Γ"=>G.lieDim
abbrev tug:= (Real.sqrt q.direct)⁻¹
lemma kold: 0≤ tug q:=by unfold tug; positivity
lemma worry(i:PlaqAxes)(b:Site n)(x:Altar G n): ‖heeled (q:=q) b i x‖ ≤ tug q *‖x‖:=by
 apply (floret_bound i _).trans
 refine (pi_norm_le_iff_of_nonneg (mul_nonneg (kold _) (norm_nonneg _))).mpr ?_
 intro s; unfold Etch.river; rw [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (kold q)]
 apply mul_le_mul_of_nonneg_left _ (kold q)
 let o(_:Unit):Site n:=b; have U:Unit:= (); have he:=Etch.cup_sum o (Function.injective_of_subsingleton _) (ringT G s) x; simpa [o] using he
lemma can(o:Site n)(i:PlaqAxes):Continuous (@heeled n G q o i):=by
 unfold heeled; refine (cblossom _).continuous.comp (continuous_pi fun x=> LinearMap.continuous_of_finiteDimensional _)
variable {q}
open _root_.Factory
open scoped RealInnerProductSpace
variable (o:Site n)(i:PlaqAxes)(j:G.ColorIndex)(hx:0 <δ)
include B P L hx
lemma arcane : ‖fibreR B P o i j‖ ≤ tug q:=by
 let l:=fibreR B P o i j
 have h1:=worry q i o (l.val); let x:=heeled (q:=q) o i l.val
 have he : x j= ‖l‖^2 := (interests B P L o i j hx l).trans (real_inner_self_eq_norm_sq l)
 have hx: |x j|≤ ‖x‖:= by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p:=2) x j
 rw [he,abs_of_nonneg (sq_nonneg _)] at hx
 have hb:‖l.val‖=‖l‖:=rfl; rw [hb] at h1; change ‖x‖ ≤_ at h1
 change ‖l‖ ≤ _; exact le_of_not_gt (fun g=> (by nlinarith only [hx,h1,g, (kold q).trans_lt g]))
local notation "Sx" => stamen B P n
local notation "μ*" =>stdGaussian Sx
abbrev ePower(k:ℕ)(t:Sx):ℝ:=(heeled (q:=q) o i t.val j)^k
abbrev component{G:Gauge}(i:G.ColorIndex)(x:G.Color):=x i
lemma loc_int(k:ℕ):Integrable (ePower B P o i j k) μ*:=by unfold ePower; simp_rw [interests B P L _ _ _ hx]; exact pow_int _ _
lemma loc_mix (a v:ℕ)(x:Site n)(m:PlaqAxes)(r:G.ColorIndex): Integrable ((ePower B P o i j a)*(ePower B P x m r v)) μ*:=by
   unfold ePower; simp_rw [interests B P L _ _ _ hx]; exact price_powers ..
lemma grazed : (∫ x,ePower B P o i j 6 x ∂μ*)≤ 15*(tug q)^6 :=by
 unfold ePower; simp_rw [interests B P L o i j hx]; rw [sexta]; apply mul_le_mul_of_nonneg_left _ (by norm_num); rw [(InnerProductSpace.toDual ℝ Sx).norm_map]; exact pow_le_pow_left₀ (norm_nonneg _) (arcane B P L o i j hx) _
-- `cloud` can buy.Hick
#print axioms grazed
end Ridgetop
end Risa
end YM.Gleam.Luster
