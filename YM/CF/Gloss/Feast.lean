import YM.CF.Spark.Atone
import YM.CF.Gloss.Year
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP.Str
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova Spark Sample Reflect Fock
attribute [local instance] opCStarAlgebra
variable {m B: Side} (p:Clip)(S T:ℝ){A D d:ℝ}{c:Foot m B}(W₀: Scroll m B c)(e β t a:ℝ)(u':Foot m B)
local notation "G0"=>SU.group
local notation "n'"=> Domain m B
local notation "U'"=> Pack m B
local notation "μ"=> wheel m B
variable (f:RP.Test m B)
abbrev hoistF (x:Pack m B):ℂ:= ↑(primal p n' T S x.1) * (ratioRF W₀ e β t a u' f x) -- m binder clashes n
-- knot integral
def shireF:= ∫ x, hoistF p S T W₀ e β t a u' f x ∂μ
lemma weightedF (g:U'→ℂ)(x:Pack m B) :ratioRF W₀ e β t a u' (fun x=>g x • f x) x=g x*(ratioRF W₀ e β t a u' f x):=by
 unfold ratioRF; by_cases h:x∈TallyR m B e β
 · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]; unfold amplitudeF; rw [Algebra.smul_mul_assoc,act_smul,inner_smul_right]; ring
 rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
lemma obtainRF (h:Continuous f)(H: ScaleK A D W₀)(Hp:Budget B e d): Integrable (hoistF p S T W₀ e β t a u' f) μ:=by
 let Q(x:U'):=-(T*basicP p x.1); let W(x:U'):ℂ:= ↑(Real.exp (Q x)); let S':= Prod.fst ⁻¹' Calm G0 n' S ∩ (Set.univ:Set U')
 let F:= ratioRF W₀ e β t a u' f
 have he:Continuous W:= (Complex.continuous_ofReal.comp Real.continuous_exp).comp (Continuous.neg (continuous_const.mul ((ren_c p).comp continuous_fst)))
 obtain ⟨q,w,hq⟩:= roofC he
 rw [show hoistF p S T W₀ e β t a u' f=S'.indicator (fun x=>W x * F x) from ?_]; swap
 · funext x; unfold hoistF primal; by_cases k':x.1∈ Calm G0 n' S; rw [Set.indicator_of_mem k', Set.indicator_of_mem (show x∈S' from ⟨k',Set.mem_univ _⟩)]; rw [Set.indicator_of_notMem k',Complex.ofReal_zero,zero_mul, Set.indicator_of_notMem (show x∉S' from fun v=> k' v.1)]
 exact ((sojournF H Hp h β t a u').bdd_mul' he.aestronglyMeasurable (ae_of_all _ hq)).indicator ((measurable_fst (calm_m ..)).inter MeasurableSet.univ)
lemma greenRF(hp:0≤t)(H1:ScaleK A D W₀)(H:Budget B e d)(i b)(l:Site (More m))(h:OfferedF m B i f b):0 ≤ shireF p S T W₀ e β t a u' (squareR m B l u' i f b):=by
 let G:=squareR m B l u' i f b; let F:=ratioRF W₀ e β t a u' G; let W (v:ℕ)(x:U'):= (Real.exp (sail p S T v x.1):ℂ) * F x
 have hf:Continuous G:= square_c f i b l u' h
 have he v : 0 ≤ ∫ x,W v x ∂μ:=by
    let g:= loadR p S T v i f; let f':= squareR m B l u' i g b
    have hu:=displacementF β H1 H l u' i t a hp g b (wellR p i S T v f b h)
    change 0 ≤ rawEF W₀ e β t a u' f' at hu; unfold rawEF at hu; rw [show f'=(fun x:U'=> (Real.exp (sail p S T v x.1):ℂ) • G x) from funext fun x=> lax ..] at hu; simp_rw [weightedF] at hu; exact hu
 obtain ⟨q,w,hq⟩:= roofC (show Continuous (fun x:Pack m B=>Real.exp (sail p S T 0 x.1)) from Real.continuous_exp.comp ((sail_c p S T _).comp continuous_fst)); let B'(x:Pack m B):= q * ‖F x‖; let X:= sojournF H1 H hf β t a u'
 refine ge_of_tendsto' (tendsto_integral_filter_of_dominated_convergence (l:=atTop) (F:=W) (f:=hoistF p S T W₀ e β t a u' G) B' ?_ ?_ (X.norm.const_mul q) ?_) he -- tune bound need spec
 · exact Eventually.of_forall fun a=>(show AEStronglyMeasurable (W a) μ from (((Complex.continuous_ofReal.comp Real.continuous_exp).comp ((sail_c p S T a).comp continuous_fst)).aestronglyMeasurable.mul X.aestronglyMeasurable))
 · apply Eventually.of_forall; intro v; apply ae_of_all; intro x
   unfold W; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); refine (Real.exp_le_exp.mpr ?_).trans ((le_abs_self _).trans (hq x)); unfold sail; simp; exact mul_nonneg (by positivity) (toll_pos ..)
 apply ae_of_all; intro x; exact ((Complex.continuous_ofReal.tendsto _).comp (going p S T x.1)).mul_const _
end YM.CF.RP.Str
