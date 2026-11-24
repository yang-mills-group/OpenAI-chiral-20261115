import YM.CF.Spark.Team
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova Sample Reflect Fock
attribute [local instance] opCStarAlgebra
variable {m B: Side} {e β:ℝ} (p:Clip)(S T:ℝ)(R:Reg β e B)(k:ℕ)
local notation "G0"=>SU.group
local notation "n'"=> Domain m B
local notation "U'"=> Pack m B
local notation "μ"=> wheel m B
variable (f:RP.Test m B)
abbrev hoist (x:Pack m B):ℂ:= ↑(primal p n' T S x.1) * (ratioR (R.W m) e β (R.time k) R.knob (R.c m) f x) -- m binder clashes n
-- knot integral
def shire:= ∫ x, hoist p S T R  k f x ∂μ
lemma weighted (g:U'→ℂ)(x:Pack m B) :ratioR (R.W m) e β (R.time k) R.knob (R.c m) (fun x=>g x • f x) x=g x*(ratioR (R.W m) e β (R.time k) R.knob (R.c m) f x):=by
 unfold ratioR; by_cases h:x∈TallyR m B e β
 · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]; unfold amplitude; rw [Algebra.smul_mul_assoc,act_smul,inner_smul_right]; ring
 rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
lemma warp(H:R.Works)(v:Geometry (CSide m B)): shire p S T R k (rideG m B v f)=shire p S T R k f:=by
 let W(x:Pack m B):ℂ:= primal p n' T S x.1; let L(g:RP.Test m B)(x:Pack m B):= W x • g x
 have he(g:RP.Test m B): shire p S T R k g= rawE (R.W m) e β (R.time k) R.knob (R.c m) (L g):=by
    unfold shire rawE hoist; unfold L; simp_rw [weighted]; rfl
 have hp:L (rideG m B v f)=rideG m B v (L f):=by
    funext x; unfold L rideG; dsimp only; rw [show W (nextG v x)= W x from congrArg Complex.ofReal (prim_g p x.1 _ T S),twist_formula,twist_formula,Algebra.mul_smul_comm,Algebra.smul_mul_assoc] -- order tune
 have ht:= H.gauge m k v (L f); unfold Reg.schwinger at ht; have hu:=R.Z m k
 rw [he,he,hp]; exact (div_left_inj' hu.ne').mp ht
lemma obtainR (h:Continuous f)(H:R.Works): Integrable (hoist p S T R  k f) μ:=by
 let Q(x:U'):=-(T*basicP p x.1); let W(x:U'):ℂ:= ↑(Real.exp (Q x)); let S':= Prod.fst ⁻¹' Calm G0 n' S ∩ (Set.univ:Set U')
 let F:= ratioR (R.W m) e β (R.time k) R.knob (R.c m) f
 have he:Continuous W:= (Complex.continuous_ofReal.comp Real.continuous_exp).comp (Continuous.neg (continuous_const.mul ((ren_c p).comp continuous_fst)))
 obtain ⟨q,w,hq⟩:= roofC he
 rw [show hoist p S T R  k f=S'.indicator (fun x=>W x * F x) from ?_]; swap
 · funext x; unfold hoist primal; by_cases k':x.1∈ Calm G0 n' S; rw [Set.indicator_of_mem k', Set.indicator_of_mem (show x∈S' from ⟨k',Set.mem_univ _⟩)]; rw [Set.indicator_of_notMem k',Complex.ofReal_zero,zero_mul, Set.indicator_of_notMem (show x∉S' from fun v=> k' v.1)]
 exact ((H.integrates m k f h).bdd_mul' he.aestronglyMeasurable (ae_of_all _ hq)).indicator ((measurable_fst (calm_m ..)).inter MeasurableSet.univ)
lemma going(U:Config G0 n') : Tendsto (fun i:ℕ=>Real.exp (sail p S T i U)) atTop (𝓝 (primal p n' T S U)):=by
 unfold primal sail; let r:= -(T* basicP p U)
 by_cases h:U∈ Calm G0 n' S
 · simp_rw [Set.indicator_of_mem h,show tollX S U=0 from (tolled ..).mpr h,mul_zero,sub_zero]; exact tendsto_const_nhds
 rw [Set.indicator_of_notMem h]; let b:=Real.exp (-tollX S U); have hp:b<1:= Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (lt_of_le_of_ne (toll_pos U S) (fun u=> h ((tolled ..).mp u.symm))))
 have he(i:ℕ): Real.exp (r-(i:ℝ)*tollX S U)=Real.exp r*b^i:=by rw [sub_eq_add_neg,Real.exp_add,show -((i:ℝ)*tollX S U)= (i:ℝ)*(-tollX S U) by ring,Real.exp_nat_mul]
 change Tendsto (fun i=>Real.exp (r-(i:ℕ)*tollX S U)) atTop (𝓝 0); simp_rw [he]; exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hp).mul_left _).tendsto_atTop_zero
lemma square_c (i b)(l:Site (More m))(t:Foot m B)(h:OfferedF m B i f b):Continuous (squareR m B l t i f b):=by
 unfold squareR; refine Continuous.comp ?c ((?d : Continuous (fiscal m B i f b)).comp ((northTrip m l).convey B))
 case d => unfold fiscal; exact (continuous_const (y:=chord b)).smul (((theta_cont (finger m B i)).comp (h.cont.comp ((slideM m i).convey B))).mul h.cont)
 exact (twist (star (quantU (costarU m B l t i)))).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional -- tune
lemma greenR(H:R.Works)(i b)(l:Site (More m))(h:OfferedF m B i f b):0 ≤ shire p S T R k (squareR m B l (R.c m) i f b):=by
 let G:=squareR m B l (R.c m) i f b; let F:=ratioR (R.W m) e β (R.time k) R.knob (R.c m) G; let W (v:ℕ)(x:U'):= (Real.exp (sail p S T v x.1):ℂ) * F x
 have hf:Continuous G:= square_c f i b l (R.c m) h
 have he v : 0 ≤ ∫ x,W v x ∂μ:=by
    let g:= loadR p S T v i f; let f':= squareR m B l (R.c m) i g b
    let z:=rawE (R.W m) e β (R.time k) R.knob (R.c m) (emptyF m B)
    have hu:0<z:=R.Z ..; have hx:0≤R.schwinger m k f':= H.mirror m k _ _ _ _ (wellR p i S T v f b h)
    have hp:R.schwinger m k f' * z=∫ x,W v x∂ μ:=by
       unfold Reg.schwinger; change _ / z * z=_; rw [div_mul_cancel₀ _ hu.ne']; unfold rawE; rw [show f'=(fun x:U'=> (Real.exp (sail p S T v x.1) : ℂ) • G x) from funext fun x=>lax ..]; simp_rw [weighted]; rfl
    exact hp ▸ mul_nonneg hx hu.le
 obtain ⟨q,w,hq⟩:= roofC (show Continuous (fun x:Pack m B=>Real.exp (sail p S T 0 x.1)) from Real.continuous_exp.comp ((sail_c p S T _).comp continuous_fst)); let B'(x:Pack m B):= q * ‖F x‖; let X:= H.integrates m k G hf
 refine ge_of_tendsto' (tendsto_integral_filter_of_dominated_convergence (l:=atTop) (F:=W) (f:=hoist p S T R k G) B' ?_ ?_ (X.norm.const_mul q) ?_) he -- tune bound need spec
 · exact Eventually.of_forall fun a=>(show AEStronglyMeasurable (W a) μ from (((Complex.continuous_ofReal.comp Real.continuous_exp).comp ((sail_c p S T a).comp continuous_fst)).aestronglyMeasurable.mul X.aestronglyMeasurable))
 · apply Eventually.of_forall; intro v; apply ae_of_all; intro x
   unfold W; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); refine (Real.exp_le_exp.mpr ?_).trans ((le_abs_self _).trans (hq x)); unfold sail; simp; exact mul_nonneg (by positivity) (toll_pos ..)
 apply ae_of_all; intro x; exact ((Complex.continuous_ofReal.tendsto _).comp (going p S T x.1)).mul_const _
lemma calmio(H:R.Works) : 0 ≤ shire p S T R k (emptyF m B):=by
  let i : Axis := 0; let v := emptyF m B; let l : Site (More m) := 0
  have ht : OfferedF m B i v false := ⟨continuous_const,fun _=> Sector.one,fun _ _ _=>rfl⟩
  have he : squareR m B l (R.c m) i v false=v := by
    funext x; unfold squareR fiscal
    let U := star (quantU (costarU m B l (R.c m) i))
    change twist U ((1:ℂ) • (theta _ 1 *1))=1
    rw [theta_one,one_mul,one_smul]; rw [twist_formula,mul_one]; exact U.property.2
  rw [show emptyF m B= _ from he.symm]; exact greenR p S T R k v H i false l ht -- tune
end YM.CF.Spark
