import YM.SU5.FiniteGaugeData.Trigonal.Radian
import YM.SU5.FiniteGaugeData.ArchiveK.Oak
/-! # Coefficient uniqueness in open box, L1 (no periodic continuity required) -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option linter.unusedSimpArgs false
namespace YM.CF.Window.Trigo
open Function Filter Finset Metric
open Laurent Lattice Next.Free Bloch Fir Lat ArchiveK Largo WithLp MeasureTheory Complex
open scoped Topology BigOperators Set Pointwise InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra μFin
set_option quotPrecheck false
section
-- concentrate using maximum at interior spot
variable {X:Type*}[TopologicalSpace X][MeasurableSpace X][BorelSpace X]
private lemma locusL (f:X→ℝ)(μ:Measure X)[IsFiniteMeasure μ]{x:X}(p:∀ U∈𝓝 x,0< μ U){S:Set X}(vK:IsCompact S)(vM:∀ᵐ i∂μ, i∈S)(F:X→ℝ)(g:Continuous F)(v:Integrable f μ)(hc:ContinuousAt f x)(w:F x=1)(H: f x>0)(hp:∀ u,0≤F u)(hw:∀ y∈ S,y≠x→F y<1)(hL:∀ n:ℕ, Integrable (fun y=> F y^n*f y) μ): ∃ n:ℕ,0<∫ u,F u^n*f u∂μ:=by
 let y:= f x/2; have h0:0<y:=half_pos H; obtain ⟨A,a,s,h⟩:= _root_.mem_nhds_iff.mp (show ∀ᶠ q in 𝓝 x,y ≤ f q from hc.eventually (le_mem_nhds (half_lt_self H)))
 let T:= S\ A; have ht:IsCompact T:=vK.diff s; have hh:∃ ν:ℝ,0≤ν ∧ ν<1 ∧∀ x∈T,F x≤ν:=by
    by_cases h1:T.Nonempty; · obtain ⟨u,t,p⟩:= ht.exists_isMaxOn h1 g.continuousOn; exact ⟨_,hp u, hw _ t.1 (fun e=> t.2 (e.symm ▸ h)),fun _ q=>p q⟩
    exact ⟨0,le_rfl,zero_lt_one,fun i p=>False.elim (h1 ⟨i,p⟩)⟩
 obtain ⟨ν,V,V',v'⟩:=hh; obtain ⟨r,hr,hr'⟩:= exists_between V'; have hx:0<r:= V.trans_lt hr; let U:Set X:= A ∩ {i:X|r<F i}
 have hu: x∈ U:=⟨h,show r< F x from hr'.trans_eq w.symm⟩; have hU:IsOpen U:= s.inter (isOpen_lt continuous_const g); have hb:0< μ.real U:=by unfold Measure.real; exact ENNReal.toReal_pos (p _ (hU.mem_nhds hu)).ne' (measure_ne_top μ U)
 let C:= ∫ z,‖f z‖ ∂μ; let D:= μ.real U*y; have hD:0<D:=mul_pos hb h0; obtain ⟨n,HN⟩:= ((show Tendsto (fun n:ℕ=> (ν/r)^n*C) atTop (𝓝 0) from by rw [← zero_mul C]; exact (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg V hx.le) ((div_lt_one hx).2 hr)).mul_const C).eventually (gt_mem_nhds hD)).exists -- tune
 let B(z:X):= (U.indicator (fun _=> r^n*y) z:ℝ) - ν^n*‖f z‖; have hk(v:X)(d:v∈S) : B v ≤ F v^n*f v:=by
    have hq:0≤ν^n*‖f v‖:=by positivity
    unfold B; by_cases i:v∈ U
    · have hm:y≤ f v:= a i.1; rw [Set.indicator_of_mem i]; exact (sub_le_self _ hq).trans (mul_le_mul (pow_le_pow_left₀ hx.le ((show r<F v from i.2).le) _) hm h0.le (pow_nonneg (hp _) n))
    rw [Set.indicator_of_notMem i,zero_sub]; by_cases b:v∈A; · exact (neg_nonpos.mpr hq).trans (mul_nonneg (pow_nonneg (hp _) n) (h0.le.trans (a b)))
    refine (neg_le_neg ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hp _) (v' v ⟨d,b⟩) _) (norm_nonneg _)): F v ^ n * ‖f v‖ ≤ _)).trans ?_; rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (by simp only [Real.norm_eq_abs]; exact neg_abs_le _) (pow_nonneg (hp _) n)
 have he: (∫ u,B u∂μ) ≤ ∫ u,F u^n*f u∂μ:=integral_mono_ae (((integrable_const _).indicator hU.measurableSet).sub (v.norm.const_mul _)) (hL n) (vM.mono hk)
 refine ⟨n,lt_of_lt_of_le ?_ he⟩; unfold B; rw [integral_sub ((integrable_const _).indicator hU.measurableSet) (v.norm.const_mul _), integral_indicator hU.measurableSet,setIntegral_const,integral_const_mul]; apply sub_pos.mpr; change ν^n*C< μ.real U * _; change (ν/r)^n*C<D at HN; rwa [div_pow, div_mul_eq_mul_div,div_lt_iff₀ (pow_pos hx _),show D*r^n= μ.real U*(r^n*y) by unfold D; ring] at HN
#print axioms locusL
end
-- strict neighbourhood.Ages. moments set.
variable {x y:E4}{p:Momentum}{t C:ℝ}
local notation "π"=> Real.pi
local notation "Ξ"=> emitX
abbrev pulseFT(a:Cover)(x:E4):ℂ:= mode (brushQ x) a
def LP:= Submodule.span ℂ (Set.range pulseFT)
lemma lp_axis (a:Cover): pulseFT a∈LP:=Submodule.subset_span ⟨a,rfl⟩
lemma lp_γ(c:ℂ): (fun _:E4=>c)∈LP:=by
 convert LP.smul_mem c (lp_axis 0) using 1; funext i; simp [pulseFT,mode_zero]
lemma lp_join {f g:E4→ℂ}(h:f∈LP)(q:g∈LP): (fun i=> f i * g i)∈LP:= by
 change f*g∈ LP; induction h using Submodule.span_induction with
 | mem f v=>
    obtain ⟨x,rfl⟩:=v; induction q using Submodule.span_induction with
    | mem g h=> obtain ⟨y,rfl⟩:=h; rw [show pulseFT x*pulseFT y=pulseFT (x+y) from funext fun q=>(mode_shift ..).symm]; exact lp_axis _
    | zero=> rw [mul_zero]; exact LP.zero_mem
    | add f g _ _ h t=> rw [mul_add]; exact LP.add_mem h t
    | smul d x' _ h=> rw [Algebra.mul_smul_comm]; exact LP.smul_mem _ h
 | zero=>rw [zero_mul]; exact LP.zero_mem
 | add f k _ _ h t=> rw [add_mul]; exact LP.add_mem h t
 | smul d x _ p=> rw [Algebra.smul_mul_assoc]; exact LP.smul_mem _ p
lemma lp_sum{I:Type*}(A:Finset I)(f:I→E4→ℂ)(p:∀ i∈ A,f i∈LP): (fun x=>∑ i∈A,f i x)∈LP:= by rw [show (fun x:E4=>_)=(∑ i∈A,f i) from funext fun x=>(Finset.sum_apply ..).symm]; exact LP.sum_mem p -- tune
lemma lp_t {f:E4→ℂ}(h:Integrable f μF){Y:E4→ℂ}(p:Y∈LP)(t:∀ a:Cover, scout f a=0) : Integrable (Y*f) μF∧∫ x,(Y*f) x ∂μF =0:=by
 induction p using Submodule.span_induction with
 | mem y p=>
    obtain ⟨a,rfl⟩:= p; refine ⟨sing_in h a,?_⟩; exact (smul_eq_zero_iff_right (inv_pos.mpr gain_h).ne').1 (t a)
 | zero=> simp
 | add y z _ _ u v=> rw [add_mul]; exact ⟨u.1.add v.1,by simp_rw [Pi.add_apply]; rw [integral_add u.1 v.1,u.2,v.2,add_zero]⟩
 | smul c f t' u=> rw [Algebra.smul_mul_assoc]; refine ⟨u.1.smul _,?_⟩; simp_rw [Pi.smul_apply, integral_smul,u.2,smul_zero]
-- localization poker. LP contains the test `bell`
def peak(a:Axis)(x y:E4):ℝ:=2+Real.cos (y a-x a)
def bell(x y:E4):ℝ:= (∑ i:Axis, peak i x y)/12
private lemma aff(a:Axis)(x y:E4): Complex.exp ((↑(y a-x a):ℂ)*Complex.I) = pulseFT (step a) y * star (pulseFT (step a) x) := by
 have ht(x:E4): pulseFT (step a) x=Complex.exp (↑(x a)* Complex.I):=by simp only [pulseFT,surfK, pis, emit_axis,step_apply]; unfold coastE; simp [mul_ite]; rw [mul_comm] -- tune
 rw [ht,ht,Complex.star_def,←Complex.exp_conj, map_mul,conj_I,conj_ofReal,←Complex.exp_add]; apply congrArg; push_cast; ring
#print axioms lp_t
lemma lp_ringR: (fun y:E4=> (bell x y:ℂ))∈LP:=by
 let f(a:Axis)(y:E4):ℂ:= Complex.exp ((↑(y a-x a):ℂ)*Complex.I)
 have he(a:Axis): (fun y:E4=> (peak a x y:ℂ))∈LP:=by
    have hV(h k): star (pulseFT h k)=pulseFT (-h) k:=by unfold pulseFT; rw [surfK,surfK,emit_neg,inner_neg_right,coast_inv]
    let c:= pulseFT (step a) x; let u:= (step a:Cover)
    have hm:f a∈LP:=by
       rw [show f a= (star c) • pulseFT u from (funext fun i=> (aff a x i).trans (mul_comm ..))]; exact LP.smul_mem _ (lp_axis u)
    have ht: star ∘ (f a) ∈ LP:=by
       rw [show star ∘ f a=c • pulseFT (-u) from ?_]; · exact LP.smul_mem _ (lp_axis _)
       funext y; unfold f; simp only [Function.comp_apply,aff, star_mul,hV,neg_neg]; rfl
    let z:ℂ:=2; let F: E4→ℂ:= fun i=>(peak a x i:ℂ)
    change F∈_; have hp:F=(fun _=>z) + z⁻¹ • ((f a)+ star ∘ (f a)):=by
       funext i; let v:= f a i; let t:=(star v); unfold F; have he: v.re=Real.cos (i a-x a):= Complex.exp_ofReal_mul_I_re _
       rw [peak,←he]; push_cast; change 2+(v.re:ℂ)=2+ ((2:ℂ)⁻¹)*(v+t); apply congrArg (fun x:ℂ=>2+x); unfold t; rw [show v+star v=2*(v.re:ℂ) from ?_, inv_mul_cancel_left₀ (by norm_num : (2:ℂ)≠0)]; apply Complex.ext <;> simp [Complex.star_def,Complex.mul_re,Complex.mul_im,two_mul] -- tune
    rw [hp]; exact LP.add_mem (lp_γ _) (LP.smul_mem _ (LP.add_mem hm ht))
 let u:= (12:ℂ); let H(i:E4):ℂ:= (bell x i:ℂ); have hp:H=u⁻¹ • (fun i=>∑ a:Axis, (peak a x i:ℂ)):=by funext i; unfold H bell u; push_cast; rw [Pi.smul_apply,smul_eq_mul,inv_mul_eq_div]; -- tune
 change H∈LP; rw [hp]; exact LP.smul_mem _ (lp_sum univ _ fun i _=>he i) -- goal with H unification
@[fun_prop] lemma bell_cont(x:E4): Continuous (bell x):=by unfold bell peak; fun_prop
abbrev realIn:= {p:E4|∀ i:Axis,|p i|<π}
def realOut:= {p:E4|∀ i:Axis, |p i|≤π}
lemma realIn_g : IsOpen realIn:= by
 rw [show realIn=⋂ i:Axis,{p:E4| |p i|< π} by ext; simp [realIn]]; exact isOpen_iInter_of_finite fun _=> isOpen_lt (by fun_prop) continuous_const
lemma realIn_cover : realIn ⊆ stair:= fun x h=> (in_snow ..).2 fun i=> ⟨(abs_lt.mp (h i)).1.le, by have hp: x i<π:=(abs_lt.mp (h i)).2; unfold τ; linarith⟩
lemma stair_out : stair ⊆ realOut:= fun x h => fun i=> by
 obtain ⟨u,v⟩:= (in_snow _ _ _).1 h i; refine abs_le.mpr ⟨u,?_⟩; change x i < -π+2*π at v; linarith
lemma compactR : IsCompact realOut:= by
 refine (isCompact_closedBall (0:E4) (2*π)).of_isClosed_subset ?_ ?_
 · rw [show realOut=⋂ i:Axis,{p:E4| |p i|≤π} by ext; simp [realOut]]; exact isClosed_iInter fun i=> isClosed_le (by fun_prop) continuous_const
 intro x h; obtain ⟨i,hp⟩:= one_arm x; exact mem_closedBall_zero_iff.mpr (hp.trans (mul_le_mul_of_nonneg_left (h i) zero_le_two))
lemma bell_pos :0≤bell x y:=div_nonneg (sum_nonneg fun i _=>by unfold peak; linarith [Real.neg_one_le_cos (y i-x i)]) (by norm_num)
lemma bell_r(x:E4): bell x x=1:=by norm_num [bell,peak,Axis]
lemma bell_m (h:x∈realIn)(p:y∈realOut)(v:y≠x): bell x y<1:=by
 obtain ⟨i,b⟩:= Function.ne_iff.mp ((WithLp.ofLp_injective 2).ne v)
 let f(i):= peak i x y; have he(i:Axis):f i≤3:=by unfold f peak; linarith [Real.cos_le_one (y i-x i)]; -- tune no ; hg inside
 have hv:f i ≠3:=by
    intro e; apply b; apply sub_eq_zero.mp; have hp:= abs_lt.mp (h i); have hz:= abs_le.mp (p i);
    have hh:y i - x i=0:=(Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).1 (by unfold f peak at e; linarith); exact hh -- tune
 unfold bell; exact (div_lt_one (by norm_num)).2 ((sum_lt_sum (fun j _=> he j) ⟨i,mem_univ _, (he i).lt_of_ne hv⟩).trans_eq (by simp [Axis]; norm_num))
lemma powersR (x:E4)(n:ℕ) : (fun y=> ((bell x y:ℂ)^n))∈LP:= by induction n with| zero=>exact (funext (fun y:E4=> pow_zero (bell x y:ℂ))).symm ▸ (lp_γ 1)|succ n ih=>simp_rw [pow_succ]; exact lp_join ih lp_ringR
lemma μposR (h:x∈realIn)(S:Set E4)(t:S∈𝓝 x):0< μF S:=by
 unfold μF; obtain ⟨U,v,p,z⟩:= _root_.mem_nhds_iff.mp (inter_mem t (realIn_g.mem_nhds h)); have hu: volume U=(volume.restrict stair) U:=by rw [Measure.restrict_apply p.measurableSet,Set.inter_eq_left.mpr (fun i q=> realIn_cover (v q).2)]
 exact (p.measure_pos volume ⟨x,z⟩).trans_le (hu.le.trans (measure_mono (fun i q=>(v q).1)))
lemma Fabre (f:E4→ℂ)(t:Integrable f μF)(p:∀ a:Cover,scout f a=0)(u:x∈realIn)(h:ContinuousAt f x): f x=0:=by
 by_contra v; let Y':= f x; let L:ℂ→L[ℝ]ℝ:= Complex.reCLM.comp ( ((star Y') • (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ); let F(n:ℕ) (y:E4):= bell x y^n*f y; -- coercion ambiguous; adjust
 let Y:= L ∘ f
 have hz:0< Y x:=by
    change 0< (star Y'* Y').re; rw [mul_comm,Complex.star_def,Complex.mul_conj]; simpa using (Complex.normSq_pos.mpr v)
 have hp(n:ℕ): Integrable (fun y=> bell x y^n* Y y) μF ∧ ∫ y,bell x y^n*Y y∂μF=0:=by
    let Q: E4→ℂ:= fun y=> (bell x y:ℂ)^n; obtain ⟨g,z⟩:= lp_t (Y:=Q) t (powersR x n) p
    have hh(y:E4):bell x y^n*Y y=L ((Q*f) y):=by
       unfold Q; rw [Pi.mul_apply]; -- adjust maybe Q removed binder
       simp_rw [← Complex.ofReal_pow]; exact (map_smul L (bell x y^n) _).symm -- real_smul not def?
    have hv : Integrable (fun y=> L ((Q*f) y)) μF:= L.integrable_comp g; simp_rw [hh]; refine ⟨hv,(L.integral_comp_comm g|>.trans ?_)⟩; rw [z,map_zero]
 obtain ⟨n,z⟩:=locusL Y μF (x:=x) (μposR u) compactR ((ae_restrict_mem (snowC (-π) τ)).mono (fun x u=>stair_out u)) (bell x) (bell_cont x) (L.integrable_comp t) (L.continuous.continuousAt.comp h) (bell_r x) hz (fun _=>bell_pos) (fun v p t=> bell_m u p t) (fun i=>(hp i).1); exact z.ne' (hp n).2
#print axioms Fabre
end YM.CF.Window.Trigo
