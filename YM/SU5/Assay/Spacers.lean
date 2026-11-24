import YM.SU5.Aria.Screens
import YM.SU5.Assay.BSOT
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)
/-! Heat spacers (clip at zero) and currency of packed operators
 strictly above a width threshold. -/
abbrev wax (a:ℝ):=S.E a.toNNReal
local notation "ω"=>S.wax
variable {a b c:ℝ}
lemma wax_symm (a:ℝ): star (ω a)=ω a:= S.sym _
lemma wax_zero : ω 0=1:=by unfold wax; rw [Real.toNNReal_zero];exact S.eZero
lemma wax_pay (a:ℝ): ‖ω a‖ ≤ 1:= S.shrinks _
lemma wax_sq (h:0≤a)(q:0≤b): ω a*ω b=ω (a+b):=by unfold wax; rw [Real.toNNReal_add h q,S.time];rfl
lemma wax_split (h:0≤a)(q:a≤b) : ω (b-a)*ω a=ω b ∧ ω a*ω (b-a)=ω b:=by
 have t:=sub_nonneg.mpr q; rw [wax_sq S t h,wax_sq S h t,sub_add_cancel,add_comm a,sub_add_cancel]; exact ⟨rfl,rfl⟩
lemma wax_strong (u:H):Continuous (fun r=>ω r u):=(S.continuousE u).comp continuous_real_toNNReal
lemma wax_pin (a:ℝ):BSOT S.wax (𝓝 a) (ω a):=by
 refine ⟨⟨_,zero_le_one,Eventually.of_forall (S.wax_pay)⟩,fun _=> (S.wax_strong _).tendsto _,?_⟩
 intro u; simp only [wax_symm]; exact (S.wax_strong _).tendsto _
lemma wax_limit {I:Type*}{l:Filter I}{f:I→ℝ}(h:Tendsto f l (𝓝 b)): BSOT (fun i=>ω (f i)) l (ω b):=
   (S.wax_pin b).visit h
lemma wax_cont (h:0<a):ContinuousAt S.wax a:= CF.Buffered.Afterglow.Tower.Aria.steam_contPos S a h
lemma wax_analytic (h:0<a):AnalyticAt ℝ S.wax a:=by
 let C:ℝ→ℂ:= Complex.ofRealCLM; have t:C a∈inside:=h
 refine ((S.localHeat (C a) t).restrictScalars.comp (Complex.ofRealCLM.analyticAt _)).congr ?_
 filter_upwards [lt_mem_nhds h] with x u
 exact (congrArg S.F (show C x = duration x.toNNReal from (congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal x u.le)).symm)).trans (S.roots_heat (Real.toNNReal_pos.mpr u))

abbrev sand (A:H.Op)(a b:ℝ):=ω a*A*ω b
lemma sand_star (A:H.Op)(a b:ℝ):star (S.sand A a b)= S.sand (star A) b a:=by
 unfold sand; rw [star_mul,star_mul,wax_symm,wax_symm,mul_assoc]
lemma sand_pay (A:H.Op)(a b:ℝ): ‖S.sand A a b‖≤‖A‖:=by
 refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.wax_pay _)).trans ?_)
 exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.wax_pay _))
lemma sand_join {a b x y:ℝ}(ha:0≤a)(hb:0≤b)(hx:0≤x)(hy:0≤y)(A:H.Op):
 S.sand (S.sand A a b) x y= S.sand A (a+x) (b+y):=by
 unfold sand; rw [←mul_assoc,←mul_assoc, mul_assoc _ (ω b), S.wax_sq hx ha,S.wax_sq hb hy, add_comm x a]
lemma sand_step {x y z u w:ℝ}(a:w≤x)(b:w≤y)(p:x≤z)(q:y≤u)(A:H.Op):
   S.sand A (z-w) (u-w) = S.sand (S.sand A (x-w) (y-w)) (z-x) (u-y):=by
 rw [sand_join S (sub_nonneg.mpr a) (sub_nonneg.mpr b) (sub_nonneg.mpr p) (sub_nonneg.mpr q),show x-w+(z-x)=z-w by abel,show y-w+(u-y)=u-w by abel]
lemma sand_limit {I:Type*}{l:Filter I}{a b:ℝ}{f g:I→ℝ}{A:H.Op}{m:I→H.Op}
 (p:BSOT m l A)(u:Tendsto f l (𝓝 a))(v:Tendsto g l (𝓝 b)):
 BSOT (fun i=>S.sand (m i) (f i) (g i)) l (S.sand A a b):=
 ((S.wax_limit u).mul p).mul (S.wax_limit v)
end YM.OS.Semigroup
