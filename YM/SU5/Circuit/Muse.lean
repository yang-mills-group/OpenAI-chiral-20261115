import YM.SU5.Circuit.Daylight
import YM.Maxwell.Curls
set_option autoImplicit false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06 MeasureTheory
open YM.Stationary (Gaia cartWeight springAx spring_unit springTouch)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Classical
variable {v:ℝ}{x:Gaia}
def arrow (x:Gaia)(a:Axis):ℂ:= Complex.I*(x a:ℂ)
def music (a b:Axis)(v:ℝ)(x p:Gaia): ℂ:= arrow p a * nerve b v x p
lemma music_d (a b:Axis)(v r:ℝ)(x p:Gaia):HasDerivAt (fun t:ℝ=> nerve b v (errH a x t) p) (music a b v (errH a x r) p) r :=by
 unfold music nerve arrow; convert (rite r v x p a).const_mul (Complex.I*(p b:ℂ)) using 1 <;> try rfl
 unfold nerve; ring
lemma music_cap (a b:Axis)(v:ℝ)(x p:Gaia): ‖music a b v x p‖≤ tog v p:=by
 unfold music arrow; rw [norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]; by_cases e:p=0; · subst p; simp [tog]
 have he:= norm_pos_iff.mpr e; exact (mul_le_mul (sed ..) (dial ..) (norm_nonneg _) (norm_nonneg _)).trans_eq (by unfold house; field_simp)
lemma toneBudget (h:0<v)(a b:Axis)(x:Gaia): Integrable (music a b v x):=by
 refine (Onyx.pearl h).1.mono' ?_ (Eventually.of_forall fun i=>music_cap ..); unfold music nerve purr arrow burn pet tog; apply Measurable.aestronglyMeasurable; fun_prop
lemma lyric (h:0<v)(x:Gaia)(a b:Axis): HasDerivAt (fun z:ℝ=>∫ p,nerve b v (errH a x z) p) (∫ p,music a b v x p) 0:=by
 let F(t:ℝ):=nerve b v (errH a x t); let V(t:ℝ):=music a b v (errH a x t)
 have ht:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=V) (univ_mem (f:=𝓝 0)) (Eventually.of_forall fun i=> (reek h _ _).aestronglyMeasurable) (reek h _ _) (toneBudget h _ _ _).aestronglyMeasurable (Eventually.of_forall fun x y _=>music_cap ..) (Onyx.pearl h).1 (Eventually.of_forall fun x r _=>music_d ..)).2
 have hv: V 0=music a b v x:=by simp [V, errH]
 rwa [hv] at ht
-- explicit derivative of dye
abbrev βrock (v:ℝ)(x:Gaia):=fieldV x/v
def velvet (v:ℝ)(x:Gaia):ℝ:= Real.pi^2/(fieldV x)^3 * (2- (2+2*βrock v x + (βrock v x)^2)*elf x v)
lemma love (e:x≠0)(p:0<v)(a:Axis):HasDerivAt (fun z:ℝ=>dye v (errH a x z)) (velvet v x * (x a/2)) 0:=by
 let F:=fieldV x; let H(z):=fieldV (errH a x z); let J(z):=βrock v (errH a x z)
 have hv:=spring_v a x; have h0:errH a x 0=x:=by simp [errH]
 have he:=fen e; have hP:= (((hasDerivAt_const _ (Real.pi^2)).div (hv.pow 2) (by change (fieldV (errH a x 0))^2≠0; rw [h0]; positivity)).mul ((((hv.neg.div_const v).exp).mul ((hv.div_const v).const_add 1)).sub_const 1)); unfold velvet dye βrock elf; convert hP using 1 <;> try rfl
 norm_num only [Pi.pow_apply,Pi.div_apply, Pi.mul_apply, Pi.neg_apply,h0]
 field_simp; ring
lemma gaze (a b:Axis)(e:x≠0)(p:0<v): (cartWeight:ℂ) * (∫ p,music a b v x p)= (↑(cartWeight*(velvet v x*(x a/2)*(x b/2)+dye v x*(basis a b /2))):ℂ):=by
 let F:=errH a x
 let G(t:ℝ):= (F t) b/2
 have hm:F 0=x:=by simp [F,errH]
 have hv : HasDerivAt G (basis a b/2) 0:=by
    unfold G F errH; simp_rw [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]; change HasDerivAt _ (basis a b / 2) _; have ht := (((hasDerivAt_id' (0:ℝ)).mul_const (springAx a b)).const_add (x b)).div_const 2; convert ht using 1 <;> try rfl -- inspect
    simp [basis_eq,springAx,eq_comm]
 have hh:= ((love e p a).mul hv).ofReal_comp
 have ht:(∫ p,music a b v x p)=((velvet v x*(x a/2)*(x b/2)+dye v x*(basis a b/2):ℝ):ℂ):=by
   have hp: HasDerivAt (fun z:ℝ=> (↑(dye v (F z) * (F z b/2)):ℂ)) _ _:= hh
   unfold G at hp
   simp only [hm,show errH a x 0=x from hm] at hp
   apply (lyric p x a b).unique (hp.congr_of_eventuallyEq ?_); filter_upwards [(show Continuous F by unfold F errH; fun_prop).continuousAt.eventually_ne (show F 0≠0 from hm.trans_ne e)] with i hi; exact say _ p hi
 rw [ht,Complex.ofReal_mul cartWeight]
def kinder (i j:Axis)(d:ℝ)(x:Gaia):ℂ:= (cartWeight:ℂ)*∫ p,music i j (d^2)⁻¹ x p
lemma kiss (a b:Axis)(e:x≠0) : Tendsto (fun d:ℝ=> kinder a b d x) atTop (𝓝 ((Maxwell.grad a (Maxwell.grad b Maxwell.Green) x :ℝ) :ℂ)):=by
 let F:=fieldV x; let z(d:ℝ):= βrock (d^2)⁻¹ x; have he:=fen e
 have hp:Tendsto z atTop atTop:=by simpa [z,βrock,div_eq_mul_inv] using (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).const_mul_atTop he -- tune
 let g(d:ℝ):= elf x (d^2)⁻¹; have ht(k:ℕ): Tendsto (fun d=> (z d)^k * g d) atTop (𝓝 0):=by have hv:= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hp; simp only [Function.comp_def] at hv; simpa only [z,βrock,g,elf,neg_div] using hv
 have h:Tendsto g atTop (𝓝 0):=by simpa using ht 0
 have hl:Tendsto (fun d=>velvet (d^2)⁻¹ x) atTop (𝓝 (Real.pi^2/F^3*2)):=by
    let G(d:ℝ):= (2+2*z d+(z d)^2)*g d
    have h':Tendsto G atTop (𝓝 0):=by have h':= ((h.const_mul 2).add ((ht 1).const_mul 2)).add (ht 2); simpa [G,add_mul,mul_assoc] using h'
    simpa only [sub_zero,G,F,g,z,velvet] using (h'.const_sub 2).const_mul (Real.pi^2/F^3)
 have hr:Tendsto (fun d:ℝ=> dye (d^2)⁻¹ x) atTop (𝓝 (-(Real.pi^2/F^2))):=by
    have hv:Tendsto (fun d=> g d*(1+z d)) atTop (𝓝 0):=by simpa [mul_add,mul_comm] using h.add (ht 1)
    simpa [dye, F,z,g] using (hv.sub_const 1).const_mul (Real.pi^2/F^2)
 have hx:= Complex.continuous_ofReal.continuousAt.tendsto.comp ((((hl.mul_const (x a/2)).mul_const (x b/2)).add (hr.mul_const (basis a b/2))).const_mul cartWeight)
 change Tendsto _ _ (𝓝 (↑(cartWeight*_):ℂ)) at hx; have hs : (Maxwell.grad a (Maxwell.grad b Maxwell.Green) x :ℝ)=cartWeight*(Real.pi^2/F^3*2*(x a/2)*(x b/2)+ -(Real.pi^2/F^2)*(basis a b/2)):=by
    rw [Maxwell.second_Green e]; unfold cartWeight F fieldV Maxwell.normal; have _he:=norm_pos_iff.mpr e; have hp:=Real.pi_pos; field_simp; ring
 rw [hs]; exact hx.congr' ((eventually_gt_atTop 0).mono fun d u=> (gaze a b e (show 0<(d^2)⁻¹ by positivity)).symm)
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.kiss
