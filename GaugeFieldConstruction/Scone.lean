import YM.SU5.Regis.Easel
import YM.SU5.Circuit.Lark
import GaugeFieldConstruction.Rods
/-! # Projection budgets for monomials on actual covariance space. Dimension-free: dominating exponential assignment depends on factor count, not n. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 45000
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis Regis.Head ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
-- Put smooth frame and multiplier. Uniform derivative eff.
namespace Hood
private def Φ : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
private abbrev Υ (x:ℝ):=Φ x*x
private lemma Υ_lips : ∃ C:ℝ≥0,LipschitzWith C Υ:=by
 have hx:HasCompactSupport Υ:= Φ.hasCompactSupport.mul_right (f':=fun x=> x) -- maybe orientation
 have hv : ContDiff ℝ 1 Υ:=Φ.contDiff.mul contDiff_id
 obtain ⟨C,p⟩:= (hx.fderiv ℝ).exists_bound_of_continuous (hv.continuous_fderiv (by norm_num))
 refine ⟨⟨C,(norm_nonneg _).trans (p 0)⟩,lipschitzWith_of_nnnorm_fderiv_le (hv.differentiable (by norm_num)) fun x=>?_⟩; exact p x
def Rpod:ℝ≥0:= Υ_lips.choose
def parcel (a x:ℝ):= a*Υ (x/a)
variable {a r:ℝ}
lemma parcel_now (h:0<a)(x:ℝ): parcel a x= Φ (x/a)*x:=by unfold parcel Υ; field_simp
lemma parcel_id (h:0<a){x}(g:|x| ≤ a): parcel a x=x:=by
 rw [parcel_now h, Φ.one_of_mem_closedBall,one_mul]; rw [mem_closedBall_zero_iff,Real.norm_eq_abs,abs_div, abs_of_pos h,div_le_iff₀ h]; exact g.trans_eq (one_mul _).symm
lemma parcel_cost (h:0<a)(x:ℝ):|parcel a x| ≤ 2*a ∧ |parcel a x| ≤ |x| :=by
 rw [parcel_now h, abs_mul, abs_of_nonneg Φ.nonneg]; have hp:Φ (x/a)*|x| ≤ |x|:= mul_le_of_le_one_left (abs_nonneg _) Φ.le_one; refine ⟨?_,hp⟩; by_cases t:|x| ≤ 2*a; · exact hp.trans t
 rw [Φ.zero_of_le_dist,zero_mul]; · positivity
 change 2≤ dist (x/a) 0; rw [dist_zero_right,Real.norm_eq_abs,abs_div,abs_of_pos h,le_div_iff₀ h]; exact (lt_of_not_ge t).le -- tune
lemma parcel_diff (a:ℝ): ContDiff ℝ 1 (parcel a):= contDiff_const.mul ((Φ.contDiff.mul contDiff_id).comp (contDiff_id.div_const a))
lemma parcel_lip (h:0<a)(x y:ℝ): |parcel a x-parcel a y|≤ Rpod* |x-y|:=by
 unfold parcel; rw [← mul_sub,abs_mul, abs_of_pos h]; have hx: |Υ (x/a)-Υ (y/a)|≤ Rpod* |x/a-y/a|:= Υ_lips.choose_spec.dist_le_mul (x/a) (y/a)
 apply (mul_le_mul_of_nonneg_left hx h.le).trans_eq; rw [← sub_div,abs_div,abs_of_pos h]; field_simp

-- dominate term by sum over ± exponentials, price exponent independent of cap. Monomial arguments *independently* capped.
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
local notation "J" => StrongDual ℝ E
abbrev factorV {I : Type*} (x: List I)(f:I→ℝ):= (x.map f).prod
def horus (Z:J) (L:List J)(w:ℝ)(x:E):ℝ:= Real.exp (Z x + w * (L.map (fun i=> |i x|)).sum)
private lemma vault_Z (L:List J) (w:ℝ)(p:0≤w)(k:ℝ)(e:0≤ k)(t:∀ i∈L,‖i‖ ≤ k)(r:ℝ)(Z:J)(v:‖Z‖≤r): Integrable (horus Z L w) (stdGaussian E) ∧ (∫ x,horus Z L w x∂stdGaussian E) ≤ 2^L.length*Real.exp ((r+w*L.length*k)^2/2):=by
 induction L generalizing r Z with
 | nil=>
    have ht: horus Z [] w=fun x=> Real.exp (1*Z x):=by funext i; simp [horus]
    simp only [ht,List.length_nil,Nat.cast_zero,pow_zero,mul_zero,zero_mul,add_zero, one_mul 1];
    constructor
    · apply (mgf_pos_iff (X:= ⇑Z) (t:=1)).1; rw [Regis.exp_linear]; exact Real.exp_pos _
    change mgf (⇑Z) _ 1 ≤ _; rw [one_mul,Regis.exp_linear, one_pow,mul_one]; exact Real.exp_monotone (by gcongr)
 | cons i l ih =>
    have he : ‖w • i‖≤ w*k:=by rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg p]; exact mul_le_mul_of_nonneg_left (t i List.mem_cons_self) p
    let x:= fun a:E=> Real.exp (r+horus Z l w a); let K:=r+w*k; let R:= Z+w • i; let V:= Z-w • i; have ht:= fun i h=> t i (List.mem_cons_of_mem _ h)
    obtain ⟨f,g⟩:= ih ht K R ((norm_add_le ..).trans (add_le_add v he)); obtain ⟨u,h⟩:= ih ht K V ((norm_sub_le ..).trans (add_le_add v he))
    have hm(a): horus Z (i::l) w a≤ horus R l w a+horus V l w a:=by
        unfold horus; rw [List.map_cons,List.sum_cons]; rcases le_total 0 (i a) with k|k
        · rw [abs_of_nonneg k]; have hp:R a=Z a+w*i a:=rfl
          rw [hp, mul_add,← add_assoc]; exact le_add_of_nonneg_right (Real.exp_pos _|>.le) -- tune
        rw [abs_of_nonpos k]; rw [show V a=Z a-w*i a from rfl,mul_add, mul_neg,← add_assoc, ← sub_eq_add_neg]; exact le_add_of_nonneg_left (Real.exp_pos _|>.le)
    have hz:Continuous fun x:E=> (l.map fun i=> |i x|).sum:=by clear ht t f u g h ih hm x; induction l with
                                                                             | nil=> exact continuous_const
                                                                             | cons i l H=> exact i.continuous.abs.add H
    have hi: Integrable (horus Z (i::l) w) (stdGaussian E) := (f.add u).mono' (Z.continuous.add (continuous_const.mul (i.continuous.abs.add hz))|>.rexp|>.aestronglyMeasurable) (ae_of_all _ fun a=> by rw [Real.norm_of_nonneg (show 0 ≤ horus Z (i::l) w a from (Real.exp_pos _).le)]; exact hm a)
    refine ⟨hi, (integral_mono hi (f.add u) hm).trans ?_⟩; simp_rw [Pi.add_apply]; rw [integral_add f u]; apply (add_le_add g h).trans_eq; rw [List.length_cons,Nat.cast_add,Nat.cast_one,show r+w*_ * k= K+w* l.length*k by unfold K; ring,pow_succ]; ring
abbrev domeP (k:ℝ)(w:ℝ)(m:ℕ):= 2^m*Real.exp (((0:ℝ)+w*m*k)^2/2)
lemma dome_v (k:ℝ)(p:0≤ k)(L:List J)(t:∀ i∈L, ‖i‖≤ k){m:ℕ}(w:L.length ≤ m)(a:ℝ)(hv:0 ≤ a) : Integrable (horus 0 L a) (stdGaussian E) ∧ (∫ x,horus 0 L a x∂stdGaussian E) ≤ domeP k a m:=by
 obtain ⟨p,h⟩:= vault_Z L a hv k p t 0 0 (by simp); refine ⟨p,h.trans ?_⟩; unfold domeP; gcongr; norm_num -- tune
lemma dome_W (k:ℝ)(w:ℝ)(m:ℕ): 0 < domeP k w m :=by unfold domeP; positivity
private lemma shelter (g:ℝ→ℝ)(w:∀ x,|g x|≤|x|)(L:List J)(x:E): |factorV L (fun i=> g (i x))|≤ horus 0 L 1 x:=by
 induction L with
 | nil=> simp [factorV,horus]
 | cons i l ih=> rw [show factorV (i::l) _= g (i x)* _ from rfl,abs_mul]; apply (mul_le_mul ((w _).trans (le_trans (by linarith: |i x| ≤ |i x|+1) (Real.add_one_le_exp _))) ih (abs_nonneg _) (Real.exp_pos _|>.le)).trans; unfold horus; rw [List.map_cons,List.sum_cons,one_mul,one_mul]; simp [Real.exp_add]
lemma snack (g:ℝ→ℝ)(h:Continuous g)(L:List J): Continuous (fun x:E=> factorV L (fun i=>g (i x))):=by
 induction L with
 | nil=> exact continuous_const
 | cons i l ih=> exact (h.comp i.continuous).mul ih
lemma shelter_v (g:ℝ→ℝ)(h:Continuous g)(w:∀ x, |g x|≤|x|)(k:ℝ)(p:0 ≤ k)(L:List J)(t:∀ i∈L, ‖i‖ ≤ k){m:ℕ}(u:L.length ≤ m): Integrable (fun x:E=>factorV L (fun i=>g (i x))) (stdGaussian E) ∧ |∫ x,factorV L (fun i=>g (i x))∂stdGaussian E|≤domeP k 1 m:=by
 obtain ⟨j,b⟩:= dome_v k p L t u 1 zero_le_one
 have ht(x:E): |factorV L (fun i=>g (i x))| ≤ horus 0 L 1 x:= shelter g w L x; have hx: ∀ᵐ x ∂stdGaussian E, ‖factorV L (fun i=> g (i x))‖≤ horus 0 L 1 x:= ae_of_all _ ht
 exact ⟨j.mono' (snack g h L).aestronglyMeasurable hx, (norm_integral_le_of_norm_le j hx).trans b⟩
lemma cuts (g:ℝ→ℝ)(h:Continuous g)(a:ℝ)(f:∀ x,|x|≤a→ g x=x)(b:∀ x,|g x|≤|x|)(k:ℝ)(p:0≤ k)(L:List J)(t:∀ i∈L, ‖i‖ ≤ k){m:ℕ}(u:L.length ≤ m): |(∫ x:E,factorV L (fun i=>g (i x))∂stdGaussian E)-(∫ x:E,factorV L (fun i=>i x)∂stdGaussian E)| ≤ 2*domeP k 2 m*Real.exp (-a):=by
 obtain ⟨hp,-⟩:=shelter_v _ h b _ p L t u; obtain ⟨hv,-⟩:=shelter_v id continuous_id (by simp) _ p L t u; simp_rw [id] at hv; rw [← integral_sub hp hv]
 obtain ⟨hq,hs⟩:= dome_v k p L t u 2 (by norm_num)
 let F(x):=2*Real.exp (-a)*horus 0 L 2 x; have hf : Integrable F (stdGaussian E):= hq.const_mul _; let Q(x:E):= factorV L (fun i=>g (i x)); let R(x:E):=factorV L (fun i=> i x)
 change |∫ x,(Q x-R x)∂stdGaussian E|≤ _; rw [← Real.norm_eq_abs]; refine le_trans (b:= (∫ x,F x∂stdGaussian E)) (norm_integral_le_of_norm_le hf (ae_of_all _ fun i=>?_)) ?_
 · by_cases c:∃ j∈L,a ≤|j i|
   · obtain ⟨j,w,v⟩:=c; apply (norm_sub_le ..).trans; have he:(L.map (fun j=> |j i|)).sum ≥ a:= by
          clear h t hp hv hf hq hs F Q R u b f; induction L with
          | nil=> simp at w
          | cons k l ih=>
              rw [List.map_cons,List.sum_cons]; rcases List.mem_cons.mp w with rfl|h; · exact v.trans (le_add_of_nonneg_right (List.sum_nonneg (fun i v=> by obtain ⟨r,h,rfl⟩:=List.mem_map.mp v; exact abs_nonneg _)))
              exact (ih h).trans (le_add_of_nonneg_left (abs_nonneg _))
     apply (add_le_add (show ‖Q i‖≤ _ from shelter g b L i) (show ‖R i‖ ≤ _ from shelter id (by simp) L i)).trans; rw [← two_mul]; unfold F; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by norm_num); unfold horus; rw [← Real.exp_add]; apply Real.exp_monotone; change 0+1*_ ≤ -a+(0+2*_); linarith only [he]
   push Not at c; rw [show Q i=R i from ?_,sub_self,norm_zero]; · unfold F horus; positivity
   unfold Q R factorV; congr 1; apply List.map_congr_left; intro j v; exact f (j i) (c j v).le
 rw [show F=_ from rfl,show (∫ x,F x∂stdGaussian E) =2*Real.exp (-a)*(∫ x,horus 0 L 2 x∂stdGaussian E) from integral_const_mul ..]; linarith only [mul_le_mul_of_nonneg_left hs (Real.exp_pos (-a)|>.le)]
end Hood
end YM.Gleam.Guide
end
