import YM.CF.Acorn.Altar
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch MeasureTheory
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D]
variable {X:Master D Y}{a c h v K:ℝ}{R S:Seal Y}{F G:D→ ℂ}
def Cash (X:Master D Y)(R:Seal Y)(a:ℝ)(F:D→ℂ)(K:ℝ):Prop := ∃ (H:Seal Y→ D→ℂ)(C:Seal Y→ℝ), (∀ S,Pro X S (H S) (C S)∧(C S≠0→R⊆S)) ∧ (∑ i, cost a R i*C i) ≤ K ∧ ∀ x,F x=∑ i,H i x
lemma any_t{f:ℕ→ℝ}(p:∑' i,f i≠0):∃ i,f i≠0:=by by_contra! h; simp [h] at p
lemma Pro.top (t:ℕ→D→ℂ)(K:ℕ→ℝ)(h:Summable K)(p:∀ i, Pro X S (t i) (K i)): Pro X S (fun x=> ∑' i,t i x) (∑' i,K i):=by
 have hK(i):0≤ K i :=(p i).pos; refine ⟨tsum_nonneg hK,?_,continuous_tsum (fun i=> (p i).cont) h (fun i x=>(p i).sumline x),fun x=>(norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun i=>norm_nonneg (t i x)) (fun i=>(p i).sumline x) h)).trans (Summable.tsum_le_tsum (fun i=>(p i).sumline x) (Summable.of_nonneg_of_le (fun i=>norm_nonneg (t i x)) (fun i=>(p i).sumline x) h) h),fun x y v=>tsum_congr fun i=> (p i).reads x y v,?_⟩
 · intro v; obtain ⟨i,h⟩:= any_t v; exact (p i).travel h
 intro E _ _ _ V r f q x g
 let A (i:ℕ):= t i ∘ f; have he(i:ℕ)(x)(hx:x∈ V): Allows X.k (A i) x (K i):=(p i).plot E V r f q x hx
 have hs:= under (μ':=(Measure.count:Measure ℕ)) r (f:=A) (b:=K) (fun i x hx=>(he i x hx).smooth) (fun y hy=> (measurable_of_countable _).stronglyMeasurable) (integrable_count_iff.mpr h.norm) he
 have hz: Allows X.k (Planned.AtomRegular.average Measure.count A) x (∑' i,K i) := by
   refine ⟨hs.germ r g,fun i hi=>?_⟩; rw [(hs.less hi).differentiate r g]
   apply le_trans (norm_integral_le_of_norm_le hs.cost (Eventually.of_forall (fun v=> (he v x g).norm_le i hi)))
   rw [integral_countable hs.cost]; simp
 apply hz.germ
 filter_upwards [r.mem_nhds g] with x y; unfold Planned.AtomRegular.average; rw [integral_countable (hs.observe y)]; simp [A]
lemma Pro.collects{J:Type}(f:J→D→ℂ)(S:Finset J){R:Seal Y}(b:J→ℝ)(h:∀ i∈S,Pro X R (f i) (b i)):Pro X R (fun x=> ∑ i∈S,f i x) (∑ i∈S,b i):=by
 classical
 induction S using Finset.induction_on with
 | empty=> simp only [sum_empty]; have he:=Pro.nonzero (X:=X) (c:=0) R (fun e=> False.elim (e rfl)); rwa [norm_zero] at he
 | @insert i S b ih=> simp only [sum_insert b]; exact (h i (by simp)).sum (ih (fun i k=> h i (mem_insert_of_mem k)))
namespace Cash
lemma tab{J:Type}[Fintype J](F:J→D→ℂ)(c:J→ℝ)(P:J→Seal Y)(h:∀ i, Pro X (P i) (F i) (c i)∧(c i≠0→R⊆P i))(u:∑ i,cost a R (P i)*c i ≤ K): Cash X R a (fun x=>∑ i,F i x) K :=by
 classical
 refine ⟨_,_,fun i=> ⟨Pro.collects F (univ.filter fun j=>P j=i) c (fun j p=> (mem_filter.mp p).2 ▸ (h j).1),fun t=>?_⟩,?_,?_⟩
 · obtain ⟨j,p,v⟩:=exists_ne_zero_of_sum_ne_zero t; rw [←(mem_filter.mp p).2]; exact (h j).2 v
 · simp_rw [mul_sum, sum_filter]; rw [sum_comm]; simpa using u
 intro x; simp_rw [sum_filter]; rw [sum_comm]; simp
lemma pos(c:Cash X R a F K):0 ≤ K:=by obtain ⟨F,C,h,k,l⟩:=c; exact (sum_nonneg fun i _=> mul_nonneg (rent_pos ..).le (h i).1.pos).trans k
lemma mul(p:Cash X R a F c)(q:Cash X R a G K)(h:R.Nonempty)(r:0≤a): Cash X R a (F*G) (worth X.k*c*K):=by
 have hc:= p.pos; obtain ⟨T,C,H,g,l⟩:=p; obtain ⟨Y',S,i,j,e⟩:=q
 let M(v: Seal Y × Seal Y):= T v.1*Y' v.2
 let k(v: Seal Y × Seal Y):= worth X.k*C v.1*S v.2
 rw [show F*G=fun x=> ∑ v,M v x from funext fun x=>by rw [Pi.mul_apply,l,e,sum_mul_sum,Fintype.sum_prod_type]; rfl]
 apply tab M k (fun x=>x.1∪x.2)
 · rintro ⟨x,y⟩; refine ⟨(H x).1.twice (i y).1 (fun p l=>by obtain ⟨v,h⟩:=h; exact ⟨v,mem_inter.mpr ⟨(H x).2 p h,(i y).2 l h⟩⟩),fun p=>?_⟩
   exact ((H x).2 (right_ne_zero_of_mul (left_ne_zero_of_mul p))).trans subset_union_left
 have hW:=lt_of_lt_of_le zero_lt_one (one_w X.k)
 rw [Fintype.sum_prod_type,mul_assoc]; calc
    _ ≤ ∑ x:Seal Y, ∑ y:Seal Y, worth X.k*(cost a R x*C x*(cost a R y*S y)):=by
     refine sum_le_sum fun x _=> sum_le_sum fun y _=>?_ ; exact (mul_le_mul_of_nonneg_right (cost_join r R x y) (show 0≤k (x,y) from mul_nonneg (mul_nonneg hW.le (H x).1.pos) (i y).1.pos)).trans_eq (by unfold k; dsimp only; ring)
    _ ≤ _:=by simp_rw [←mul_sum,←sum_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul g j (sum_nonneg fun i' _=> mul_nonneg (rent_pos ..).le (i i').1.pos) hc) hW.le
lemma direct {c:ℂ}(hr:Grove X.frame R):Cash X R a (fun _=>c) ‖c‖:=by
 have hp: Pro X R (fun _=>c) ‖c‖:= Pro.nonzero R (fun _=>hr)
 simpa using tab (fun (_:Unit) _=> c) (fun _=>‖c‖) (fun _=> R) (fun (_:Unit)=>⟨hp,fun _=> subset_rfl⟩) (show _ ≤ ‖c‖ from by simp [cost,rent]) -- tune
lemma sc(p:Cash X R a F K)(v:ℂ):Cash X R a (v • F) (‖v‖*K):=by
 obtain ⟨G,C,p,q,h⟩:=p; refine ⟨_,_,fun i=>⟨(p i).1.sc v,fun g=> (p i).2 (right_ne_zero_of_mul g)⟩,?_,?_⟩
 · simp_rw [mul_left_comm _ ‖v‖ _, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left q (norm_nonneg _)
 intro i; rw [Pi.smul_apply,h,Finset.smul_sum]; rfl
lemma series (v:ℕ→D→ℂ)(L:ℕ→ℝ)(h:∀ i,Cash X R a (v i) (L i))(p: Summable L):Cash X R a (fun x=>∑' i,v i x) (∑' i,L i) :=by
 choose M C z u w using h
 have he(i) :Summable (fun x=> C x i):=by
   have ht :0<cost a R i:=rent_pos ..
   exact Summable.of_nonneg_of_le (fun x=> (z x i).1.pos) (fun k=>show C k i ≤ L k/cost a R i from (le_div_iff₀ ht).mpr ((by rw [mul_comm]; exact (single_le_sum (f:=fun i=> cost a R i * C k i) (fun i _=>mul_nonneg (rent_pos ..).le (z k i).1.pos) (mem_univ i)).trans (u k)))) (p.div_const _)
 refine ⟨fun S x=> ∑' i,M i S x,_,fun S=> ⟨Pro.top _ _ (he S) (fun i=>(z i S).1), fun g=> ?_⟩,?_,fun x=>?_⟩
 · obtain ⟨i,h⟩:=any_t g; exact (z i S).2 h
 · simp_rw [←tsum_mul_left]; rw [← Summable.tsum_finsetSum (fun i _=>(he i).mul_left _)]; apply Summable.tsum_le_tsum u _ p; exact summable_sum (fun i _=> (he i).mul_left _) -- tune
 simp_rw [w]; rw [Summable.tsum_finsetSum (fun i _=> ?_)]
 exact Summable.of_norm_bounded (he i) (fun k=> (z k i).1.sumline x)
lemma embark(q:Cash X R a F K)(p:0≤a)(g:R.Nonempty)(f:Grove X.frame R): Cash X R a (Complex.exp ∘ F) (Real.exp (worth X.k*K)) :=by
 let T:=worth X.k*K; have hp:0≤ T:=mul_nonneg (zero_le_one.trans (one_w _)) q.pos
 let d(i:ℕ):ℝ:= (i.factorial:ℝ)⁻¹ • T^i; have hD:= NormedSpace.norm_expSeries_summable' (𝕂:=ℝ) T
 have hf(i:ℕ):Cash X R a (fun x=>F x ^ i) (T^i):=by
   induction i with
   | zero=> simp only [pow_zero]; have h:= direct (a:=a) (c:=(1:ℂ)) f; rwa [norm_one] at h
   | succ i ih=> simp only [pow_succ']; exact q.mul ih g p
 let Y(i:ℕ)(x:D):= ((i.factorial:ℂ)⁻¹) • F x^i
 have ht(i): Cash X R a (Y i) (d i):=by
   have h:=(hf i).sc ((i.factorial:ℂ)⁻¹); rw [norm_inv, Complex.norm_natCast] at h; exact h
 rw [Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]; exact_mod_cast (show Cash X R a (Complex.exp ∘ F) (∑' i,d i) from by
   rw [show Complex.exp ∘ F=fun x=>∑' i,Y i x from funext fun i=> by unfold Function.comp; rw [Complex.exp_eq_exp_ℂ,exp_eq_tsum ℂ]]; exact series _ _ ht hD.of_norm)
end Cash
end YM.CF.Acorn
