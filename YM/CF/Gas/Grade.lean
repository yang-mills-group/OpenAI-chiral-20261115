import YM.CF.Gas.Assets
import YM.CF.Pastry.Bliss
import YM.CF.Petal.Event
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Fock Petal Pastry
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {n:Type*}[LinearOrder n][Fintype n] {Y:Type}[NormedCommRing Y][NormedAlgebra ℝ Y][NormOneClass Y]{k:ℕ}{v a u:ℝ}{f:E→Y}{x:E}
lemma Assets.times (p:0≤a)(h:Assets k f x a v){g:E→Y}(z:Assets k g x a u) : Assets k (fun i=> f i*g i) x a (v*u):=⟨h.1.mul z.1,(pot_k p h.1 z.1).trans (mul_le_mul h.2 z.2 (sum_nonneg (fun i _=> Jet.pos_nob p _)) ((norm_nonneg _).trans (h.valueB p)))⟩
lemma Assets.powF (p:0≤a)(h:Assets k f x a v)(l:ℕ): Assets k (fun x=> f x ^ l) x a (v^l):=by induction l with|zero => simp_rw [pow_zero]; exact fixed _ (by simp)|succ l ih=> simp_rw [pow_succ]; exact ih.times p h
lemma Assets.prodF (p:0≤a){I:Type*}(S:Finset I){f:I→ E→Y}{c:I→ℝ}(h:∀ i∈S,Assets k (f i) x a (c i)):Assets k (fun x=>∏ j∈S,f j x) x a (∏ i∈S,c i):=by
 classical
 induction S using Finset.induction_on with|empty=>simp_rw [prod_empty]; exact fixed _ norm_one.le|insert i P p' ih=>simp_rw [prod_insert p']; exact (h i (mem_insert_self ..)).times p (ih (fun i p=>h i (mem_insert_of_mem p)))
lemma assets_front [FiniteDimensional ℝ E] [CompleteSpace Y](p:0<a)(q:a ≤1)(S:Set E)(t:IsOpen S)(u:x∈ S)(g:∀ y∈S,Assets k f y a v)(s:v ≤1/2) : Assets k (fun x=> secA (f x)) x a (2*v):=by
 let F(y:E)(i:ℕ):= ((i.factorial:ℝ)⁻¹ • (f y)^i)
 have hp:= (norm_nonneg _).trans ((g x u).valueB p.le); obtain ⟨H,w⟩:=Petal.Pool.sized v hp (s.trans_lt (by norm_num)); let P(y:E)(i:ℕ):= F y (i+1)
 have hm(y:E)(hy:y∈ S)(i:ℕ) : Assets k (fun x=> P x i) y a (v^(i+1)):=by
    refine (((g y hy).powF p.le (i+1)).smB p.le ((↑(Nat.factorial (i+1)):ℝ)⁻¹)).monoL ?_
    rw [Real.norm_of_nonneg (by positivity)]; exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (i+1)))
 have he: Assets k (fun y=>∑' i,P y i) x a (∑' i:ℕ,v^(i+1)):= sum_assets (f:=fun i y=>P y i) t u p q (fun i y g=>hm y g i) H
 have hh: (fun y=>secA (f y)) =ᶠ[𝓝 x] (fun y=>∑' i,P y i):=by
    filter_upwards [t.mem_nhds u] with y hy; unfold secA; rw [exp_eq_tsum ℝ]; change (∑' i,F y i)-_= _
    have hv:= ((summable_nat_add_iff 1).mp (show Summable (fun i:ℕ=> F y (i+1)) from H.of_norm_bounded fun i=>Assets.valueB (f:=fun y=>P y i) p.le (hm y hy i))).sum_add_tsum_nat_add 1; rw [← hv, show ∑ i∈range 1, F y i=1 by simp [F]]; unfold P; abel
 refine ⟨he.1.congr_of_eventuallyEq hh, le_trans ?_ (le_trans he.2 ?_)⟩
 · unfold Jet.potash; apply sum_le_sum; intro i _; unfold Jet.noble; rw [(hh.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]
 rw [w]; apply (div_le_iff₀ (by linarith)).mpr; nlinarith

abbrev doseN(H:ℝ) : Poly n n:=⟨fun i=> (H:ℂ) • put i, by intro i j; rw [antiB_smul,antiB_smul']; simp [antiB, put_put]⟩
lemma toneB (h:ℝ)(X: Finset n): (doseN h).tag X=(h:ℂ)^X.card • poke X:=by
 induction X using Finset.induction_on with|empty=>simp [Poly.tag_void,poke]|insert i p l ih=>
   rw [Poly.tag_any _ _ _ l, show poke _= _ from Poly.tag_any _ p i l,ih,card_insert_of_notMem l]; change parity i p • (((h:ℂ) • put i)*((h:ℂ)^_ • poke p))=_ • (parity i p • (put i*poke p)); rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; simp only [smul_smul,pow_succ,mul_left_comm,mul_comm,mul_assoc] -- tune
lemma preserve (h:ℝ)(X:Finset n)(D:Dough n)(g:D∈stretch X): (doseN h).cook D∈ pasta X:=by
 let f:Poly n n:=doseN h; let A:=D.val; change Flour X (f.eval A); have he:Flour X A:=g; rw [he.pin,map_sum]; apply Flour.sum; intro i p; rw [map_smul,Poly.eval_oneT]; exact (show Flour X _ from (toneB h i).symm ▸ (Flour.point p).smul _).smul _ -- tune
noncomputable def dilF (h:ℝ) : Dough n →ₐ[ℝ] Dough n:= ((doseN h).cook).codRestrict _ (fun x=> preserve h univ x (fineShape x)) -- tune
lemma dil_p (h:ℝ)(x: Dough n)(i:Finset n): crumb (dilF h x).val i=(h:ℂ)^i.card * crumb x.val i:=by
 change crumb ((doseN h).eval x.val) i= _; unfold Poly.eval; simp only [LinearMap.coe_mk, AddHom.coe_mk]; rw [crumb_sum,sum_eq_single i]; · rw [crumb_scale,toneB,crumb_scale,chip]; simp [mul_comm];
 · intro j _ l; rw [crumb_scale,toneB,crumb_scale,chip]; simp [l.symm]
 simp
lemma price_d (h:ℝ)(p:0≤h)(D:Dough n): ‖dilF h D‖ ≤ tier h D.val:=by
 apply (lies le_rfl _).trans_eq; unfold tier; apply sum_congr rfl; intro i _; rw [dil_p]; simp [abs_of_nonneg p, Real.norm_of_nonneg p]
def augL(h:ℝ):Dough n →L[ℝ] Dough n:= LinearMap.toContinuousLinearMap (dilF h).toLinearMap -- tune
end YM.CF.Gas
