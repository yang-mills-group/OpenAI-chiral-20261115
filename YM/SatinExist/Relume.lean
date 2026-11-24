import YM.SatinExist.Lancet
import YM.Heat.Lift
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.SatinExist.Lancet
open Function Filter Metric Set Complex MeasureTheory
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators Classical
open OS.Semigroup
variable {H:Hilbert}{j:Axis}{N:Type} [Fintype N][DecidableEq N]
variable {f g:ℂ→ℂ}
def Full (f:ℂ→ℂ):Prop:= ∃ k:ℝ,0≤k ∧ Aim f k
namespace Full
lemma add (p:Full f)(q:Full g): Full (fun x=> f x+g x):=by obtain ⟨a,b,c⟩:=p; obtain ⟨d,e,t⟩:=q; exact ⟨a+d,add_nonneg b e, c.holo.add t.holo,fun z p=> (norm_add_le ..).trans (add_le_add (c.price z p) (t.price z p))⟩
lemma mul (p:Full f)(q:Full g): Full (fun x=> f x*g x):=by obtain ⟨a,b,c⟩:=p; obtain ⟨d,e,t⟩:=q; exact ⟨a*d,mul_nonneg b e, c.holo.mul t.holo,fun z p=> by rw [norm_mul]; exact mul_le_mul (c.price z p) (t.price z p) (norm_nonneg _) b⟩
lemma con (x:ℂ):Full (fun _=>x):=⟨‖x‖,norm_nonneg _,differentiableOn_const x,fun _ _=>le_refl _⟩
lemma sums {F:N→ℂ→ℂ}(p:∀ i,Full (F i)) (L:Finset N):Full (fun z=>∑ i∈ L,F i z):=by
 induction L using Finset.induction_on with| empty=>simp [con]| insert i L hi h=> simp only [Finset.sum_insert hi]; exact add (p i) h
lemma prods {F:N→ℂ→ℂ}(p:∀ i,Full (F i)) (L:Finset N):Full (fun z=>∏ i∈ L,F i z):=by
 induction L using Finset.induction_on with| empty=>simp [con]| insert i L hi h=> simp only [Finset.prod_insert hi]; exact mul (p i) h
lemma billD (f:ℂ→Matrix N N ℂ)(h:∀ i j: N, Full (fun z=> f z i j)):Full (fun z=> (f z).det):=by
 simp only [Matrix.det_apply']; exact sums (fun p:Equiv.Perm N=> mul (con (((Equiv.Perm.sign p).val:ℤ):ℂ)) (prods (fun i=>h (p i) i) Finset.univ)) Finset.univ -- order
end Full
variable (S:OS.Semigroup H j)(X Y: N→ H.space)
noncomputable def ahead (t:ℝ) : Matrix N N ℂ:= Matrix.of (fun i j=> inner ℂ (X i) (S.E t.toNNReal (Y j)))
private def best (x:Matrix N N ℂ):ℂ:= x.det * ∏ i,x i i
local notation "A"=> ahead S X Y
lemma happy_clock (h:(ahead S X Y 0).det≠0∧∀ i:N,A 0 i i≠0)(d:ℝ)(p:0<d) : ∃ᶠ i:ℕ in atTop,(A (i*d)).det≠0 ∧ ∀ j:N,A (i*d) j j≠0:=by
 let f(z:ℂ):= Matrix.of (fun i i'=>inner ℂ (X i) (S.F z (Y i')))
 have ht:N→ True:=fun _=>trivial
 have hx (y:ℝ)(v:0<y): f y=A y:=by
    unfold f ahead
    rw [← S.roots_heat (Real.toNNReal_pos.mpr v),OS.Semigroup.duration,Real.coe_toNNReal _ v.le]
 let J:= best ∘ f
 have hz(i k:N): Full (fun z=> f z i k):=by
    let g:= (innerSL ℂ (X i)).comp (ContinuousLinearMap.apply ℂ H.space (Y k)); refine ⟨‖X i‖*‖Y k‖,by positivity,fun z b=>(g.analyticAt _|>.comp (S.localHeat z b)).differentiableAt.differentiableWithinAt,fun z b=>?_⟩
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((S.F z).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.norm_row b))) (norm_nonneg _))
 obtain ⟨K,a,g⟩:= (Full.billD f hz).mul (Full.prods (fun i=> hz i i) Finset.univ)
 have he(i:Matrix N N ℂ): best i≠0 ↔ i.det≠0 ∧ ∀ k,i k k≠0:= by rw [best,mul_ne_zero_iff]; simp [Finset.prod_ne_zero_iff]
 have hc: Continuous (fun t=> best (ahead S X Y t)):=by
    have hu:Continuous A:= continuous_pi fun i=> continuous_pi fun k=> continuous_const.inner ((S.continuousE (Y k)).comp continuous_real_toNNReal)
    exact hu.matrix_det.mul (continuous_finsetProd _ fun i _=> (continuous_apply i).comp ((continuous_apply i).comp hu))
 have gz : ∀ᶠ x:ℝ in 𝓝[>] (0:ℝ),0<x:=self_mem_nhdsWithin
 obtain ⟨t,b,w⟩:= (gz.and (((hc.tendsto 0).eventually (isOpen_ne.mem_nhds ((he _).mpr h))).filter_mono nhdsWithin_le_nhds)).exists
 have hw:J t≠0:= by unfold J; rw [comp_apply,hx t b]; exact w
 refine ((Lancet.cont_rail J K a g d t p b hw).and_eventually (eventually_gt_atTop (0:ℕ))).mono fun i hv=> ?_
 have hu : (↑(i:ℕ):ℂ)*(d:ℂ)= ↑((i:ℝ)*d):=by push_cast; rfl
 apply (he _).1; simpa only [J,hu,comp_apply,hx ((i:ℝ)*d) (mul_pos (by exact_mod_cast hv.2) p)] using hv.1
end YM.SatinExist.Lancet
