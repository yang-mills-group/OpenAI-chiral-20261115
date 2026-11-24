import GaugeFieldConstruction.Epigram
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale.Veins
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
open Exterior Next.Free.Stretch Finset Matrix
variable {L c f:Side}{C:ℝ}
private lemma roofcap : ∃ A:ℝ,0<A ∧ ∀ L: Side, Odd L.val →∀ (p:Momentum), p∈ baseCube→∀ (l:Site L)(a: Cover × PlaqAxes)(r:TypeFace 1), ‖fenceW a p L l r‖ ≤ A*decay 4 l * ‖creditW a p r‖ :=by
 obtain ⟨V,v,h⟩:= alias_rail; refine ⟨(V^4)^4*V,mul_pos (pow_pos (pow_pos v _) _) v,fun L w p pv l a r=>?_⟩
 let q:=aliasAt p l; have he(i):= h L w p (mem_cube_real (base_subset_realCube zone_pos pv) zone_pos) l i; have hh: ‖area L q‖ ≤ V^4*(mix l)⁻¹:=by
    unfold area; rw [norm_prod]; refine (prod_le_prod (s:=univ) (fun i _=>norm_nonneg _) (fun i _=>(he i).2)).trans ?_; simp [prod_mul_distrib,mix,Axis]
 rw [receipts_B,norm_mul,norm_mul,norm_pow]
 apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); refine (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hh 4) ((he _).1.trans ((mul_le_of_le_one_right v.le (inv_le_one_of_one_le₀ (up_ge ..))))) (norm_nonneg _) (pow_nonneg (hh.trans' (norm_nonneg _)) 4)).trans ?_
 rw [mul_pow (V^4),inv_pow]; apply le_of_eq; unfold decay; ring
-- fix
private lemma heelD : ∃ C:ℝ,0<C∧∀ L:Side,Odd L.val→∀ p:Momentum,p∈baseCube→∀ (l:Site L), l≠0→ ‖(divisor L (L.val • aliasAt p l))⁻¹‖ ≤ C:=by
 let X:= (Σ n:{L:Side // Odd L.val}, {l: Site n.val// l≠ 0}); -- PSigma type? change
 obtain ⟨σ,C,h,e,V⟩:= blow_firm (fun i : X=>i.1.val) (fun _=>1) (fun i=>i.1.property) (fun i=>i.2.val) (fun i=>i.2.property)
 refine ⟨C⁻¹,inv_pos.mpr e,fun L w p g l h₀=>?_⟩
 rw [risen,norm_inv]
 have he: C*Next.Free.grade l^2≤‖(L.val:ℂ)^2*divisor 1 (aliasAt p l)‖:=V ⟨⟨L,w⟩,l,h₀⟩ p (base_subset_realCube h g)
 have hp:= (le_mul_of_one_le_right e.le (one_le_pow₀ (grade_ge l))).trans he; exact (inv_le_inv₀ (e.trans_le hp) e).mpr hp
lemma tipW : ∃ D:ℝ,0<D ∧ ∀ L:Side, Odd L.val →∀ p:Momentum,p∈baseCube→∀ (l:Site L)(a b: Cover × PlaqAxes)(r:TypeFace 1), ‖gateW a b p L l r‖ ≤ D*decay 2 l:=by
 obtain ⟨A,u,v⟩:=roofcap; obtain ⟨C,e,x⟩:=heelD
 let B:=meter.high+meter.high; let J:=meter.low; have hb:0<B:=add_pos meter.high_pos meter.high_pos; have hg:0<J:=meter.low_pos
 let V:= (A*4)^2; let D:= C*V+(A*B)^2/(J^2); have hd:0<D:=by unfold D V; positivity
 refine ⟨D,hd,fun L w p pH l a b r=>?_⟩; unfold gateW; rw [norm_mul,norm_mul,norm_star]
 have hK(z):= v L w p pH l z r
 have hy:= chipQ a p pH r; have hn:= chipQ b p pH r; have hP:=decay_pos l 4
 by_cases K:l=0
 · subst l
   rw [alias_scale]; simp only [Next.Free.lift_origin] -- tune
   have h0:reciprocal (0:Cover)=0:=by ext i; simp [reciprocal]
   simp_rw [h0,add_zero]
   by_cases h:p=0
   · subst p; simp only [divisor_origin,_root_.inv_zero,norm_zero,zero_mul]; exact (mul_pos hd (decay_pos _ _)).le
   let g:=cli p; have ht:0<g:= Real.sqrt_pos.mpr (lengthSq_pos h)
   have he:J^2*g^2 ≤ ‖divisor L p‖ := by unfold g; rw [cli_sq]; exact ((divisor_real_bounds L (base_subset_realCube zone_pos pH)).1).trans (Complex.re_le_norm _)
   have hh:0< J^2*g^2:=mul_pos (pow_pos hg _) (pow_pos ht _)
   rw [norm_inv,show decay 2 (0:Site L)=1 from (by simp [decay,mix,up]),mul_one]
   have hp': decay 4 (0 :Site L)=1:=by simp [decay,mix,up]
   rw [hp',mul_one] at hK -- at universal
   refine (mul_le_mul ((inv_le_inv₀ (lt_of_lt_of_le hh he) hh).mpr he) (mul_le_mul ((hK b).trans (mul_le_mul_of_nonneg_left hn.1 u.le)) ((hK a).trans (mul_le_mul_of_nonneg_left hy.1 u.le)) (norm_nonneg _) (mul_nonneg u.le (mul_nonneg hb.le ht.le))) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.mpr hh.le)).trans ?_ -- tune inv arguments
   apply le_trans (le_of_eq (b:= (A*B)^2/J^2) (by change _ * ( A*(B*g)*(A*(B*g)))=_; field_simp [ht.ne',hg.ne'] <;> ring)) (le_add_of_nonneg_left (mul_nonneg e.le (sq_nonneg _))) -- tune
 have hx:0≤ decay 4 l:= hP.le
 have ho : 0≤A*decay 4 l:=mul_nonneg u.le hx
 refine (mul_le_mul (x L w p pH l K) (mul_le_mul ((hK b).trans (mul_le_mul_of_nonneg_left hn.2 ho)) ((hK a).trans (mul_le_mul_of_nonneg_left hy.2 ho)) (norm_nonneg _) (by positivity)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) e.le).trans ?_
 rw [show C*(A*decay 4 l*4* (A*decay 4 l*4))=C*V*decay (4+4) l by rw [decay_add]; unfold V; ring]; apply mul_le_mul (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (sq_nonneg _))) ((decay_anti l) (by omega)) (decay_pos _ _).le hd.le
end YM.CF.Vale.Veins
end
