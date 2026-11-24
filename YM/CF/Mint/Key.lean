import YM.CF.Mint.Site
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {x y A B:ℕ→ℝ}
variable {N:ℕ→Side}{c b w r:ℝ}{β θ L:ℕ→ℝ}
structure RangeH(x β:ℕ→ℝ)(c b:ℝ):Prop where
 pos:0<c
 top:0<b
 rank:Tendsto x atTop atTop
 bound:∀ᶠ i in atTop,β i∈Set.Icc (c*x i) (b*x i)
abbrev eur(N:ℕ→Side)(i:ℕ):ℝ:= (N i).val
open Tulip Lat Cube SU Emu Rush Scree Graph RG
variable (P:RangeH x β c b)
namespace RangeH
include P
lemma age {N:ℕ→ Side}(g:Gray (lum x) (eur N)):Gray (lum x) (eur (fun i=>More (N i))):=by rw [show eur (fun i=>_)=_ from funext (fun i=> show eur (fun i=> More (N i)) i=eur N i*2 from by unfold eur; push_cast; norm_num [More])]; exact g.mul (Gray.coef (tc P.rank) 2)
lemma infl : ∀ᶠ i in atTop, 0<x i ∧0<β i∧ 0<tame x i∧ 0< vast x i:=by
 filter_upwards [P.rank.eventually_gt_atTop 0,P.bound] with i e q; have ht:0<tame x i:=by unfold tame temp; positivity
 exact ⟨e,(mul_pos P.pos e).trans_le q.1,ht, mul_pos e (pow_pos ht _)⟩
lemma ratio_v : Gray (lum x) fun i=> β i / x i:= by
 refine ⟨b,P.top,0,?_⟩; filter_upwards [P.infl,P.bound] with i ⟨e,v,t,u⟩ h; rw [Real.norm_of_nonneg (by positivity),pow_zero,mul_one]; exact (div_le_iff₀ e).mpr h.2
lemma invG: Gray (lum x) fun i=> (x i)⁻¹ := Gray.thin (tc P.rank) (tendsto_inv_atTop_zero.comp P.rank)
lemma tax_p (D:ℝ)(l:Gray (lum x) (eur N))(h:Gray (lum x) L): Aqua (lum x) fun i=> taxY (N i) (β i) (tame x i) D (L i)*(vast x i)⁻¹:=by
 let A:=lum x; have he:= tc P.rank; have ht:= damp P.rank; let F1(i):=β i/x i; let T (i):= tame x i; let Z:=eur N
 have hQ:= l.powG he 4 -- tune argument order
 have hv:Aqua A fun i=> (F1 i*Z i^4 * D)*(T i+T i*T i):= ((ht.panel (ht.pays (Gray.thin he ht.shrinks) he)).fed (((P.ratio_v.mul hQ).mul (Gray.coef he D))) he)
 have hy: -- term Z⁴*l*T²/vast=Z⁴*l/x; need Aqua x^-1 prove
       Aqua A fun i=> (x i)⁻¹:=by
    refine (Aqua.exp_neg he 1 one_pos).changeA ?_; filter_upwards [P.infl] with i ⟨e,u,t,h⟩; change Real.exp (-1*(lum x i))=(x i)⁻¹; rw [neg_one_mul,Real.exp_neg, show Real.exp (lum x i)= _ from Real.exp_log e]
 have hh:= hv.panel (hy.fed (hQ.mul h) he); refine hh.changeA ?_; filter_upwards [P.infl] with i ⟨e,u,t,h⟩; change F1 i*Z i^4*D*(T i+T i*T i)+(Z i^4*L i)*(x i)⁻¹= _; unfold F1 Z T taxY vast; unfold eur; field_simp
-- suppressed action denominator scaling
lemma lo_cost {T:ℕ→ BudgetPoint}(u:∀ᶠ i in atTop,(T i).threshold=tame x i)(p:Gray (lum x) (eur N))(g:Gray (lum x) L)(D:ℝ)(k:0<w): ∀ᶠ i in atTop, c*w/2*vast x i ≤ kinetic (N i) (T i) D (L i) (β i) w:=by
 have hc:=P.pos; filter_upwards [u,P.infl,P.bound, (P.tax_p D p g).shrinks.eventually (ge_mem_nhds (by positivity :0<c*w/2))] with i q ⟨e,xh,y,b⟩ t l
 unfold kinetic; rw [q]; rw [le_sub_iff_add_le]; have hv: taxY (N i) (β i) (tame x i) D (L i) ≤ c*w/2*vast x i:=(div_le_iff₀ b).1 l; refine le_trans (add_le_add_right hv _) ?_; exact le_trans (le_of_eq (show _= (c*x i)*(w*tame x i^2) by unfold vast; ring)) (mul_le_mul_of_nonneg_right t.1 (by positivity))
end RangeH
end YM.CF.Mint
