import YM.CF.Graph.Choc
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
variable {G:Gauge}{n:Side}{h v a k C L W:ℝ}{R:PathData G}{F:RG.Clip}{i:ℕ}
lemma sparF (A:RG.Atom G i)(x:Site n)(U:Config G n)(p:BudgetPoint): ‖A.placed p U x‖ ≤ A.magnitude *p.threshold^i:=by
 have hg:=p.threshold_pos
 by_cases h:Healthy p.threshold (A.footprint x) U
 · rw [Atom.placed,masked_eq _ _ _ _ h]; unfold Atom.unmasked Atom.poly; let C (j:Fin i):=(A.leg j).atSite U x; have ht(j:Fin i):‖C j‖ ≤ p.threshold:=by
      let s:=A.leg j; let P:=slotFace s x; have he:P.1∈A.footprint x:=by
         refine mem_image.mpr ⟨s.offset,mem_insert_of_mem ?_,rfl⟩; refine mem_biUnion.mpr ⟨j,mem_univ _,mem_union_right _ ?_⟩; exact List.mem_toFinset.mpr (show s.offset∈ s.offset::_ from List.mem_cons_self)
      unfold C; rw [atSite_path,G.norm_adjoint]; refine le_trans (G.curvature_norm _) ?_; by_contra! t; exact Finset.disjoint_left.mp h he ((flags_spec ..).mpr ⟨P,Work.E01.base_touched _,t⟩)
   have hp(j)(b:G.ColorIndex): ‖C j b‖ ≤ p.threshold:= (PiLp.norm_apply_le _ _).trans (ht j) -- tune
   refine (norm_sum_le ..).trans ?_; rw [Atom.magnitude,sum_mul]; refine sum_le_sum fun b _=> ?_; rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]; refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _); refine (prod_le_prod (fun i _=>abs_nonneg _) (g:=fun _=>p.threshold) (fun i _=> hp i (b i))).trans_eq (by simp)
 rw [Atom.placed,masked_ne _ _ _ _ h,norm_zero]; unfold Atom.magnitude; positivity
lemma yarn (X:ℕ→RG.Atom G i)(u:SumBudget (fun j=> (X j).budget a) C)(p:0<a)(o: Site n)(V:Config G n)(P:BudgetPoint) : ‖atomSeries X P V o‖ ≤ C*P.threshold^i:=by
 have hh(j:ℕ):‖(X j).placed P V o‖≤ (X j).budget a *P.threshold^i:= (sparF ..).trans (mul_le_mul_of_nonneg_right ((X j).lower_budget _ p) (pow_nonneg P.threshold_pos.le i))
 have ht:=u.2.1.mul_right (P.threshold^i); exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun i=> norm_nonneg ((X i).placed P V o)) hh ht)).trans ((Summable.tsum_mono (Summable.of_nonneg_of_le (fun j=>norm_nonneg _) hh ht) ht hh).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right u.2.2 (pow_nonneg P.threshold_pos.le _)))
lemma oath (W:R.Bounds F a C L)(p:BudgetPoint)(V:Config G n) :
     ‖∑ x:Site n,(atomSeries R.cubic p V x+atomSeries R.quartic p V x)‖ ≤ n.val^4 *(C*p.threshold^3+C*p.threshold^4) ∧ ‖∑ x:Site n,atomSeries R.loop p V x‖ ≤ n.val^4*(L*p.threshold^2):=by
 constructor
 · refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=> (norm_add_le ..).trans (add_le_add (yarn _ W.three W.width i V p) (yarn _ W.four W.width i V p)))).trans_eq ?_); rw [sum_const,card_univ,site_card]; simp; ring
 exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=> yarn _ W.two W.width i V p)).trans_eq (by rw [sum_const,card_univ,site_card]; simp))
def taxY (n:Side)(β t C L:ℝ):ℝ:= β*((n.val:ℝ)^4 *(C*t^3+C*t^4))+n.val^4*(L*t^2)
def kinetic (N:Side)(P: BudgetPoint)(C L β c:ℝ):= β*(c*P.threshold^2)-taxY N β P.threshold C L
lemma harvest(W:R.Bounds F a C L)(p:BudgetPoint)(V:Config G n)(l:0≤ k)(s:k≤ F.linear)(e:0≤v)(h: flags p.threshold V≠∅): kinetic n p C L v k ≤ R.principal F p v V:=by
 have hp:= F.tail_pos; have he(q:Face (Per n)): 0≤R.baseTerm F p V q:=by
    unfold baseTerm; apply add_nonneg ?_ ?_
    · unfold clipped; split; apply div_nonneg; apply mul_nonneg F.quadratic_pos.le (by positivity); norm_num; exact mul_nonneg (mul_nonneg hp.le p.threshold_pos.le) (G.chord_nonneg _)
    split <;> positivity
 have ht: k*p.threshold^2 ≤ ∑ q,R.baseTerm F p V q:=by
    obtain ⟨i,h⟩:= nonempty_iff_ne_empty.mpr h; obtain ⟨j,v,t⟩:= (flags_spec ..).mp h; apply (single_le_sum (fun y _=>he y) (mem_univ j)).trans'; unfold baseTerm; apply (le_add_of_nonneg_right ?_).trans'
    · rw [clipped,if_neg t.not_ge,sq, ←mul_assoc]; exact mul_le_mul (mul_le_mul_of_nonneg_right s p.threshold_pos.le) t.le p.threshold_pos.le (mul_nonneg hp.le p.threshold_pos.le)
    split<;> positivity
 obtain ⟨A,B⟩:=oath W p V; unfold kinetic taxY PathData.principal; apply le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left (add_le_add ht (neg_le_of_abs_le A)) e) (neg_le_of_abs_le B)); exact le_of_eq (by ring)
lemma fullH(W:R.Bounds F a C L)(p:BudgetPoint)(V:Config G n)(l:0≤ k)(s:k≤ F.linear)(e:0≤v)(h: flags p.threshold V≠∅): kinetic n p C L v k ≤ R.inChannels F p v V:=by
 have he (s':Signed):= harvest W p (pull s' 0 V) l s e (by intro u; exact h (by rw [←Work.H03.flags_send (U:=V) s' 0 p.threshold,u]; simp))
 exact ((mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun i _=> he i)) (show 0≤ (Fintype.card Signed :ℝ)⁻¹ by positivity))).trans' (by simp)
end YM.CF.Graph
