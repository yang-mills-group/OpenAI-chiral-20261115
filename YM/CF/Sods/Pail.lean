import YM.CF.Sods.Verd
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset Kea
open scoped Topology BigOperators Matrix ContDiff Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E:Type*}[Fintype E][DecidableEq E][Nonempty E]
set_option maxHeartbeats 320000 in
lemma rig(f:UNI E):∃ (V:UNI E), V.val.det=1 ∧ ∀ H:E→ℂ,twist V (Matrix.diagonal H)=twist f (Matrix.diagonal H):=by
 classical
 let i:E:=Classical.arbitrary E
 let t(e):= if e=i then star f.val.det else 1; let D:=Matrix.diagonal t
 have h: D∈unitary (Op E):=by
   apply Matrix.mem_unitaryGroup_iff.mpr; rw [show star D= Matrix.diagonal (star ∘ t) from ?_]; swap
   · ext a b; by_cases h:a=b<;> simp [D,h,Ne.symm]
   unfold D; rw [Matrix.diagonal_mul_diagonal]; ext a b; have ht:= (Matrix.det_of_mem_unitary f.property).1; by_cases e:a=b; swap; · rw [Matrix.diagonal_apply_ne _ e,Matrix.one_apply_ne e]
   subst b; rw [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]; by_cases g:a=i; unfold t; simp only [g,ite_true,Function.comp_apply,star_star]; exact ht; simp [g,t]
 let U:UNI E:=⟨D,h⟩; refine ⟨f*U,?_,?_⟩
 · change (f.val*D).det=1; have he :D.det=star f.val.det:=by rw [show D.det=_ from Matrix.det_diagonal]; simp [t]
   rw [Matrix.det_mul,he]; exact (Matrix.det_of_mem_unitary f.property).2
 intro H; unfold twist; rw [map_mul]; change twist f (twist U _)=_; have hp: Commute U.val (Matrix.diagonal H):=by
   change Matrix.diagonal t * Matrix.diagonal H = Matrix.diagonal H * Matrix.diagonal t; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; funext i; exact mul_comm ..
 rw [twist_formula U,hp.eq,mul_assoc,U.property.2,mul_one]; rfl
lemma tone(f:UNI E):‖f.val‖=1:=CStarRing.norm_of_mem_unitary f.property
lemma opt {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F](f:Op E→ F)(h:ContDiff ℝ 1 f):∃ C:ℝ,0<C∧ ∀ U V:UNI E, ‖f U.val-f V.val‖≤ C* ‖U.val-V.val‖:=by
 let A:= closedBall (0:Op E) 2
 obtain ⟨c,g⟩:= (isCompact_closedBall (0:Op E) (2:ℝ)).bddAbove_image ((h.continuous_fderiv (by simp)).norm.continuousOn)
 let C:=max 1 c; have hc:0<C:=lt_max_of_lt_left one_pos; refine ⟨C,hc,fun V W=>?_⟩; have ht(U:UNI E):U.val ∈ A:=by rw [show A= _ from rfl, mem_closedBall_zero_iff,tone]; norm_num
 exact (convex_closedBall (0:Op E) (2:ℝ)).norm_image_sub_le_of_norm_fderiv_le (fun _ _=> h.differentiable (by simp) _) (fun i hi=> le_trans (g ⟨_,hi,rfl⟩) (le_max_right ..)) (ht W) (ht V) -- order
lemma accord {I: Type*}[Fintype I]:∃ (r:ℕ)(C c:ℝ),1 ≤ r ∧0<C∧0<c∧∀ (k:ℝ),0<k→ k≤1→∀ U:I→UNI E,(∀ i,(U i).val.det=1)→ (∀ i j, Switch (U i).val (U j).val (c*k^r)) → ∃ (V:UNI E), V.val.det=1∧ ∀ i,∃ F:E→ℝ,∑ j,F j=0 ∧ (∀ j, |F j| ≤ Fintype.card E*Real.pi) ∧ ‖(U i).val-twist V (Matrix.diagonal (pw∘F))‖≤ C*k :=by
 obtain ⟨r,C,c,l,h,v,Q⟩:=turned (E:=E) (@univ I _); obtain ⟨b,hb,B⟩:=opt _ (mat_curve E)
 let m:ℝ:=Fintype.card E; have he:0<m:=by unfold m; positivity; -- scope
 refine ⟨r,(C+m*C)+m*b*(C+m*C),c,l,by positivity,v,fun k g p U u q=>?_⟩
 obtain ⟨V,W⟩:=Q k g p U (fun i _ j _=>q i j); obtain ⟨R,T,H⟩:=rig V; refine ⟨R,T,fun i=>?_⟩; obtain ⟨F,h⟩:= W i (mem_univ i)
 let f:UNI E:=⟨twist (star V) (U i).val,by rw [twist_formula]; exact (unitary _).mul_mem ((unitary _).mul_mem (star V|>.property) (U i).property) (by simpa using (star (star V:UNI E):UNI E).property)⟩
 have he:f.val.det=1:=by unfold f; simp only; rw [twist_formula,Matrix.det_mul,Matrix.det_mul,mul_right_comm,← Matrix.det_mul, (star V:UNI E).property.2,Matrix.det_one,one_mul,u]
 obtain ⟨z,hz,Z⟩:=coast f F h; obtain ⟨D,d,E',J⟩:=spark_D (Classical.arbitrary E) z hz f he ((norm_sub_le_norm_sub_add_norm_sub f.val _ _).trans (add_le_add h Z)) b hb (B f)
 refine ⟨D,d,E',?_⟩; rw [H,← twist_norm (star V),map_sub,twist_inv]; exact J.trans_eq (by unfold m; ring)
end YM.CF.Sods
