import YM.CF.BPress.Pf.Plog
import YM.CF.Support.Hit
/-! Take intervals height one for unified Cauchy increments, path parameter common. Lift stage eval by paying stereo 2 if different. Preserve continuities but no charge for change in parameter. `Pull stage ℝ`: supports for log. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock MeasureTheory Spin Spin.Pledge Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
namespace Currency
variable {I D Y : Type}[Fintype I][LinearOrder I][Nonempty I][TopologicalSpace D][DecidableEq Y][Fintype Y]

abbrev PartH (a:ℝ):= Set.Icc a (a+1)
variable (A:ℝ)
def rope (b : Stage Y I D Empty) : Stage Y I (D×PartH A) Empty := ⟨b.F,b.home,fun _=>id,fun S x y=> b.eval S x.1 y.1+(if x.2=y.2 then 0 else 2),fun S x y=>add_nonneg (b.pos ..) (by split<;> norm_num),fun h x y=> add_le_add (b.includeV h ..) le_rfl⟩
variable {b:Stage Y I D Empty}{P:Pledge}
lemma token_t : Trans.Tune (rope 0 b) (fun x=> x.2.val) 1:= by
 refine ⟨fun x=>by simpa only [Real.norm_of_nonneg x.2.property.1,zero_add] using x.2.property.2, one_pos,continuous_subtype_val.comp continuous_snd,fun S _ x y=> ?_⟩; have he:=x.2.property; have ht:=y.2.property; have hm:= b.pos S x.1 y.1; rw [Real.norm_eq_abs,one_mul]; change _≤b.eval S x.1 y.1+_; split; next h=> rw [h]; simpa
 next h=> apply abs_le.mpr; rcases he with ⟨he,hh⟩; rcases ht with ⟨hv,ht⟩; constructor <;> linarith
lemma spine {C:ℝ}(h:Capacity b C): Capacity (rope A b) C:=by obtain ⟨h,v,u⟩:=h; exact ⟨h,v,u⟩
lemma pullT (k:Raw D I)(p:P.Costs b k): P.Costs (rope A b) (fun x=> k x.1):=by refine Costs.pulls (b:=rope A b) p Prod.fst continuous_fst rfl rfl (fun S x y=> le_add_of_nonneg_right ?_); split<;> norm_num
lemma subview (k:ℝ)(h:k∈PartH A){f:D→ℝ→Op I}(p:P.Costs (rope A b) (fun x=> f x.1 x.2.val)): P.Costs b (fun x=> f x k):=by refine Costs.pulls p (fun x:D=>(x,(⟨k,h⟩:PartH A))) (continuous_id.prodMk continuous_const) rfl rfl (fun S x y=>?_); simp [rope]
variable {F: D→ℝ→Op I}(h:P.Costs (rope A b) (fun x=>F x.1 x.2.val))
lemma scont {J:Raw D I} (h: P.Costs b J):Continuous J:=by obtain ⟨F,K,t,d,w⟩:=h; rw [funext w]; exact continuous_finsetSum _ fun i _=> (t i).cont
include h
lemma atop :Continuous fun x:D × PartH A=> F x.1 x.2.val:= scont h
lemma sky (x:D): IntervalIntegrable (F x) MeasureTheory.volume A (A+1) := by
 refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) (continuousOn_iff_continuous_restrict.mpr ?_); exact (atop A h).comp (f:=fun i :PartH A=>(x,i)) (continuous_const.prodMk continuous_id)
lemma testTrace (x:D): (∫ t in A..A+1,F x t).trace=∫ t in A..A+1,(F x t).trace:= ((Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap.intervalIntegral_comp_comm (sky A h x)).symm
lemma plan : P.Costs b (fun x=> ∫ t in A..A+1,F x t):=by
 obtain ⟨N,C,t,K,g⟩:=h; have ht:A≤A+1:=by linarith
 let f(S: Seal Y) (x:D)(v:ℝ):= N S (x,Set.projIcc A (A+1) ht v); let G(S:Seal Y)(x:D): Op I:=∫ v in A..A+1,f S x v; have hc(S):Continuous (Function.uncurry (f S)):= (t S).cont.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)); have hF(S x): Continuous (f S x):=(t S).cont.comp (continuous_const.prodMk continuous_projIcc)
 refine ⟨G,C,fun S=>⟨fun i _=> Empty.elim i,fun i j=>?_⟩,K,fun x=>?_ ⟩; swap
 · dsimp only; rw [show (∫ t in A..A+1,F x t)=∫ t in A..A+1,∑ S,f S x t from intervalIntegral.integral_congr (fun a (ha:a∈Set.uIcc A (A+1))=>?_ ), intervalIntegral.integral_finsetSum (fun i (_:i∈univ)=> (hF i x).intervalIntegrable A (A+1))]
   rw [Set.uIcc_of_le ht] at ha; specialize g (x,Set.projIcc A (A+1) ht a); simp only [Set.coe_projIcc,min_eq_right ha.2,max_eq_right ha.1] at g; exact g -- tune names
 let V:Op I→L[ℂ] ℂ:= (LinearMap.toContinuousLinearMap (⟨⟨fun x:Op I=>x i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩: Op I→ₗ[ℂ] ℂ)); have he(x): G S x i j= ∫ a in A..A+1, V (f S x a):=(V.intervalIntegral_comp_comm ((hF S x).intervalIntegrable _ _)).symm
 let X:= (t S).expo i j; refine ⟨X.positive,X.triggered,fun x=>?_,fun x y=>?_,(intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=MeasureTheory.volume) (hc S) A (A+1)).matrix_elem ..⟩
 · rw [he]; exact (intervalIntegral.norm_integral_le_of_norm_le_const (fun i _=> X.bounded (x,Set.projIcc A _ ht i))).trans_eq (by simp)
 rw [he,he,←intervalIntegral.integral_sub (f:=fun i=> V (f S x i)) (g:=fun i=>V (f S y i)) ((V.continuous.comp (hF S x)).intervalIntegrable _ _) ((V.continuous.comp (hF S y)).intervalIntegrable _ _)]
 apply (intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun i=>V (f S x i)-V (f S y i)) (C:=C S i j*b.eval S x y) ?_).trans_eq (by simp)
 intro a _; exact (X.variation (x,Set.projIcc A _ ht a) (y,Set.projIcc A _ ht a)).trans_eq (congrArg (C S i j* ·) (by simp [rope]))
end Currency
end YM.CF.BPress.Pf
