import YM.CF.BProof.Wick.Taste

/-! Price of complete up/down integration. Dependence includes path & its derivative.
No variation charged in path parameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory Stint
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I D J Y:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D J}{s t:Tag b}
lemma est {g:D×Time→Op I}{p:Pay} (h:Earn p (straw s) (straw t) g)(x:Time): Earn p s t (fun i=>g (i,x)):=by apply h.restrict _ (continuous_id.prodMk continuous_const) rfl rfl ?_ id (fun _ _=>rfl) rfl rfl; intro S a b; simp only [Ella,ite_true,add_zero,id_eq,le_refl]
variable (A T P Q: Raw D I)(V Z V' Z': D→Line I)
def divY (g: D→Line I)(x:D×Time):Op I:= g x.1 x.2.val
def partI (x:D)(u:ℝ): Op I:= salary (rug (A x) (T x) u) (T x) (V x 0)
def partJ (x:D)(u:ℝ): Op I:= (bonus (crownP (A x) (T x)) (V' x u) (V x u))ᵀ
def partK (x:D)(u:ℝ): Op I:=let a:=crownP (A x) (T x); salary (floorH a (P x) (Q x) u) (shutter a (P x) (Q x) u) (V x 1)
def partM (x:D)(u:ℝ): Op I:= (bonus (floorH (crownP (A x) (T x)) (P x) (Q x) 0) (Z' x u) (Z x u))ᵀ
def rollF (x:D):Op I:= (avg (divY (partI A T V)) x + avg (divY (partJ A T V V')) x) - avg (divY (partK A T P Q V)) x + avg (divY (partM A T P Q Z Z')) x
lemma bonusPaid (B:Op I)(x:D)(V V':Line I)(f:D×Time→Op I)(H:Continuous f)(h:∀ u:Time, f (x,u)=(bonus B (V' u.val) (V u.val))ᵀ): hose B V V' 0 1=(avg f x).trace ∧ ContinuousOn (fun t=>(bonus B (V' t) (V t)).trace) walking :=by
 let g:=fun t=>(bonus B (V' t) (V t))ᵀ; constructor; · unfold hose; rw [show (fun t=>(bonus B (V' t) (V t)).trace)=(fun t=>(g t).trace) from funext fun i=> (Matrix.trace_transpose ..).symm]; exact avgTrace _ H g x (fun i=>(h i).symm)
 apply interior_c (fun i=>(f i).trace) H.matrix_trace _ x; intro i; rw [h,Matrix.trace_transpose]
lemma can (x:D)(H:Continuous (divY (partI A T V)))(g:Continuous (divY (partJ A T V V')))(f:Continuous (divY (partK A T P Q V)))(e:Continuous (divY (partM A T P Q Z Z'))): SumK (A x) (T x) (V x) (Z x) (V' x) (Z' x) (P x) (Q x) ∧ rolled (A x) (T x) (V x) (Z x) (V' x) (Z' x) (P x) (Q x)=(rollF A T P Q V Z V' Z' x).trace:=by
 let a:=A x; let t:=T x; obtain ⟨hJ,pJ⟩:= bonusPaid (crownP a t) x (V x) (V' x) _ g (fun _=>rfl); obtain ⟨hM,pM⟩:= bonusPaid (floorH (crownP a t) (P x) (Q x) 0) x (Z x) (Z' x) _ e (fun _=>rfl)
 refine ⟨⟨?_,pJ,?_,pM⟩,?_⟩
 · apply interior_c (fun i=>(divY (partI A T V) i).trace) H.matrix_trace _ x (fun _=>rfl)
 · apply interior_c (fun i=>(divY (partK A T P Q V) i).trace) f.matrix_trace _ x (fun _=>rfl)
 unfold rolled rollF; rw [hJ,hM, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_add]; have h1:linestretch a t (V x 0)=(avg (divY (partI A T V)) x).trace:=avgTrace _ H (partI A T V x) x (fun _=>rfl); have h2:spentDown (crownP a t) (V x 1) (P x) (Q x)=(avg (divY (partK A T P Q V)) x).trace:=avgTrace _ f (partK A T P Q V x) x (fun _=>rfl); rw [h1,h2]
end YM.CF.BProof.Wick
