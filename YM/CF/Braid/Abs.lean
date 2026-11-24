import YM.CF.Braid.Spend
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
variable {U Y:U2}
private lemma paid_l{p:Momentum}{v:TypeFace 2→ℂ}{k:Axis}(i:TypeFace 2)(h:k∈i.val)(hp:q p=Pi.single k (q p k))(hm:q p k ≠ 0)(ht: ((symbol 1 p).transpose *ᵥ v) (Exterior.remove k i h)=0): v i=0:=by
 rw [symbol,wedge,hp] at ht; simp only [Pi.single_apply,ite_smul,zero_smul,Finset.sum_ite_eq',mem_univ,↓reduceIte] at ht
 simp_rw [Matrix.transpose_smul,Matrix.smul_mulVec, Pi.smul_apply] at ht; rw [eliminate_transpose,dif_pos (notMem_cut k i h),addAxis_remove] at ht
 simpa [smul_eq_mul,hm,parity] using ht
private lemma shared(p: Corn (Keys 1))(F:U2)(h:Fall F 0)(i:CurRun 2)(k:Axis)(hi:k∈ (i 0).val)(hj:k∈ (Fin.tail i 0).val)(hm:∀ j:Fin 2,q (cardR 0 (axes p) j) =Pi.single k (q (cardR 0 (axes p) j) k) ∧ q (cardR 0 (axes p) j) k≠0): F i (axes p)=0:=by
 let a:=cardR 0 (axes p); let v:= Exterior.remove k (i 0) hi; let w:= Exterior.remove k (Fin.tail i 0) hj
 have he:= congr_fun (h p) (Fin.cons v (Fin.cons w default)); rw [fromCurl_cons,Fin.cons_zero,Fin.tail_cons] at he
 let X:=fun x=> fromCurl (Fin.tail a) (fun y=>F (Fin.cons x y) (axes p)) (Fin.cons w default)
 have hx:X (i 0)=0:= paid_l (i 0) hi (hm 0).1 (hm 0).2 he
 unfold X at hx; rw [fromCurl_cons, Fin.cons_zero, Fin.tail_cons] at hx; simp only [fromCurl] at hx; simp at hx -- tune
 let V:=fun j:TypeFace 2=> F (Fin.cons (i 0) (Fin.cons j default)) (axes p)
 have hw: V (Fin.tail i 0)=0:=paid_l _ hj (hm (Fin.succ (0:Fin 1))).1 (hm (Fin.succ (0:Fin 1))).2 hx
 refine Eq.trans ?_ hw
 unfold V; congr 2
 rw [← show Fin.tail (Fin.tail i)=default from Subsingleton.elim ..,Fin.cons_self_tail,Fin.cons_self_tail]
lemma void_0 (hp:Paid M A U)(h:Fall U 0)(i:CurRun 2)(k:Axis)(hi:k∈(i 0).val)(hj:k∈(i 1).val): U i 0=0:=by
 let s:= ((0:Fin 1),k); let p(τ:ℝ):= shadow (0:Corn (Keys 1)) s τ; let V(x:Corn (Keys 1)):= (U i ∘ axes) x; have hev: U i 0=V 0:=by unfold V; rw [Function.comp_apply,show axes (0:Corn (Keys 1))=0 from funext fun b=>by simp [axes]]
 rw [hev]; refine tendsto_nhds_unique_of_eventuallyEq (((hp i).analytic.analytic_real 0).continuousAt.tendsto.comp (shadows 0 s)) tendsto_const_nhds ?_
 filter_upwards [shadow_fee (0:Corn (Keys 1)) s, divisor_nonzero (r:=0) (-1) (by norm_num)] with v hv hV; apply shared (p v) U h i k hi hj
 intro j; refine Fin.cases ?_ ?_ j
 · have hS: cardR 0 (axes (p v)) 0=Pi.single k (-(v:ℂ)):=by ext1 a; rw [cardR,Fin.cons_zero]; simp [twist,missing, projected,strand,axes,s, shadow,p, Pi.single_apply]; split <;> simp [*]
   rw [hS]; constructor
   · ext1 a; by_cases hh:a=k <;> simp [hh,q]
   simpa [q] using hV
 intro j; rw [show j=0 from Subsingleton.elim ..]
 have hS:cardR 0 (axes (p v)) (0:Fin 1).succ=Pi.single k (v:ℂ):=by ext1 a; simp only [cardR,Fin.cons_succ]; by_cases hh:a=k <;> simp [hh, axes,p,shadow,projected,strand,s]
 rw [hS]; constructor; · ext1 a; by_cases hh:a=k <;> simp [hh,q]
 simpa [q,divZ, axes,shadow] using hv -- tune
end YM.CF.Braid
