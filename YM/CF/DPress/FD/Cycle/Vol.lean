import YM.CF.DPress.FD.Cycle.Wind
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
variable {I:Type*} (P Q:I→Finset C)
def evalP (P:I→Finset C) : List I→(Word→ℝ)→ℝ
| [],f=>f []
| x::k,f=>∑ i∈P x, evalP P k (fun w=> f (i::w))
abbrev N(x:I):Finset C:=Finset.univ
lemma lengthE (x:List I)(f g:Word→ℝ)(h:∀ y:Word,y.length=x.length → f y=g y): evalP P x f=evalP P x g:=by
 induction x generalizing f g with
 |nil=> exact h [] rfl
 |cons i x ih=> rw [evalP,evalP]; exact Finset.sum_congr rfl fun i p=> ih _ _ fun y t=> h (i::y) (by simp [t])
lemma eval_append (f:Word→ℝ)(x y:List I): evalP P (x++y) f=evalP P x (fun w=> evalP P y (fun z=>f (w++z))):=by
 induction x generalizing f with| nil=> rfl| cons i x h=> rw [cons_append,evalP,evalP]; exact Finset.sum_congr rfl fun i _=> h _
lemma innerAdd {J:Type*}(S:Finset J)(x:List I)(f:J→Word→ℝ) : evalP P x (fun x=> ∑ j∈S, f j x)= ∑ j∈S,evalP P x (f j):=by
 induction x generalizing f with|nil=>rfl|cons i x h=>simp only [evalP]; rw [Finset.sum_comm (f:=fun j k=>evalP P x (fun v=> f j (k::v)))]; exact Finset.sum_congr rfl fun k _=> h (fun j v=> f j (k::v)) -- syntax placeholder needs ∀.
lemma inner_mul(x:List I)(c:ℝ)(f:Word→ℝ):evalP P x (fun w=>c*f w)= c*evalP P x f:=by induction x generalizing f with|nil=>rfl|cons i x h=>rw [evalP,evalP,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> h (fun v=> f (i::v))
lemma commute(x y:List I)(f:Word→Word→ℝ):evalP P x (fun w=> evalP Q y (f w))=evalP Q y (fun t=> evalP P x (fun w=> f w t)):=by
 induction x generalizing f with
 |nil=>rfl
 |cons i x h=> 
    simp only [evalP]; rw [innerAdd Q (P i) y (fun a t=>evalP P x (fun u=> f (a::u) t))]; exact Finset.sum_congr rfl fun i _=> h (fun u t=> f (i::u) t)
lemma splitU(x y:List I)(p:I)(h:P p=Finset.univ):evalP P (x++p::y) ν= evalP P x ν*evalP P y ν:=by
 rw [eval_append]; let a:=evalP P y ν; suffices b:∀ i:Word, evalP P (p::y) (fun z=> ν (i++z))=a*ν i by rw [show (fun w=> evalP P (p::y) _)= _ from funext b,inner_mul,mul_comm]; -- meta
 intro w; rw [evalP,h,← innerAdd P Finset.univ y (fun (j:C) z=>ν (w++j::z)),show (fun z=> ∑ i:C,ν (w++i::z))=_ from funext (splitH w), inner_mul,mul_comm]
lemma rotH(x y:List I): evalP P (x++y) θ= evalP P (y++x) θ:=by rw [eval_append,eval_append,commute P P x y (fun w z=> θ (w++z))]; refine lengthE P y _ _ ?_; intro i p; exact lengthE P _ _ _ (fun j _=> θsym j i)
lemma spinH(x:List I)(q:x≠[])(p:I)(h:P p=Finset.univ): evalP P (x++[p]) θ=evalP P x ν:=by
 rw [eval_append]; refine lengthE P x _ ν ?_; intro i f; have he: i≠ []:= length_pos_iff.mp (f.trans_gt (length_pos_iff.mpr q)); simpa only [evalP,h] using (monoH i he) -- rhs λ? tune f.trans
lemma eval_e (x:List I)(q:∀ i∈x,P i=Q i)(f:Word→ℝ): evalP P x f=evalP Q x f:=by
 induction x generalizing f; · rfl
 rename_i i x ih; rw [evalP,evalP,q i (mem_cons_self ..)]; refine Finset.sum_congr rfl fun b t=>ih (fun j v=>q j (mem_cons_of_mem i v)) _
lemma path_zero (x:List I) : evalP N x ν=1:=by
 induction x with
 |nil=> exact νn
 |cons i x ih=> rw [show i::x=[]++i::x from rfl, splitU N [] x i rfl, ih, evalP, νn,mul_one]
lemma cycle_one (x:List I)(p:1<x.length) :evalP N x θ=1:=by
 induction x using List.reverseRecOn with
 |nil=> simp at p
 |append_singleton u i h=> rw [spinH N u (by intro t; simp_all) i rfl]; exact path_zero u
end YM.CF.DPress.FD.Cycle
