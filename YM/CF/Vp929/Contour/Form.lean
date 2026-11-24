import YM.CF.Vp929.Budget.Correction
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Calculus.Deriv.Star
/-! Formal complex. All real-linear point tests of values. -/
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate
open Complex Function Topology Module Set
open scoped ComplexConjugate
variable {E X B: Type*}
abbrev liftV (u v:ℝ) := (u:ℂ)+I*v
def probing (v:X→ℝ)(x:Pair X):ℂ:= liftV (v x.1) (v x.2)
@[simp] lemma prob_re (v:X→ℝ)(x:Pair X) : (probing v x).re=v x.1:=by simp [probing,liftV]
@[simp] lemma prob_im (v:X→ℝ)(x:Pair X) : (probing v x).im=v x.2:=by simp [probing,liftV]
lemma beam_diff {f:ℂ→ℂ}{S:Set ℂ}(hs:IsOpen S) (hp:DifferentiableOn ℂ f S): DifferentiableOn ℂ (fun z=> conj (f (conj z))) (conj ⁻¹' S) :=
 fun z x=> (differentiableAt_conj_conj_iff.mpr (hp.differentiableAt (hs.mem_nhds x))).differentiableWithinAt
section Re
variable [NormedAddCommGroup X] [NormedSpace ℝ X]{S:Set ℂ}{f:ℂ→Pair X}
def Form (S:Set ℂ)(f:ℂ→Pair X) : Prop:= ∀ p:X→L[ℝ]ℝ,DifferentiableOn ℂ (fun z=> probing p (f z)) S
lemma Form.congr {g:ℂ→Pair X}(h:Form S f)(u:EqOn g f S): Form S g:= fun p=> (h p).congr fun _ k=> congrArg (probing p) (u k)
lemma Form.mono {A:Set ℂ}(h:Form S f)(e:A⊆S):Form A f:=fun p=>(h p).mono e
lemma Form.comp {L:Set ℂ}{b:ℂ→ℂ}(h:Form S f)(hb:DifferentiableOn ℂ b L)(p:MapsTo b L S): Form L (f ∘ b):= fun q=> (h q).comp hb p
lemma form_const (S:Set ℂ)(X:Pair X) : Form S (fun _=>X):=fun p=> differentiableOn_const _
lemma Form.add {g:ℂ→ Pair X}(p:Form S f)(h:Form S g): Form S (fun z=>(f z).1 + (g z).1 |> fun x=>(x,(f z).2 +(g z).2)):=fun v=> ((p v).add (h v)).congr fun z _=> by simp only [Pi.add_apply,probing,liftV,map_add,mul_add,ofReal_add]; ring
lemma Form.sub {g:ℂ→ Pair X}(p:Form S f)(h:Form S g): Form S (fun z=>((f z).1 - (g z).1,(f z).2 -(g z).2)):=fun v=> ((p v).sub (h v)).congr fun z _=> by simp only [Pi.sub_apply,probing,liftV,map_sub,mul_sub,ofReal_sub]; ring
lemma Form.probe [NormedAddCommGroup E] [NormedSpace ℝ E](p:Form S f)(v:X→L[ℝ]E):Form S (fun z=> (v (f z).1,v (f z).2)):=fun w=> p (w.comp v)
lemma Form.scale {g:ℂ→ℂ}(h:Form S f)(p:DifferentiableOn ℂ g S): Form S (fun z=> ((g z).re • (f z).1 - (g z).im • (f z).2,(g z).re • (f z).2+(g z).im • (f z).1)):=fun x=> (p.mul (h x)).congr fun z _=> by apply Complex.ext<;>simp only [Pi.mul_apply,probing,liftV,mul_re,mul_im,map_smul,map_add,map_sub,add_re,add_im,I_re,I_im,ofReal_re,ofReal_im,smul_eq_mul]<;>ring
lemma Form.join [NormedAddCommGroup E] [NormedSpace ℝ E]{g:ℂ→ Pair E}(p:Form S f)(h:Form S g): Form S (fun z=>(((f z).1,(g z).1),((f z).2,(g z).2))):= (p.probe (ContinuousLinearMap.inl ℝ X E) |>.add (h.probe (ContinuousLinearMap.inr ℝ X E))).congr fun x k=>by simp
lemma form_ballot {i:Type*}(t:Finset i)(S:Set ℂ)(f:i→ℂ→Pair X)(p:∀ i∈t,Form S (f i)):Form S (fun z=> (∑ i∈t,(f i z).1,∑ i∈t,(f i z).2)):=by
 classical
 induction t using Finset.induction_on with
 | empty=> simpa using form_const S (X:=X) (0,0)
 | @insert i t hi ih=> simp_rw [Finset.sum_insert hi]; exact (p _ (Finset.mem_insert_self ..)).add (ih fun _ h=> p _ (Finset.mem_insert_of_mem h))
lemma form_real {f:ℂ→ℂ}(h:DifferentiableOn ℂ f S):Form S (fun z=> ((f z).re,(f z).im)):=fun x=> (h.const_mul (x 1:ℂ)).congr fun z k=>by
 have hh (t:ℝ):x t=t*x 1:= (congrArg x (smul_eq_mul t 1|>.trans (mul_one t)).symm).trans (x.map_smul t 1)
 apply Complex.ext <;> simp only [prob_re,prob_im,mul_re,mul_im,ofReal_re,ofReal_im] <;> rw [hh] <;> ring
end Re
section
variable [NormedAddCommGroup X][NormedSpace ℂ X] [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]{S:Set ℂ}{f:ℂ→Pair X}
lemma Holo.form (h:Holo S f)(hs:IsOpen S): Form S f:=by
 intro p; let P:= StrongDual.extendRCLike p (𝕜:=ℂ)
 have hh(v): (P v).re=p v:= StrongDual.re_extendRCLike_apply (𝕜:=ℂ) p v
 let F(z):= P (Pair.plus (f z)); let G(z):= P (Pair.minus (f (conj z)))
 have he:DifferentiableOn ℂ (fun z=> conj (G (conj z))) S:=by apply (beam_diff (hs.preimage continuous_conj) (P.differentiable.comp_differentiableOn h.2)).mono; intro x h; simpa
 apply ((P.differentiable.comp_differentiableOn h.1).add he|>.const_mul ((2:ℂ)⁻¹)).congr; intro z k; apply Complex.ext<;> simp [G,Pair.plus,Pair.minus,mul_re,mul_im,map_smul,hh,smul_eq_mul]<;>ring
lemma Holo.probe [NormedAddCommGroup E][NormedSpace ℂ E](h:Holo S f)(p:X→L[ℂ]E) : Holo S (fun z=>(p (f z).1,p (f z).2)) := by
 constructor; · apply (p.differentiable.comp_differentiableOn h.1).congr; intro x h; simp only [Pair.plus,comp_apply,map_add,map_smul]
 apply (p.differentiable.comp_differentiableOn h.2).congr; intro x h; simp only [Pair.minus,comp_apply,map_sub,map_smul]
lemma holog (hs:IsOpen S){g:ℂ→ Pair ℂ}(u:DifferentiableOn ℂ (fun z=> probing re (g z)) S)(v:DifferentiableOn ℂ (fun z=>probing im (g z)) S): Holo S g:=by
 constructor
 · apply (u.add (v.const_mul I)).congr; intro x _; apply Complex.ext<;>simp [Pair.plus,mul_re,mul_im,smul_eq_mul,sub_eq_add_neg]<;> ring
 apply (beam_diff hs (u.sub (v.const_mul I))).congr; intro x h; apply Complex.ext<;>simp [sub_re,sub_im,Pair.minus,mul_re,mul_im,smul_eq_mul]<;>ring
lemma tri [FiniteDimensional ℂ X]{f:ℂ→X}(p:∀ v:X→L[ℂ]ℂ,DifferentiableOn ℂ (v ∘ f) S):DifferentiableOn ℂ f S:=by
 classical
 let e:= (Module.finBasis ℂ X).equivFun.toContinuousLinearEquiv
 rw [←e.comp_differentiableOn_iff, differentiableOn_pi]; intro i; exact p ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
lemma Form.holo [FiniteDimensional ℂ X] (h:Form S f)(hs:IsOpen S): Holo S f:=by
 have h(p:X→L[ℂ]ℂ) : Holo S (fun z:ℂ=>(p (f z).1,p (f z).2)):= holog hs (h (reCLM.comp (p.restrictScalars ℝ))) (h (imCLM.comp (p.restrictScalars ℝ)))
 constructor; · refine tri (fun p=> (h p).1.congr fun x _=> ?_); simp only [Pair.plus,comp_apply,map_add,map_smul]
 refine tri (fun p=> (h p).2.congr fun x _=> ?_); simp only [Pair.minus,comp_apply,map_sub,map_smul]
lemma Form.piForm [Fintype B](S:Set ℂ)(F:ℂ→Pair (B→X))(h:∀ i:B,Form S (fun z=> ((F z).1 i, (F z).2 i))):Form S F:=by

 classical
 let p(i:B):= (h i).probe (ContinuousLinearMap.single ℝ (φ:=(fun _=>X)) i)
 refine (form_ballot Finset.univ S _ (fun i _=> p i)).congr fun z _=> ?_; simp
 apply Prod.ext <;> funext x<;>simp [Finset.sum_apply, Pi.single_apply]
end
/- J-form extension for ordinary complex formula over inputs. Given two assignments, write CAT explicitly to return pair. -/
namespace Pair
variable [AddCommGroup X] [Module ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
def cat (x y : X) : Pair X := ((2:ℂ)⁻¹ • (x+y), (2*I)⁻¹ • (x-y))
omit [Module ℝ X] [IsScalarTower ℝ ℂ X]

@[simp] lemma plus_cat (x y:X) : Pair.plus (Pair.cat x y)=x:=by
 have H:I*(2*I)⁻¹=(2:ℂ)⁻¹:=by simp [←mul_assoc]
 simp only [Pair.plus,cat,smul_smul,H,←smul_add]; rw [show x+y+(x-y)= (2:ℂ) • x by rw [two_smul]; abel,inv_smul_smul₀ (by norm_num)]
@[simp] lemma minus_cat(x y:X) : Pair.minus (Pair.cat x y)=y:=by
 have H:I*(2*I)⁻¹=(2:ℂ)⁻¹:=by simp [←mul_assoc]
 simp only [Pair.minus,cat,smul_smul,H,←smul_sub]; rw [show x+y-(x-y)= (2:ℂ) • y by rw [two_smul]; abel,inv_smul_smul₀ (by norm_num)]
lemma ext_pm(x y:Pair X)(p:Pair.plus x=Pair.plus y)(q:Pair.minus x=Pair.minus y):x=y:=by
 refine Prod.ext ?_ ?_
 · apply smul_right_injective _ (by norm_num:(2:ℂ)≠0)
   simp only [two_smul]; rw [show x.1+x.1=Pair.plus x+Pair.minus x from by unfold Pair.plus Pair.minus; abel,show y.1+y.1=Pair.plus y+Pair.minus y from by unfold Pair.plus Pair.minus; abel,p,q]
 apply smul_right_injective _ (by exact I_ne_zero)
 apply smul_right_injective _ (by norm_num:(2:ℂ)≠0)
 simp only [two_smul]; rw [show I•x.2+I•x.2=Pair.plus x-Pair.minus x from by unfold Pair.plus Pair.minus; abel,show I•y.2+I•y.2=Pair.plus y-Pair.minus y from by unfold Pair.plus Pair.minus; abel,p,q]
end Pair
section
variable [NormedAddCommGroup X][NormedSpace ℂ X]{S:Set ℂ}{f g:ℂ→X}
lemma holo_cat (u:DifferentiableOn ℂ f S)(v:DifferentiableOn ℂ (fun z=>g (conj z)) (conj ⁻¹' S)):Holo S (fun z=> Pair.cat (f z) (g z)):=⟨u.congr fun _ _=> Pair.plus_cat .., v.congr fun _ _=>Pair.minus_cat ..⟩
end
end YM.CF.Py.Rate
