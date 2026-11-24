import YM.CF.Vp929.Contour.Signs
/- Coherent price tests. Includes subtraction among items fitting the budget. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Complex Function Set Filter Topology
variable {X Y Z E : Type*}
abbrev Book (X:Type*) := X → ℝ → Prop
abbrev Looks (X:Type*) := Set ℂ → (ℂ→ Pair X) → Prop
abbrev Enough (c:Book X)(x:X):= ∃ v,c x v
variable {c:Book X}{d:Book Y}{h:Looks X}{g:Looks Y}
abbrev Valid (c:Book X) (h:Looks X)(S:Set ℂ)(f:ℂ→Pair X):= IsOpen S ∧ h S f ∧ ∃ Q:ℝ,∀ z∈S,Both (fun x=>c x Q) (f z)
protected lemma Valid.minted {V:Set ℂ}{F:ℂ→Pair X}(e:Valid c h V F) {x:ℂ}(hx:x∈ V): Enough c (F x).1 ∧ Enough c (F x).2:=by obtain ⟨_,_,v,H⟩:= e; exact ⟨⟨_,(H _ hx).1⟩,⟨_,(H _ hx).2⟩⟩
variable [Sub X] [Sub Y]
structure Accountable (c:Book X)(h:Looks X)(F:X→ℝ):Prop where
 receipt : ∀ x y, Enough c x → Enough c y → F (x-y) = F x-F y
 liable : ∀ S f, Valid c h S f → DifferentiableOn ℂ (fun z=> probing F (f z)) S

open scoped ContDiff

def accounts (c: Book X)(h:Looks X) : Submodule ℝ (X→ℝ) where
 carrier := {k| _root_.YM.CF.Py.Rate.Accountable c h k}
 zero_mem' := ⟨by simp,fun _ _ _=> differentiableOn_const (liftV 0 0)⟩
 add_mem' := @fun a b (u: YM.CF.Py.Rate.Accountable c h a) (v: YM.CF.Py.Rate.Accountable c h b) => ⟨fun x y t p=> by simp only [Pi.add_apply,u.receipt _ _ t p,v.receipt _ _ t p]; ring,fun x f t=> ((u.liable _ _ t).add (v.liable _ _ t)).congr fun z _=> by simp only [probing,liftV,Pi.add_apply,mul_add,ofReal_add]; ring⟩
 smul_mem' := @fun a b (u: YM.CF.Py.Rate.Accountable c h b)=> ⟨fun x y t p=> by simp only [Pi.smul_apply,smul_eq_mul,u.receipt _ _ t p,mul_sub],fun S f t=> ((u.liable S f t).const_mul (a:ℂ)).congr fun z _=> by simp only [probing,liftV,Pi.smul_apply,smul_eq_mul,ofReal_mul]; ring⟩
abbrev Portfolio (c:Book X)(h:Looks X):= Display (accounts c h) c
namespace Portfolio
lemma permit (v:Y→ℝ)(t:v∈accounts d g)(F:X→Y)(p:∀ x y,F (x-y)=F x-F y)(h₁:∀ x, Enough c x→Enough d (F x))(h₂:∀ S f,Valid c h S f→ Valid d g S (fun z=> (F (f z).1,F (f z).2))):v ∘ F∈accounts c h := by
 change Accountable d g v at t; rcases t with ⟨A,t⟩; refine ⟨fun x y t k=> by simp only [Function.comp_apply,p,A _ _ (h₁ _ t) (h₁ _ k)],fun S f v=>t _ _ (h₂ _ _ v)⟩
lemma engage (F:X→Y)(p:∀ x y,F (x-y)=F x-F y)(h₁:∀ x,Enough c x→ Enough d (F x))(h₂:∀ S f,Valid c h S f→ Valid d g S (fun z=>(F (f z).1,F (f z).2)))(p₀:Portfolio d g): Display (accounts c h) (fun x=> d (F x)):= Display.pull F (fun x t=> permit x t F p h₁ h₂) p₀
end Portfolio

lemma probing_norm (F:X→ℝ)(x:Pair X)(u:ℝ)(p:Both (fun k=> |F k|≤ u) x): ‖probing F x‖ ≤ 2*u:=by
 apply (Complex.norm_le_abs_re_add_abs_im _).trans; simp only [prob_re,prob_im,two_mul]; exact add_le_add p.1 p.2
lemma probing_view (F:X→ℝ)(x:Pair X)(u:ℝ)(p: ‖probing F x‖ ≤ u) : Both (fun k=> |F k|≤ u) x:=by
 have he:= (Complex.abs_re_le_norm _).trans p; have hh:= (Complex.abs_im_le_norm _).trans p; simp only [prob_re,prob_im] at he hh; exact ⟨he,hh⟩
lemma Accountable.norm_le (p:Portfolio c h){r:X→ℝ}(u:∀ x a,c x a→ |r x| ≤ a){X₁:Pair X}{Q:ℝ}(v:Both (fun x=>c x Q) X₁): ‖probing r X₁‖ ≤ 2*Q:= probing_norm _ _ _ ⟨u _ _ v.1,u _ _ v.2⟩
lemma Portfolio.evaluate (p:Portfolio c h){f:Pair X}(u:Both (Enough c) f)(v:ℝ)(w:∀ F∈ accounts c h, (∀ x a,c x a→ |F x| ≤ a)→ ‖probing F f‖ ≤ v): Both (fun k=> c k v) f:=by
 obtain ⟨L,s,p,e⟩:=p.exists_T; have θ (F)(H:F∈L):= probing_view _ _ _ (w F (s H) (fun x a u=>(e x ⟨_, u⟩ a).1 u F H)); exact ⟨(e _ u.1 v).2 fun F H=> (θ _ H).1,(e _ u.2 v).2 fun F H=> (θ _ H).2⟩
end YM.CF.Py.Rate
