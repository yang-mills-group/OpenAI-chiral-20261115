import YM.CF.Mew.Terms
import YM.SU5.Exchange.Seed.Flow

/-!
 Degrees of a Key-gas recurrence, don't price beyond the actual rake.
 Keep each order even when no norm on Copy (all Pane maps).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.Mew
open Function Metric Filter MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I]{i j : ℕ}

-- linear combinations of degree-j Key monomials. avoids requiring smoothness of a
-- copy-to-copy motion until evaluation on x. For R+Forces a single orientation root.
abbrev pTerm(j:ℕ):= Fin j→I -- ensure implicit I from result? not syntactic const? Lean includes I
abbrev lTerm {j:ℕ}(v:Fin j→I)(x:Key I):ℂ:=∏ i,x (v i)
section
variable [AddCommGroup E][Module ℂ E]{f g: Key I→E}
def Solvent (j:ℕ)(f:Key I→E):Prop:= ∃ a:(Fin j→I)→E,∀ x,f x=∑ i:Fin j→I,lTerm i x • a i
lemma Solvent.zero (j:ℕ) : Solvent j (fun _:Key I=>(0:E)):=⟨0,fun x=>by simp⟩
lemma Solvent.term (v:Fin j→I)(Y:E): Solvent j (fun x:Key I=> lTerm v x • Y):=by
 refine ⟨Pi.single v Y,fun x=>?_⟩; rw [sum_eq_single v]; simp; intro i _ p; rw [Pi.single_eq_of_ne p,smul_zero]; simp
lemma Solvent.still(Y:E) : Solvent 0 (fun _:Key I=>Y):=by
 let v:Fin 0 → I:= Fin.elim0; have h(x:Key I): Y=lTerm v x • Y:=by simp [lTerm]
 rw [funext h]; exact Solvent.term v Y
lemma Solvent.add (p:Solvent i f)(q:Solvent i g): Solvent i (fun x=> f x+g x):=by
 obtain ⟨a,p⟩:=p; obtain ⟨b,q⟩:=q; refine ⟨a+b,fun x=>?_⟩; simp only [p,q,Pi.add_apply,smul_add,sum_add_distrib]
lemma Solvent.sum {J:Type*}(s:Finset J)(F:J→Key I→E)(w:∀ a∈s,Solvent j (F a)) : Solvent j (fun x=>∑ i∈s,F i x):=by
 induction s using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; exact Solvent.zero _
 | insert i s u ih=> simp_rw [sum_insert u]; exact (w i (mem_insert_self ..)).add (ih (fun i z=>w i (mem_insert_of_mem z)))
lemma Solvent.map [AddCommGroup F][Module ℂ F](v:E→ₗ[ℂ]F)(p:Solvent i f): Solvent i (fun x=>v (f x)):=by
 obtain ⟨a,p⟩:=p; refine ⟨v ∘ a,fun x=>?_⟩; simp [p,map_sum,Function.comp_def]
lemma Solvent.smul (x:ℂ)(p:Solvent i f): Solvent i (fun z=> x • f z):= Solvent.map (x • LinearMap.id) p
end
lemma Solvent.bill (i:I): Solvent 1 (fun x:Key I=>x i):=by
 let v:Fin 1 → I:=fun _=>i; have h: (fun x:Key I=> lTerm v x • (1:ℂ))=fun x=>x i:=by ext x:1; simp [lTerm,v]
 rw [←h]; exact Solvent.term _ _
lemma lTerm_stacks (s:Fin i→I)(t:Fin j→I)(x:Key I): lTerm (Fin.append s t) x=lTerm s x*lTerm t x:=by rw [lTerm,Fin.prod_univ_add]; congr 1 <;> simp only [lTerm,Fin.append_left,Fin.append_right]
lemma Solvent.pair [AddCommGroup E][Module ℂ E] [AddCommGroup F][Module ℂ F] [AddCommGroup N] [Module ℂ N] (M:E→ₗ[ℂ]F→ₗ[ℂ]N) {f:Key I→E}{g:Key I→F}(p:Solvent i f)(q:Solvent j g) : Solvent (i+j) (fun x=> M (f x) (g x)):=by
 obtain ⟨a,p⟩:=p; obtain ⟨b,q⟩:=q; simp only [p,q,map_sum,map_smul, LinearMap.smul_apply, LinearMap.sum_apply,Finset.smul_sum];
 -- order of sums
 apply Solvent.sum; intro V _; apply Solvent.sum; intro U _
 have hh(x:Key I): lTerm V x • lTerm U x • M (a U) (b V)=lTerm (Fin.append U V) x • M (a U) (b V):=by rw [smul_smul,lTerm_stacks,mul_comm]
 simp_rw [hh]; exact Solvent.term _ _
lemma Solvent.times [Ring E][Algebra ℂ E] {f g:Key I→E}(p:Solvent i f)(q:Solvent j g) : Solvent (i+j) (fun x=> f x*g x):= Solvent.pair (LinearMap.mul ℂ E) p q -- Semiring remove
lemma Solvent.prod {J:Type*}[CommRing E][Algebra ℂ E](S:Finset J)(F:J→Key I→E)(v:J→ℕ) (p:∀ i∈S,Solvent (v i) (F i)):Solvent (∑ i∈S,v i) (fun z=>∏ i∈S, F i z):=by
 classical
 induction S using Finset.induction_on with
 |empty=> simp_rw [sum_empty,prod_empty]; exact Solvent.still _
 |insert i S u ih=> simp_rw [sum_insert u,prod_insert u]; exact (p i (mem_insert_self ..)).times (ih (fun i t=> p i (mem_insert_of_mem t)))
section
variable [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E] {f:Key I→E}
lemma Solvent.dif (w:Solvent i f) : Differentiable ℂ f:=by
 obtain ⟨a,p⟩:=w; rw [funext p]; apply Differentiable.fun_sum; intro i _
 refine Differentiable.smul (show Differentiable ℂ (lTerm i) from ?_) (differentiable_const _)
 have h {J:Type}(f:J→I)(S:Finset J):Differentiable ℂ (fun z:Key I=>∏ j∈S,z (f j)):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp
    | insert x s u ih=> simp_rw [prod_insert u]; exact (differentiable_apply (f x)).mul ih
 exact h i _
lemma Solvent.riv (w:Solvent i f) : River f:=by
 let p:= w.dif; constructor; exact p.continuous.continuousOn; intro z u i x h; let G(y:ℂ):= update z i y
 have he:Differentiable ℂ G:= differentiable_pi.mpr (fun a=> by by_cases v:a=i <;> simp [G,v,differentiable_fun_id,differentiable_const])
 exact p.differentiableAt.comp _ he.differentiableAt
lemma Solvent.amp (w:Solvent i f)(x:ℂ)(z:Key I): f (x • z)=x^i • f z:=by
 obtain ⟨a,p⟩:=w; rw [p,p,Finset.smul_sum]; simp only [lTerm,Pi.smul_apply,smul_eq_mul,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,smul_smul]
lemma dAmp (h:River f)(x:ℂ)(v:‖x‖≤1) (L:List I) (p:River (fun z:Key I=> f (x • z))) : tipI (fun z:Key I=>f (x • z)) L= x^L.length • tipI f L:=by
 -- derive lance identity on z∈hill directly to avoid re-river h.flow
 have q(z:Key I)(w:z∈ hill I): x • z∈hill I:=mem_closedBall_zero_iff.mpr ((norm_smul ..).trans_le ((mul_le_of_le_one_left (norm_nonneg _) v).trans (mem_closedBall_zero_iff.mp w)))
 -- need flowProof River G∘x. build
 have d {g:Key I→E}(e:River g): River (fun z=> g (x • z)):=by
    refine ⟨e.shore.comp (Continuous.continuousOn (by fun_prop:Continuous (fun z:Key I=> x • z))) (fun i w=>q _ w),?_⟩
    intro z w j y u; let l(y:ℂ):=x*y; have he(y:ℂ): x • update z j y=update (x • z) j (x*y):=by ext i:1; by_cases h:i=j <;>simp [h]
    simp_rw [he]; apply (e.slope _ (q z w) j _ ?_).comp y; exact (differentiableAt_id.const_mul x); apply mem_ball_zero_iff.mpr; rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg y) v) (mem_ball_zero_iff.mp u)
 induction L generalizing f with
 | nil=> simp [tipI,lance]
 | cons i L ih=>
    let f'(z:Key I):= f (x • z); let u:= cutI f i; let v':=(fun z:Key I=> u (x • z))
    have hh(z:Key I)(w:z∈hill I): cutI f' i z=x • v' z:=by
       let H:=mitt p w i; let l(y:ℂ):=x*y; have hx: HasDerivAt l x 0:=by simpa only [mul_one] using (hasDerivAt_id' (x:=(0:ℂ))).const_mul x
       rw [←H.deriv]; have he(y:ℂ): x • update z i y=update (x • z) i (l y):=by ext j:1; by_cases h:j=i<;>simp [h,l]
       simp_rw [he]; have hG:=mitt h (q z w) i; have hz:l 0=0:=mul_zero _
       exact ((hz.symm ▸ hG).scomp _ hx).deriv
    calc
       _ = tipI (cutI f' i) L:=rfl
       _ = tipI (fun z=> x • v' z) L :=lace_C L (fun z r=>hh z r) roots
       _ = _:=by rw [tip_C,show tipI v' L=x^L.length • tipI u L from ih (h.flow _) (d (h.flow _)),smul_smul,List.length_cons, pow_succ']; rfl; exact d (h.flow _) -- order of ih tune
lemma Solvent.skip (w:Solvent i f)(l:List I)(p:l.length ≠ i) : tipI f l=0:=by
 let x:ℂ:=1/2; have ht:‖x‖< 1:=by unfold x; norm_num
 have v:‖x‖>0:= norm_pos_iff.mpr (by unfold x; norm_num)
 have e: (fun z:Key I=>f (x • z))=fun z=>x^i • f z:=funext fun z=>w.amp ..
 let V:= w.riv; have h:=dAmp V x ht.le l (e.symm ▸ V.scale _); rw [e,tip_C V] at h; have he:=congrArg (‖·‖) h; rw [norm_smul,norm_smul,norm_pow,norm_pow] at he
 by_contra z; exact p ((pow_right_strictAnti₀ v ht).injective (mul_right_cancel₀ (norm_ne_zero_iff.mpr z) he.symm)) -- use strictAnti
end
end YM.CF.Mew
