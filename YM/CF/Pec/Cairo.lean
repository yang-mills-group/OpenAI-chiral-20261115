import YM.CF.Pec.Sorrel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n: Side}{Z:Type}[NormedAddCommGroup Z][InnerProductSpace ℝ Z]
lemma mirror_t(i:Axis)(v w:Axis)(z:ℝ):skew (Signed.mirror i) (crest v w z)=crest v w (dye (Signed.mirror i) v*dye (Signed.mirror i) w*z):=by
 let u:=Signed.mirror i; funext k l; by_cases t:ask v w k l=0; · change (_:ℝ) * (ask v w k l * z)= ask v w k l*_ ; rw [t]; ring
 by_cases h:v=k ∧ w=l; · obtain ⟨rfl,rfl⟩:=h; change (_:ℝ)* (ask v w v w*z)= ask v w v w*_; ring
 have he:w=k ∧ v=l:=by by_contra e; apply t; rw [ask, if_neg h,if_neg e]; simp
 obtain ⟨rfl,rfl⟩:=he; change (dye u w*dye u v)* (ask v w w v*z)= ask v w w v*(dye u v*dye u w*z); ring
lemma par(P:Case)(i j k l a:Axis):let s:= Signed.mirror a; (dye s i*dye s j*dye s k*dye s l) • crystalC P i j k l=star (crystalC P i j k l):=by
 intro s; have he:= humid s P (crest i j (1:ℝ)) (crest k l 1); rw [complX,show detX s=_ from det_t a, mirror_t,mirror_t,lineB] at he; rw [show dye s i*dye s j*dye s k*dye s l = inner ℝ (dye s i*dye s j*1) (dye s k*dye s l*1) from ?_]; exact he; simp; ring
lemma swapXY(P:Case)(i j k l:Axis)(x:Equiv.Perm Axis):pays (X x) (crystalC P (x i) (x j) (x k) (x l))=crystalC P i j k l:=by
 have hx(i j:Axis): skew (X x) (crest (x i) (x j) (1:ℝ))=crest i j 1:=by funext u v; simp [dye,skew,crest,X, ask]
 rw [crystalC,← humid,hx,hx]; rfl
lemma ascL(P:Case)(i j k l:Axis): crystalC P i j k l= -crystalC P j i k l ∧ crystalC P i j k l= -crystalC P i j l k:=by
 have he(i j): crest i j (1:ℝ)=crest j i (-1:ℝ):=by funext a b; simp [crest,ask]
 constructor; · nth_rw 1 [crystalC,he i j,lineB]; simp
 nth_rw 1 [crystalC]; rw [he k l,lineB]; simp
lemma selfC(P:Case)(i j k:Axis):crystalC P i i j k=0∧ crystalC P i j k k=0:=by constructor <;> simp [crystalC,crest,hum,beam,ask,skew]
private lemma trans_pair (i j u v:Axis)(h:i≠j)(t:u≠v):∃ p:Equiv.Perm Axis, p i=u ∧ p j=v:=by
 let p:=Equiv.swap i u; let t':=Equiv.swap (p j) v; have ht:p i=u:=Equiv.swap_apply_left ..; have hp:t' u=u:= Equiv.swap_apply_of_ne_of_ne (ht ▸ p.injective.ne h) t; refine ⟨t'*p, (congrArg t' ht).trans hp, Equiv.swap_apply_left (p j) v⟩
def priceC(P:Case):ℝ:= (crystalC P 0 1 0 1).re
lemma tallyC(P:Case)(p:PlaqAxes): (crystalC P p.val.1 p.val.2 p.val.1 p.val.2).re=priceC P:=by obtain ⟨f,w,y⟩:= trans_pair 0 1 _ _ (by decide) p.property.ne; rw [←w,←y]; exact (pays_v (X f) _).1.symm.trans (congrArg Complex.re (swapXY P 0 1 0 1 f))
lemma vanishC(P:Case)(a b:PlaqAxes)(p:a≠b): (crystalC P a.val.1 a.val.2 b.val.1 b.val.2).re=0:=by
 rcases a with ⟨⟨i,j⟩,h⟩; rcases b with ⟨⟨k,l⟩,t⟩; change i<j at h; change k<l at t; have hx:¬(i=k∧j=l):= fun w=> p (Subtype.ext (Prod.ext w.1 w.2))
 have ht :∃ v:Axis, let s:=Signed.mirror v; dye s i*dye s j*dye s k*dye s l= -1:=by
    by_cases q:i=k
    · subst k; have e:j≠l:=by tauto
      refine ⟨j,?_⟩; simp [dye,Signed.mirror,h.ne,h.ne.symm,e,e.symm]
    by_cases w:i=l; swap; · exact ⟨i,by simp [dye,Signed.mirror,h.ne,q,w]⟩
    subst l; have z:k≠j:= ne_of_lt (t.trans h); exact ⟨j,by simp [dye,Signed.mirror,h.ne,z.symm,h.ne.symm]⟩
 obtain ⟨w,hx⟩:=ht; have hx':=par P i j k l w; dsimp only at hx hx'; rw [hx] at hx'; have he:=congrArg Complex.re hx'; simp at he; change (crystalC P i j k l).re=0; linarith
lemma lessC(P:Case)(i j k l a:Axis)(p:a≠ i)(v:a≠j)(w:a≠k)(r:a≠ l): (crystalC P i j k l).im=0:=by
 have he:=congrArg Complex.im (par P i j k l a); simp [dye,Signed.mirror,p,v,w,r] at he; linarith
private lemma avoidsE(a b c:Axis):∃ i:Axis, i≠a∧ i≠b∧ i≠c:=by
 have h:∀ a b c:Axis, ∃ i:Axis, i≠a∧ i≠b∧i≠c:=by decide
 exact h a b c
lemma swap_im(P:Case)(i j k l:Axis): (crystalC P i j k l).im= -(crystalC P k j i l).im:=by
 by_cases h:i=k; · subst k; obtain ⟨a,t,v,w⟩:=avoidsE i j l; rw [lessC P i j i l a t v t w,neg_zero]
 by_cases p:i=j; · subst j; obtain ⟨a,t,v,w⟩:=avoidsE i k l; rw [lessC P i i k l a t t v w,lessC P k i i l a v t t w,neg_zero]
 by_cases q:i=l; · subst l; obtain ⟨a,t,v,w⟩:=avoidsE i j k; rw [lessC P i j k i a t v w t,lessC P k j i i a w v t t,neg_zero]
 by_cases w:k=j; · subst j; obtain ⟨a,t,v,w⟩:=avoidsE i k l; rw [lessC P i k k l a t v v w,lessC P k k i l a v v t w,neg_zero]
 by_cases r:k=l; · subst l; obtain ⟨a,t,v,w⟩:=avoidsE i j k; rw [lessC P i j k k a t v w w,lessC P k j i k a w v t w,neg_zero]
 have he:= swapXY P i j k l (Equiv.swap i k); rw [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm p) (Ne.symm w),Equiv.swap_apply_of_ne_of_ne (Ne.symm q) (Ne.symm r),complX,detSwap i k h] at he; exact congrArg Complex.im he.symm
end YM.CF.Pec
