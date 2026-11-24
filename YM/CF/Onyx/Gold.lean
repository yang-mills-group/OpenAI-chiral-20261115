import YM.CF.Flare.Foot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
-- continuum diagnostic of Flat ALL Slater interpolation. graph tilt L high = dip. low arbitrary
variable {ι:Type*}{A:Tax ι}{j:ℕ}
abbrev Peb:= Op SpinIdx
def lash(p:Momentum):Peb:=-(minA*zen p)
def dip(j:ℕ)(M:Jill.Male)(p:Momentum): Peb:= (shell j M.val p)⁻¹ • lash (skin j M.val p)
lemma lash_a(p q:Momentum):lash (p+q)=lash p+lash q:=by unfold lash; rw [zenP,mul_add, neg_add]
lemma lash_s(p:Momentum)(c:ℂ):lash (c • p)= c • lash p:=by unfold lash; rw [zenS, Matrix.mul_smul,smul_neg]
def lashCL: Momentum→L[ℂ] Peb:= LinearMap.toContinuousLinearMap ⟨⟨lash,lash_a⟩,fun c p=>lash_s p c⟩ -- inspect
lemma pear(j:ℕ)(M:Male)(p:Momentum):minA*bar j M.val p*Aop=lash (skin j M.val p):=by
 let v:=skin j M.val p; have hp:minA*grading= -minA:=by unfold minA; rw [ordA]; simp only [mul_sub,Matrix.mul_smul,sub_mul,mul_one,one_mul,AOne]; module
 have he:minA*Aop=0:=by unfold minA; rw [sub_mul,one_mul,AOne,sub_self]
 have hv:minA*zen v*Aop=minA*zen v:=by rw [show minA*zen v=zen v*Aop from zenAA _,mul_assoc,AOne] -- tune
 unfold bar; rw [mul_add,mul_add,Matrix.mul_smul,Matrix.mul_smul,hp,mul_one,←mul_assoc minA, hp,add_mul,add_mul, Matrix.smul_mul,Matrix.smul_mul, neg_mul, he, neg_zero,smul_zero,smul_zero,zero_add,zero_add,neg_mul,neg_mul,hv]; rfl
lemma seep (j:ℕ)(M:Male){p q:Bin}(h:peers p q)(g:tmap p∈realCube zone)(w:tmap q∈realCube zone): dip j M (tmap p)=dip j M (tmap q):=by
 obtain ⟨x,rfl⟩:=h; unfold dip; rw [map_stem] at w ⊢; rw [shell_overlap _ _ _ g x w, ← pear, ← pear,bar_overlap _ _ g x w] -- direction
lemma foxy (j:ℕ)(M:Male){p:Momentum}(h:p∈realCube zone)(g:-p∈realCube zone): shell j M.val (-p)=shell j M.val p:=by
 by_cases e:p=0; · simp [e];
 rw [shell_inv _ _ h e,shell_inv _ _ g (neg_ne_zero.mpr e), mix_neg _ _ M.property]; simp [prodM] -- tune
lemma dusk(j:ℕ)(M:Male){p:Momentum}(h:p∈realCube zone)(g:-p∈realCube zone):dip j M (-p)= -dip j M p:=by
 have hv w:lash (-w)= -lash w:=by rw [←neg_one_smul ℂ w, lash_s,neg_one_smul]
 unfold dip; rw [skin_mix _ _ g,skin_mix _ _ h,foxy _ _ h g,mix_neg _ _ M.property,smul_neg,hv,smul_neg]
lemma lime {F:ι→ℂ→Momentum}(h:Move A F)(H:1≤j)(M:ι→Male):Act A 2 fun i z=>lash (skin j (M i).val (F i z))- (1/2:ℂ) • lash (F i z):=by
 simp_rw [←lash_s]; unfold lash zen; simp only [Matrix.mul_sum, ← sum_neg_distrib,← sum_sub_distrib,Pi.smul_apply,smul_eq_mul]; -- inspect
 refine Act.finiteSum univ _ fun a _=> ?_
 have he:=(h.coldS (fun i=>(M i).val) (fun i=>(M i).property) j H a).smul (Act.anchor A (- (minA*(Complex.I • gammaOp a))))
 norm_num1 at he; convert he using 1; ext1 i; ext1 z; rw [sub_smul, Matrix.mul_smul,Matrix.mul_smul,smul_neg,smul_neg]; simp only [Matrix.mul_smul]
variable {x:ι→Bin} (e:∀ i,A.r i=‖x i‖)(w:∀ i,Bound Real.pi (x i))
include e w
lemma cane (M:ι→Male)(H:1≤j): ∃ c:ℝ,0<c∧∀ i,c*A.r i^2 ≤ (shell j (M i).val (tmap (x i))).re:=by
 obtain ⟨c,h,K⟩:=court j H M x e w; refine ⟨c,h,fun i=>?_⟩; rw [express _ (x i) _ (base_subset_realCube zone_pos (b_base (w _))) (M i).property,Complex.ofReal_re]; exact K _
lemma turn_s(M:ι→Male)(a:Axis):Move A fun i z=>tmap (x i)+spark a (raf A i z):= Move.add (go_b x e w) (sparkBud A (raft ..) a) (fun i=> by simp [raf,spark])
lemma drill(M:ι→Male)(H:1≤j)(a:Axis):Act A (-1) fun i z=>dip j (M i) (tmap (x i)+spark a (raf A i z)):=by
 let X i z:=tmap (x i)+spark a (raf A i z); have h:Move A X:=turn_s e w M a
 let G(i:ι)(z:ℂ):=shell j (M i).val (X i z); obtain ⟨c,hc,K⟩:= cane e w M H
 have he:Act A 1 fun i z=> lash (skin j (M i).val (X i z)):=by
    let Z(i:ι)(z:ℂ):=(1/2:ℂ) • lash (X i z)
    have ht:Act A 1 Z:=(Act.anchor A (1/2:ℂ)).smul (h.act.via lashCL)
    have hz:= ((lime h H M).loose (show (1:ℤ)≤2 by decide)).add ht
    simpa only [Z, sub_add_cancel] using hz
 exact ((h.glass (fun i=>(M i).val) (fun i=>(M i).property) j H).inv ⟨c,hc,fun i=> by simp only [X,raf,spark,mul_zero,zero_smul,add_zero,zpow_ofNat]; exact ((K i).trans (Complex.re_le_norm _))⟩).smul he -- tune
end YM.CF.Onyx
