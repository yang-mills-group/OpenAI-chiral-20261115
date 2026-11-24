import YM.CF.Thera.Jolt
import YM.CF.Matter.Anomaly
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Filter Function MeasureTheory Gauge Matrix Fock SU Finset NormedSpace
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable (a:F₀)
abbrev Color:= group.Color
def ξ (i:F₀):Color→ₗ[ℝ]ℂ:= ({toFun:=fun x: V=>x a i,map_add':=by intros;rfl,map_smul':=by intros;rfl} : V →ₗ[ℝ]ℂ).comp group.colorMat -- tune structure
lemma hut_k : group.casimir=50:=by
 let a:F₀:=0; let X:= hut a; let x:=group.projectColor X; have hx:group.colorMat x=X:=group.colorMat_project_self (hutL a)
 have he:=trace_adjoint yet_one x x
 have hA:=trace_color group x x; rw [hx] at hA; have hB:Matrix.trace (X*X)= -(4/5:ℂ):=by unfold X hut a; rw [diagonal_mul_diagonal, trace_diagonal]; norm_num [F₀,Gauge.repDim, SU.group, Fin.sum_univ_succ, Complex.ext_iff] -- tune
 let J:= group.ad x * group.ad x; let U:=univ.erase a
 let f(i:F₀):=Complex.reLm.comp (ξ a i); let g(i:F₀):= Complex.imLm.comp (ξ a i) -- tune
 let z(i:F₀)(t:ℂ):= group.projectColor (curlA a i t); let L(i:F₀):= (f i).smulRight (z i 1)+(g i).smulRight (z i Complex.I)
 have hp(i:F₀)(k:i∈U)(t:ℂ): group.colorMat (z i t)=curlA a i t:= group.colorMat_project_self (curl_v a i t (mem_erase.mp k).1.symm)
 have hi (c:Color) (i:F₀) (p:i∈U): group.colorMat (L i c)=curlA a i (ξ a i c):=by -- p: infer
   unfold L; rw [LinearMap.add_apply,LinearMap.smulRight_apply,LinearMap.smulRight_apply,map_add,map_smul,map_smul,hp i p,hp i p,←curl_s,←curl_s,← curl_u]; congr 1; rw [Complex.real_smul,Complex.real_smul,mul_one]; exact Complex.re_add_im (ξ a i c) -- tune
 have hv : ∑ i∈ U,L i= -J:=by
    apply LinearMap.ext; intro c; apply group.colorMat_injective
    let Y:= group.colorMat c; rw [LinearMap.sum_apply,map_sum, LinearMap.neg_apply,map_neg]; unfold J; simp_rw [Module.End.mul_apply,colorMat_ad,hx]; ext i j; simp only [Matrix.sum_apply, Matrix.neg_apply]
    change ∑ u∈U,(_:_)= -(bracket X (bracket X Y) i j); rw [sum_congr rfl (g:=fun u=>curlA a u (Y a u) i j) (fun u v=> congr_fun (congr_fun (hi c u v) _) _)]; unfold X; simp only [hut_b];
    by_cases k:i=a
    · subst i; by_cases p:j=a
      · rw [p]; simp only [if_true]; rw [Finset.sum_eq_zero]; simp
        intro i h; let f:= (mem_erase.mp h).1; simp [curlA,f]
      simp only [p,ite_false,ite_true,←mul_assoc,Complex.I_mul_I,neg_mul,one_mul,neg_neg]; rw [sum_eq_single_of_mem j (show j∈U from mem_erase.mpr ⟨p, mem_univ _⟩)]; simp [curlA,p, Ne.symm]; intro b h l; simp [curlA,p, Ne.symm,l]
    by_cases p:j=a
    · subst j; simp only [k,ite_false,ite_true, neg_mul,mul_neg, ←mul_assoc,Complex.I_mul_I,one_mul,neg_neg]; rw [sum_eq_single_of_mem i (show i∈U from mem_erase.mpr ⟨k,mem_univ _⟩)]; rw [curlA]; have hx:star (Y a i)= -Y i a:=Matrix.ext_iff.mpr (group.colorMat_skew c) i a; simp [k,Ne.symm]; exact neg_eq_iff_eq_neg.mpr hx -- tune
      intro b h l; simp [curlA,k, Ne.symm,l]
    simp only [k,p,ite_false, neg_zero]; exact sum_eq_zero fun t _=>by simp [curlA,k,p, Ne.symm]
 have hg:∑ i∈U,LinearMap.trace ℝ Color (L i)=(8:ℝ):=by
   rw [sum_congr rfl (g:=fun i=> (2:ℝ))]; change _=_; simp only [sum_const,nsmul_eq_mul]; rw [show U.card=4 from by unfold U; rw [card_erase_of_mem (mem_univ _),card_univ]; rfl]; norm_num
   intro i h; unfold L; rw [map_add,LinearMap.trace_smulRight,LinearMap.trace_smulRight]; change (group.colorMat _ a i).re + (group.colorMat _ a i).im=_; rw [hp i h,hp i h]; simp [curlA,(mem_erase.mp h).1]; norm_num
 rw [← map_sum (LinearMap.trace ℝ Color),hv,map_neg] at hg; rw [hB] at hA; change _= (↑(5:ℕ):ℝ)*_ at hA; norm_num at hA; change -(LinearMap.trace ℝ Color) J=_ at he; rw [hg,real_inner_self_eq_norm_sq, show ‖x‖^2=(4:ℝ)/25 from by linarith] at he; linarith -- tune
lemma hue_v (c: group.Color)(h:‖c‖=1): Matrix.trace (SU.dMatter (group.colorMat c)^2)= -(60:ℂ):=by
 let X:=group.colorMat c; have hx:=league.mp (group.colorMat_mem c); have ht:= local_polynomial X ⟨hx.1,hx.2⟩; have he:=group.trace_color c c; rw [real_inner_self_eq_norm_sq,h] at he; change -(Matrix.trace (X*X)).re = (↑(5:ℕ):ℝ)*_ at he; norm_num at he
 have hp:(X*X).trace.im=0:=group.trace_color_real c c
 have hz:Matrix.trace (X^2)= -(5:ℂ):=by apply Complex.ext; norm_num [sq]; linarith; norm_num [sq]; exact hp
 have hx:12*(X^2).trace=-(60:ℂ):=by rw [hz]; norm_num
 exact ht.2.1.trans hx
lemma asym : 0 < group.slopeConstant-60/(12*Real.pi^2):=by unfold Gauge.slopeConstant; rw [hut_k]; have he:=Real.pi_pos; field_simp; norm_num
end YM.CF.Thera
