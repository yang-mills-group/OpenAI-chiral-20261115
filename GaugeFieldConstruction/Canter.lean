import GaugeFieldConstruction.BarrT
/- offshell ge EOM integration -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 70000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
variable (o:Site n)(q:Clip)(e: Axis)
lemma huppy(t:ℝ): let X:=Turret o (G:=G) t ∘ increment 1
 X 0=1 ∧ fderiv ℝ X 0=0 ∧ ∀ i j,iteratedFDeriv ℝ 2 X 0 ![i,j]=0:=by
 intro X; let f (s:Finset (Face (Per n)))(x:Directions G n):=∏ i∈s, TestVe t i (increment 1 x)
 have hp(s:Finset (Face (Per n))):ContDiffAt ℝ ω (f s) 0∧ f s 0=1 ∧ fderiv ℝ (f s) 0=0∧∀ i j,iteratedFDeriv ℝ 2 (f s) 0 ![i,j]=0:=by
    induction s using Finset.induction_on with
    | empty=> simp only [f,prod_empty]; refine ⟨contDiffAt_const,True.intro,fderiv_const_apply ..,fun i j=>?_⟩; simp [iteratedFDeriv_const_of_ne]
    | @insert i s l ih =>
      obtain ⟨ht,A,V,W⟩:= ih; let g:=TestVe (G:=G) t i ∘ increment 1; have ⟨hz,hp,hw⟩:= light_F (G:=G) i t; have hh:ContDiffAt ℝ ω g 0:= lineTur _ t i
      have he: f (insert i s) = fun x=> g x*f s x:=funext fun x=> prod_insert l; rw [he]; have hv:=(hh.differentiableAt (by simp)).hasFDerivAt.mul ((ht.differentiableAt (by simp)).hasFDerivAt)
      have hz':HasFDerivAt (fun x=> g x*f s x) (0:Directions G n→L[ℝ]ℝ) 0:=by rw [show fderiv ℝ g 0=0 from hp,V, smul_zero,smul_zero,add_zero] at hv; exact hv
      refine ⟨hh.mul ht, by change g 0*f s 0=1; rw [show g 0=1 from hz,A,mul_one], hz'.fderiv,fun j k=>?_⟩
      let M:= fun x=>g x*f s x; let T (u:Directions G n):=g u • fderiv ℝ (f s) u + f s u • fderiv ℝ g u
      have hm:fderiv ℝ M =ᶠ[𝓝 0] T:=by
          filter_upwards [ht.eventually (by simp),hh.eventually (by simp)] with i hi hu; exact ((hu.differentiableAt (by simp)).hasFDerivAt.mul (hi.differentiableAt (by simp)|>.hasFDerivAt)).fderiv -- sum order tune
      have hb:= ((hh.differentiableAt (by simp)).hasFDerivAt.smul (ht.fderiv_right (m:=1) (by simp)|>.differentiableAt (by norm_num)|>.hasFDerivAt)).add ((ht.differentiableAt (by simp)|>.hasFDerivAt).smul ((hh.fderiv_right (m:=1) (by simp)|>.differentiableAt (by norm_num)).hasFDerivAt))
      change iteratedFDeriv ℝ 2 M _ _ =_; rw [iteratedFDeriv_two_apply, hm.fderiv_eq (𝕜:=ℝ), show fderiv ℝ T 0 = _ from hb.fderiv]
      have hv: fderiv ℝ (fderiv ℝ g) 0 j k=0:= by have he:=hw j k; rw [iteratedFDeriv_two_apply] at he; exact he
      have hu: fderiv ℝ (fderiv ℝ (f s)) 0 j k=0:= by have he:=W j k; rw [iteratedFDeriv_two_apply] at he; exact he
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.coe_zero, Pi.zero_apply, Matrix.cons_val_zero,Matrix.cons_val_one, add_zero, smul_zero] -- don't rewrite V before hv
      rw [hv,hu, V,show fderiv ℝ g 0=0 from hp]; simp
 exact (hp (slab o)).2
local notation "GS"=>SU.group
lemma yuppie: let X:= Dorm o q ∘ increment 1
 X 0=0 ∧ fderiv ℝ X 0=0∧∀ i j, iteratedFDeriv ℝ 2 X 0 ![i,j]=∑ f∈ slab o,inner ℝ (faceCurl f (mapCo i)) (faceCurl f (mapCo j)):=by
 intro X; let g(i:Face (Per n)) (V):= Score q (V:Config SU.group n) i; let S(f):=g f ∘ increment 1; have h(f): S f 0=0:=(bankShape q f).1; have v(f):fderiv ℝ (S f) 0=0:= (bankShape q f).2.1; have H(f):ContDiffAt ℝ ω (S f) 0:= score_π _ q f; have hx:X=∑ i∈slab o,S i:=by funext i; rw [Finset.sum_apply]; rfl
 rw [hx]; simp only [Finset.sum_apply,h,sum_const_zero]; refine ⟨True.intro,?_,fun i j=>?_⟩
 · have hw := HasFDerivAt.fun_sum (u:=slab o) (A:=S) fun i _=> ((H i).differentiableAt (by simp)).hasFDerivAt; simp only [v,sum_const_zero] at hw; rw [←hx]; exact hw.fderiv
 rw [iteratedFDeriv_sum_apply (fun i _=>(H i).of_le le_top), _root_.sum_apply]; exact sum_congr rfl fun f _=> (bankShape q f).2.2 i j
abbrev area (i:Face (Per n))(A:Directions G n):= faceCurl i (mapCo A)
abbrev at_E (w:G.Color):Directions G n:=Pi.single (o,e) w
lemma petra(f:Face (Per n))(w:G.Color)(p:f∉ slab o): area f (at_E o e w)=0:=by
 unfold area; rw [credit_rule]; have hp(i: Fin 4): at_E o e w (edges f i)=0:=Pi.single_eq_of_ne (by intro h; exact p ((slab_q _).mpr ((show (edges f i).1=o from congrArg Prod.fst h) ▸ edges_visit f i))) _
 rw [hp,hp,hp,hp]; simp
lemma face_hill(A:Directions G n)(X:G.Color): (∑ f∈ slab o,inner ℝ (area f A) (area f (at_E o e X)))= ∑ b:PlaqAxes, ((if e=b.val.1 then inner ℝ (area (o,b) A-area (o-step b.val.2,b) A) X else 0)-(if e=b.val.2 then inner ℝ (area (o,b) A-area (o-step b.val.1,b) A) X else 0)):=by
 rw [sum_subset (subset_univ _) fun i _ h=> (by rw [petra o e i X h,inner_zero_right]),Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro b _; let i:= b.val.1; let j:= b.val.2; let H(x:Site n):ℝ:= inner ℝ (area (x,b) A) X; let y:= (if e=i then H o else 0); let Q:= at_E o e X
 have hx(x:Site n): area (x,b) Q= Q (x,i)+Q (x+step i,j)-Q (x+step j,i)-Q (x,j):= credit_rule ..
 have hw(x v:Site n)(i:Axis): inner ℝ (area (x,b) A) (Q (v,i))= if e=i then (if v=o then H x else 0) else 0:=by
    unfold Q at_E; rw [Pi.single_apply]; split_ifs <;> simp_all [H]
 change (∑ x:Site n,inner ℝ (area (x,b) A) (area (x,b) Q))=_
 simp_rw [hx, inner_sub_right, inner_add_right, hw]
 have he(u:Axis)(x:Site n): (x+step u=o)=(x=o-step u):= propext (eq_sub_iff_add_eq|>.symm)
 simp_rw [he]; unfold i j; by_cases h:e=b.val.1 <;> by_cases u:e=b.val.2 <;> simp [h,u,Finset.sum_sub_distrib,Finset.sum_add_distrib, H,inner_sub_left,b.property.ne,Ne.symm b.property.ne] <;> ring -- tune
end Shield
end YM.CF.XGarden
end
