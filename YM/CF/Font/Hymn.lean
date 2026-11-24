import YM.CF.Font.Halt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {f n c: Side}
lemma credit_b {α β:Type*}[Fintype β] {R:Cross n α β}{G:Ratio c f}(g:G.count=n){a C:ℝ}(h:0≤a): R.strip a C→ ∀ {Z:Cross G.count α β}, HEq Z R→∀ (x:Site f)(i:α)(z:Co c β), ‖installed G Z (x,i) z‖ ≤ Fintype.card β*C:=by
 subst n; intro p Z k x i z; rw [eq_of_heq k]; clear Z k; have he :1≤ Faro a (G.parent x) z.1:=Real.one_le_exp (mul_nonneg h (by positivity)); exact le_trans (b:=Faro _ _ _ * ‖installed G R (x,i) z‖) (le_mul_of_one_le_left (norm_nonneg _) he) ((single_le_sum (f:=fun y:Co c β=> Faro a (G.parent x) y.1 * ‖installed G R (x,i) y‖) (fun y _=>mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _)) (mem_univ z)).trans (coat_cross G h p x i))
lemma pdist_leN(x:Site n):pdist x≤ n.val:=by
 unfold pdist; refine Finset.sup_le ?_; intro i h; have hp:=lift_centers x i; omega
lemma lowN(x:Site n)(u:Wind n):dial x u≤ n.val:=by cases u with| inl y=> exact pdist_leN _| inr i=> exact le_rfl
lemma signal(x:Site n)(w:Walk)(v: form 1 n)(a:ℝ)(h:∀ i,|v i|≤a):|integralLink x w v|≤ w.length*a:=by
 induction w generalizing x with
 | nil=>simp [integralLink,linkSum]
 | cons d w ih=>
    change |(if d.neg then -_ else _)+integralLink (x+d.vec) w v| ≤ _
    simp only [List.length_cons,Nat.cast_add, Nat.cast_one,add_mul,one_mul]; rw [add_comm _ a]; refine (abs_add_le ..).trans (add_le_add ?_ (ih _)); split; · rw [abs_neg]; exact h _
    exact h _
def tall (f c:Side)(A:ℝ):= (Fintype.card (TypeFace 1):ℝ)*c.val^4*((f.val:ℝ)*(Fintype.card (TypeFace 1):ℝ)*A) * (4*(9*((c.val:ℝ)+1)+1)^2)
variable {S:StepData c f}
section
variable {P Q:Bed}{T:Towers S.patch.L}{a A B γ D:ℝ}(h:0<a)(he:P.dual_diag.strip a A)(hf:Q.diagonal.strip a B)(v:T.Deep a A 1){p:Clip}(H:Floor P p f γ D)(g:Towers.Diagonal S P Q T)
include h he hf v H g
lemma hail(hA:0≤A)(y:Site c)(z:Site f)(i:Axis): let W:=installed S.ratio T.A0
 ∃ K:Wind c→ℝ,(∑ j,|K j|)≤ tall f c A ∧ ∀ x:form 1 c, integralLink z (swirl f i) (W *ᵥ x)=∑ j, K j*heat y (lamp x) j:=by
 intro W
 let w:=swirl f i; let I: form 1 c→ₗ[ℝ]ℝ:= (integralLink z w).comp W.mulVecLin; let L:= Channel.bondBody c; let b(e:Blip c): Lett c:= Pi.single (L e) 1; let M:= (Fintype.card (TypeFace 1):ℝ)*A; let N:= f.val*M
 have hp(j:Body 1 f)(e:Blip c): |(W *ᵥ b e) j| ≤ M:=by
    obtain ⟨x,r⟩:=j; unfold b; simp only [mulVec_single, MulOpposite.op_one, one_smul,col_apply];
    have hk:T.A0.strip a (A/(S.patch.L.val:ℝ)):=by simpa [advanceC] using (v.2.2.2 [] (by simp)).1
    unfold M; refine le_trans (credit_b (G:=S.ratio) rfl h.le hk HEq.rfl x r (L e)) ?_; apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _) -- tune
    apply div_le_self hA; exact period_one (g:=S.ratio)
 have hi(e:Blip c): |I (b e)|≤N:=by
    have h:=signal z w (W *ᵥ b e) M ?_; swap; · exact fun j=> hp j e
    simpa only [I,LinearMap.comp_apply,mulVecLin_apply,w,swirl,List.length_replicate,N] using h
 have hz(u:form 0 c): I (d 0 c *ᵥ u)=0:=by
    obtain ⟨x,e⟩:= rotor S h he hf v H g u
    change integralLink z w (W*ᵥ _)= 0; rw [e, Precision.telescopes,swirl_stop,sub_self]
 choose F l m Γ using (funnel ℝ y)
 let K j:=∑ e:Blip c,I (b e)* F e j; refine ⟨K,?_,fun x=>?_⟩
 · have hw (e:Blip c): ∑ j,|I (b e)* F e j| ≤ N*(4*(9*((c.val:ℝ)+1)+1)^2):=by
      simp_rw [abs_mul, ← Finset.mul_sum]; apply mul_le_mul (hi e) ?_ (sum_nonneg fun _ _=>abs_nonneg _) ((abs_nonneg _).trans (hi e)); apply (l e).trans; unfold slope; push_cast; gcongr; exact pdist_leN _
   unfold K; apply le_trans (sum_le_sum (g:=fun j=> ∑ e:Blip c,|I (b e)*F e j|) (fun j _=> abs_sum_le_sum_abs ..)); rw [sum_comm]; refine (sum_le_sum fun i _=> hw i).trans_eq ?_; unfold tall N M; simp [Blip,Edge, site_card]; ring -- tune
 let u:=lamp x; let Z:=sap y u; let T(i:Body 0 c):=Z i.1; let X:= x-d 0 c *ᵥ T
 have he(e) : lamp X e=(u-pure Z) e:=by unfold lamp X; rw [Pi.sub_apply,d_sites]; rfl
 have hv : X=∑ i:Blip c,lamp X i • b i:=by
    funext i; obtain ⟨i,rfl⟩:=L.surjective i; nth_rw 1 [Finset.sum_apply]; simp [b,Pi.single_apply]; rfl
 change I x=_
 rw [show I x= I X by unfold X; rw [map_sub,hz,sub_zero]]; calc
   I X=∑ i:Blip c,lamp X i* I (b i):=by
     conv_lhs => rw [hv,map_sum]; -- tune syntax
     simp
   _ = _ :=by
      unfold K; simp_rw [he, show ∀ i:(Blip c),(u-pure Z) i = ∑ j,F i j • heat y u j from fun i=> Γ i u, smul_eq_mul,sum_mul]; rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; apply sum_congr rfl; intros; unfold u; ring
lemma slopeH_r {G:Gauge}(R:Forest S.ratio)(z:Site f)(i:Axis)(y: Site c)(hA:0≤A): let W:=installed S.ratio T.A0;∃ K:Wind c→ℝ,(∑ j,|K j|)≤ tall f c A ∧ ∀ x:fieldDir G c 1, heat z (collect G (Channel.rising R W x)) (.inr i)= ∑ j,K j • heat y (collect G x) j:=by
 intro W; obtain ⟨K,p,H⟩:=hail h he hf v H g hA y z i; refine ⟨K,p,fun x=>?_⟩; let f':=Channel.rising R W x; let V(a):=parts G 1 x a
 ext1 a; have hv :=Work.F04.parts_stretch R W x a; change parts G 1 f' a= _ at hv
 have hp(j:Wind c):(heat y (collect G x) j).ofLp a=heat y (lamp (V a)) j:=by cases j <;> exact (path_component G x _ _ a).symm
 change (linkSum (collect G f') z _).ofLp a = _; rw [←path_component]
 change integralLink z _ (parts G 1 f' a)=(∑ j,K j • heat y (collect G x) j).ofLp a
 rw [hv,extracted,add_mulVec,LinearMap.map_add,← mulVec_mulVec,Precision.telescopes,swirl_stop,sub_self,add_zero]; rw [show integralLink z (swirl f i) _=∑ j,K j* _ from H (V a),WithLp.ofLp_sum,Finset.sum_apply]; simp_rw [WithLp.ofLp_smul,Pi.smul_apply,hp]; rfl
end
end YM.CF.Font
