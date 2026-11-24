import ForceSatin.Truncate
import ForceSatin.RealMean
import ForceSatin.Canto
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu Lifted Loaves Verses
open Lamour
open Next.Free
open _root_.YM.Regis.Circuit.SpringDay Spring
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side} (M:Jill.Male)
local notation "ν" => FlatPaneP 4 M N
variable (a:IsStarProjection (FlatPaneP 4 M N))
def nerveK (M:Jill.Male)(p:Momentum): Op SpinIdx:= (1-zen (mixL 4 M.val p))* Aop
include a
lemma motor (x:Site N): Tendsto (fun k:ℕ=> let P:= bar 4 M.val (mel x); P+star (Comb Aop P k)) atTop (𝓝 (nerveK M (mel x))):=by
 let A:=Aop; let p:=mel x; let P:=bar 4 M.val p; let Z:= zen (mixL 4 M.val p); let z:= zTar 4 M x; have ht:IsStarProjection P:=f_native (by decide : 1≤(4:ℕ)) a x; have hs:0<z:=amp 4 (by decide) M x; have hz:z≤1:=z_cap (by decide : 1≤(4:ℕ)) a x
 have hp : p∈ realCube Next.Free.zone:= base_subset_realCube zone_pos (mel_h x)
 have he : shell 4 M.val p=(z:ℂ):=express 4 (pm x) M.val hp M.property
 have hV:P=(z:ℂ) • ((1-Z)*A*(1+Z)):=by unfold P; rw [(bar_full _ _ hp (mel_away x) (graphs_ne (phys_mix _ _ M.property p hp.1))).1,he]
 have hW:A*P=(z:ℂ)•(A*(1+Z)):=by unfold A P; rw [(bar_side _ _ hp).1,he]
 have hK: A*Z*A=0:=by unfold A Z; rw [zenA,mul_assoc,sub_mul, one_mul,AOne,sub_self,mul_zero] -- tune
 let K:=nerveK M p
 have hh: P*A=(z:ℂ) • K:= calc
    P*A= (z:ℂ) • ((1-Z)*(A*(1+Z)*A)):=by rw [hV,Algebra.smul_mul_assoc]; simp [mul_assoc]
    _=_:=by rw [mul_add A,mul_one,add_mul,hK,add_zero,AOne]; rfl -- tune defeq
 have hl: K*P=P:=by change (1-Z)*A*P=_; rw [mul_assoc,hW,Algebra.mul_smul_comm,←mul_assoc]; exact hV.symm
 let W(k:ℕ):ℝ:=(1-(1-z)^k)/z; have hw:Tendsto W atTop (𝓝 z⁻¹):=by simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hz) (by linarith only [hs] : 1-z<1)).const_sub 1).div_const z)
 let C':=(1-P)*A*P
 have hc(k:ℕ): Comb A P k=W k • C':= angled (by decide : 1≤ (4:ℕ)) a x k
 have hy: K=P+star (z⁻¹ • C'):=by
    unfold C'; rw [star_smul,star_mul,star_mul,ht.one_sub.isSelfAdjoint,Aadj,ht.isSelfAdjoint,star_id_of_comm,←mul_assoc,mul_sub, mul_one,hh, Algebra.smul_mul_assoc,hl,smul_sub]; simp only [←Complex.coe_smul, Complex.ofReal_inv]; -- tune
    have hx:(z:ℂ)≠0:=by exact_mod_cast hs.ne'
    rw [smul_smul,smul_smul,inv_mul_cancel₀ hx]; simp -- tune
 change Tendsto (fun k=> P+star (Comb A P k)) _ (𝓝 K); rw [hy]; simp_rw [hc]; exact Tendsto.add tendsto_const_nhds (hw.smul_const C').star

-- flat directional probe all (not necessarily sale). w exact heat
noncomputable abbrev trooper (a:IsStarProjection (FlatPaneP 4 M N)) := exactShear 4 M N (by decide) a
noncomputable def paceSing(S:Shaft (Single N))(i:Bite):Reader0 (Single N):=(i.hand,acts (if i.hand then star S.buy else S.sell) (i.loc N))
def bells(u v:Bite):ℂ:= tooth ν (paceSing (trooper M a) u) (paceSing (trooper M a) v)
lemma kine (v w: Bite)(hp:v.hand=false)(hq:w.hand=true): bells M a v w=inner ℂ (w.loc N) (acts (ν +star (flatComb 4 M N (by decide) a)) (v.loc N)):=by
 let J:=tickA N; let P:=ν; let θ:=flatComb 4 M N (by decide) a
 let U:=trooper M a; have hu: U.sell*P=P:=shear_on_flat 4 M N _ a; have he: U.buy*P=P:=by nth_rw 1 [←hu]; rw [←mul_assoc,U.pay,one_mul]
 have ht: Tendsto (Comb J P) atTop (𝓝 θ):= flatComb_tends 4 M N _ a; have hv: θ*P=θ:=tendsto_nhds_unique (ht.mul_const P) (ht.congr fun i=>(comb_xp (B:=J) a i).symm)
 have hy: U.buy*P*U.sell=ν+ star θ:=by rw [he]; change P*(1+star θ)=_; rw [mul_add,mul_one,show P*star θ=star θ from (by simpa [star_mul,show star P=P from a.isSelfAdjoint] using congrArg star hv)]
 unfold bells paceSing Loaves.tooth; simp only [hp,hq,Bool.false_eq_true,↓reduceIte]; rw [show _+star (flatComb 4 M N _ a)=_ from hy.symm, act_mul,act_mul]; exact act_inner _ _ _ -- tune inner convention
omit a in
lemma luminous (i:Bite)(S:Shaft (Single N)): S.glow (vix N i)= ton (paceSing S i):=by
 unfold paceSing ton vix; cases e:i.hand 
 · exact S.glow_up _
 exact S.glow_down _
lemma flick(v:Wave (Single N))(p:Sea ν v)(L:List Bite): alleyR (mateK N) v (chartP N L)= runes (bells M a) L:=by
 let S:= trooper M a; let P:= ν
 rw [show alleyR _ _ _=inner ℂ v (acts (S.glow (chartP N L)) v) from (?_), show S.glow (chartP N L)=rollC (ton ∘ paceSing S) L from ?_,choral a _ _ p]
 · rfl
 · induction L with|nil=>simp only [chartP,List.map_nil,List.prod_nil,rollC,Shaft.glow_nil]|cons i l ih=>unfold chartP rollC at *; simp only [List.map_cons,List.prod_cons, Function.comp_apply]; rw [Shaft.glow_mult,ih,luminous] -- swap tune
 change (inner ℂ (mateK N) v)⁻¹ * inner ℂ (mateK N) (acts _ v)= _; rw [← flat_price 4 M N (by decide) a _ p (tickB N),div_eq_mul_inv,mul_comm]
#print axioms flick
noncomputable abbrev terraL (M:Jill.Male)(N:Side)(F:Momentum→Op SpinIdx)(x y:Bite):ℂ:= if x.cost=y.cost then ((N.val:ℂ)^4)⁻¹* ∑ z:Site N, mode (mel z) (x.root-y.root)*F (mel z) x.spin y.spin else 0
omit a in
lemma starStamp (M:Jill.Male)(N:Side)(F:Momentum→Op SpinIdx)(x y:Bite): inner ℂ (x.loc N) (acts (lens F N) (y.loc N))= terraL M N F x y:=by
 unfold Bite.loc terraL; rw [stamper x.root y.root]; split; swap; · rfl
 congr 1; apply sum_congr rfl; intro i h; have hz:= mode_adjoint (mel i) (-x.root); simp only [show star (mel i)=mel i from (mel_h i).1, mode_opposite] at hz
 rw [sub_eq_add_neg,mode_shift]; simp only [mode_opposite,hz, inv_inv]
-- untruncated Fourier.Factor. AP heights retained. arbitrary costs but read only when legal. includes all flat mixed prices even N
lemma soarCost(x y:Bite)(he:y.hand=false)(hu:x.hand=true) : bells M a y x= terraL M N (nerveK M) x y:=by
 rw [kine M a y x he hu]; let P:=ν; let C:= flatComb 4 M N (by decide) a; let G(n:ℕ):=Comb (tickA N) P n; let K(v:Op (Single N)):= inner ℂ (x.loc N) (acts (P+star v) (y.loc N)); let F(n:ℕ)(p:Momentum):= bar 4 M.val p+star (Comb Aop (bar 4 M.val p) n)
 have he: Tendsto (K ∘ G) atTop (𝓝 (K C)):= ((show Continuous K by unfold K; fun_prop).tendsto _).comp (flatComb_tends ..); apply tendsto_nhds_unique he; have hp(i:ℕ): (K ∘ G) i=terraL M N (F i) x y:=by
    change inner ℂ _ (acts (P+star (G i)) _)=_; rw [show G i=_ from angledK (M:=M) (N:=N) (by decide : 1≤ (4:ℕ)) i, show P=lens (bent true 4 M.val) N from nativeP N true 4 M (by decide),l_star,l_plus]; exact starStamp ..
 rw [funext hp]; unfold terraL; split_ifs; swap; · exact tendsto_const_nhds
 refine Tendsto.const_mul _ (tendsto_finsetSum _ (fun i _=>?_)); have hv:=motor M a i; refine ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv _) _).const_mul _) -- tune
abbrev terra₀(a:Axis)(z:Momentum):ℂ:= imp a M z
def rubrix (i j:SpinIdx)(a:Axis):ℂ:=-(Complex.I*(gammaOp a i j)) -- `-i H_a*` for legal i row. 
noncomputable def CupM (N:Side)(i j:SpinIdx)(x:Cover):ℂ:=∑ a:Axis,rubrix i j a* skyPrice (micaO N) (fun z=> terra₀ M a (mel z)) x
omit a in
lemma golden (M:Jill.Male)(w:Site N)(i j:SpinIdx)(p: i∉plusHalf)(u:j∈plusHalf): nerveK M (mel w) i j=∑ a:Axis, rubrix i j a* terra₀ M a (mel w):=by
 let z:=mel w; have he :z∈realCube Next.Free.zone:= base_subset_realCube zone_pos (mel_h w)
 have hs:shell 4 M.val z≠0:= norm_pos_iff.mp (amp 4 (by decide) M w); let Z:= zen (mixL 4 M.val z); have hv:Aop=cutM plusHalf:= lid true; have hx:i≠j:=fun h=>p (h ▸ u)
 unfold nerveK; rw [hv]; change ((1-Z)*_ ) i j=_ -- tune
 rw [cutM, Matrix.mul_diagonal,if_pos u,mul_one,Matrix.sub_apply,Matrix.one_apply_ne hx,zero_sub]; unfold Z zen; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul, ← Finset.sum_neg_distrib]; apply sum_congr rfl; intro a _; unfold rubrix terra₀ imp; rw [skin_mix 4 M.val he]; change _ =_*( (shell _ _ z* _) * (shell 4 M.val z)⁻¹); field_simp -- tune
lemma pastoral(x y:Bite)(he:y.hand=false)(hu:x.hand=true)(p:x.spin∉plusHalf)(v:y.spin∈plusHalf) : bells M a y x= if x.cost=y.cost then CupM M N x.spin y.spin (x.root-y.root) else 0 :=by
 rw [soarCost M a x y he hu]; unfold terraL; split; swap; · rfl
 simp_rw [golden M _ _ _ p v, Finset.mul_sum]; rw [sum_comm]; unfold CupM skyPrice chants; simp_rw [Finset.mul_sum]; refine sum_congr rfl fun i t=> sum_congr rfl fun j v=> ?_; simp only [charK,glen,micaO,add_zero]; change _= _*(_ * (mode (mel j) _ * _)); ring
#print axioms motor
lemma bells_flip {x y:Bite}(p:x.hand=false)(h:y.hand=true)(k:x.spin≠y.spin): bells M a y x= - bells M a x y:=by
 let Q:=trooper M a; let X:=x.loc N; let Y:=y.loc N; have hx:inner ℂ Y X=0:=by
    unfold X Y Bite.loc Lifted.basisC; rw [inner_smul_left,inner_smul_right,basis_inner,basis_apply,if_neg (show Lifted.index N y.root y.spin y.cost≠_ from fun z=>k (congr_arg (fun v:Single N=> v.1.2) z.symm))]; simp -- tune
 unfold bells Loaves.tooth paceSing; simp only [p,h,reduceCtorEq,↓reduceIte]; rw [act_sub,act_one,inner_sub_right]; rw [show inner ℂ (acts (star Q.buy) Y) (acts Q.sell X)=0 from ?_,zero_sub]; rw [act_inner,←act_mul,Q.pay,act_one,hx]
omit a in
lemma twoPair (x y:Bite)(d:Bite→Bite→ℂ):runes d [x,y]=d x y:=by simp [runes, spinC, offer, claps,picks, cites,besideX,Fock.cval,extendsU]
#print axioms pastoral
end YM.CF.Papyrus.Franc.SatinForce
