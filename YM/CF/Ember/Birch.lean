import YM.CF.Ember.Pool
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
namespace Move
variable {ι:Type*}{t:Tax ι}{p:ι→ℂ→Momentum}(P:Move t p)
include P
lemma oneA (a:Axis) : Act t 1 fun i z=> p i z a:=P.act.via (ContinuousLinearMap.proj a)
lemma knot : Act t 2 fun i z=> prodM (p i z) (p i z):= by
 have H:=Act.finiteSum Finset.univ _ fun i h=> (oneA P i).mul (oneA P i)
 exact H -- tune
variable (M:ι→Side)(h:∀ i,Odd (M i).val)(j:ℕ)(hj:1≤j)
lemma dense (a:Axis):Act t 1 fun i z=> ds (M i) (p i z) a := P.freeze (ds_cost M a) (fun i=>by simp [ds,sine,narrow])
lemma deter (a:Axis):Act t 2 fun i z=> ds (M i) (p i z) a-p i z a:=by
 refine P.daze (f:=fun i z=> ds (M i) z a-z a) ((ds_cost M a).sub ?_) (fun i=>by simp [ds,sine,narrow]) ?_
 · refine ⟨zone,domainRadius,zone_pos,domainRadius_pos,fun i=>⟨fun x _=>by fun_prop,fun x hx=>?_⟩⟩; simpa using zone_in_disk x hx a
 intro i x; let c:ℂ:=(M i).val; have hc:c≠0:=by unfold c; exact_mod_cast (M i).property.ne'
 have ht:HasDerivAt (fun z:ℂ=> c⁻¹*(z*x a)) (c⁻¹*x a) 0:= by simpa using (((hasDerivAt_id' (0:ℂ)).mul_const (x a)).const_mul c⁻¹)
 have he:= (((Complex.hasDerivAt_sin _).comp (0:ℂ) ht).const_mul c).sub ((hasDerivAt_id' (0:ℂ)).mul_const (x a))
 change HasDerivAt (fun z:ℂ=>c*Complex.sin (c⁻¹*(z*x a))-z*x a) 0 0
 simp [Function.comp_def, ← mul_assoc,hc] at he ⊢; exact he
include h
lemma damp: Act t 2 fun i z=> D (M i) (p i z):=by
 let H(i:ι)(z:ℂ):=D (M i) (p i z)
 let K(i:ι)(z:ℂ):=Cminus (M i) (p i z)
 have hx: Act t 2 fun i z=> H i z*K i z:=by
   simp_rw [H,K, ← ds_sq,sq]; exact Act.finiteSum univ _ fun a _=>(dense P M a).mul (dense P M a)
 have hp:=P.freeze (D_cost M h) (fun i=>by norm_num [D,gD,rad,mag,kin,narrow,sine,pl]); let F:=fun i x=> Cminus (M i) x-2
 have hh:= P.freeze (f:=F) ((C_cost M h).sub (Moderate.const 2)) (fun i=>by norm_num [F,Cminus,rad,mag,kin,pl,sine,narrow])
 have he:=Act.lit (hx.sub (hp.mul hh)) (1/2:ℂ) -- maybe 1+1
 convert he using 1; ext1 i; ext1 z; unfold F H K; ring
lemma dote : Act t 3 fun i z=> D (M i) (p i z)-(1/2)*prodM (p i z) (p i z):=by
 let F:=fun i x=> Cminus (M i) x-2
 have hh:= P.freeze (f:=F) ((C_cost M h).sub (Moderate.const 2)) (fun i=>by norm_num [F,Cminus,rad,mag,kin,pl,sine,narrow]); let K i x:= D (M i) (p i x)
 have hy:Act t 3 fun i z=> K i z*(Cminus (M i) (p i z))-prodM (p i z) (p i z):=by
   simp_rw [K,← ds_sq,prodM,← sum_sub_distrib,sq]
   exact Act.finiteSum univ _ fun a _=>Act.diffM (a:=1) (oneA P a) (dense P M a) (deter P M a) (deter P M a)
 have he:= Act.lit (hy.sub ((damp P M h).mul hh)) (1/2:ℂ)
 convert he using 1; ext1 i; ext1 z; unfold F K; ring
include hj
lemma glass: Act t 2 fun i z=> shell j (M i) (p i z) := by simpa only [shell,div_eq_mul_inv,add_zero] using (damp P M h).mul (P.plunge (invMass j hj M h))
lemma quartz: Act t 3 fun i z=> shell j (M i) (p i z)-(1/4)*prodM (p i z) (p i z):=by
 let F:=fun i x=> (mass j (M i) x)⁻¹-1/2
 have hm:= P.freeze (f:=F) ((invMass j hj M h).sub (Moderate.const _)) (fun i=>by norm_num [F]) -- tune
 have h' :Act t 3 fun i z=> D (M i) (p i z)*((mass j (M i) (p i z))⁻¹)-((1/2)*prodM (p i z) (p i z))*(1/2):= Act.diffM (a:=1) (p:=2) (q:=0) (Act.lit P.knot _) (P.plunge (invMass j hj M h)) (P.dote M h) hm
 convert h' using 1; ext1 i; ext1 z; unfold shell; ring
lemma coldS (a:Axis): Act t 2 fun i z=> skin j (M i) (p i z) a-(1/2)*p i z a:=by
 let F:=fun i x=> bloom j (M i) x * (mass j (M i) x)⁻¹-1/2
 have hx:=P.freeze (f:=F) (by have hp:= (bloomPay j M h).mul (invMass j hj M h); simp only [mul_one] at hp; exact hp.sub (Moderate.const (1/2))) (fun i=>by norm_num [F,bloom,muff,narrow])
 have hz:= P.plunge (invMass j hj M h); have hg:= P.plunge (extras_pay j hj M h a); have hu:= (damp P M h).mul hz |>.mul hg
 have he:= Act.lit (deter P M a) (1/2:ℂ)
 have hl:= he.add (hx.mul (dense P M a)) |>.add hu
 convert hl using 1; ext1 i; ext1 z; unfold F skin; simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]; ring
end Move
end YM.CF.Ember
