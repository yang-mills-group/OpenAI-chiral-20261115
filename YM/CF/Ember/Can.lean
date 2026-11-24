import YM.CF.Ember.Birch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (n:Type*)[Fintype n][DecidableEq n]
abbrev coneA:=SpinIdx×n
def Lent (p:Momentum): Op (coneA n) := ((1/2:ℂ) • (Aop*zen p)) ⊗ₖ 1
def fuel (j:ℕ)(M:Side)(p:Momentum): Op (coneA n) := (Aop*bar j M p) ⊗ₖ 1
def bins : Op (coneA n):= Aop ⊗ₖ 1
def edgeH(j:ℕ)(M:Side)(p:Momentum):Op (coneA n):=(shell j M p)⁻¹ • bins n
def tipH(p:Momentum):Op (coneA n):= ((1/4)*(prodM p p))⁻¹ • bins n
lemma fuel_p(j:ℕ)(M:Side)(h:Odd M.val)(p:Momentum)(e:p∈realCube zone): fuel n j M p *star (fuel n j M p)=shell j M p • bins n:=by
 unfold fuel bins; rw [op_star_kron,star_mul,star_one,op_kron_mul,Aadj,(firm_bar j M h e).2]
 rw [← Matrix.smul_kronecker,mul_assoc, ← mul_assoc (bar j M p),(firm_bar j M h e).1, ← mul_assoc _ _ Aop]
 rw [(bar_side j M e).1]; rw [Matrix.smul_mul,mul_add,mul_one,add_mul,AOne,zenA,mul_assoc _ (1-Aop),sub_mul,AOne,one_mul,sub_self,mul_zero,add_zero,mul_one]
lemma binsSq: bins n*bins n=bins n:=by rw [bins,op_kron_mul,AOne,mul_one]
lemma binsAdj:star (bins n)=bins n:=by rw [bins,op_star_kron,Aadj,star_one]
lemma binsF (j M p):bins n*fuel n j M p= fuel n j M p:=by rw [bins,fuel,op_kron_mul,← mul_assoc,AOne,mul_one]
section mov
variable {ι:Type*}{t:Tax ι}{p:ι→ℂ→Momentum}
lemma kronact {F:ι→ℂ→Op SpinIdx}{s:ℤ}(T:Op n)(h:Act t s F):Act t s fun i z=> F i z⊗ₖ T:=by
 let L:Op SpinIdx→ₗ[ℂ] Op (coneA n):= { toFun:=fun f=> f⊗ₖ T,map_add':=fun a b=>Matrix.add_kronecker ..,map_smul':=fun b x=>Matrix.smul_kronecker .. }
 exact h.via L.toContinuousLinearMap
namespace Move
variable (P: Move t p)
include P
lemma pulseL: Act t 1 fun i z=> Lent n (p i z):=by
 have ht:= Act.finiteSum (p:=1) univ _ (fun a _ => (oneA P a).smul (Act.anchor t (Complex.I • gammaOp a)))
 apply kronact; exact (Act.anchor t (1/2:ℂ)).smul ((Act.anchor t Aop).mul ht)
variable (M:ι→Side)(h:∀ i,Odd (M i).val)(j:ℕ)(hj:1≤j)
include hj h
lemma sap : Act t 2 fun i z=> fuel n j (M i) (p i z)-Lent n (p i z):=by
 have hk:Act t 2 fun i z=> zen (skin j (M i) (p i z))-(1/2:ℂ) • zen (p i z):=by
   simp_rw [zen,Finset.smul_sum,← sum_sub_distrib,smul_smul (1/2:ℂ),← sub_smul]; exact Act.finiteSum univ _ (fun a _=>(coldS P M h j hj a).smul (Act.anchor t (Complex.I • gammaOp a)))
 have he:=Act.add (p:=2) ((P.glass M h j hj).smul (Act.anchor t Aop)) ((Act.anchor t Aop).mul hk)
 have hp:= kronact n 1 he
 convert hp using 1; ext1 i; ext1 z; unfold Lent fuel
 let a:=bar j (M i) (p i z)
 rw [show ((Aop*a) ⊗ₖ (1:Op n))- _=(Aop*a-(1/2:ℂ) • (Aop*zen (p i z))) ⊗ₖ 1 from ?_]; swap
 · simp_rw [sub_eq_add_neg, Matrix.add_kronecker,op_kron_neg]
 congr 1
 simp only [a,bar,mul_add,mul_sub,Matrix.mul_smul,mul_one, ← mul_assoc Aop grading _, show Aop*grading=Aop from (BZ.atom 0).plusChir]; module
lemma fossil : Act t 1 fun i z=> fuel n j (M i) (p i z):=by
 have ht:= ((P.sap n M h j hj).loose (by decide : (1:ℤ)≤2)).add (P.pulseL n); simpa only [sub_add_cancel] using ht
end Move
end mov
open Stationary
lemma xMaps(x:Gaia): lengthSq (axes (exileE x))=‖x‖^2:=by simp only [lengthSq,axes,Complex.norm_real, Real.norm_eq_abs,sq_abs]; exact geode_sum _
lemma xParity(x:Gaia): prodM (axes (exileE x)) (axes (exileE x))=((‖x‖^2:ℝ):ℂ):=by rw [prodM_self (axes (exileE x)) (show physical (axes (exileE x)) from tmap_physical _),← geode_sum x]; rfl
namespace Move
variable {ι:Type*}{t:Tax ι}{p:ι→ℂ→Momentum}(P:Move t p)(M:ι→Side)(h:∀ i,Odd (M i).val)(j:ℕ)(hj:1≤j)(x:ι→Gaia)(v:∀ i,p i 0=axes (exileE (x i)))(e:∀ i,t.r i= ‖x i‖)(g:∀ i,x i∈ boundsEarth)
include v e g h hj
lemma chill_mag:∃ C:ℝ,0<C∧∀ i,C*(t.r i)^(2:ℤ)≤‖shell j (M i) (p i 0)‖:=by
 obtain ⟨a,C,ha,hc,H⟩:=massPay j hj M h; have ht:=meter.low_pos; refine ⟨(1/2*meter.low^2)/C,by positivity,fun i=>?_⟩
 have hp : p i 0∈baseCube:=by rw [v]; exact ⟨tmap_physical _,cradleFront _ (g i)⟩ -- tune
 have he:= D_lower (M i) hp.1; rw [shell,norm_div]
 have hm:=mass_ne j (M i) (h i) (base_subset_realCube zone_pos hp)
 have hx:= t.pos i
 have hf : ‖mass j (M i) (p i 0)‖≤ C:=by simpa using (H i).bound _ (mem_cube_real (base_subset_realCube ha hp) ha)
 have hk := (mul_le_mul_of_nonneg_left (divisor_real_bounds (M i) (base_subset_realCube zone_pos hp)).1 (show (0:ℝ)≤1/2 by norm_num)).trans (he.trans (Complex.re_le_norm _))
 rw [v i,xMaps,← e] at hk
 rw [le_div_iff₀ (norm_pos_iff.mpr hm)]; refine (mul_le_mul_of_nonneg_left hf (by positivity : 0≤ 1/2*meter.low^2/C*(t.r i)^(2:ℤ))).trans ?_; rw [show (1/2*meter.low^2/C)*(t.r i)^(2:ℤ)*C=(1/2)*(meter.low^2*(t.r i)^2) from ?_]
 · rw [v i]; exact hk
 rw [_root_.zpow_ofNat]; field_simp
include P
lemma moisten : Act t (-2) fun i z=> edgeH n j (M i) (p i z) :=
 ((P.glass M h j hj).inv (chill_mag M h j hj x v e g)).smul (Act.anchor t _)
omit h hj g in -- fix
lemma firmV(i:ι): (1/4)*(t.r i)^(2:ℤ)≤ ‖(1/4)*(prodM (p i 0) (p i 0))‖:=by
 have he:= t.pos i; rw [v,xParity,← e,_root_.zpow_ofNat]; rw [show (1/4:ℂ)=((1/4:ℝ):ℂ) by norm_num,← Complex.ofReal_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
lemma chillL : Act t (-1) fun i z=> edgeH n j (M i) (p i z)-tipH n (p i z):=by
 obtain ⟨D,hd,H⟩:= chill_mag M h j hj x v e g
 have hp:= Act.inv_gap (P.glass M h j hj) (Act.lit P.knot (1/4)) (P.quartz M h j hj) hd (show (0:ℝ)<1/4 by norm_num) H (firmV P x v e)
 unfold edgeH tipH; simp_rw [← sub_smul]; convert hp.smul (Act.anchor t _) using 1; norm_num
end Move
end YM.CF.Ember
