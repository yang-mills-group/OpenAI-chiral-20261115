import YM.CF.Leaf.Stone
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Leaf
open Function NormedSpace Fock Pastry Tap Sault Cadre Matrix Palot MeasureTheory Filter
open Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι σ α I:Type*}[LinearOrder ι][Fintype ι][LinearOrder I][Fintype I]
lemma e_spin (A:FC ι)(t:ℝ): Commute A (exp (t • A)):=by
 letI : NormedAlgebra ℚ (FC ι):= NormedAlgebra.restrictScalars ℚ ℝ (FC ι); exact ((Commute.refl _).smul_right _).exp_right
lemma earn_T(A:FC ι)(t:ℝ): HasDerivAt (fun x:ℝ=> exp (-x • A)) (-(exp (-t • A)*A)) t:=by simpa only [Function.comp_def,neg_smul,one_smul] using ((hasDerivAt_exp_smul_const A (-t:ℝ)).scomp t ((hasDerivAt_id' t).neg)) -- issue simp lhs function comp not unfolds
abbrev era_L (A B:FC ι)(t:ℝ):= exp (-t • B) * A*exp (t • B)
lemma ht_T(A B:FC ι)(t:ℝ): HasDerivAt (era_L A B) (era_L (bump A B) B t) t:=by
 apply (((earn_T B t).mul_const A).mul (hasDerivAt_exp_smul_const B t)).congr_deriv
 let L(s:ℝ):= exp (s • B); change -(L (-t)*B)*A* L t+ L (-t)*A*(L t*B)= _; rw [←(e_spin B t).eq]; unfold era_L bump; change _= L (-t)*(A*B-B*A)*L t; rw [mul_sub, sub_mul]; simp only [neg_mul,mul_assoc]; abel
private lemma tide{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E](F Y:ℝ→E)(G:ℝ→E)(p:∀ t,HasDerivAt F (Y t) t)(q:∀ t, HasDerivAt G (Y t) t)(z:F 0=G 0): F=G:=by
 funext t; let L:= F-G; have hp:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (f:=L) (f':=fun _=>0) (fun i _=>by simpa only [sub_self] using HasDerivAt.sub (p i) (q i)) (by exact intervalIntegrable_const); change _= F t-G t-(F 0-G 0) at hp; simpa [z, eq_comm,sub_eq_zero] using hp -- orientation
lemma Yz_h(A:FC ι)(X:Dough ι)(p:rank2 A): A*(exp X).val=(exp X).val *(A+bump A X.val+(2:ℝ)⁻¹ • bump (bump A X.val) X.val):=by
 let B:=X.val; let L:= bump A B; let C:= bump L B
 have he(u:FC ι): era_L u B 0=u:=by simp [era_L]
 have hv: era_L C B=fun _=>C:= tide _ (fun _=>0) _ (fun i=>by simpa only [C,L,B,p, era_L, mul_zero,zero_mul] using (ht_T C B i)) (fun _=>hasDerivAt_const ..) (he _) -- comp not syntax
 have ht:era_L L B=fun t=> L + t • C:=by
    apply tide _ (fun _=>C); · intro t; apply (ht_T L B t).congr_deriv; exact congrFun hv t
    · intro t; exact (by simpa only [one_smul] using (((hasDerivAt_id' t).smul_const C).const_add L))
    rw [he,zero_smul, add_zero]
 have hK:era_L A B=fun t=>A+t • L+(t*t/2) • C:=by
    apply tide _ (fun t=>L+t • C); · intro i; apply (ht_T A B i).congr_deriv; exact congrFun ht i
    · intro t; let f:=hasDerivAt_id' t; have hu: HasDerivAt (fun t:ℝ=>t*t/2) t t:=by apply ((f.mul f).div_const (2:ℝ)).congr_deriv; ring
      apply (((f.smul_const L).const_add A).add (hu.smul_const C)).congr_deriv; rw [one_smul]
    rw [he,zero_smul,add_zero,zero_mul, zero_div,zero_smul,add_zero]
 letI:NormedAlgebra ℚ (Dough ι):= NormedAlgebra.restrictScalars ℚ ℝ (Dough ι); letI:NormedAlgebra ℚ (FC ι):= NormedAlgebra.restrictScalars ℚ ℝ (FC ι)
 rw [show A+bump A _+_=era_L A X.val 1 from (by change A+L+_ = era_L A B 1; rw [hK]; simp only [one_smul,one_mul,one_div]; rfl),show (exp X).val=exp X.val from map_exp (Dough ι).val continuous_subtype_val X]; unfold era_L; rw [one_smul,neg_smul,one_smul, ←mul_assoc,←mul_assoc,←NormedSpace.exp_add_of_commute (Commute.refl _|>.neg_right),add_neg_cancel,NormedSpace.exp_zero,one_mul] -- tune
-- ∆ tag realization. control finite endpoints.
def hushV(X:Wave I): FC I →L[ℂ] Wave I:= (show FC I→ₗ[ℂ] Wave I from ⟨⟨fun V=> acts V X,fun _ _=>act_add .. ⟩,fun t v=> act_smul .. ⟩).toContinuousLinearMap
theorem rock_V (U:Wave ι→L[ℂ]Wave I)(A:FC ι)(B:FC I)(p:rank2 A)(t:∀ x:Wave ι, U (acts A x)=acts B (U x))(F Y:ℝ→Dough ι)(q:∀ i∈Set.Icc (0:ℝ) 1, HasDerivAt F (Y i) i)(z:∀ i∈Set.Icc (0:ℝ) 1,(Y i).val=Sault.rind (A+bump A (F i).val+(2:ℝ)⁻¹ • bump (bump A (F i).val) (F i).val)): U (acts (exp (F 1)).val (vacuum ι))=acts (exp B) (U (acts (exp (F 0)).val (vacuum ι))):=by
 let v:= vacuum ι; let G(i:ℝ):= U (acts (exp (F i)).val v); let H(i:ℝ):= acts (exp (-i • B)) (G i); let Φ:=(U.restrictScalars ℝ).comp Cadre.pea
 have hk: G=fun t=>Φ (exp (F t)):=rfl; have hu(i:ℝ)(p':i∈Set.Icc (0:ℝ) 1) :HasDerivAt G (acts B (G i)) i:=by
    let g:=F i; let y:= Y i
    have hv:= (hasFDerivAt_exp (𝕂:=ℝ) (x:=g)).comp_hasDerivAt i (q i p') -- expects x=F i
    rw [hk]
    apply ((Φ.hasFDerivAt).comp_hasDerivAt i hv).congr_deriv
    change U (acts (exp g*y).val v)= (acts B) (U (acts (exp g).val v)) -- tune
    rw [←t,Subalgebra.coe_mul,act_mul,←act_mul A _,Yz_h A g p]; rw [show y.val=_ from z i p', Sault.tileL,act_mul] -- tune
 have hv(i:ℝ)(p:i∈Set.Icc (0:ℝ) 1):HasDerivAt H 0 i:=by
    let P: FC I →L[ℝ] (_ →L[ℂ] Wave I):=((show FC I→ₗ[ℝ] (Wave I →L[ℂ] Wave I) from ⟨⟨acts,fun A B=>ContinuousLinearMap.ext (act_add A B)⟩,fun t v=>ContinuousLinearMap.ext fun x=> Pastry.actReal v t _⟩).toContinuousLinearMap)
    let Q:= (show (Wave I →L[ℂ] Wave I)→L[ℝ] (Wave I→L[ℝ]Wave I) from ((show (Wave I →L[ℂ] Wave I)→ₗ[ℝ] (Wave I→L[ℝ]Wave I) from ⟨⟨fun v=>v.restrictScalars ℝ,fun _ _=>rfl⟩,fun _ _=>rfl⟩).toContinuousLinearMap)).comp P
    apply ( ((Q.hasFDerivAt.comp_hasDerivAt i (earn_T B i))).clm_apply (hu i p)).congr_deriv
    let T:= exp (-i • B); change acts (-(T*B)) (G i) + acts T (acts B (G i))=0; simp only [act_neg,act_mul]; abel -- tune clm syntax
 have ht:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (f:=H ) (f':=fun _=>0) (fun i h=> hv i (Set.uIcc_of_le (show (0:ℝ)≤1 from zero_le_one) ▸ h)) (by exact intervalIntegrable_const)
 have h': H 1= G 0:=by rw [←show H 0=G 0 from (by simp [H,act_one])]; apply sub_eq_zero.mp; simpa only [intervalIntegral.integral_zero] using ht.symm
 change G 1= _; change G 1= acts (exp B) (G 0); rw [←h']; unfold H; rw [neg_smul,one_smul, ←act_mul]; letI:NormedAlgebra ℚ (FC I):= NormedAlgebra.restrictScalars ℚ ℝ _; rw [←NormedSpace.exp_add_of_commute (Commute.refl _|>.neg_right),add_neg_cancel,NormedSpace.exp_zero,act_one]
end YM.CF.Leaf
