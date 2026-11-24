import YM.CF.Kea.Pale
import YM.CF.Reflect.Regular
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
def BallG(N:Side)(d:Candle)(i:Slot)(a:Axis):=pw (rise d i a)^N.val
lemma catchV (N:Side)(d:Candle)(a:Slot)(S:Slide N d)(x:Stag N)(u:x.2=a)(i:Axis):pw (angle S x i)^N.val=(-1:ℂ)*BallG N d a i:=by
 subst a; rw [←modal,←wage (peer_p S x) (step i),modal,Pi.add_apply,phase_a,mul_pow]
 unfold BallG; rw [show pw (pm x.1 i)^N.val=(-1:ℂ) by change BZ.phase (principal _)^_= _; rw [wind_eq,wind_p]]
def Shade(N:Side)(d:Candle):Prop:= ∀ i, BallG N d i 0 ≠-1 -- may prefer any
lemma height_d (d:Candle)(a:Axis)(h:∀ i,BallG N d i a≠-1)(S:Slide N d)(i:Stag N):angle S i a≠0:=by
 intro x; have he:=catchV N d _ S i rfl a; rw [x,phase_z,one_pow,neg_mul,one_mul] at he; exact h i.2 (by rw [←neg_inj]; exact he.symm.trans (by ring))

def skyV:TF:=⟨0,by simp⟩
def emptyC:Candle:=fun _=>skyV
lemma toll_e(N:Side)(a:Axis)(d:Candle)(h:d a=skyV)(i:Slot):BallG N d i a ≠ -1:=by unfold BallG rise; simp only [Pi.add_apply,pulse,h]; cases i with | mk a i=> cases i <;> norm_num [freqD,pw,BZ.phase,skyV]
def snapC(u:TF)(v:ℝ):TF:=⟨v • u.val,(by rw [Pi.smul_def]; simp only; rw [← Finset.smul_sum,u.property,smul_zero])⟩
def lease (X:Finset Axis)(P:Candle)(t:ℝ):Candle:=fun i=> if i∈X then snapC (P i) t else P i
lemma spark_c(U:TF):Continuous (snapC U):=Continuous.subtype_mk (by change Continuous fun t:ℝ => t • U.val; fun_prop) _
lemma lease_c(X:Finset Axis)(P:Candle):Continuous (lease X P):=by
 apply continuous_pi; intro i; by_cases h:i∈X; · simpa only [lease,h,ite_true] using spark_c (P i)
 simp only [lease,h,ite_false]; exact continuous_const
lemma lease_u(X:Finset Axis)(P:Candle):lease X P 1=P:=by funext i; apply Subtype.ext; by_cases h:i∈X<;>simp [h,lease,snapC]
lemma rent_t(N:Side)(X:Finset Axis)(P:Candle)(i:Axis)(h:i∈X)(v:Slot): AnalyticOnNhd ℝ (fun t=> BallG N (lease X P t) v i) Set.univ:=by
 have hp(t): rise (lease X P t) v i=t*rise P v i:=by obtain ⟨m,a|a⟩:=v<;> simp [rise,pulse,lease,h,snapC,freqD] <;> ring
 simp_rw [BallG,hp,pw,BZ.phase]; intro x _
 apply AnalyticAt.pow; simp_rw [Complex.exp_eq_exp_ℂ]; apply AnalyticAt.comp
 · exact NormedSpace.exp_analytic (𝕂:=ℝ) _
 exact ((Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.mul analyticAt_const)).mul analyticAt_const
lemma popC(X:Finset Axis)(P:Candle)(p:ℝ)(h:p<1)(a: Axis)(ha:a∈X):∃ t:ℝ,p<t ∧ t<1 ∧ ∀ i,BallG N (lease X P t) i a ≠ -1:=by
 let F(i:Slot)(t:ℝ):=BallG N (lease X P t) i a+1
 have ht:lease X P 0 a=skyV:=by unfold lease; rw [if_pos ha]; apply Subtype.ext; simp [skyV,snapC]
 have hh(i):AnalyticOnNhd ℝ (F i) Set.univ:=fun x hx=> (rent_t N X P a ha i _ hx).add analyticAt_const
 obtain ⟨t,u,r,v⟩:=RP.choose_price F hh (fun i H=>toll_e N a _ ht i (eq_neg_of_add_eq_zero_left H)) p 1 h
 refine ⟨t,u,r,fun i P'=>v i ?_⟩; unfold F; rw [P',neg_add_cancel]
end YM.CF.Kea
