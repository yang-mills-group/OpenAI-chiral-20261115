import YM.CF.BProof.Stint.Earn
import YM.CF.BProof.Moment.Priced

/-! Diagonal trace to a scalar-price anchoring. Keep the root exactly for each diagonal
site, working equally through diagonal groups of sites with Board tag block not finer. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch MeasureTheory Push.AbsoluteSums
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {D G Y I: Type}[Fintype I][DecidableEq I][Fintype Y][DecidableEq Y][TopologicalSpace D]
def peak (b:Stage Y I D G)(o:Y)(A:Op I):= (strip b {o} * A).trace
lemma peak_eq (b:Stage Y I D G)(o:Y)(A:Op I): peak b o A= ∑ i∈ board b {o},A i i:=by unfold peak Matrix.trace; simp only [Matrix.diag_apply,stripL,board,sum_filter] -- tune
lemma fullTrace (b:Stage Y I D G)(A:Op I): Matrix.trace A=∑ o:Y,peak b o A:=by simp_rw [peak_eq,board,sum_filter]; rw [sum_comm]; simp; rfl
structure Ticker (b:Stage Y I D G)(A:Raw D I) where
 line:Y× Seal Y→ D→ℂ
 pay:Y× Seal Y→ℝ
 taxes(i:Y×Seal Y): Element b i.2 (pay i) (line i)
 loc (i:Y×Seal Y)(u:pay i≠0): i.1∈i.2 ∧ ∃ j:I,b.home j=i.1
 book (o:Y)(d:D): peak b o (A d)=∑ T:Seal Y, line (o,T) d
variable {b: Stage Y I D G}{x:Tag b}{p:Pay}{A:Raw D I}{C:ℝ}
def vaultPay (p:Pay)(C:ℝ):= (∑' i:ℕ, Real.exp (-p.rate/2*i)*(C*((i:ℝ)+1)^4))*p.cash
lemma tickable (e:0≤C)(h:Capacity b C) (u:Earn p x x A): ∃ y:Ticker b A, Moment.Toll Prod.snd y.pay (p.rate/2) (vaultPay p C):=by
 obtain ⟨F,W,L,V,s⟩:=u; let N(i:Y×Seal Y):= ∑ j∈ board b {i.1}, W i.2 j j; let G'(i:Y×Seal Y)(x:D):=peak b i.1 (F i.2 x); have ht(i:Y×Seal Y)(q:N i≠0): Grove b.F i.2 ∧ i.1∈i.2 ∧ ∃ j:I,b.home j=i.1:=by obtain ⟨k,v,h⟩:= exists_ne_zero_of_sum_ne_zero q; have he:b.home k=i.1:= mem_singleton.mp (mem_filter.mp v).2; obtain ⟨j,t,-⟩:= ((L i.2).expo k k).triggered h; exact ⟨j,he ▸ t,k,he⟩ -- flatten tune
 have hx(i:Y×Seal Y):0≤N i:=sum_nonneg fun i _=> (L _).nonn i i; let E:Ticker b A:={
    line:= G', pay:= N
    taxes i:= ⟨hx i,fun q=>(ht i q).1,fun t l=> (by unfold G' peak; rw [(L i.2).frame.frame,←mul_assoc,←mul_assoc,strip_tag,mul_assoc _ (strip b _),Matrix.trace_mul_comm,←mul_assoc (_:Op I) ((x.run t).val),(x.run t).property.1,one_mul]),((continuous_const.mul (L i.2).cont).matrix_trace),fun x=> (by unfold G'; rw [peak_eq]; exact (norm_sum_le ..).trans (sum_le_sum fun j _=> ((L _).expo _ _).bounded _)),fun a c=>by unfold G'; rw [peak_eq,peak_eq,←sum_sub_distrib]; unfold N; rw [sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun j _=> ((L _).expo _ _).variation a c) ⟩
    loc i q:= (ht i q).2
    book i d:= (by unfold G'; rw [s d,peak,Matrix.mul_sum,Matrix.trace_sum]; rfl) }
 refine ⟨E,hx,fun i=>?_⟩; let f(j:Y×Seal Y):=Moment.hit Prod.snd E.pay (p.rate/2) i j; have he(j:Y×Seal Y): 0≤ f j:=by unfold f Moment.hit; split; exact mul_nonneg (Real.exp_pos _).le (hx _); exact le_rfl
 refine ⟨he, Summable.of_finite,?_⟩; change ∑' j,f j≤_; rw [tsum_fintype,Fintype.sum_prod_type, sum_comm]; refine le_trans ?_ (tall L V p.charge h e i); unfold hitE hit0; rw [sum_filter]; refine sum_le_sum fun k _=> ?_; by_cases H:i∈k; swap; · simp [f,Moment.hit,H]
 rw [if_pos H]; simp only [f,Moment.hit,H,↓reduceIte]; rw [←mul_sum]
 have hp: ∑ j:Y, N (j,k)=∑ j:I,W k j j:= by unfold N; simp_rw [board,sum_filter]; rw [sum_comm]; simp
 refine mul_le_mul_of_nonneg_left (show ∑ j:Y,N (j,k) ≤ ledgerV (W k) from hp.trans_le (sum_le_sum fun i _=> single_le_sum (f:= W k i) (fun j _=>(L k).nonn i j) (mem_univ i))) (Real.exp_pos _).le
end YM.CF.BProof.Stint
