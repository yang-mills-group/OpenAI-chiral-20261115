import YM.CF.BProof.Prox.Trace
import YM.CF.BProof.Gauss.Month

/- entropy charge root reset. D any index type (actual we will use atoms aggregated by
support already). On f!= 0 only. No entropy multiplier depending on spin-out. PT price. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Function Filter MeasureTheory Finset Prox Moment Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {D I J : Type*}[Fintype I][Fintype J]
variable (B:Prox.Base J)(f:I→ J)(S: D→ Finset I)(Z: D→ Finset J)(p:D→ℝ)
-- for |Z| ≤ A + K*|S|/r. K PL, r≥K. also α≥0. scale `Price` factors.
structure Factor (r A K:ℕ)(t α:ℝ) : Prop where
  pos : 0<r
  cost : K ≤ r
  t_pos : 0<t
  α_pos : 0≤α
  tariff : α*K ≤ t*r

abbrev table (b A K: ℕ)(α t:ℝ):= (((2*A+2)^b:ℕ):ℝ)* (Prox.trBill b K t)*(Real.exp (α*A)) -- trBill overpays by 2^b
lemma factor_table (b A:ℕ)(g:ℝ→ℕ)(p:ℝ→ℝ)(α:ℝ)(h:PL fun y=> (g y:ℝ))(u:PL (fun y=>(p y)⁻¹))(v:∀ y,0<p y)(q:∀ y,p y≤ 1): PL (fun y=> table b A (g y) α (p y)):=by
 let f(y:ℝ):= trBill b 1 (p y); have he:= Gauss.Month.tr_receipt b 1 p u v q; have hg(y:ℝ): trBill b (g y) (p y)=(g y:ℝ)*f y:=by unfold f trBill; ring
 unfold table; simp_rw [hg]; exact ((PL.mul (PL.const _) (h.mul he)).mul (PL.const _))

namespace Factor
variable (a J₀ r d:ℕ)(t α C:ℝ)(h:Factor r a d t α) (u:Toll S p (3*t) C)(v:0≤C)
variable (R:I→Prop)(hm:∀ j:J,(Finset.univ.filter fun i=> R i∧ f i=j).card≤ J₀)
variable (H:∀ i,p i≠0→ (Z i).card*r≤ a*r+d*(S i).card)
variable (L:∀ i,p i≠0 → B.C (Z i) ∧ ∃ j∈ S i, R j ∧ f j∈ Z i)
include hm
private lemma seats (o:J)(k:ℕ): let X:= univ.filter fun i=> R i∧ f i∈B.ball o k; X.card ≤ (2*k+1)^B.dim * J₀ := by
 let V:=B.ball o k; intro X
 let z(j:J):= univ.filter fun i=> R i ∧ f i=j; apply le_trans (b:=(V.biUnion z).card) (card_le_card (fun i (hi:i∈X)=>?_)); apply card_biUnion_le.trans; apply (sum_le_sum (fun i _=>hm i)).trans; rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (B.size ..); obtain ⟨l,v⟩:= (mem_filter.mp hi).2; exact mem_biUnion.mpr ⟨_,v,mem_filter.mpr ⟨mem_univ i,l,rfl⟩⟩ -- tune includes hm

omit hm
include h H
private lemma cost_size (i:D)(g:p i≠0): (Z i).card≤a+(S i).card:= by
 apply Nat.le_of_mul_le_mul_right _ h.pos; apply (H i g).trans; rw [add_mul]; exact Nat.add_le_add_left ((Nat.mul_le_mul_right _ h.cost).trans_eq (mul_comm ..)) _
lemma fee (i:D)(g:p i≠0): Real.exp (α*(Z i).card)≤ Real.exp (α*a) * Real.exp (t*(S i).card):=by
 let b:=(S i).card; have hv:(0:ℝ)<r:= Nat.cast_pos.mpr h.pos; have ht:0≤α:=h.α_pos; have hg: ↑(Z i).card*(r:ℝ) ≤ a*r+d*(b:ℝ):=by exact_mod_cast H i g -- Nat.cast weird
 rw [← Real.exp_add]; apply Real.exp_monotone; apply (mul_le_mul_iff_left₀ hv).mp; nlinarith only [hg,h.tariff, mul_le_mul_of_nonneg_right h.tariff (show 0≤ (b:ℝ) by positivity),mul_le_mul_of_nonneg_left hg ht]
include L u v hm
lemma grant : Toll Z p α (C*table B.dim a J₀ α t):=by
 let E:=Real.exp (α*a); let K:ℝ:= (((2*a+2)^B.dim:ℕ):ℝ) * ((2:ℝ)^B.dim*J₀*(t⁻¹^B.dim*B.dim.factorial*Real.exp t))
 have ht:= h.t_pos; have hk:0≤K:=by unfold K; positivity
 constructor; exact u.nonneg
 intro o
 rw [show C*_=(K*(C*E))*(1-Real.exp (-t))⁻¹ from ?_] -- tune
 swap; · unfold table trBill K E; ring
 apply budget_degrees (fun i=>(S i).card) (f:=hit Z p α o) (fun i=>by unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (u.nonneg i); exact le_rfl) (by unfold E; positivity : 0≤ K*(C*E)) (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
 intro n s hs; let X:=univ.filter fun i => R i ∧ f i∈ B.ball o (a+n); let T:=Real.exp (-(2*t*n))*E; have hT:0≤T:=by unfold T E; positivity
 have H'(i:D)(k:i∈s)(o':o∈Z i)(g:p i≠0): ∃ j∈ X,j∈ S i:=by obtain ⟨l,j,u,v,q⟩:= L i g; exact ⟨j,mem_filter.mpr ⟨mem_univ _,v,(B.ball_m ..).2 (B.mono (hs i k ▸ cost_size S Z p a r d _ _ h H i g) (B.dia l o' q))⟩,u⟩ -- tune shadow
 have P(i:D)(k:i∈s): hit Z p α o i ≤ ∑ j∈ X,T*hit S p (3*t) j i:=by
    have he(j:I):0≤T*hit S p (3*t) j i:= mul_nonneg hT ((u.pays j).1 i); unfold hit; split
    · rename_i q; by_cases g:p i=0; simp only [g,mul_zero,ite_self,sum_const_zero,le_refl]
      obtain ⟨j,hj,v⟩:= H' i k q g; apply le_trans _ (single_le_sum (f:=fun j=>T*hit S p (3*t) j i) (fun j _=>he j) hj); unfold hit; rw [if_pos v,← mul_assoc]; refine mul_le_mul_of_nonneg_right ((fee _ _ p a r d t α h H i g).trans ?_) (u.nonneg i); unfold T; rw [mul_comm _ E,mul_assoc, ←Real.exp_add, hs i k]; ring_nf -- tune
      unfold E; rw [←Real.exp_add,←Real.exp_add]; ring_nf; exact le_rfl
    exact sum_nonneg (fun i _=> he i)
 apply (sum_le_sum P).trans; rw [sum_comm]; simp_rw [← mul_sum]; rw [mul_sum]; apply (sum_le_sum (g:=fun _=>T*C) (fun i _=>mul_le_mul_of_nonneg_left (budget_sum (u.pays i) _) hT)).trans; rw [sum_const,nsmul_eq_mul]
 have he: (X.card:ℝ) ≤ (((2*a+2)^B.dim:ℕ):ℝ) * ((2:ℝ)^B.dim * J₀* (1+(n:ℝ))^B.dim):=by
    have hh : 2*(a+n)+1 ≤ (2*a+2)*(2*(1+n)) := by nlinarith
    have hr : (2*(a+n)+1)^B.dim*J₀ ≤ ((2*a+2)*(2*(1+n)))^B.dim*J₀:=by gcongr
    have hv : X.card≤(2*a+2)^B.dim*(2^B.dim*J₀*(1+n)^B.dim):= (seats B f J₀ R hm o (a+n)).trans (hr.trans_eq (by rw [mul_pow,mul_pow (2:ℕ)]; ring))
    exact_mod_cast hv
 let f:=Real.exp (t*n); have hv':0≤T*C:=mul_nonneg hT v; calc
   _ ≤ (K*f)*(T*C):=mul_le_mul_of_nonneg_right (he.trans (by unfold K; rw [mul_assoc (Nat.cast ((2*a+2)^B.dim):ℝ) _ f,mul_assoc (2^_* J₀:ℝ) _ f]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact mul_le_mul_of_nonneg_left (polynomial_cost (p:=(n:ℝ)) ht (by positivity) _) (by positivity))) hv'
   _ ≤ _:= by unfold f T; rw [show K*Real.exp (t*n)*(Real.exp (-(2*t*n))*E*C)=K*(C*E)*(Real.exp (t*n)*Real.exp (-(2*t*n))) by ring, ←Real.exp_add,← Real.exp_nat_mul]; ring_nf; exact le_rfl
end Factor
end YM.CF.BProof.Mapping
