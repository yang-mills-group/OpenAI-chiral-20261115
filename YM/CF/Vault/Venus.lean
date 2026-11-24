import YM.CF.Vault.Visa
import YM.CF.Dial.Moose
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {ι:Type*}{L N P:Side}(ho:Odd L.val){A B R:Chop ι}{u t:Bool}
private lemma rate_zero(q:TickZ): ‖((q.val/2:ℝ):ℂ)‖≤ 1:=by rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg q.property.1 (by norm_num))]; exact (div_le_self q.property.1 (by norm_num)).trans q.property.2
abbrev ℒ(u:Bool):AxisT:=(u,true)
-- deform by approximate equivariance up to antisymmetric quaternion at real end.
def twinX (A B C:Chop ι): Chop (ι×TickZ):=fun i _ _ G x=>
 let t:ℂ:= ((i.2.val/2:ℝ):ℂ); let F:=A i.1 G x
 F+t • (B i.1 G x*cc (A i.1 G (chargeB x))*star (C i.1 G (chargeB x))- F)
lemma twist_X(p:BoxD L (ℒ u) (ℒ t) A)(q:BoxD L (ℒ u) (upright (ℒ u)) B)(v:BoxD L (ℒ t) (upright (ℒ t)) R): BoxD L (ℒ u) (ℒ t) (twinX A B R):= (p.reindex Prod.fst).add ((((q.chain p.abrade).chain v.balm).sub p).reindex Prod.fst|>.scale (fun i=> ((i.2.val/2:ℝ):ℂ)) _ fun i=> rate_zero i.2)
def scrap (b:Bool)(A:Chop ι): Chop (ι × TickZ):=fun i _ _ G x=>  (2:ℂ) • twinX A (rentD b) (rentD b) i G x-1
def paddle (b:Bool)(A:Chop ι): Chop (ι × TickZ):=fun i _ _ G x=> projector (scrap b A i G x)
section
variable {α:Type*}[Fintype α][DecidableEq α][Nonempty α]
def royal (P:Op α):Op α := (2:ℂ) • P-1
lemma royal_sq {P:Op α}(h:IsStarProjection P): royal P ^2=1:=by unfold royal; simp only [sq,sub_mul,mul_sub, Matrix.smul_mul,one_mul,mul_one,Matrix.mul_smul,h.isIdempotentElem.eq]; module
lemma royal_safe {P:Op α}(h:IsStarProjection P):Safe (royal P) :=by
 have he:= royal_sq h; have hp:IsSelfAdjoint (royal P):=by rw [isSelfAdjoint_iff,royal,star_sub,star_smul,h.isSelfAdjoint.star_eq]; simp
 refine ⟨hp,?_,?_⟩
 · have hk: ‖star (royal P)*royal P‖=‖royal P‖*‖royal P‖:= CStarRing.norm_star_mul_self; rw [hp,←sq, he,norm_one] at hk; nlinarith
 rw [he]; exact smul_le_of_le_one_left (by exact zero_le_one) (by norm_num) -- tune
lemma royal_c {P:Op α}(h:IsStarProjection P): projector (royal P)=P:=by
 rw [projector,polarity_scalar (royal_safe h) 1 (by norm_num) (by simpa only [sq,one_pow,one_mul,one_smul] using royal_sq h)]; norm_num; unfold royal; -- ℂ vs ℝ
 rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; norm_num; module
end
variable (Q:BoxD L (ℒ u) (ℒ u) A)
abbrev vacantR (G:Ratio N P)(i:ι){A:Chop ι}:=A i G (vacancyY N P)
def Atrest (L:Side)(A:Chop ι): Prop:=∀ i {N P:Side}(G:Ratio N P),G.count=L→
 IsStarProjection (vacantR G i (A:=A)) ∧ vacantR G i (A:=A) *helmC G=helmC G*cc (vacantR G i (A:=A))
variable (BB:Atrest L A)
lemma version (i:ι×TickZ)(G:Ratio N P)(F E X:Chop ι) (U T:Op (Iota G))(k:U*cc (X i.1 G (vacancyY N P))=X i.1 G (vacancyY N P)*T)(p:T∈unitary _)(b:vacantR G i.1 (A:=F)=U)(y:vacantR G i.1 (A:=E)=T): twinX X F E i G (vacancyY N P)=vacantR G i.1 (A:=X):=by
 unfold twinX; rw [show chargeB (vacancyY N P)=vacancyY N P from charge_p _]; dsimp only
 unfold vacantR at *; rw [b,y,k,mul_assoc _ T,p.2,mul_one,sub_self,smul_zero,add_zero] -- charge snippet
include BB
lemma reserve_c (b:Bool)(i:ι×TickZ)(G:Ratio N P)(p:G.count=L): vacantR G i (A:=scrap b A)= royal (vacantR G i.1 (A:=A)):=by
 let C:=vacantR G i.1 (A:=rentD b); let V:=vacancyY N P
 have ht:C=helmC G:= helm_eq G b
 have hv:twinX A (rentD b) (rentD b) i G V=vacantR G i.1 (A:=A):=version i G (rentD b) (rentD b) A _ _ ((BB i.1 G p).2.symm) (ht ▸ unit_square G b _) ht ht -- tune
 unfold vacantR scrap; rw [hv]; rfl
lemma pad_f (u:Bool)(i:ι×TickZ)(G:Ratio N P)(p:G.count=L): vacantR G i (A:=paddle u A)=vacantR G i.1 (A:=A):=by
 unfold vacantR paddle; rw [show scrap u A i G _=_ from reserve_c BB u i G p]; exact royal_c (BB i.1 G p).1
abbrev oneL :TickZ:=⟨1,Set.right_mem_Icc.mpr zero_le_one⟩
abbrev noneL : TickZ:=⟨0,Set.left_mem_Icc.mpr zero_le_one⟩
omit BB
include Q ho
lemma pad_top:BoxD L (ℒ u) (ℒ u) (scrap u A):=by
 have hq: BoxD L (ℒ u) (upright (ℒ u)) (rentD u (ι:=ι)):=tablesB _ u L ho
 exact ((twist_X Q hq hq).scale (fun _=> (2:ℂ)) ‖(2:ℂ)‖ (fun i=> le_rfl)).sub BoxD.one
include BB
lemma pad_money: BoxD L (ℒ u) (ℒ u) (paddle u A):=by
 let F:=scrap u A; have hp:=pad_top ho Q
 let X:Chop (ι×TickZ):=fun i c f G x=> slack (F i G x)
 have ht: BoxD L (ℒ u) (ℒ u) X:=by
    unfold X slack; simp_rw [sq,show ∀ (N P:Side)(G:Ratio N P)(t:Op (Iota G)),(1/256:ℝ) • t=((↑(1/256:ℝ):ℂ)) • t from fun _ _ _ t=> by ext; simp [Complex.real_smul]]
    exact BoxD.one.sub ((hp.chain hp).scale (fun _=>_) _ (fun i=> le_rfl))
 obtain ⟨a,C,e,p,pC,k,v,W⟩:=ht
 obtain ⟨d,m,K,Y,h,q,-,hK,hY,hL,t,M⟩:=awaken W p pC k rho_pos rho_lt (fun i _ _ G he hv=> by unfold X; rw [show F i G _=_ from reserve_c BB u i G he]; exact (royal_safe (BB i.1 G he).1).good)
 let f(k:ℕ):= K*Y^k; have hh:Summable f:= (summable_geometric_of_lt_one hY.le hL).mul_left K
 have hj:BoxD L (ℒ u) (ℒ u) (fun i _ _ G x=>rsEval (F i G x)):=by
    refine boxify (k:=t) (C:=∑' k,f k) (fun i _ _ G he hv=>?_ ) h q
    unfold rsEval; apply Crown.tsK f _ h.le hh; intro j; have ht:= (M j i G he hv).scale (SignScalar.c j:ℂ)
    simp_rw [Complex.norm_real] at ht; apply Crown.books _ (mul_le_of_le_one_left _ (SignScalar.c_norm j)); swap; positivity
    convert ht using 1; ext; simp [rsTerm,X,Complex.real_smul]
 have hc {t:ℝ}{P:Chop (ι× TickZ)} (h:BoxD L (ℒ u) (ℒ u) P): BoxD L (ℒ u) (ℒ u) (fun i _ _ G x=> t • P i G x):=by
    simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact h.scale _ _ (fun i=> le_rfl)
 exact hc (BoxD.one.add ((hc hp).chain hj))
end YM.CF.Vault
