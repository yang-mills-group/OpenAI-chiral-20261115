import YM.CF.Fir.Elder
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (u:Bool)(j:ℕ)(L M:Side)(hj:Even j)(ho:Odd L.val)(he:Odd M.val){p:Momentum}
def born (p:Momentum): Stk L:=stack L fun i=> bent u j M (aliasAt p i)
def tall : Stk L:= sA u L*(1-peb L)
def grow (p:Momentum): Stk L:=spike L (bent u j (L*M) p)
def vine (p:Momentum): Stk L:= tall u L+grow u j L M p
def tower (p:Momentum): Stk L:= col L (fun l=> arm u j L M l p)
lemma high_tall : tall u L= (1-peb L)*sA u L:=by rw [tall, sub_mul,mul_sub,one_mul,mul_one,pebSlate]
lemma tall_peb : tall u L*peb L=0:=by rw [tall,mul_assoc,sub_mul,one_mul,peb_sq,sub_self,mul_zero]
lemma peb_tall : peb L*tall u L=0:=by rw [high_tall,← mul_assoc,mul_sub,mul_one,peb_sq,sub_self,zero_mul]
lemma tall_s : sA u L*tall u L=tall u L:=by rw [tall,← mul_assoc,slate]
lemma tall_s' : tall u L*sA u L=tall u L:=by rw [high_tall,mul_assoc,slate]
lemma tall_sq : tall u L*tall u L=tall u L:=by
  conv_lhs=>lhs;rw [high_tall]
                                                         -- edit
  rw [mul_assoc,tall_s,sub_mul,peb_tall,one_mul,sub_zero]
lemma grow_c (p:Momentum): peb L*grow u j L M p=grow u j L M p ∧ grow u j L M p*peb L=grow u j L M p:=by simp [peb, grow,spike_times]
lemma b_p {L:Side}(hp:p∈realCube zone)(h: Odd L.val): bent u j L p*bent u j L p=bent u j L p ∧ star (bent u j L p)=bent u j L p := by
  obtain ⟨hq,hb⟩:= firm_bar j L h hp; cases u
  · simp only [bent, Bool.false_eq_true, ↓reduceIte,star_sub,star_one,hb,and_true]; simp only [mul_sub,sub_mul,hq,mul_one,one_mul]; abel
  exact ⟨hq,hb⟩
include ho he in
lemma growth (hp:p∈realCube zone): grow u j L M p*grow u j L M p=grow u j L M p:=by simp [grow,spike_times,(b_p u j hp (show Odd (L*M).val from ho.mul he)).1]
include ho he in
lemma budding (hp:p∈realCube zone): vine u j L M p*vine u j L M p=vine u j L M p:=by
  let X:= grow u j L M p; let R:= peb L; let T:= tall u L
  change (T+X)*(T+X)=_
  rw [add_mul,mul_add,mul_add,show T*T=T from tall_sq ..,show X*X=X from growth u j L M ho he hp,show T*X=0 from (by rw [← show R*X=X from (grow_c ..).1,← mul_assoc,show T*R=0 from tall_peb ..,zero_mul]),show X*T=0 from (by rw [← show X*R=X from (grow_c ..).2,mul_assoc,show R*T=0 from peb_tall ..,mul_zero]),zero_add,add_zero]; rfl
lemma stalk {v:Momentum} : angle u * zen v * angle u=0:=by
  rw [mul_assoc,zenAngle,← mul_assoc,mul_sub,mul_one,slabQ,sub_self,zero_mul]
include ho in
lemma lead (hp:p∈realCube zone)(hx:p≠0): bent u j L p*((1-zen (mixL j L p))*angle u)=(1-zen (mixL j L p))*angle u:=by
  let Z:= zen (mixL j L p); let K:= prodM (mixL j L p) (mixL j L p); let A:=angle u
  rw [aspTrace u j L ho hp hx, shell_inv _ _ hp hx]
  have he:(1+Z)*(1-Z)=(1+K) • (1:Op SpinIdx):=by rw [add_mul,one_mul,mul_sub,mul_one,show Z*Z=-K • 1 from zenSq _]; module
  change ((1+K)⁻¹ • ((1-Z)*A*(1+Z))) * ((1-Z)*A)=(1-Z)*A
  rw [Matrix.smul_mul, mul_assoc ((1-Z)*A),← mul_assoc (1+Z),he, Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_assoc,slabQ,inv_smul_smul₀ (by exact graphs_ne (phys_mix j L ho _ hp.1))]
lemma rider (i:Site L) (hp:p∈realCube zone)(hx:p≠0): arm u j L M i p=money j L i p • ray u j L M p i:=by rw [arm_w _ _ _ _ _ hp hx]; exact smul_smul ..
include ho he in
lemma posts (hp:p∈realCube zone)(hx:p≠0): born u j L M p*tower u j L M p=tower u j L M p:=by
  rw [born,tower,stacked]; congr 1; funext i; dsimp only [Pi.mul_apply]; rw [rider _ _ _ _ _ hp hx, ray, Matrix.mul_smul, ← mul_assoc,lead u j M he (alias_in_real zone_pos hp i ho) (knocked L i ho hp hx)]
lemma haul (hp:p∈realCube zone)(hx:p≠0): sA u L*tower u j L M p= sprig j L p* spike L (angle u * bent u j (L*M) p):=by
  rw [sA,slashA,tower,stacked,sprig,col_spike]; congr 1; funext i; dsimp only [Pi.mul_apply]
  rw [rider _ _ _ _ _ hp hx, ray, Matrix.mul_smul, Matrix.smul_mul,one_mul, ← mul_assoc,← mul_assoc,mul_sub,mul_one,sub_mul,stalk,sub_zero,slabQ]
lemma hold (hp:p∈realCube zone)(hx:p≠0): (stackW j L p)*(sA u L*grow u j L M p) = sA u L*tower u j L M p:=by
  rw [haul _ _ _ _ hp hx, ← Ws_end, mul_assoc, sA,slashA,grow,mul_spike,peb,spike_times,one_mul]
lemma bottom (hp:p∈realCube zone)(hx:p≠0)(h:Odd L.val)(e:Odd M.val): peb L * (star (stackW j L p)) * ((1-sA u L)*tower u j L M p)=(1-sA u L)*grow u j L M p:=by
  rw [← peb_star L, ← star_mul,Ws_end]; let A:=angle u; let P:=bent u j (L*M) p; let n:=L*M
  have hg : 1-sA u L= stack L (fun _=>1-A):=by rw [sA,slashA,← stack_one, ← stack_sub]; rfl
  rw [hg,tower,stacked,sprig,chunks,grow,mul_spike]; congr 1
  let O i := mixL j M (aliasAt p (i:Site L)); let V:= mixL j n p
  let k i := money j L i p
  have hu : P=(1-zen V)*(A*P):=by rw [show A*P= _ from aspect u j n hp, Matrix.mul_smul,← mul_assoc]; exact aspTrace u j n (h.mul e) hp hx
  have hh (Z:Momentum): (1-A)*((1-zen Z)*A*P)= -(zen Z*A*P):=by
    rw [← mul_assoc,← mul_assoc,mul_sub,mul_one,sub_mul,show (1-A)*A=0 by rw [sub_mul,one_mul,show A*A=A from slabQ u,sub_self], zero_sub, neg_mul]; rw [show (1-A)*zen Z=zen Z*A from (by rw [sub_mul,one_mul,show A*zen Z=zen Z*(1-A) by cases u <;> simp [A,angle,zenA,zenAA],mul_sub,mul_one]; abel),mul_assoc (zen Z) A A,show A*A=A from slabQ u]
  have hz:(∑ i:Site L, k i^2 • O i)= V:=by
    have hy (i:Site L): k i^2=(L.val:ℂ)⁻¹*muff j L (aliasAt p i)^2:=by
      unfold k money; rw [mul_pow,← Complex.ofReal_pow, inv_pow,Real.sq_sqrt (side_pos _).le]; push_cast; rfl
    unfold V n
    rw [mix_jump _ _ _ h e]; simp_rw [Finset.smul_sum,hy,smul_smul,O]
  have hz' : zen V=∑ i:Site L,k i^2 • zen (O i):=by rw [← hz]; unfold zen; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Finset.sum_mul,Finset.sum_smul,Finset.smul_sum,smul_smul,mul_assoc]; rw [Finset.sum_comm]
  have ht : (1-A)*P= -(zen V*A*P):=by
    conv_lhs=>rhs; rw [hu,← mul_assoc]
    exact hh V
  simp only [Pi.mul_apply]; change (∑ i,star (k i • (1:Op SpinIdx))* ((1-A)*arm _ _ _ _ i p))=(1-A)*P
  rw [ht,hz',Matrix.sum_mul,Matrix.sum_mul,← sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _
  rw [rider _ _ _ _ _ hp hx]; change star (k i • (1:Op SpinIdx)) * ((1-A)*(k i • ((1-zen (O i))*A*P))) = _
  rw [star_smul,star_one, show star (k i)=k i from money_real j L h i hp.1,Matrix.mul_smul,hh]; simp only [Matrix.smul_mul,Matrix.mul_smul,one_mul]; module
end YM.CF.Fir
