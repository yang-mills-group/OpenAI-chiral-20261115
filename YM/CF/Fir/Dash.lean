import YM.CF.Fir.Altar
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (u:Bool)(j:ℕ)(L M:Side)(hj:Even j)(hl:Odd L.val)(hm:Odd M.val){p:Momentum}
def splitY (p:Momentum):Stk L:= vine u j L M p*wood u j L p*born u j L M p
def clockK (p:Momentum):Stk L:=
 (tower u j L M p+grain u j L M p-tower u j L M p * (grow u j L M p*wood u j L p*grain u j L M p))*vine u j L M p
include hj hl hm in
lemma chase (hp:p∈realCube zone)(hx:p≠0):
    splitY u j L M p*clockK u j L M p=vine u j L M p ∧ clockK u j L M p*vine u j L M p=clockK u j L M p ∧ born u j L M p * clockK u j L M p=clockK u j L M p:=by
  let V:= vine u j L M p; let P:=born u j L M p; let S:=wood u j L p; let R:=tower u j L M p; let H:= tall u L; let G:=grow u j L M p; let Q:=grain u j L M p
  have he: P*R=R:=posts u j L M hl hm hp hx
  obtain ⟨hh,h2⟩:=fieldForm u j L M hj hl hm hp hx
  change P*Q=Q at hh; change H*S*Q=H at h2
  have hu:V*S*R=G:=(emeritus u j L M hj hl hm hp hx).2
  have hs:V*V=V:=budding u j L M hl hm hp
  have hw:G*G=G:=growth u j L M hl hm hp
  let N:=R+Q-R*(G*S*Q); have hpN:P*N=N:=by unfold N; rw [mul_sub,mul_add, he,hh, ← mul_assoc,he]
  change V*S*P*(N*V)=V ∧ N*V*V=N*V ∧ P*(N*V)=N*V
  refine ⟨?_,by rw [mul_assoc,hs],by rw [← mul_assoc,hpN]⟩
  rw [← mul_assoc, mul_assoc (V*S) P N,hpN]; unfold N; rw [mul_sub,mul_add,hu,← mul_assoc _ R,hu,← mul_assoc _ (G*S),← mul_assoc _ G S,hw,show V=H+G from rfl,add_mul, add_mul,h2];
  rw [show G+(H+G*S*Q)-G*S*Q=H+G by abel]; exact hs
lemma burn_neg (p : Momentum): born (!u) j L M p=1-born u j L M p:=by rw [← stack_one]; unfold born bent; rw [← stack_sub]; congr 1; ext1 l; cases u <;> simp
lemma s_neg : sA (!u) L=1-sA u L:=by rw [sA,sA,slashA,slashA,← stack_one,← stack_sub]; congr 1; funext i; cases u <;> simp [angle]
lemma vine_neg (p:Momentum): vine (!u) j L M p=1-vine u j L M p:=by
  have hh : grow (!u) j L M p=peb L-grow u j L M p:=by rw [peb,grow,grow]; unfold spike; rw [← stack_sub]; congr 1; ext1 i; by_cases h:i=0 <;> cases u <;> simp [h,bent]
  rw [vine,vine,tall,tall, s_neg,hh,sub_mul,one_mul]; abel
include hl hm in
lemma split_s (hp:p∈realCube zone): vine u j L M p*splitY u j L M p= splitY u j L M p ∧ splitY u j L M p *born u j L M p=splitY u j L M p:=by
  have hh: born u j L M p * born u j L M p = born u j L M p := by rw [born, ← stack_mul]; congr 1; funext i; exact (b_p u j (alias_in_real zone_pos hp i hl) hm).1
  simp only [splitY,← mul_assoc,budding u j L M hl hm hp, true_and]; rw [mul_assoc, hh]
include hj hl hm in
lemma roundabout (hp:p∈realCube zone)(hx:p≠0): clockK u j L M p*splitY u j L M p=born u j L M p:=by
  let K:=clockK u j L M p; let J:=clockK (!u) j L M p; let Y:=splitY u j L M p; let Z:=splitY (!u) j L M p; let V:=vine u j L M p; let P:=born u j L M p
  have ⟨hV,hP⟩:= split_s u j L M hl hm hp; have ⟨hg,hk⟩:=split_s (!u) j L M hl hm hp; rw [vine_neg] at hg; rw [burn_neg] at hk
  change V*Y=Y at hV; change Y*P=Y at hP; change (1-V)*Z=Z at hg; change Z*(1-P)=Z at hk
  have ⟨hh,hK,hX⟩:= chase u j L M hj hl hm hp hx; have ⟨hs,hJ,hU⟩:= chase (!u) j L M hj hl hm hp hx; rw [vine_neg] at hs hJ; rw [burn_neg] at hU
  change Y*K=V at hh; change Z*J=1-V at hs
  change K*V=K at hK; change P*K=K at hX; change J*(1-V)=J at hJ; change (1-P)*J=J at hU
  have h1 : K*Z=0:=by calc
    _ = K*((1-V)*Z):=by rw [hg]
    _ = 0:= by rw [← mul_assoc, mul_sub, hK, mul_one,sub_self,zero_mul]
  have hzP: Z*P=0:=by rw [mul_sub,mul_one] at hk; exact sub_eq_self.mp hk -- inspect
  have hpU:P*J=0:=by rw [sub_mul,one_mul] at hU; exact sub_eq_self.mp hU
  have hQ:(Y+Z)*(K+J)=1:=by rw [add_mul,mul_add,mul_add, hh, hs, show Y*J=0 by
                                        calc
                                          _ = Y*(P*J):=by rw [←mul_assoc,hP]
                                          _ = 0:=by rw [hpU,mul_zero], show Z*K=0 by
                                        calc
                                          _ = Z*P*K:=by rw [mul_assoc,hX]
                                          _ = 0:=by rw [hzP,zero_mul]]; abel
  have he := congr_arg (fun a=>P*a) (mul_eq_one_comm.mp hQ)
  change P*((K+J)*(Y+Z))= P*1 at he; rw [← mul_assoc,mul_add P,hX,hpU,add_zero,mul_add,h1,add_zero,mul_one] at he; exact he
include hj hl hm in
lemma driver (hp:p∈realCube zone)(hx:p≠0):clockK u j L M p*peb L=tower u j L M p:=by
  let K:=clockK u j L M p; let R:=peb L; let P:= born u j L M p; let H:= tower u j L M p; let U:=splitY u j L M p; let V:=vine u j L M p; let G:=grow u j L M p
  have hx' : K*U=P:= roundabout u j L M hj hl hm hp hx
  have he:P*H=H:=posts u j L M hl hm hp hx
  have hh:U*H=G:=by unfold U splitY; rw [mul_assoc,he]; exact (emeritus u j L M hj hl hm hp hx).2
  have hV : K*V=K:=(chase u j L M hj hl hm hp hx).2.1
  have hg : V*R=G:=by unfold V vine; rw [add_mul,tall_peb,zero_add,(grow_c ..).2]
  change K*R=H
  calc
    _ = K*G:=by rw [← hg,← mul_assoc,hV]
    _ = H:=by rw [←hh,←mul_assoc,hx',he]
end YM.CF.Fir
