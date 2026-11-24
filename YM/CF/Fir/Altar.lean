import YM.CF.Fir.Grove
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
private lemma rendez {n:Type*} [Fintype n] [DecidableEq n] (W R G A H D T : Op n) (w:IsUnit W)
    (hb:T= (1-R)*A) (hp:R*A=A*R)(hg:R*G=G)(hs:G*R=G) (hsq:G*G=G)
    (hk:W*(A*H)=A)(hr:(1-A)*H=star W*(1-A))(hd:W*(A*G)=A*D)
    (hm : R*star W*((1-A)*D)=(1-A)*G)(hrr:R*R=R):
    R*H*D=G ∧ (T+G)*H*D=G:=by
  have he:A*H*D=A*G:= w.mul_left_cancel (by rw [← mul_assoc, hk, hd])
  have hx:R*(A*H)*D=A*G:=by rw [mul_assoc,he, ← mul_assoc, hp,mul_assoc,hg] -- inspect
  have hh:R*H*D=G:=by calc
    _ = R*(A*H)*D + R*((1-A)*H)*D:=by rw [← add_mul,← mul_add, ← add_mul]; simp
    _ = _:=by rw [hx,hr,← mul_assoc _ (star W),mul_assoc _ (1-A),hm,sub_mul,one_mul]; abel
  refine ⟨hh,?_⟩
  rw [add_mul,add_mul,hb,mul_assoc (1-R),mul_assoc,he,sub_mul,← mul_assoc R,hp,mul_assoc A,hg,one_mul,sub_self,zero_add];
  calc
    _ = G*(R*H*D) := by rw [← mul_assoc,← mul_assoc G R H,hs] -- fix
    _ = G := by rw [hh,hsq]
variable (u:Bool)(j:ℕ)(L M:Side)(hj:Even j)(ho:Odd L.val)(hm:Odd M.val){p:Momentum}
include hj ho hm in
lemma emeritus (hp:p∈realCube zone)(hx:p≠0): peb L*wood u j L p*tower u j L M p=grow u j L M p ∧
    vine u j L M p *wood u j L p*tower u j L M p=grow u j L M p :=
  rendez _ _ _ _ _ _ _ (lofty j L hj ho hp) (high_tall u L) (pebSlate u L) (grow_c ..).1 (grow_c ..).2 (growth u j L M ho hm hp) (timber u j L hj ho hp).1 (timber u j L hj ho hp).2.2 (hold u j L M hp hx) (bottom u j L M hp hx ho hm) (peb_sq _)

/-- Fill high independently from the graph at nonprincipal aliases. -/
def spare (p : Momentum):Stk L:=stackW j L p*tall u L

def filterH (p: Momentum): Stk L:= spare u j L p-(money j L 0 p)⁻¹ • (sprig j L p*(peb L*spare u j L p))
def gate (p:Momentum): Stk L:= stack L fun l=> if l=0 then 0 else (1-zen (mixL j M (aliasAt p l)))*angle u
def grain (p:Momentum): Stk L := gate u j L M p*filterH u j L p
include hj ho in
lemma filter_zero (hp:p∈realCube zone): peb L*filterH u j L p=0:=by
  let R:=peb L; let m:=money j L 0 p; let Y:=sprig j L p; have he:R*Y=m • R:=by unfold Y R peb sprig; rw [plucks, one_mul,spike_scale]
  have hx:m≠0:= by intro hh; have he:=money_pos j L hj ho hp; change 0 < m.re at he; rw [hh] at he; exact lt_irrefl 0 he
  unfold filterH; rw [mul_sub, Matrix.mul_smul, ← mul_assoc,he,Matrix.smul_mul, inv_smul_smul₀ hx, ← mul_assoc,peb_sq,sub_self]
lemma filter_s (hp:physical p): sA u L * filterH u j L p= filterH u j L p:=by
  let A:=sA u L; let T:= stackW j L p; let R:=peb L; let S:=tall u L; let Y:=sprig j L p
  have he:A*spare u j L p=spare u j L p := by rw [spare,← mul_assoc,← slateW u j L hp,mul_assoc,tall_s]
  have hb:A*Y=Y*A:=(stackA L _ _).eq
  rw [filterH]; change A*(_-_)=_; rw [mul_sub,he, Matrix.mul_smul,← mul_assoc A Y,hb,mul_assoc,← mul_assoc A R,← pebSlate,mul_assoc,he]
include ho hm in
lemma gate_p (hp:p∈realCube zone)(hx:p≠0): born u j L M p * gate u j L M p = gate u j L M p := by
  rw [gate,born, ← stack_mul]; congr 1; funext i; by_cases h:i=0
  · simp [h]
  dsimp only [Pi.mul_apply]; rw [if_neg h,lead u j M hm (alias_in_real zone_pos hp i ho) (knocked L i ho hp hx)]
lemma gate_snap (p : Momentum): sA u L*gate u j L M p=tall u L:=by
  rw [sA,slashA,gate, ← stack_mul, high_tall,sA,slashA,← stack_one, peb, spike, ← stack_sub, ← stack_mul]; congr 1
  funext i; by_cases he:i=0
  · simp [he]
  simp only [if_neg he,Pi.mul_apply,Pi.sub_apply,Pi.one_apply,sub_zero,one_mul, ← mul_assoc,mul_sub,sub_mul,mul_one,stalk,sub_zero,slabQ]
include hj ho hm in
lemma fieldForm (hp:p∈realCube zone)(hx:p≠0): born u j L M p*grain u j L M p=grain u j L M p ∧
    tall u L*wood u j L p *grain u j L M p=tall u L :=by
  let R:=peb L; let S:=sA u L; let W:= stackW j L p; let H:= wood u j L p; let T:=tall u L; let Y:=grain u j L M p; let G:=grow u j L M p
  have hw: S*Y=filterH u j L p:=by unfold Y grain; rw [← mul_assoc, gate_snap,high_tall,mul_assoc,filter_s u j L hp.1,sub_mul,filter_zero u j L hj ho hp,one_mul,sub_zero]
  have hh: R*spare u j L p= peb L * spare u j L p:=rfl
  have ht:=tall_s u L
  have hk:S*(R*spare u j L p)=R*spare u j L p:=by rw [← mul_assoc,← pebSlate,mul_assoc, spare,← mul_assoc S,← slateW u j L hp.1,mul_assoc,tall_s]
  let V:=T-(money j L 0 p)⁻¹ • (R*spare u j L p)
  have hp': S*H*Y=V:=by
    apply (lofty j L hj ho hp).mul_left_cancel
    change W*(S*H*Y)=_
    rw [← mul_assoc,show W*(S*H)=S from (timber u j L hj ho hp).1, hw]
    change spare u j L p-(money j L 0 p)⁻¹ • (sprig j L p*(R*spare u j L p))= W*(T-(money j L 0 p)⁻¹ • (R*spare u j L p))
    have hxT: W*(R*spare u j L p)=sprig j L p*(spare u j L p):=by rw [← mul_assoc,show W*R=_ from Ws_end ..]
    -- aha spare term missing R after Ws_end, sprig*R=sprig
    have hxS:sprig j L p*(R*spare u j L p)=sprig j L p*(spare u j L p):=by rw [← mul_assoc,sprig,show R=peb L from rfl,peb_col]
    conv_rhs => rw [mul_sub,Matrix.mul_smul,hxT]
    rw [hxS,show W*T=spare u j L p from rfl]

  have ht1:R*T=0:=peb_tall u L
  change born _ _ _ _ _ * Y=Y ∧ T*H*Y=T
  constructor
  · unfold Y grain; rw [← mul_assoc,gate_p _ _ _ _ ho hm hp hx]
  calc
    T*H*Y=(1-R)*V:=by rw [show T= _ from high_tall u L,← hp']; simp only [mul_assoc]; rfl -- defin
    _ = T:=by unfold V; simp only [sub_mul,one_mul,mul_sub,Matrix.mul_smul,ht1,← mul_assoc,show R*R=R from peb_sq L]; abel
end YM.CF.Fir
