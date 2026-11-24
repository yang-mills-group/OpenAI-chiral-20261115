import YM.CF.DPress.Wagon.Rates
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Race.Ribbon
open Credit
variable {T:Race n L}(X:Ribbon T){ℒ:Fixed.Test n→ℝ}{x y:ℝ} (p:Bound T ℒ)(Y:0<x)(H:0<y)(b:ℒ 1 ≤ x^T.η) {q k:ℕ}
-- Θ.Cargo $eq:Chess-P$ voice variant. upper supp only needed on P-slots.
def allE (y:ℝ) (V:Fixed.Test n→ℝ):Prop:=∀ k:ℕ,k*X.P=T.η→Upper X.full V (List.replicate k true) (y^T.η)
variable (v: X.allE y ℒ)
include p b v Y H
lemma nthPower(k:ℕ)(t:k*X.P=T.η)(f:Even k)(A:List Bool)(h:A.length=k): Upper X.full ℒ A ((X.ρ Y H).cost A):=by
 apply law_clock _ p t f (fun i=>?_ ) A h; have hh(x:ℝ): (x^X.P)^k=x^T.η:=by rw [←pow_mul,Nat.mul_comm,t]
 cases i with| false=> intro i w U ht; change ℒ U ≤ (x^_)^k; rw [hh,X.homB _ _ _ ht]; exact b| true=> change Upper _ ℒ _ ((y^_)^k); rw [hh]; exact v _ t -- tune
private lemma lastU(k:ℕ)(L0: X.Frame k)(h:k*X.b=X.P)(t:q*X.Γtime k=T.η)(g:Even q)(s:List Bool)(u:s.length=q): Upper (X.stripe L0) ℒ s (X.growth x y k^q):=by
 have hk:(k+1)* X.P=X.Γtime k:=by unfold Γtime runB mulT; rw [h,add_mul,one_mul];
 let Z:= (k+1)*q; have hs:Z*X.P=T.η:=by unfold Z; rw [mul_comm (k+1),mul_assoc,hk,t];
 intro a gZ W e; obtain ⟨c,h₁,hV,k'⟩:= X.terminal L0 h Y H s true e; rw [u] at h₁ k'; exact k' ▸ (X.nthPower p Y H b v Z hs (g.mul_left _) c h₁ a _ W hV) -- name conflict
omit p b v Y H
lemma happy(r:ℕ)(p:2^(r+1)∣q):Even q:=by
 obtain ⟨k,u⟩:=p; refine ⟨2^r*k,?_⟩; rw [u,pow_succ',mul_assoc,two_mul]
lemma worthX (p:(q+q)*X.Γtime k=T.η)(v:0< k): X.Frame (k+k):=by -- k implicit
 have ht:0<q:=by by_contra! e; have h:=T.height_p; rw [Nat.eq_zero_of_le_zero e] at p; simp only [add_zero,zero_mul] at p; omega
 rw [Frame, X.fold_time]; refine ⟨by omega,?_⟩; have hp:= Nat.le_mul_of_pos_left (X.Γtime k) ht; rw [add_mul] at p; omega
lemma μind {k:ℕ}{x y:ℝ} : X.growth x y (k+k)= X.growth x y k^2:=by unfold growth mulT runB; repeat rw [add_mul,pow_add]; ring -- tune
include p v b Y H
lemma lift_clock (i k q:ℕ)(g:(2^i*k)*X.b=X.P)(u: X.Frame k)(t:q*X.Γtime k=T.η)(d:2^(i+1)∣ q)(z:List Bool)(h:z.length=q) : Upper (X.stripe u) ℒ z (X.growth x y k ^ q) :=by
 induction i generalizing k q z with
 | zero=> rw [pow_zero,one_mul] at g; exact X.lastU p Y H b v k u g t (happy _ d) _ h -- tune
 | succ i ih=>
    obtain ⟨n,rfl⟩:=happy _ d; let P:= X.Γtime k; let Q:=n+n; let A:=X.stripe u; let L' := k+k; let μ:=X.rent u Y H;
    have hω:Even Q:= ⟨n,rfl⟩; have hz:X.Frame L':= X.worthX t u.1; have hp: (2^i*L')*X.b=X.P:=by rw [←g,pow_succ]; unfold L'; ring
    have ht: n* X.Γtime (k+k)=T.η:=by rw [X.fold_time,mul_add,←add_mul,t]
    obtain ho:2^(i+1)∣ n:= (by obtain ⟨m,p⟩:=d; refine ⟨m,Nat.mul_left_cancel (show 0<2 by decide) ?_⟩; rw [two_mul,p,pow_succ' (a:=2) (n:=i+1),mul_assoc])
    have he(b':Bool):Upper A ℒ (List.replicate Q b') (μ.fee b'^Q):=by
       intro a b Y h; obtain ⟨u',v,t',hK,hW⟩:= X.forecast _ hz n t Y h; have hk:= ih L' n hp hz ht ho _ hK v t' Y hW; change ℒ Y ≤ X.growth x y k ^ Q; refine hk.trans_eq ?_; rw [show L'=k+k from rfl,X.μind,← pow_mul, two_mul]
    rw [←h,←X.rent_p (x:=x) _ Y H z]; exact law_clock μ p t hω he z h
end Race.Ribbon
end YM.CF.DPress.Wagon
#print axioms YM.CF.DPress.Wagon.Race.Ribbon.lift_clock
