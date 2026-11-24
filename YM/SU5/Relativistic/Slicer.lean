import YM.SU5.Relativistic.Impala

/-! # Tilt charge conjugated by finite Neumann shears.
Equality BEFORE cutoff. det includes the identity complement.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Lattice Finset
open Thera Papyrus.Granat
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
-- general lift
structure Shaft (I:Type*) [Fintype I][LinearOrder I] where
 sell : Op I
 buy : Op I
 payment : sell*buy=1
namespace Shaft
variable (S T:Shaft I)
lemma pay : S.buy*S.sell=1:= mul_eq_one_comm.mp S.payment
/-- conjugate with sell; S trans. -/
def glow (A:FC I): FC I:= quant S.sell*A*quant S.buy
lemma glow_mult (A B:FC I) : S.glow (A*B)=S.glow A*S.glow B:=by
 unfold glow; have he:quant S.buy*quant S.sell=1:=by rw [←quant_mul,S.pay,quant_one]
 simp only [mul_assoc]; rw [←mul_assoc (quant S.buy),he,one_mul] -- check
lemma glow_nil : S.glow 1=1:=by rw [glow,mul_one,←quant_mul,S.payment,quant_one]
lemma glow_zero : S.glow 0=0:=by rw [glow,mul_zero,zero_mul]
lemma glow_sum(A B:FC I) : S.glow (A+B)=S.glow A+S.glow B:=by rw [glow,mul_add,add_mul]; rfl
lemma glow_free (k:ℂ)(A:FC I) : S.glow (k • A)=k • S.glow A:=by rw [glow,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rfl
lemma glow_up (v:Ket I): S.glow (create v)=create (acts S.sell v):=by rw [glow,quant_create,mul_assoc,←quant_mul,S.payment,quant_one,mul_one]
def mirrorC : Shaft I:= ⟨star S.buy,star S.sell,by rw [←star_mul,S.payment,star_one]⟩
lemma glow_rake(A:FC I): S.glow (star A)=star ((S.mirrorC).glow A):=by
 unfold glow mirrorC; simp only [quant_star,star_mul,star_star,mul_assoc]
lemma glow_down(v:Ket I): S.glow (Fock.remove v)=Fock.remove (acts (star S.buy) v):=by unfold Fock.remove; rw [glow_rake, glow_up]; rfl
lemma lawn (p q:Wave I)(A:FC I): inner ℂ p (acts A q)=inner ℂ (acts (quant (star S.buy)) p) (acts (S.glow A) (acts (quant S.sell) q)):=by
 rw [glow,←act_mul, mul_assoc _ (quant S.buy), ←quant_mul,S.pay,quant_one,mul_one,quant_star, act_inner,←act_mul,←mul_assoc,←quant_mul,S.pay,quant_one,one_mul]
def foldC : Shaft I := ⟨S.sell*T.sell,T.buy*S.buy,by simp only [mul_assoc]; rw [←mul_assoc T.sell,T.payment,one_mul,S.payment]⟩
lemma fold_use (A:FC I): (S.foldC T).glow A=S.glow (T.glow A):=by unfold glow foldC; simp only [quant_mul,mul_assoc]
end Shaft
variable {P Q B:Op I} (p:IsStarProjection P)(q:IsStarProjection Q)(b:IsStarProjection B)
local notation "Ω" => Wave I
def Comb (B P:Op I): ℕ→Op I
 | 0=> 0
 | n+1=> (1-P)*B*P+Comb B P n*(1-P*B*P)
local notation "X" => Comb B P
local notation "D"=> P*B*P
local notation "K₀" => (1-P)

section
include p
lemma comb_px (k): P*X k=0:=by induction k with|zero=> rw [Comb,mul_zero]|succ n ih=> rw [Comb,mul_add, ←mul_assoc, ←mul_assoc, Porth p,zero_mul,zero_mul,←mul_assoc,ih,zero_mul,add_zero]
lemma comb_xp (k): X k*P=X k:=by
 have he:(1-P*B*P)*P=P*(1-P*B*P):=by
    rw [sub_mul,mul_sub,one_mul,mul_one, mul_assoc (P*B) P P,p.isIdempotentElem.eq, ←mul_assoc P (P*B),←mul_assoc, p.isIdempotentElem.eq]
 induction k with| zero=> rw [Comb,zero_mul]| succ n ih=> rw [Comb,add_mul,mul_assoc _ P P,p.isIdempotentElem.eq,mul_assoc (X n),he, ←mul_assoc (X n),ih]
lemma comb_nil (k:ℕ) : X k *X k=0:=by nth_rw 1 [←comb_xp (B:=B) p]; rw [mul_assoc,comb_px p,mul_zero]
def Saber (k:ℕ) : Shaft I:= ⟨1+star (X k),1-star (X k),by
 have he:star (X k)*star (X k)=0:=by rw [←star_mul,comb_nil p,star_zero]
 rw [add_mul,one_mul,mul_sub,mul_one,he,sub_zero]; abel⟩
lemma under (k:ℕ)(x:Ω)(h:Sea P x):acts (quant (Saber (B:=B) p k).sell) x=x:=by
 let S:= Saber (B:=B) p k; have hx :acts (quant P) x=x:=by nth_rw 1 [←h.1]; rw [←act_mul,line_quant p,h.1]
 nth_rw 1 [←hx]; rw [←act_mul,←quant_mul, show S.sell*P=P from ?_,hx]; unfold S Saber; simp only [add_mul, one_mul]; rw [show star (X k)*P=0 from (?_),add_zero]; nth_rw 2 [← (show star P=P from p.isSelfAdjoint)]; rw [←star_mul,comb_px p,star_zero]
include b
lemma comb_cross(k): Comb (1-B) (1-P) k= -star (X k):=by
 let V:= K₀; have he:P*V=0:=Porth p; have hb:star V=V:=p.one_sub.isSelfAdjoint
 -- need incremental pow
 let R(A Y:Op I):=1-A*Y*A; let E:=R P B; let H:=R V (1-B); let C:=V*B*P
 have h:X 0=(0:Op I):=rfl
 have hz:P*(1-B)*V= -star C:=by unfold C; rw [mul_sub P 1 B,mul_one,sub_mul _ _ V,he,zero_sub]; simp only [star_mul,hb,p.isSelfAdjoint.star_eq,b.isSelfAdjoint.star_eq,mul_assoc]
 have hx: star E=E:=by unfold E R; simp only [star_sub, star_one,star_mul,p.isSelfAdjoint.star_eq,b.isSelfAdjoint.star_eq,mul_assoc]
 have hd:E*star C=star C*H:=by
    have hu:star C=P*B*V:=by unfold C; simp only [star_mul,hb,p.isSelfAdjoint.star_eq,b.isSelfAdjoint.star_eq,mul_assoc]
    rw [hu]; unfold E H R; 
    rw [sub_mul 1 (P*B*P), mul_sub (P*B*V) 1, one_mul,mul_one]; congr 1
    -- derive via terms: D PBQ=P B P B Q; PBQ Q(1-B)Q =P B (1-P)(1-B)Q=P B P B Q.
    calc
      _ = P*B*(P*P)*B*V:=by noncomm_ring
      _ = P*B*P*B*V:=by rw [p.isIdempotentElem.eq]
      _ = P*B*(1-P)*(1-B)*V:=by
         simp only [mul_sub,sub_mul,mul_one, show P*B*B=P*B from (by rw [mul_assoc,b.isIdempotentElem.eq])]
         rw [show P*B*P*V=0 from by rw [mul_assoc _ P V,he,mul_zero]]; abel
      _ = (P*B)*(V*V)*(1-B)*V:=by rw [show V*V=V from p.one_sub.isIdempotentElem]
      _ = _:=by noncomm_ring
 have ho(A Z:Op I)(n:ℕ) : Comb Z A (n+1)=Comb Z A n+ (1-A)*Z*A*(R A Z)^n:=by
    induction n with| zero=> rw [Comb,Comb,Comb,pow_zero,zero_mul,add_zero,mul_one,zero_add]| succ n ih=>
      nth_rw 1 [Comb]; nth_rw 1 [ih]; rw [add_mul]; rw [show Comb Z A (n+1) = _ from (Comb.eq_2 ..)]; unfold R; rw [pow_succ,←mul_assoc ((1-A)*Z*A)]; abel -- check
 induction k with| zero=> rw [Comb,Comb,star_zero, neg_zero]| succ n ih=> rw [ho,ho,star_add,neg_add,ih]; congr 1; rw [show 1-(1-P)=P from sub_sub_cancel 1 P, hz]; change -star C*H^n = -star (C*E^n); rw [star_mul C (E^n), star_pow,hx,neg_mul]; exact congrArg (fun V:Op I=> -V) ((SemiconjBy.pow_right (a:=star C) (x:=H) (y:=E) hd.symm n)) -- maybe pow_right
end
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.Saber
