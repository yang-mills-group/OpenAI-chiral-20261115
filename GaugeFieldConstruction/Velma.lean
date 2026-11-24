import YM.CF.Sault.Faro
import YM.CF.Sedge.Plume
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
namespace Wosk
open Wosk
variable {n I:Type}[LinearOrder n][Fintype n][LinearOrder I][Fintype I]
variable (X Y D: FC n) (p:X*Y-Y*X=D)(t: Commute D Y)
include p t
lemma hus (k:ℕ): X*Y^(k+1)-Y^(k+1)*X=(k+1:ℂ) • (Y^k*D):=by
 induction k with
 | zero=>simp only [pow_one,pow_zero,one_mul,Nat.cast_zero,zero_add,one_smul,p]
 | succ k ih=>
   calc
    _=(X*Y^(k+1)-Y^(k+1)*X)*Y+Y^(k+1)*(X*Y-Y*X):=by noncomm_ring
    _ = _ := by rw [ih,p,smul_mul_assoc,mul_assoc (Y^_),t.eq,←mul_assoc,←pow_succ,Nat.cast_add_one]; simp only [add_smul,one_smul]

lemma hus_E : X*exp Y-exp Y*X= exp Y*D:=by
 let S(j:ℕ):=(j.factorial:ℂ)⁻¹ • Y^j; have hT: HasSum S (exp Y):= exp_series_hasSum_exp' _
 let Z(j:ℕ):=X*S j-S j*X
 have hy:HasSum Z _:= (hT.mul_left X).sub (hT.mul_right X)
 have hv(i:ℕ):Z (i+1)=S i * D:=by
    unfold Z S; rw [mul_smul_comm,smul_mul_assoc,←smul_sub,hus X Y D p t i,smul_smul,smul_mul_assoc]; congr 1; rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]; field_simp -- note factorial type
 have h:HasSum Z (exp Y*D):=by
    have hZ:= hT.mul_right D; simp_rw [←hv] at hZ; apply (hasSum_nat_add_iff' (f:=Z) 1).mp; simpa [Z,S] using hZ -- tune
 exact hy.unique h
omit p t

variable (F C K:I→ FC n)(H:I→I→ℂ)(w:Wave n)
structure Flesh : Prop where
 rent : ∀ i j,antiB (C i) (C j)=0
 tear : ∀ i j,antiB (K i) (C j)=H i j • 1
 remP : ∀ i,acts (K i) w=0
 oak : ∀ i,F i=C i + K i
#check Flesh
abbrev PairLog (I:Type):= Option (I×I) →ℂ
abbrev Rad (I:Type):= I→ℂ
def logL (u:Option (I×I)):FC n:= u.elim 1 fun x=>F x.1*F x.2
abbrev binE (S:PairLog I):FC n:= ∑ i,S i • logL F i
abbrev radE (S:Rad I):FC n:= ∑ i:I,S i • F i
variable (h:Flesh F C K H w)
def inPlace (i:I): Rad I:= Pi.single i 1
def crossL (x y:I): PairLog I:= Pi.single (some (x,y)) 1
def L_0 :PairLog I:= Pi.single none 1
lemma bedL (i:I): radE C (inPlace i)=C i:=by simp [radE,inPlace,Pi.single_apply,ite_smul]
lemma creekL (i j:I): binE C (crossL i j)=C i*C j:=by unfold crossL; simp [binE,Pi.single_apply,ite_smul,logL]
lemma creek_0 : binE C L_0=1:=by unfold L_0; simp [binE,Pi.single_apply,ite_smul,logL]
abbrev orbitC (s t u:FC n)(a b:ℂ): Prop:= s*(t*u)-t*u*s= a • u-b • t
lemma oakV (i j k:FC n)(u v:ℂ)(ht:antiB i j=u • 1)(hv:antiB i k=v • 1): orbitC i j k u v:=by
 have he:= congrArg (· *k) ht; have hu:= congrArg (j *·) hv; unfold antiB at he hu; rw [add_mul,smul_mul_assoc,one_mul] at he; rw [mul_add,mul_smul_comm,mul_one] at hu; unfold orbitC; rw [←he,←hu]; simp only [mul_assoc]; abel
include h
lemma x_mark (i:I)(j:Option (I×I)):Commute (C i) (logL C j):=by
 letI :NormedAlgebra ℚ (FC n):= NormedAlgebra.restrictScalars ℚ ℝ _
 rcases j with _|⟨u,v⟩; exact Commute.one_right _; refine sub_eq_zero.mp ?_; exact (oakV _ _ _ 0 0 (by simpa using h.rent i u) (by simpa using h.rent i v)).trans (by simp)
variable (Yζ:PairLog I)(Wζ:Rad I)
lemma y_mark(i:I):Commute (C i) (binE C Yζ):=by
 unfold Commute SemiconjBy binE; simp_rw [mul_sum,sum_mul,mul_smul_comm,smul_mul_assoc,(x_mark _ _ _ _ _ h i _).eq]
omit h
def RadW : (Rad I)→ₗ[ℂ] FC n where
 toFun:=radE C
 map_add' _ _:=by simp [radE,add_smul,sum_add_distrib]
 map_smul' _ _:=by simp [radE,mul_smul,smul_sum]
def binW : PairLog I →ₗ[ℂ] FC n where
 toFun:=binE C
 map_add' _ _:=by simp [binE,add_smul,sum_add_distrib]
 map_smul' _ _:=by simp [binE,mul_smul,smul_sum]
def rainfall (i:I) :Option (I×I) → Rad I
 | none=>0
 | some (u,v)=> H i u • (inPlace v)- H i v • (inPlace u)
def riseP (i:I):Rad I:= ∑ t,Yζ t • rainfall H i t -- implicit order #check
include h
#check riseP
lemma falls(i:I)(Z:Option (I×I)): K i * logL C Z-logL C Z*K i=RadW C (rainfall H i Z):=by
 rcases Z with _|⟨u,v⟩
 · change K i*1-1*K i=_; rw [rainfall,mul_one,one_mul,sub_self,map_zero]
 rw [rainfall,map_sub,map_smul,map_smul]; change _=H i u • radE C _-H i v • radE C _; rw [bedL,bedL]; exact oakV _ _ _ _ _ (h.tear ..) (h.tear ..)
lemma k_mark(i:I):K i*binE C Yζ-binE C Yζ*K i=RadW C (riseP H Yζ i):=by
 unfold riseP binE; simp_rw [map_sum,mul_sum,sum_mul,mul_smul_comm,smul_mul_assoc,←sum_sub_distrib,map_smul,←smul_sub,falls _ _ _ _ _ h i]
lemma R_sk:Commute (radE C Wζ) (binE C Yζ):=by
 change Commute (∑ j:I, Wζ j • C j) _; let X:= binE C Yζ; change (∑ _,_)*X=X*(∑ _,_); rw [sum_mul,mul_sum]; exact sum_congr rfl fun j _=> ((y_mark _ _ _ _ _ h Yζ j).smul_left (Wζ j)).eq -- i unused

abbrev drawP (i:I):Rad I:= inPlace i+riseP H Yζ i
lemma Formula37P (i:I): F i * exp (binE C Yζ)=exp (binE C Yζ)*(RadW C (drawP H Yζ i)+K i):=by
 let Q:=binE C Yζ
 letI:NormedAlgebra ℚ (FC n) :=NormedAlgebra.restrictScalars ℚ ℝ _
 have he:= ((y_mark _ _ _ _ _ h Yζ i).exp_right).eq
 have hu:= hus_E (K i) Q (RadW C (riseP H Yζ i)) (k_mark _ _ _ _ _ h Yζ i) (R_sk _ _ _ _ _ h Yζ (riseP H Yζ i)); dsimp only [Q] at hu
 rw [h.oak, add_mul,he,show RadW C (drawP H Yζ i)=C i+ RadW C (riseP H Yζ i) from (map_add ..).trans (by rw [show RadW C (inPlace i)=C i from bedL C i])]; simp only [mul_add]; rw [sub_eq_iff_eq_add.mp hu]; abel
abbrev quarry(i:I):ℂ:= ∑ j:I,Wζ j * H i j
def fusT(D E:Rad I): PairLog I:= fun u => u.elim 0 fun x=> D x.1*E x.2
def quadR(i j:I): PairLog I:= fusT (drawP H Yζ i) (drawP H Yζ j)+quarry H (drawP H Yζ j) i • L_0
abbrev plotD (Z:Option (I×I)): PairLog I:= Z.elim L_0 fun x=>quadR H Yζ x.1 x.2
lemma FloodP(i:I):antiB (K i) (RadW C Wζ)=quarry H Wζ i • 1:=by
 change antiB (K i) (radE C Wζ)=_; simp only [quarry,radE,antiB_sum',antiB_smul',h.tear,smul_smul,sum_smul] -- tune
omit h
lemma fuse_L (D E:Rad I): binW C (fusT D E)= RadW C D* RadW C E:=by
 change binE C _= radE C D * radE C E; simp only [binE,fusT,logL,radE,Fintype.sum_option,Fintype.sum_prod_type]; simp only [Option.elim_none,zero_smul,Option.elim_some,zero_add,sum_mul]; simp_rw [mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
include h
lemma Annual(i j:I): acts (logL F (some (i,j))) (acts (exp (binE C Yζ)) w)= acts (binW C (quadR H Yζ i j)) (acts (exp (binE C Yζ)) w):=by
 letI : NormedAlgebra ℚ (FC n):= NormedAlgebra.restrictScalars ℚ ℝ _
 let A:=exp (binE C Yζ); let Qi:= drawP H Yζ i; let Qj:=drawP H Yζ j; let T:=RadW C Qi; let V:=RadW C Qj; let z:=quarry H Qj i
 have ht:Commute T A:= (R_sk _ _ _ _ _ h Yζ Qi).exp_right; have hv:Commute V A:= (R_sk _ _ _ _ _ h Yζ Qj).exp_right
 have hf:F i*A=A*(T+K i):=Formula37P _ _ _ _ _ h Yζ i; have hg:F j*A=A*(V+K j):=Formula37P _ _ _ _ _ h Yζ j
 have pe:acts (F j) (acts A w)=acts A (acts V w):=by rw [←act_mul,hg,act_mul,act_add,h.remP j,add_zero]
 change acts (F i*F j) (acts A w)=_; rw [act_mul,pe,←act_mul,hf,act_mul,act_add,map_add,quadR,map_add,map_smul,fuse_L]; change acts A (acts T (acts V w))+ acts A (acts (K i) (acts V w))= acts (T*V+ z • binE _ L_0) (acts A w); rw [act_add,←act_mul T,←act_mul A,←(ht.mul_left hv).eq,act_mul]; refine congrArg _ ?_; -- may pick wrong argument
 rw [←act_mul (K i),show K i*V = z • 1 - V*K i from eq_sub_of_add_eq (FloodP _ _ _ _ _ h Qj i),act_sub,act_mul _ (K i),h.remP i,map_zero,sub_zero,act_smul,act_one,map_smul,creek_0 C,act_smul,act_one
       ] -- tune

def bondR (Q:PairLog I): PairLog I:= ∑ t,Q t • plotD H Yζ t
lemma Tap_P (x:PairLog I): acts (binW F x) (acts (exp (binW C Yζ)) w)= acts (binW C (bondR H Yζ x)) (acts (exp (binW C Yζ)) w):=by
 let P:= acts (exp (binW C Yζ)) w
 change acts (∑ t,x t • logL F t) P = acts ((binW C) (bondR H Yζ x)) P; unfold bondR; rw [map_sum (binW C)]; simp_rw [act_sum,map_smul (binW C),act_smul] -- tune
 apply sum_congr rfl; rintro (_|⟨i,j⟩) u
 · change _= _ • acts (binE C L_0) P; rw [creek_0]; rfl
 exact congrArg _ (Annual _ _ _ _ _ h _ i j)
lemma Tax_P (x:PairLog I):Commute (binW C x) (binW C Yζ):=by
 let V:=binW C Yζ; change (∑ t,x t • logL C t)*V= V* (∑ t,x t • logL C t); rw [sum_mul,mul_sum]; refine sum_congr rfl fun a _=>?_ ; apply Commute.eq; apply Commute.smul_left; rcases a with _|⟨i,j⟩; exact Commute.one_left _; exact (y_mark _ _ _ _ _ h Yζ i).mul_left (y_mark _ _ _ _ _ h Yζ j)
#print axioms Tap_P
end Wosk
end YM.CF.Fock
end
