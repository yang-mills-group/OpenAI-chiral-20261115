import Compass.Energy
import Compass.Schools
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 25000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
open scoped Classical
open Complex
local notation "SX"=> SpinIdx
abbrev shade1 : SX → ℂ:=![1,1,-1,-1]
abbrev shade2 : SX → ℂ:=![I,-I,I,-I] -- gamma0gamma1 compute 0,0=(-i)*-1=i; 2,2=i*-1? gamma0[2,1]=I,g1[1,2]=1 so i yes
abbrev shade3 : SX → ℂ:=![-I,I,I,-I] -- gamma2 gamma3 diag -i,i,i,-i
private lemma gradD: grading=Matrix.diagonal shade1:=by ext i j; fin_cases i <;> fin_cases j <;> first|rfl|norm_num [grading,shade1,Matrix.diagonal_apply]
set_option maxHeartbeats 750000 in
private lemma cliffD: gammaOp 0 * gammaOp 1=Matrix.diagonal shade2:=by ext i j; fin_cases i <;>fin_cases j <;> first|rfl|norm_num [gammaOp,shade2,Matrix.diagonal_apply,Matrix.mul_apply, SpinIdx,Fin.sum_univ_succ]
set_option maxHeartbeats 750000 in
private lemma cliffC: gammaOp (Fin.succ (Fin.succ 0))* gammaOp (Fin.succ (Fin.succ (Fin.succ 0)))=Matrix.diagonal shade3:=by ext i j; fin_cases i <;>fin_cases j <;> first|rfl|norm_num [gammaOp,shade3,Matrix.diagonal_apply,Matrix.mul_apply, SpinIdx,Fin.sum_univ_succ] <;> simp only [show (2:Fin 4)=Fin.succ (Fin.succ 0) from rfl, show (2:Fin 3)=Fin.succ (Fin.succ 0) from rfl, Matrix.cons_val_zero, Matrix.cons_val_succ,Matrix.of_apply] <;> norm_num <;> rfl
private lemma shadeinject : Injective fun i:SX=> (shade1 i,shade2 i):=by
 rintro i j v; obtain ⟨u,w⟩:=Prod.mk.inj v
 fin_cases i <;> fin_cases j <;> first| rfl|(exfalso; have h:= congrArg Complex.im w; first| (exfalso; norm_num [shade1] at u; done)|norm_num [shade1,shade2] at h)
variable (U:UNI SX) (s:Signed)(p:Bool)
private lemma wisp (A B:Op SX)(q:sings false U A=B):U.val*A=B*U.val:=by rw [singT,twist_formula] at q; rw [←q, mul_assoc, U.property.1,mul_one]; rfl
private lemma entryP (a b:SX→ℂ)(A B:Op SX)(u : U.val*A=B*U.val)(e:A= Matrix.diagonal a)(f:B=Matrix.diagonal b)
    (i j:SX)(t:U.val j i ≠0): b j=a i:=by
 subst A B
 have h:=Matrix.ext_iff.mpr u j i; rw [Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm (b _)] at h; exact (mul_left_cancel₀ t h).symm
lemma duet_D {s:Signed}(p:Anchored s): ∃ a:SX→ℂ, gammaOp (s.perm 0)*gammaOp (s.perm 1)= Matrix.diagonal a:=by
 have he:gammaOp 2* gammaOp 3=Matrix.diagonal shade3:=cliffC
 rcases p.duet with ⟨e,v⟩|⟨e,v⟩|⟨e,v⟩|⟨e,v⟩ <;> rw [e,v]
 exact ⟨_,cliffD⟩
 rw [gammaSwap _ _ (by decide),cliffD]; exact ⟨-shade2, Matrix.diagonal_neg _⟩
 exact ⟨_,he⟩
 rw [gammaSwap _ _ (by decide),he]; exact ⟨-shade3,Matrix.diagonal_neg _⟩
lemma monJet (t:Anchored s)(q:JetS s false p U): Moncol U.val:=by
 obtain ⟨a,r⟩:= duet_D t
 let w:ℂ:=if p then -1 else 1; let z(j:Axis):ℂ:=if s.flip j then -1 else 1
 have W(u:Bool)(X:Op SX): hush u X=(if u then -1 else (1:ℂ)) • X:=by cases u <;> simp
 have w0:= wisp U _ _ ((q.cliff 0).trans (W ..)); have w1:= wisp U _ _ ((q.cliff 1).trans (W ..)); have υ: U.val*grading= (w • grading) * U.val:=wisp U _ _ ((q.grade).trans (W ..))
 have hy: U.val * (gammaOp (s.perm 0)*gammaOp (s.perm 1))=((z 0*z 1) • (gammaOp 0 * gammaOp 1))*U.val:=by
    rw [←mul_assoc,w0,mul_assoc,_root_.Matrix.smul_mul, w1]; simp [z,Matrix.mul_smul,←mul_assoc,smul_smul,Matrix.smul_mul] -- tune
 have hc(W:SX→ℂ)(Z:ℂ): Z • Matrix.diagonal W= Matrix.diagonal (Z • W):= (Matrix.diagonal_smul ..).symm
 refine ⟨fun i j k x y=> shadeinject (Prod.ext ?_ ?_)⟩
 · have h1(j:SX)(p0:U.val j i≠0): w*(shade1 j)=shade1 i:=entryP U shade1 (w • shade1) _ _ υ gradD (by rw [gradD, hc]) i j p0
   exact mul_left_cancel₀ (show w≠0 from by unfold w; split<;>norm_num) ((h1 j x).trans (h1 _ y).symm)
 have h1(j:SX)(p0:U.val j i≠0): (z 0*z 1)*(shade2 j)=a i:=entryP U a ((z 0*z 1) • shade2) _ _ hy r (by rw [cliffD,hc]) i j p0
 have hp(i:Axis): z i≠0:=by unfold z; split<;>norm_num
 exact mul_left_cancel₀ (mul_ne_zero (hp 0) (hp 1)) ((h1 _ x).trans (h1 _ y).symm)
lemma fullJet (c:Bool)(t:Anchored s)(q:JetS s c p U): Moncol U.val:=by
 obtain ⟨a,r⟩:= duet_D t
 let w:ℂ:=if p then -1 else 1; let z(j:Axis):ℂ:=if s.flip j then -1 else 1
 have W(u:Bool)(X:Op SX): hush u X=(if u then -1 else (1:ℂ)) • X:=by cases u <;> simp
 have W_(A B:Op SX)(u:sings c U A=B):sings false U (windX c A)=B:=u
 have V(A B:Op SX)(u:sings c U A=B):= wisp U _ _ (W_ A B u)
 have w0:= V _ _ ((q.cliff 0).trans (W ..)); have w1:= V _ _ ((q.cliff 1).trans (W ..)); have υ: U.val*windX c grading= (w • grading) * U.val:=V _ _ ((q.grade).trans (W ..))
 have hy: U.val * windX c (gammaOp (s.perm 0)*gammaOp (s.perm 1))=((z 0*z 1) • (gammaOp 0 * gammaOp 1))*U.val:=by
    rw [win_m,←mul_assoc,w0,mul_assoc,_root_.Matrix.smul_mul, w1]; simp [z,Matrix.mul_smul,←mul_assoc,smul_smul,Matrix.smul_mul] -- tune
 have hc(W:SX→ℂ)(Z:ℂ): Z • Matrix.diagonal W= Matrix.diagonal (Z • W):= (Matrix.diagonal_smul ..).symm
 let sh(f:SX→ℂ):SX→ℂ:=fun i=> cSignX c (f i)
 have WZ(f:SX→ℂ): windX c (Matrix.diagonal f)=Matrix.diagonal (sh f):=by cases c; rfl; ext i j; by_cases u:i=j <;> simp [windX,u,Matrix.diagonal_apply,sh,cSignX]
 refine ⟨fun i j k x y=> shadeinject (Prod.ext ?_ ?_)⟩
 · have h1(j:SX)(p0:U.val j i≠0): w*(shade1 j)=sh shade1 i:=entryP U (sh shade1) (w • shade1) _ _ υ (by rw [gradD,WZ]) (by rw [gradD, hc]) i j p0
   exact mul_left_cancel₀ (show w≠0 from by unfold w; split<;>norm_num) ((h1 j x).trans (h1 _ y).symm)
 have h1(j:SX)(p0:U.val j i≠0): (z 0*z 1)*(shade2 j)=sh a i:=entryP U (sh a) ((z 0*z 1) • shade2) _ _ hy (by rw [r,WZ]) (by rw [cliffD,hc]) i j p0
 have hp(i:Axis): z i≠0:=by unfold z; split<;>norm_num
 exact mul_left_cancel₀ (mul_ne_zero (hp 0) (hp 1)) ((h1 _ x).trans (h1 _ y).symm)
end YM.CF.Compass