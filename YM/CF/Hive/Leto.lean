import YM.CF.Atala.Wills
import YM.CF.Hest.Poet
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
abbrev feeJ (r b:Bool):ℂ:= if r&&b then -1 else 1
private lemma seat(x:Bool):(crib V t (x.xor r)).val * windX (c.xor t) (crib U r x).val=feeJ r (t.xor c) • (crib (V*whiten c U) (r.xor t) x).val :=by
 cases r <;> cases c<;> cases t <;>cases x <;> simp [feeJ,crib, Pastry.thread,whiten,windX, ccU, filmG, Matrix.smul_mul,Matrix.mul_smul,smul_smul, cc_mul,cc_smul]
abbrev sound(U:UNI n)(r x:Bool)(i:n):=∑ j:n, (crib U r x).val j i • bell (x.xor r,j)
lemma mile (x: Bool)(i:n): lotB b r U (bell (x,i))=sound U r x i:=by
 rw [mole]; unfold roseB; rw [Fintype.sum_prod_type,sum_eq_single (x.xor r)]; apply sum_congr rfl; intro i _; unfold sewV; rw [Urn.cream,if_pos rfl]; intro a _ p; apply sum_eq_zero; intro i _; unfold sewV; rw [Urn.cream,if_neg p,zero_smul]; simp
lemma lot_s (z:ℂ)(A:FC n):lotB b r U (z • A)=cSignX (b.xor r) z • lotB b r U A:=cumin b r U A z
lemma honey (x:Bool)(i:n):lotB c t V (lotB b r U (bell (x,i)))=feeJ r (t.xor c) • lotB (b.xor c) (r.xor t) (V*whiten c U) (bell (x,i)):=by
 rw [mile,mile]; unfold sound; rw [map_sum]; simp_rw [lot_s,mile]; unfold sound; rw [Finset.smul_sum]; simp_rw [Finset.smul_sum, smul_smul,Bool.xor_assoc]; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [← sum_smul]; apply congrArg (fun p:ℂ=> p • _); have he:=Matrix.ext_iff.mpr (seat (n:=n) r t c U V x) j i; rw [Matrix.smul_apply,Matrix.mul_apply,smul_eq_mul] at he; rw [← show ∑ k:n, (crib V t (x.xor r)).val j k * (windX (c.xor t) (crib U r x).val) k i= _ from he]; exact sum_congr rfl fun k _=>by rw [mul_comm]; cases c.xor t<;> rfl -- tune
abbrev drum (D:List (Hake.Oboe n)): FC n:= (D.map Hake.bell).prod
lemma kino (S T:FC n→+*FC n){z:ℂ} (p:∀ i: Hake.Oboe n,S (Hake.bell i)=z • T (bell i))(D:List (Hake.Oboe n)): S (drum D)=z^D.length • T (drum D):=by
 induction D with| nil=>simp [drum]| cons i D h=> rw [show drum (i::D)=bell i*drum D from rfl,map_mul,map_mul,h,p]; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,List.length_cons,pow_succ] -- tune
-- even generated
inductive Keys:FC n →Prop where
 | roll(D:List (Hake.Oboe n)): Even D.length→ Keys (drum D)
 | null: Keys 0
 | plus{A B}:Keys A→Keys B→Keys (A+B)
 | mul{A B}:Keys A→ Keys B→ Keys (A*B)
 | col{A}(z:ℂ):Keys A→ Keys (z • A)
lemma kin(S T:FC n→+*FC n)(z:ℂ)(k:z^2=1)(p:∀ i:Hake.Oboe n,S (bell i)=z • T (bell i))(f:ℂ→ℂ)(h:∀ y:ℂ,∀ A:FC n,S (y•A)=f y • S A)(w:∀ y:ℂ,∀ A:FC n,T (y•A)=f y • T A)(A:FC n)(v:Keys A):S A=T A:=by
 induction v with
 | roll Y g=> obtain ⟨d,x⟩:=g; rw [kino S T p,x, ←two_mul, pow_mul,k,one_pow,one_smul]
 | null=> simp
 | plus _ _ i j=> rw [map_add,map_add,i,j]
 | mul _ _ i j=> rw [map_mul,map_mul,i,j]
 | col y _ i=> rw [h,w,i]
lemma hilly (A:FC n)(h:Keys A): lotB c t V (lotB b r U A) = lotB (b.xor c) (r.xor t) (V*whiten c U) A:=by
 let f:=cSignX ((b.xor c).xor (r.xor t)); apply kin ((lotB c t V).comp (lotB b r U)) _ (feeJ r (t.xor c)) (by unfold feeJ; split<;> ring) (fun ⟨x,y⟩=>honey b r t c U V x y) f _ (fun i j=>lot_s ..) A h
 intro i P; rw [RingHom.comp_apply,lot_s,lot_s, RingHom.comp_apply]; congr 1; cases b <;> cases c <;> cases r<;> cases t<;> simp only [f,Bool.false_xor, Bool.true_xor, Bool.not_false,Bool.not_true,cSignX]; all_goals simp
end YM.CF.Hive
