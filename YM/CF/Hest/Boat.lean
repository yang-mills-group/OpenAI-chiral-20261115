import YM.CF.Hest.Mint
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open Pastry Scree
open scoped Matrix Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {τ ι n:Type*}[LinearOrder n][Fintype n]
def boat(M:Op n):ribbon n:= ⟨faceD true false M,face_flour ..⟩
lemma birth (A P:Op n)(p:IsStarProjection P): (nursery P p).cook (boat A)= dg (capT P A):=by change (nursery P p).eval (faceD true false A)= _; rw [eval_faceD]; change dyad A (seekF P) (hideF P)= _; unfold seekF hideF capT; rw [dyad_prong, ccT,p.isSelfAdjoint]; rfl -- tune
lemma bloom (P A:Op n)(h:IsStarProjection P)(hp:TagG P A): (nursery P h).cook (exp (boat A))=exp (dg A):=by rw [Poly.rising, birth, Laic.capQ hp]
lemma face_rev (u v:Bool)(A:Op n):faceD u v A= faceD v u (- Aᵀ):=by
 unfold faceD twinD; rw [sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; have he: wire u j *wire v i= -(wire v i *wire u j):= eq_neg_of_add_eq_zero_left (put_put ..); rw [he]; exact (by rw [Matrix.neg_apply,Matrix.transpose_apply,smul_neg,neg_smul]) -- tune indices
lemma hue (b:Bool)(A:Op n): windX b (faceD true false A)=faceD true false (windX b A):=by
 unfold faceD twinD; rw [win_sum]; apply Finset.sum_congr rfl; intro i _; rw [win_sum]; refine sum_congr rfl fun j _=>?_ ; rw [win_c,win_m, wire,wire,win_up,win_up]; cases b <;>rfl
lemma turn (A:Op n)(U: UNI n): twist (quantU (n:=LeanV n) (Scree.spice U true)) (faceD true false A)=faceD false true ((thread (invFilm U) false).val*A*(thread (invFilm U) true).valᵀ):=by
 unfold faceD twinD; simp_rw [map_sum,twist_scalar,map_mul,Scree.spirit,Bool.not_true,Bool.not_false]
 simp_rw [sum_mul,mul_sum,Matrix.mul_apply,sum_mul,sum_smul,smul_sum,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,Matrix.transpose_apply]
 let S := (thread (invFilm U) false).val; let T := (thread (invFilm U) true).val; let f := wire false (n:=n); let g := wire true (n:=n)
 let D (i j p q : n) := (A i j*(T q j*S p i)) • (f p*g q)
 change ∑ i,∑ j,∑ p,∑ q, D i j p q=_
 simp_rw [sum_comm (f:=fun i j=>∑ p,∑ q,D i j p q), sum_comm (f:=fun i p=>∑ q,D i _ p q),
    sum_comm (f:=fun j p=>∑ i,∑ q,D i j p q), sum_comm (f:=fun i q=>D i _ _ q), sum_comm (f:=fun j q=>∑ i,D i j _ q)]
 simp only [D,mul_comm,mul_assoc,mul_left_comm,S,T,f,g] -- tune
lemma sailR (b r:Bool)(A:Op n)(U:UNI n): paintR b r U (boat A)=boat (Thera.jazz r (sings b U A)):=by
 apply Subtype.ext; change sauce b r U (faceD true false A)=faceD true false _; rw [sauce,singT,hue]; cases r
 · rw [show Scree.spice U false=closeV U from rfl,face_fold]; unfold thread Thera.jazz; simp only [ite_true,Bool.false_eq_true,ite_false]; let V:= windX b A; rw [show (ccU U).valᵀ=star U.val from ccT ..]; rw [Bool.xor_false,singT,twist_formula]
 let X:=invFilm U; rw [turn, face_rev false true]; change faceD true false (-(cc X.val*windX (b.xor true) A*X.valᵀ)ᵀ)=faceD true false (-star _); congr 1; rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose, ccT]; have hx(B:Op n):(windX (b.xor true) B)ᵀ=star (windX b B):=by cases b; exact ccT ..; change _=star (cc B); rw [←cc_star,cc]; simp; rfl -- tune
 rw [hx, ←mul_assoc,← twist_formula, singT,map_star] -- orientation map_star moves star
 unfold X invFilm; rw [Fock.twin,rankPhase] -- tune order
lemma boats (S: Finset ι)(f:ι→ Op n): ∑ i∈S,boat (f i)=boat (∑ i∈S,f i):=by
 apply Subtype.ext; change (Dough (LeanV n)).val _ = _; rw [map_sum]; change ∑ i∈S,faceD true false (f i)=faceD true false (∑ i∈S,f i); unfold faceD twinD; simp_rw [Matrix.sum_apply,sum_smul]; rw [sum_comm]; exact Finset.sum_congr rfl fun i _=>sum_comm
end YM.CF.Hest
