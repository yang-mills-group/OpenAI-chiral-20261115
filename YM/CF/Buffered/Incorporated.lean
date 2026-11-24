import YM.CF.Buffered.Canvas
import YM.CF.Buffered.Evolution
/-!
# Factored site blocks of a tile, rect or cube

`R ≃ P×I` presented with arbitrary mode indexing. Reflection, hopping,
Pair etc. concern the embedded site slots, not a particular ordering of R.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Cin
open Function Fock NormedSpace SU Lat Lattice Cube Finset Mir Branch Reflect
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {I J R : Type*} [LinearOrder I][LinearOrder J][LinearOrder R][Fintype I][Fintype J][Fintype R]
variable (e:I↪J)(f:I↪R)(g:J↪R)
lemma into_trans {S:Finset I}{A:FC I}{b:Bool}(t:∀ i,g (e i)=f i) (p:Sector S b A):into g (into e A)=into f A:=by
 induction p with
 | zero=> simp
 | one=> simp
 | up i h=> simp [put_in,t]
 | down i h=> simp [take_in,t]
 | scale _ c p=> rw [map_smul,map_smul,map_smul,p]
 | add _ _ p q=>rw [map_add,map_add,map_add,p,q]
 | mul _ _ p q=>rw [map_mul,map_mul,map_mul,p,q]
lemma into_real (A:FC I)(c:ℝ) : into e (c • A)=c • into e A:=by simpa only [show ∀ F:FC I,c • F=(c:ℂ) • F from fun _=> RCLike.real_smul_eq_coe_smul (K:=ℂ) ..,show ∀ F:FC J,c • F=(c:ℂ) • F from fun _=> RCLike.real_smul_eq_coe_smul (K:=ℂ) ..] using map_smul (into e) (c:ℂ) A -- tune
lemma into_exp (A:FC I): into e (exp A)=exp (into e A):=by
 letI : NormedAlgebra ℚ (FC I) := NormedAlgebra.restrictScalars ℚ ℝ _
 letI : NormedAlgebra ℚ (FC J) := NormedAlgebra.restrictScalars ℚ ℝ _
 exact map_exp _ (into_cont _) _
lemma into_create (v:Ket I): into f (create v)=create (coat f v):= totalBasis f (fun x s p=> by rw [show into f _=inject f _ from rfl,insert_act f _ _ p,hoist_c f s p])
lemma into_remove (v:Ket I): into f (remove v)=remove (coat f v):= by unfold remove; rw [into_star,into_create]
/-- *Background* on the UV cover cycle. No assuming that translating to a
seam leaves antiperiodic data unchanged. `p→p'` for an embedded sector is
specified including wind signs on basis vectors. -/
def Framed (e f:I↪J)(U:UNI J)(V:UNI I): Prop := ∀ i:I, acts U.val (basisKet (e i))=coat f (acts V.val (basisKet i))
section frame
variable {f':I↪J}{U:UNI J}{V:UNI I} (h:Framed e f' U V)
include h
lemma Framed.inter (z:Ket I) : acts U.val (coat e z)=coat f' (acts V.val z):=by
 nth_rw 1 2 [← basis_expand z]; simp_rw [map_sum,map_smul,basis_shell,h ..] -- tune invalid
lemma Framed.theta {S:Finset I}{A:FC I}{b:Bool}(p:Sector S b A): theta U (into e A)=into f' (theta V A):=by
 induction p with
 | zero=> rw [map_zero,theta_zero,Fock.theta_zero,map_zero]
 | one=> rw [map_one,theta_one,Fock.theta_one,map_one]
 | up i h'=> rw [put_in,theta_up,Fock.theta_up,map_smul,h _,into_remove]
 | down i h'=> rw [take_in,theta_down,Fock.theta_down,map_smul,h _,into_create]
 | scale _ c p=>rw [map_smul,theta_smul,Fock.theta_smul,map_smul,p]
 | add _ _ p q=>rw [map_add,theta_add,Fock.theta_add,map_add,p,q]
 | mul _ _ p q=>rw [map_mul,theta_mul,Fock.theta_mul,map_mul,p,q]
lemma Framed.trans {f g':J↪R}{W:UNI R}(p:Framed f g' W U) : Framed (e.trans f) (f'.trans g') W V:= by
 have hh(z:Ket I):coat g' (coat f' z)=coat (f'.trans g') z:=by nth_rw 1 2 [←basis_expand z]; simp_rw [map_sum,map_smul,basis_shell]; rfl
 intro i; simp only [Function.Embedding.trans_apply]; rw [p _,h _,hh]
end frame

abbrev Installed (P I J:Type*) := (P × I) ≃ J
section jump
variable {P:Type*}(F:Installed P I J)
namespace Installed

def point (p:P): I↪J := ⟨fun i=> F (p,i),fun _ _ h=> congrArg Prod.snd (F.injective h)⟩
lemma apart {p q:P}(h:p≠q) : Disjoint (lows (point F p)) (lows (point F q)):= disjoint_left.mpr (fun i hi l=> by
 obtain ⟨i,-,rfl⟩:=mem_map.mp hi; obtain ⟨j,-,he⟩:=mem_map.mp l; exact h (congrArg Prod.fst (F.injective he.symm)))
variable [DecidableEq P][Fintype P] (a:Equiv.Perm P)(U:UNI I)
def uniform : UNI J:= by
 refine ⟨(Matrix.reindexAlgEquiv (R:=ℂ) ℂ F) (jump a.symm (fun _=> U.val)),?_⟩
 have hp:= jump_unitary a.symm (fun _=> U.val) (fun _=> U.property)
 -- rw reindex alg_equiv
 have he (X:Op (P×I)) : star ((Matrix.reindexAlgEquiv (R:=ℂ) ℂ F) X)=(Matrix.reindexAlgEquiv (R:=ℂ) ℂ F) (star X):=by ext i j; rfl
 constructor
 · rw [he,←map_mul,hp.1,map_one]
 rw [he,←map_mul,hp.2,map_one]
lemma uniform_apply (i j:P)(x y:I): (uniform F a U).val (F (i,x)) (F (j,y))=if i=a j then U.val x y else 0:=by
 unfold uniform; simp [Matrix.coe_reindexAlgEquiv, jump_apply,a.symm_apply_eq] -- tune
lemma uniform_sq (h : U.val*U.val= -1) (p:a.symm=a): (uniform F a U).val*(uniform F a U).val= -1:=by
 unfold uniform; rw [← map_mul,jump_mul,show a.symm.trans a.symm=Equiv.refl _ from (by nth_rw 1 [p]; rw [Equiv.self_trans_symm])]; simp_rw [h]; rw [jump_neg, jump_id,map_neg,map_one] -- tune
lemma uniform_frame (s:P):Framed (point F s) (point F (a s)) (uniform F a U) U:=by
 intro i; apply PiLp.ext; rintro w; obtain ⟨⟨z,t⟩,rfl⟩:= F.surjective w; rw [basis_act]; change (uniform F a U).val (F (z,t)) (F (s,i))=_; rw [uniform_apply]; split_ifs with h
 · subst z; change _=(coat (point F (a s)) _).ofLp (point F (a s) t); rw [←seamK,trails,basis_act]
 exact (basin _ _ _ (fun x=>by obtain ⟨j,-,he⟩:=mem_map.mp x; exact h (congrArg Prod.fst (F.injective he.symm)))).symm

def filled (s:Finset I) := univ.filter fun x:J=> (F.symm x).2 ∈ s
lemma point_grade (s:Finset I)(x:P)(i:I): point F x i ∈ filled F s ↔ i∈s:=by simp [point,filled]
lemma uniform_flip (s:Finset I)(h:twist U (cutM sᶜ)=cutM s) : twist (uniform F a U) (cutM (filled F s)ᶜ)=cutM (filled F s):=by
 apply twist_comm; ext w z; obtain ⟨⟨i,x⟩,rfl⟩:= F.surjective w; obtain ⟨⟨j,y⟩,rfl⟩:= F.surjective z; unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul,uniform_apply]; split; swap; · simp
 simp only [mem_compl, show ∀ i x,F (i,x)∈filled F s ↔ x∈s from fun i x => point_grade ..]
 have he:= Matrix.ext_iff.mpr (twist_product U (cutM sᶜ)) x y; rw [h] at he; unfold cutM at he; rw [Matrix.mul_diagonal,Matrix.diagonal_mul] at he; simpa only [mem_compl] using he.symm
end Installed
end jump
-- order with exact decEq. for local non-abbrev new sector types
noncomputable abbrev pickOrd (I : Type*) [d:DecidableEq I][Fintype I] : LinearOrder I:= by
 let l:LinearOrder I := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
 exact {l with
   toDecidableEq:=d
   compare_eq_compareOfLessAndEq:= by
     haveI : LinearOrder I := l; have h : d=l.toDecidableEq:=Subsingleton.elim _ _; rw [h]; exact l.compare_eq_compareOfLessAndEq}
end YM.CF.Buffered.Cin
#print axioms YM.CF.Buffered.Cin.Framed.theta
#print axioms YM.CF.Buffered.Cin.Installed.uniform_flip
