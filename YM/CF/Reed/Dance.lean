import YM.CF.Reed.Tip
import YM.CF.Reflect.Cone

/-! Matrix reflection restricts to order reversal on physical graded words. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock NormedSpace Function Finset Pastry Phase Reflect
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
-- Θ partner, twisted by chord to obtain actual order reversal within the nilpotent physical subspace
def reverseW (U : UNI n) (b : Bool) (A : FC n) := chord b • theta U A
inductive Fine (s t : Finset n) : Bool→ FC n → Prop where
  | empty b : Fine s t b 0
  | one : Fine s t false 1
  | seed i : i∈t→ Fine s t true ((think s).term i)
  | grow {P Q a b} : Fine s t a P → Fine s t b Q → Fine s t (a.xor b) (P*Q)
  | add {a P Q} : Fine s t a P → Fine s t a Q → Fine s t a (P+Q)
  | scale {a P} : Fine s t a P→∀ c:ℂ,Fine s t a (c • P)
namespace Fine
variable {s t : Finset n} {P Q : FC n} {a b : Bool}
lemma sector (h : Fine s t a P) : Sector t a P := by
  induction h with
  | empty=> apply Sector.zero
  | one=> apply Sector.one
  | seed i p=> by_cases g:i∈s
               · rw [show (think s).term i=put i from if_pos g]; exact Sector.up i p
               rw [show (think s).term i= -takeF i from if_neg g]; simpa using (Sector.down i p).scale (-1)
  | grow _ _ ih it=> exact ih.mul it
  | add _ _ ih it=> exact ih.add it
  | scale _ c ih=> exact ih.scale _
lemma writer (h : Fine s t a P) : ∃ x, Absorb t x ∧ P=(think s).eval x := by
  induction h with
  | empty=> exact ⟨0,Absorb.zero,(map_zero _).symm⟩
  | one=> exact ⟨1,Absorb.one,(Poly.eval_one ..).symm⟩
  | seed i p=> exact ⟨put i,Absorb.blade p,(eval_blade ..).symm⟩
  | grow _ _ ih it=> obtain ⟨x,g,H⟩:=ih; obtain ⟨y,l,L⟩:=it; exact ⟨x*y,g.times l,by rw [H,L,g.eval l]⟩
  | add _ _ ih it=> obtain ⟨x,g,H⟩:=ih; obtain ⟨y,l,L⟩:=it; exact ⟨x+y,g.sum l,by rw [H,L,map_add]⟩
  | scale _ c ih=> obtain ⟨x,g,H⟩:= ih; exact ⟨c • x,g.scale c,by rw [H,map_smul]⟩
lemma sumF {I : Type*} (S : Finset I) (F : I→FC n) (h : ∀ i∈S,Fine s t a (F i)) : Fine s t a (∑ i∈S,F i) := by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [sum_empty]; apply empty
  | insert i S p ih=> rw [sum_insert p]; exact (h i (mem_insert_self ..)).add (ih (fun i g=>h i (mem_insert_of_mem g)))
lemma sign_com (h : Fine s t a P) (k : Fine s t b Q) : P*Q=Sector.grainB a b • (Q*P) := by
  have row (P Q T:FC n) (a b c:Bool) (h:P*Q=Sector.grainB a b • (Q*P)) (g:P*T=Sector.grainB a c • (T*P)) : P*(Q*T)=Sector.grainB a (b.xor c) • (Q*T*P) := by
    rw [←mul_assoc,h,Algebra.smul_mul_assoc,mul_assoc Q,g,Algebra.mul_smul_comm, ←mul_assoc,smul_smul]; cases a <;> cases b <;> cases c <;> simp [Sector.grainB]
  have flip (P Q:FC n) (a b: Bool) (h:P*Q=Sector.grainB a b • (Q*P)): Q*P=Sector.grainB b a • (P*Q) := by rw [h,Sector.grain_swap b,smul_smul, Sector.grain_self,one_smul]
  induction h with
  | empty=>simp
  | one=> simp [Sector.grainB]
  | seed i p=>
    induction k with
    | empty=> simp
    | one=> simp [Sector.grainB]
    | seed j q=> simp only [Sector.grainB,Bool.and_true,ite_true,neg_one_smul]; exact (think s).swapV ..
    | grow _ _ ih it=> exact row _ _ _ _ _ _ ih it
    | add _ _ ih it=> rw [mul_add,add_mul, ih,it,smul_add]
    | scale _ c ih=> rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,ih,smul_comm]
  | grow _ _ ih it=> exact flip _ _ _ _ (row _ _ _ _ _ _ (flip _ _ _ _ ih) (flip _ _ _ _ it))
  | add _ _ ih it=> rw [mul_add,add_mul,ih,it,smul_add]
  | scale _ c ih=> rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,ih,smul_comm]
-- Pin map transport flips grading
variable {U : UNI n} {T : Finset n} (e : twist U (cutM t)=cutM T) (p : twist U (cutM sᶜ)=cutM s)
lemma entry {i j:n} (e : twist U (cutM t)=cutM T) (v : i∈t) (k : j∉T) : U.val j i=0 := by
  have hp : twist U (cutM t)*U.val=U.val*cutM t:= twist_product ..
  rw [e] at hp; have he := Matrix.ext_iff.mpr hp j i; simpa [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,v,k] using he.symm
lemma altitude (p : twist U (cutM sᶜ)=cutM s) : twist U (cutM s)=cutM sᶜ := by rw [dim_cut,map_sub,map_one] at p; rw [dim_cut]; nth_rw 2 [← p]; abel
-- real-time adj at bra. explicit on nil terms
lemma trans (U : UNI n) (b : Bool) (A : FC n) (c:ℂ) : reverseW U b (c • A)=star c • reverseW U b A := by rw [reverseW,theta_smul, smul_comm]; rfl
lemma renewOne {i:n} (v:i∈s) : reverseW U true ((think s).term i)=remove (acts U.val (basisKet i)) := by
  rw [reverseW, show (think s).term i=put i from if_pos v, theta_up, chord, if_pos rfl, smul_smul]; simp
lemma renewNot {i:n} (v:i∉s) : reverseW U true ((think s).term i)=create (acts U.val (basisKet i)) := by rw [reverseW, chord,if_pos rfl, show (think s).term i= -takeF i from if_neg v, show theta U (-takeF i)= -theta U (takeF i) from by simp [theta],theta_down]; simp [smul_smul]
include p e
lemma arrive (h : Fine s t b P) : Fine s T b (theta U P) := by
  induction h with
  | empty=> rw [theta_zero]; apply empty
  | one=> rw [theta_one]; apply one
  | seed i u=>
    have hz {j:n} (l:j∈T): Fine s T true ((think s).term j) := .seed j l
    have hx : Fine s T true (reverseW U true ((think s).term i)) := by
      by_cases g:i∈s
      · rw [renewOne g,←prong_t,prong]; apply Fine.sumF; intro j _
        by_cases w:U.val j i=0
        · simp only [cc_apply,w,star_zero,zero_smul]; apply empty
        have hl : j∉s := mem_compl.mp (by by_contra k; exact w (entry (altitude p) g k))
        have he := hz (j:=j) (by by_contra k; exact w (entry e u k)); rw [show (think s).term j= -takeF j from if_neg hl] at he; exact (show Fine s T true (takeF j) from by simpa using he.scale (-1)).scale _
      rw [renewNot g,←prong_p,prong]; apply Fine.sumF; intro j _; by_cases w:U.val j i=0; rw [w,zero_smul]; apply empty
      have ht : j∈s := by by_contra k; exact w (entry p (mem_compl.mpr g) k)
      apply Fine.scale; rw [←show (think s).term j=put j from if_pos ht]; exact hz (by by_contra k; exact w (entry e u k))
    have hh := hx.scale (-Complex.I); unfold reverseW at hh; simpa [chord,smul_smul] using hh
  | add _ _ ih it=> rw [theta_add]; exact ih.add it
  | grow _ _ ih it=> rw [theta_mul]; exact ih.grow it
  | scale _ c ih=> rw [theta_smul]; exact ih.scale _
lemma returnW (h : Fine s t b P) : Fine s T b (reverseW U b P) := (arrive e p h).scale _
lemma reverse_mul (h : Fine s t a P) (g : Fine s t b Q) : reverseW U (a.xor b) (P*Q)=reverseW U b Q * reverseW U a P := by
  unfold reverseW; rw [theta_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, (arrive e p g).sign_com (arrive e p h),smul_smul, ←smul_assoc, ←grade_phase, Sector.grain_swap b]; rfl -- tune order
omit p e
lemma realAdj (p : Fine s t a P) (H : U.val*U.val= -1) : reverseW U a (reverseW U a P)=P := by rw [reverseW, reverseW,theta_smul,theta_twice U H p.sector,smul_smul]; cases a <;> simp [chord]
end Fine
end YM.CF.Reed
