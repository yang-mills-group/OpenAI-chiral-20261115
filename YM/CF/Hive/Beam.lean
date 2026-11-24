import YM.CF.Hive.Watt
set_option autoImplicit false
set_option maxHeartbeats 500000
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
namespace Keys
variable {ι:Type*} [DecidableEq ι]
lemma all_s(F: Finset ι)(U:ι→FC n)(p:∀ i∈F, Keys (U i)): Keys (∑ i∈F,U i):=by induction F using Finset.induction_on with| empty=>rw [sum_empty]; exact Keys.null| insert i s h ih=> rw [sum_insert h]; exact Keys.plus (p i (mem_insert_self ..)) (ih fun _ u=>p _ (mem_insert_of_mem u))
lemma tour_b(A:FC n)(p:Keys A): Keys (lotB b r U A):=by
 induction p with
 | roll D g=>

   suffices h: ∀ j:ℕ,∀ D: List (Oboe n),D.length=j+j → Keys (lotB b r U (drum D)) by obtain ⟨j,k⟩:=g; exact h j D k
   intro j; induction j with
   | zero=> rintro D h; rcases D with (_|_)<;> simp at h; rw [show drum (n:=n) []=1 from rfl,map_one]; exact Keys.roll (n:=n) [] ⟨0,rfl⟩
   | succ k ih=>
      rintro (_|⟨⟨v,i⟩,D⟩) p; simp at p
      rcases D with (_|⟨⟨x,j⟩,D⟩); simp at p; omega
      rw [show drum _ = (bell (v,i)*bell (x,j))*drum D from ?_,map_mul,map_mul]; swap; · unfold drum; simp [mul_assoc]
      refine Keys.mul ?_ (ih _ (by simp only [List.length_cons] at p; omega))
      rw [mile,mile]; unfold sound; rw [sum_mul]; refine all_s _ _ fun a _=>?_ ; rw [mul_sum]; refine all_s _ _ fun w _=>?_
      rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; apply Keys.col; apply Keys.col; let l:List (Hake.Oboe n):=[(v.xor r,a),(x.xor r,w)]; rw [show bell (v.xor r,a)*bell (x.xor r,w)=drum l by unfold drum; simp [l]]; exact Keys.roll l ⟨1,rfl⟩
 | null=>rw [map_zero]; exact Keys.null
 | plus _ _ i j=> rw [map_add]; exact Keys.plus i j
 | mul _ _ i j=>rw [map_mul]; exact Keys.mul i j
 | col v _ i=>rw [lot_s]; exact Keys.col _ i
end Keys
open Nacre
lemma lot_one(A:FC n): lotB false false 1 A=A:=by
 change twist _ A=_; rw [show quantU (1:UNI n)=1 by exact Subtype.ext quant_one]; -- dependent
 exact Fock.one_des _
variable {N:Side}
abbrev Gaze(g:Site (More N)→ SU.E): FC (Single N)→+*FC (Single N):= lotB false false (tradew N g)
lemma trade_c(g f:Site (More N)→ E):tradew N f*tradew N g=tradew N (f*g):=by unfold tradew; apply Subtype.ext; simp only [Submonoid.coe_mul]; rw [jump_mul,Equiv.refl_trans]; congr 1; funext i; rw [Pi.mul_apply,map_mul]; rfl
lemma trade_p :tradew N 1=1:=by unfold tradew; apply Subtype.ext; dsimp only; simp_rw [Pi.one_apply,map_one, OneMemClass.coe_one]; exact jump_id
lemma gauge_t (g f:Site (More N)→ E)(A:FC (Single N))(p:Keys A): Gaze f (Gaze g A) = Gaze (f*g) A:=by
 unfold Gaze; rw [hilly _ _ _ _ _ _ _ p]; rw [show tradew N f * whiten false (tradew N g) = tradew N (f*g) from trade_c g f]; rfl
lemma tr_s (g:Site (More N)→ E): whiten b (tradew N g)=tradew N (polarT b ∘ g):=by
 apply Subtype.ext; ext ⟨i,p⟩ ⟨j,l⟩; have ht(k): (matter ((polarT b ∘ g) k)).val=windX b (matter (g k)).val:=matterX _ _; rw [glint]; unfold tradew; dsimp only; rw [jump_apply]; split; next r=> rw [ht]; cases b<;> simp [windX,jump_apply,r]; -- tune
 next r=> change i≠j at r; cases b<;> simp [windX,jump_apply,r]
lemma yoT (s:Sweep N)(g:Site (More N)→E)(A:FC (Single N))(p:Keys A): teen s (Gaze g A)= Gaze ((polarT s.charge ∘ g) ∘ (castX s).anon N) (teen s A):=by
 unfold teen yodel Gaze; rw [hilly _ _ _ _ _ _ _ p,hilly _ _ _ _ _ _ _ p,tr_s]; simp only [site_ui,Bool.false_xor,Bool.xor_false,whiten, Bool.false_eq_true,↓reduceIte,envoy]
lemma lot_i(A:FC (Single N))(p:Keys A): teen 1 A=A:=by
 suffices h:Injective (teen (N:=N) 1) from h (by rw [yetL 1 1 A p,one_mul])
 have ht:detX (castX (1:Sweep N)).s=false:= det_i
 unfold teen yodel; rw [ht]; exact (twist _).injective
end YM.CF.Hive
