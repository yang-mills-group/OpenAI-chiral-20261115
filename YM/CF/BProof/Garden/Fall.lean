import YM.CF.BProof.Garden.Green
import YM.CF.BProof.Hearth.Hoard
/-! Site phase, using determinant-one color matrix on spin 0 & spin 2. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Fig Hearth Spin
open Lat Mir SU Lattice Dial Tenant Cube Tulip
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
def stake (M:Support N):Finset (Single N):=bandSites M true∪ bandSites M false
abbrev chef (x:Site N):= stake ({x}:Support N)
@[simp] lemma mem_stake (i:Single N)(M:Support N): i∈stake M ↔ i.1.1∈M:=by simp [stake,spHalf]; tauto
@[simp] lemma stake_union(S T:Support N): stake (S∪T)=stake S∪stake T:=by ext i; simp
@[simp] lemma stake_empty : stake (∅:Support N)=∅:=by ext i; simp
@[simp] lemma stake_all : stake (univ:Support N)=univ:=by ext i; simp
lemma stake_umbrella {S T: Support N}(d:Disjoint S T): Disjoint (stake S) (stake T):= disjoint_left.mpr (fun _ h v=> disjoint_left.mp d ((mem_stake ..).mp h) ((mem_stake ..).mp v))
lemma stake_up {S T:Support N}(h:S⊆T): stake S⊆stake T:=fun i e=>(mem_stake ..).mpr (h ((mem_stake ..).mp e))
def slotsu:= Fintype.card SpinIdx * Fintype.card Slot
lemma stake_count (x:Site N): (chef x).card = slotsu:=by
 rw [show chef x=((({x}:Support N) ×ˢ (univ:Finset SpinIdx)) ×ˢ (univ:Finset Slot)) from ?_]; simp only [slotsu,card_product,card_singleton,card_univ,one_mul]
 ext ⟨⟨y,i⟩,j⟩; simp [chef,eq_comm]
lemma band_separate(S:Support N): Disjoint (bandSites S true) (bandSites S false):=by rw [Finset.disjoint_left]; simp [spHalf]; tauto
lemma stakesplit {S T:Support N}(h:Disjoint S T)(F:Quilt N): square (stake S∪stake T) (pair F)= square (stake S) (pair F)+square (stake T) (pair F):=by
 have he:=stake_umbrella h; ext i j; simp only [square_entry,Matrix.add_apply]; by_cases d:i.1.1=j.1.1; swap; · simp only [pair_local,d,↓reduceIte,ite_self, add_zero]
 have ht:i.1.1∈ S → i.1.1∉T:=fun k=>disjoint_left.mp h k; simp only [mem_union, mem_stake, ←d]; by_cases f:i.1.1∈ S; simp [f,ht f]; simp [f] -- tune
-- commute plus and all with color-only site spins
lemma leapComm (A:Page N→Stamp)(S:Support N)(u:Bool) : Commute (jump (Equiv.refl _) A) (cutM (bandSites S u)):=by
 ext ⟨x,i⟩ ⟨y,j⟩; rw [cutM, Matrix.diagonal_mul, Matrix.mul_diagonal]; by_cases h:x=y; subst y; simp only [mem_band,jump_apply]; rw [mul_comm]; simp only [jump_apply,Equiv.refl_apply,h,ite_false,mul_zero,zero_mul] -- second case
lemma totalComm (A:Page N→Stamp)(S:Support N) : Commute (jump (Equiv.refl _) A) (cutM (stake S)):=by
 ext ⟨x,i⟩ ⟨y,j⟩; rw [cutM, Matrix.diagonal_mul, Matrix.mul_diagonal]; by_cases h:x=y; subst y; simp only [mem_stake,jump_apply]; rw [mul_comm]; simp only [jump_apply,Equiv.refl_apply,h,ite_false,mul_zero,zero_mul]
def rowX(A:Quilt N) (x:Page N):Stamp:=if x.2.val=0 ∨ x.2.val=2 then A (node x.1) else 1
lemma bracketLemma (f g:Page N→Stamp)(X:Op (Page N))(i j:Page N)(u v:Slot): (jump (Equiv.refl _) f * (X ⊗ₖ (1:Stamp))*jump (Equiv.refl _) g) (i,u) (j,v)= X i j * (f i*g j) u v:=by
 have he(i j:Page N)(u v:Slot) : (jump (Equiv.refl _) f * (X ⊗ₖ (1:Stamp))) (i,u) (j,v)= X i j*f i u v:=by
   rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp_rw [jump_apply,Equiv.refl_apply,ite_mul,zero_mul,sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]; simp [Matrix.one_apply,mul_comm]
 rw [Matrix.mul_apply, Matrix.mul_apply,Fintype.sum_prod_type]; simp_rw [jump_apply,Equiv.refl_apply,mul_ite,mul_zero,sum_ite_irrel,sum_const_zero,sum_ite_eq',mem_univ,ite_true,he,mul_assoc,mul_sum]
lemma leapForm (A:Quilt N)(h:∀ x,SealH (A x)): pair A= jump (Equiv.refl _) (rowX A)*pair (fun _=>1)* (jump (Equiv.refl _) (rowX A))ᵀ:=by
 rw [pair_const, show (jump (Equiv.refl _) (rowX A))ᵀ=jump (Equiv.refl _) (rowX A) from (by
   ext ⟨x,u⟩ ⟨y,v⟩; by_cases d:x=y
   · subst y; simp only [jump_apply,Equiv.refl_apply,ite_true,Matrix.transpose_apply]; have he:(rowX A x)ᵀ=rowX A x:=by unfold rowX; split; apply (h _).symm; apply Matrix.transpose_one
     exact Matrix.ext_iff.mpr he u v
   simp only [Matrix.transpose_apply,jump_apply,Equiv.refl_apply,d,Ne.symm d,ite_false])]; -- brackets nested ?
 ext ⟨⟨x,i⟩,u⟩ ⟨⟨y,j⟩,v⟩; rw [bracketLemma]; simp only [pair_entry,tileA,jump_apply,Equiv.refl_apply]; by_cases d:x=y; · subst y; simp only [ite_true]; fin_cases i <;> fin_cases j <;> norm_num [spinJ,rowX,SpinIdx]
 simp only [d,ite_false,zero_mul]
lemma leapMoney (A:Page N→Stamp)(h:∀ i,(A i).det=1)(S:Support N) (u:Bool) : quant (jump (Equiv.refl _) A) (bandSites S u) (bandSites S u)=1:=by
 let T(i:Page N):Stamp:= if i.1∈ S ∧ i.2∈ spHalf u then A i else 1; have he:padded (bandSites S u) (jump (Equiv.refl _) A)=jump (Equiv.refl _) T:=by
   ext ⟨x,i⟩ ⟨y,j⟩; unfold padded cutM; rw [Matrix.add_apply, Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases d:x=y
   · subst y; by_cases l:x.1∈S ∧ x.2∈spHalf u <;> by_cases e:i=j <;> simp [jump_apply,l,T,e,Matrix.one_apply] -- tune
   simp [d,Matrix.one_apply,jump_apply]
 rw [Fock.principal,he,Mir.jump_det]; exact prod_eq_one fun x _=>by unfold T; split; apply h; apply Matrix.det_one
lemma sitePay (A:Quilt N)(h:∀ x,SealH (A x))(S:Support N): pf (pair A) (bandSites S true)=pf (pair (N:=N) (fun _=>1)) (bandSites S true):=by rw [leapForm A h,pf_frame (leapComm (rowX A) S true).eq,leapMoney (rowX A) (fun i=>by unfold rowX; split; exact (h _).det; exact Matrix.det_one),one_mul]
lemma siteNorm (A:Quilt N)(h:∀ x,SealH (A x))(S:Support N): ‖pf (pair A) (bandSites S true)‖=1:=pf_unit _ ⟨_,pair_unit (fun z=>(h z).norm)⟩ (pair_skew _ (fun z=>(h z).symm)) (pairCom S A true).symm
end YM.CF.BProof.Garden
