import YM.CF.BProof.Single.Stone
import YM.CF.Pic.Sig

/-! B-method pair matrices C(H) in Single N conventions. Color action R=matter,
not an independent frame per generation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Spin
open Function Filter NormedSpace Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Stint SU.Pair
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s N:Side}
abbrev Streak (N:Side) := Bkg (More N)
abbrev Stamp := Op Slot
structure SealH (M:Stamp) : Prop where
 norm : M ∈ unitary _
 symm : Mᵀ=M
 det : M.det=1
lemma sealX (x:Vect)(h:‖x‖=1) : SealH (fullM x):= ⟨(full_laws x h).2.2,(full_laws x h).1,(full_laws x h).2.1⟩
abbrev Quilt (N:Side) := Site (More N)→ Stamp
abbrev StampX(N:Side)(F:Stun N): Quilt N := fun o=>fullM (hook F o)
-- use pair joints for ANY H not necessarily unitary
abbrev Page (N:Side):= Site N× SpinIdx
def joint (A : Quilt N):Op (Single N):= jump (Equiv.refl (Page N)) (fun x=>A (node x.1))
def tileA (N: Side):Op (Page N) := jump (Equiv.refl _) (fun _=>spinJ)
def tile (N:Side): Op (Single N) := tileA N ⊗ₖ (1:Stamp)
def pair (A : Quilt N) := tile N * joint A
lemma tile_unit (N:Side): tile N∈unitary _ := Matrix.kronecker_mem_unitary (jump_unitary _ _ (fun _=> spinJ_unitary)) (unitary _).one_mem -- tune
lemma joint_unit {A: Quilt N} (h:∀ i, (A i) ∈unitary _): joint A ∈ unitary _:=jump_unitary _ _ (fun i=> h (node i.1))
lemma pair_unit {A: Quilt N} (h:∀ i, (A i) ∈unitary _): pair A ∈ unitary _:= (unitary _).mul_mem (tile_unit N) (joint_unit h)
lemma tile_entry (x y: Page N)(i j:Slot): tile N (x,i) (y,j) = (if x.1=y.1 then spinJ x.2 y.2 else 0) * (1:Stamp) i j:=rfl
lemma joint_entry (A: Quilt N)(x y: Page N)(i j:Slot): joint A (x,i) (y,j) = (if x=y then A (node x.1) i j else 0) :=rfl
lemma pair_entry (A:Quilt N)(x y:Page N)(i j:Slot): pair A (x,i) (y,j)=(if x.1=y.1 then spinJ x.2 y.2 * A (node x.1) i j else 0):=by
 rw [pair,Matrix.mul_apply]; unfold Single; rw [Fintype.sum_prod_type (α₁:= Page N)]; simp_rw [joint_entry,tile_entry,mul_ite,mul_zero,sum_ite_irrel,sum_const_zero,sum_ite_eq', mem_univ,ite_true]; by_cases h:x.1=y.1 <;> simp [h,Matrix.one_apply] -- tune
lemma tile_joint (A: Quilt N): Commute (tile N) (joint A):=by
 ext1 ⟨x,i⟩ ⟨y,j⟩ -- tune unfold Commute
 rw [←show pair A = tile _ * joint A from rfl,pair_entry,Matrix.mul_apply]; unfold Single; rw [Fintype.sum_prod_type (α₁:= Page N)]; simp_rw [joint_entry,tile_entry,ite_mul,zero_mul,sum_ite_irrel,sum_const_zero,sum_ite_eq, mem_univ,ite_true]; by_cases h:x.1=y.1 <;> simp [h,Matrix.one_apply,mul_comm] -- tune
lemma joint_mul (A B: Quilt N): joint A * joint B= joint (fun z=> A z*B z):=jump_mul .. -- Eq? tune
lemma joint_sub (A B: Quilt N): joint A-joint B=joint (A-B):=(jump_sub ..).symm -- tune
lemma joint_tr (A:Quilt N): (joint A)ᵀ=joint (fun z=>(A z)ᵀ):=by ext ⟨x,i⟩ ⟨y,j⟩; simp only [Matrix.transpose_apply,joint_entry]; by_cases h:x=y; rw [h]; simp [h,Ne.symm h]
lemma pair_local (A:Quilt N)(i j:Single N): pair A i j= (if i.1.1=j.1.1 then spinJ i.1.2 j.1.2*A (badgeOf i) i.2 j.2 else 0):= pair_entry ..
lemma pair_skew (A: Quilt N) (h:∀ i, (A i)ᵀ=A i) : (pair A)ᵀ = -pair A:=by
 have hh:spinJᵀ= -spinJ:=by have h:= spinJ_real; unfold cc at h; rw [←h,Matrix.transpose_transpose,h,spinJ_star]
 ext ⟨⟨x,b⟩,i⟩ ⟨⟨y,c⟩,j⟩; by_cases p:x=y; subst y; simp only [Matrix.transpose_apply,Matrix.neg_apply, pair_entry,ite_true]; rw [show spinJ c b= -spinJ b c from Matrix.ext_iff.mpr hh b c,show A (node x) j i = _ from Matrix.ext_iff.mpr (h (node x)) i j, neg_mul]; simp [Matrix.transpose_apply, pair_entry,p,Ne.symm p] -- tune
lemma pair_post (F:Stun N): pair (StampX N F)= postC F :=by
 ext ⟨⟨x,b⟩,i⟩ ⟨⟨y,c⟩,j⟩; rw [pair_entry]; rfl
lemma pair_const (M: Stamp) : pair (N:=N) (fun _=>M)=tileA N ⊗ₖ M:=by
 rw [pair,joint,jump_replicate,tile,op_kron_mul,mul_one,one_mul]
lemma freeAnti(j:ℕ)(h:1≤j)(M:Male)(B: Stamp): spar j M (1:Streak N) * pair (N:=N) (fun _=> B) = pair (N:=N) (fun _=> B) * cc (spar j M (1: Streak N)):=by
 obtain ⟨A,hA⟩:∃ A: Op (Page N),spar j M (1:Streak N)= A ⊗ₖ (1:Stamp):=by rw [spar,profile_trivial, funde_flat j h M N]; exact ⟨_,rfl⟩
 let L:Stamp:=fullM Dial.apex.val; have he:Pic.poleC N= tileA N ⊗ₖ L := by rw [Pic.poleC,←pair_post]; exact pair_const L -- tune
 have hp:= Pic.spoke j h M N; rw [he,hA,op_cc_kron,cc_one,op_kron_mul,one_mul,op_kron_mul,mul_one] at hp
 have hv:L ∈ unitary _:= (full_laws Dial.apex.val (by exact Cube.vote_unit _)).2.2
 have ht:= congrArg (fun K:Op (Single N) => K*((1:Op (Page N)) ⊗ₖ (star L* B))) hp; rw [op_kron_mul,op_kron_mul,←mul_assoc L,hv.2,one_mul,mul_one,mul_one] at ht; rw [hA,pair_const,op_cc_kron,cc_one,op_kron_mul,op_kron_mul,mul_one,one_mul]; exact ht
end YM.CF.BProof.Spin
