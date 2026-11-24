import YM.CF.BProof.Single.Port
import YM.CF.BProof.Align.Curt
import YM.CF.BProof.Fig.Layout

/-! Exact bits and assumptions of Prop B-Pproj. Centered on FERMION nodes in gauge
lattice. Use whole Space. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}(S:Support N)
def spot : Support (More N):= S.image node
@[simp] lemma spot_spec (x:Site N): node x ∈ spot S ↔ x∈ S:= by simp [spot, Tenant.needle.eq_iff]
lemma spotsNN {x:Site (More N)} (h:x∈spot S) : ∃ z∈S,node z=x:= mem_image.mp h
lemma spot_strip {D:Type}(b: Feet N D)(u:Bool): strip b.st (spot S)*bandCut S u=bandCut S u:=by
 apply op_columns; intro x; rw [act_mul,bandCut,cut_basis]; split; rename_i v; rw [strip,cut_basis,if_pos (show x∈board b.st (spot S) from mem_filter.mpr ⟨mem_univ _, by rw [b.index]; exact (spot_spec ..).2 ((mem_band ..).mp v).1⟩)]; exact map_zero _
lemma total {D:Type}(b: Feet N D): strip b.st (spot S)=bandCut S true+bandCut S false:= by
 apply op_columns; intro x; rw [act_add,bandCut,bandCut,strip,cut_basis,cut_basis,cut_basis]; simp only [board,mem_filter, mem_univ,true_and,mem_band,b.index,badgeOf,spot_spec]; by_cases p:x.1.1∈ S <;> by_cases e:x.1.2∈plusHalf <;> simp [p,e,spHalf] -- name conflict in similarly theorem
lemma pair_total (D:Quilt N){E:Type}(b:Feet N E): Commute (strip b.st (spot S)) (pair D):=by
 change _*_= _*_; ext i j; rw [stripL,stripR,b.index]; by_cases p: badgeOf i=badgeOf j; rw [p]; rw [pair_local,if_neg (show i.1.1≠ j.1.1 from fun h=> p (congrArg node h))]; simp
lemma duo : bandCut S true*bandCut S false=0:=by
 apply op_columns; intro i; rw [act_mul,act_zero,bandCut,bandCut,cut_basis]; split; rw [cut_basis]; exact if_neg (fun p=>(show i.1.2∉ plusHalf from mem_compl.mp ((mem_band S false i).mp ‹i∈ _›).2) ((mem_band S true i).mp p).2); exact map_zero _
lemma pairCom (D: Quilt N)(u:Bool) : Commute (pair D) (bandCut S u):=by
 -- via entries. spinJ overJ
 have ht(i j:SpinIdx)(h:i∈plusHalf)(g:j∉plusHalf):spinJ i j=0∧spinJ j i=0:=by
    have he:= Matrix.ext_iff.mpr overJ; have ht:=he i j; have hv:=he j i; rw [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal] at ht hv; simp [h,g] at ht hv; exact ⟨ht,hv.symm⟩
 ext i j; rw [bandCut,cutM,Matrix.diagonal_mul,Matrix.mul_diagonal,pair_local]; by_cases h:i.1.1=j.1.1; swap; · simp [h]
 by_cases e:i.1.2∈plusHalf <;> by_cases g:j.1.2∈plusHalf <;> by_cases t:j.1.1∈S <;> cases u <;> simp [spHalf,e,g,h,t] <;> first | simp [(ht i.1.2 j.1.2 e g).1] | simp [(ht j.1.2 i.1.2 g e).2] -- tune
lemma pairBy (D: Quilt N)(u:Bool) : Align.Twig (pair D) (bandCut S u):=by unfold bandCut; rw [Align.Twig,cut_real]; exact (pairCom S D u).symm
lemma blockG (g : Geometry N)(u:Bool): Commute (bandCut S u) (tradew N g).val:=by
 ext i j; rw [tradew,bandCut,cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]; simp only [jump_apply]; by_cases p:i.1=j.1 <;> simp only [p,mem_band,Equiv.refl_apply, ↓reduceIte,apply_ite,mul_zero, zero_mul] <;> split_ifs <;> simp_all
end YM.CF.BProof.Hearth
