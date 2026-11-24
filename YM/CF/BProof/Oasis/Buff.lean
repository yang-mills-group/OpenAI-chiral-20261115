import YM.CF.BProof.Oasis.Sand
import YM.CF.BProof.Wick.Dict
/-! Matrix granting actual extended ordered-letter costs. Never swaps across
classes before the physical pairing. Use strict LE from chosen `LinearOrder` on
LeanV (not an instance rebuilt using the product order). -/
set_option autoImplicit false
set_option synthInstance.maxSize 10000
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I]
abbrev hotter {T:Type*}[LinearOrder T](a b:T) : Prop:= a < b
def censor (d:I→I→ℂ): Op I := Matrix.of fun i j => if i < j then d i j else if j < i then -d j i else 0
lemma censor_hot(d:I→I→ℂ){i j:I}(g:i<j):censor d i j=d i j:=if_pos g
lemma censorSkew(d:I→I→ℂ):(censor d)ᵀ= -censor d:=by ext i j; rcases lt_trichotomy i j with p|p|p; simp [p,Matrix.transpose_apply,censor,not_lt.mpr p.le]; simp [p,censor,Matrix.transpose_apply]; simp [p,not_lt.mpr p.le,Matrix.transpose_apply,censor] -- tune
lemma bendEither{J:Type*} -- J Type, Flame def
 (i: Sum I (LeanV I)) : i=i:=rfl
lemma either{J:Type}[Fintype J][LinearOrder J](i:Flame I J) : (∃ j:I,bendL j=i) ∨ ∃ j:J,bendR j=i:=by cases g:ofLex i with| inl j=> exact Or.inl ⟨j,(ofLex.injective g.symm)⟩| inr j=>exact Or.inr ⟨j,ofLex.injective g.symm⟩
lemma flip_sort{J:Type}[Fintype J][LinearOrder J](i j:Flame I J)(g:i≤j): polite i j:=by
 rcases either i with ⟨b,rfl⟩|⟨b,rfl⟩; exact trivial; rcases either j with ⟨c,rfl⟩|⟨c,rfl⟩; exact False.elim (Sum.Lex.not_inr_le_inl g); exact rfl -- tune order
lemma censorTruth{J K:Type}[Fintype J][LinearOrder J][Fintype K][LinearOrder K](A:Poly I K)(B:Poly J K)(M:FC K→ₗ[ℂ] ℂ){d:Flame I J→ Flame I J →ℂ}(s: Scores d (fun l=>M (rollC (act A B) l))) : ∀ i j,polite i j→ d i j=censor d i j:=by
 have hx(i j: Flame I J)(g:polite i j)(h:polite j i) : d i j+d j i=0:=by
   rw [←s.two i j,←s.two j i]; simp only [rollC,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,←map_add]; rw [show act A B i*act A B j+ act A B j*act A B i=0 from ?_, map_zero]; rcases either i with ⟨b,rfl⟩|⟨b,rfl⟩ <;> rcases either j with ⟨c,rfl⟩|⟨c,rfl⟩; exact A.anti b c; contradiction; contradiction; exact B.anti b c -- tune contradiction
 intro i j h; unfold censor; rw [Matrix.of_apply]; split; rfl; rename_i g; have hf:= hx i j h (flip_sort _ _ (le_of_not_gt g)); by_cases t:i=j; · subst j; rw [if_neg (lt_irrefl _)]; exact add_self_eq_zero.mp hf
 rw [if_pos (lt_of_le_of_ne (not_lt.mp g) (Ne.symm t))]; exact eq_neg_of_add_eq_zero_left hf
abbrev Wind(I:Type):= Flame I (LeanV I)
abbrev Grain:= Option Bool -- none first, true creation second, false annihilation second
def seam(i:Wind I): Grain×I:= Sum.elim (fun j=>(none,j)) (fun j=>(some j.1,j.2)) (ofLex i)
def chart (I:Type)[Fintype I][LinearOrder I]: Wind I ≃ Grain×I where
 toFun:=seam
 invFun:=fun i=> i.1.elim (bendL i.2) (fun j=>bendR (j,i.2))
 left_inv i:=by rcases either i with ⟨b,rfl⟩|⟨⟨d,k⟩,rfl⟩ <;> rfl
 right_inv:=by rintro ⟨(-|i),j⟩ <;> rfl
abbrev bedT(i:Wind I): Double.Tree I:= Sum.inl (seam i).2
def stageP (A C:Op I)(u:Grain): M I:= u.elim (unitScale • bill C 0 1 0) (fun i=> if i then bill (1-A) 0 0 0 else bill 0 0 (cc A) 0)
def glass(A C:Op I)(i:Wind I): Book I:=acts (stageP A C (seam i).1) (basisKet (bedT i))
@[simp] lemma basis_mark (i:I): rows (basisKet (Sum.inl i) : Book I)=basisKet i:=by apply PiLp.ext; intro j; simp [rows,basis_apply]
@[simp] lemma basis_not (i:I): cols (basisKet (Sum.inl i) : Book I)=0:=by apply PiLp.ext; intro j; simp [cols,basis_apply]
lemma castL(A C:Op I)(i:I): glass A C (bendL i)=spear C i:=by unfold glass; change acts (unitScale • bill C 0 1 0) (basisKet (Sum.inl i))=_; rw [act_smul]; apply book_ext <;> simp [spear]
lemma castR {I:Type}[Fintype I][LinearOrder I](A C:Op I)(i:LeanV I): printT (glass A C (bendR i))= drawT A i:=by
 rcases i with ⟨(-|-),i⟩
 · rw [printed,glass]; change create (rows (acts (bill 0 0 (cc A) 0) (basisKet (Sum.inl i)))) + remove (pend (cols (acts (bill 0 0 (cc A) 0) (basisKet (Sum.inl i)))))=hideF A i; rw [hideF,prong_t]; simp [remove,pend_move,cc_cc,pend_base]
 rw [printed,glass]; change create (rows (acts (bill (1-A) 0 0 0) (basisKet (Sum.inl i)))) + remove (pend (cols (acts (bill (1-A) 0 0 0) (basisKet (Sum.inl i)))))=seekF A i; rw [seekF,prong_p]; simp [remove,pend_zero]
lemma token_x {N:Side} {A C:Op (Single N)}(h:IsStarProjection A)(v:Cᵀ= -C)(i:Lv N) : act (Oasis.letter C v) (nursery A h) i=printT (glass A C i):=by rcases either i with ⟨j,rfl⟩|⟨j,rfl⟩; rw [castL]; rfl; exact (castR ..).symm
abbrev Leads (I:Type)[Fintype I][LinearOrder I]:= Grain→Grain→ M I
def draft(M:M I)(A C:Op I): Leads I:= fun i j=> (stageP A C i)ᵀ * M *stageP A C j
def flank(A:Leads I)(i j:Wind I):= A (seam i).1 (seam j).1 (bedT i) (bedT j)
lemma flankIssue[Nonempty I]{A B P Q C:Op I}(i j: Wind I): Wick.issue A P Q C (glass B C i) (glass B C j)= flank (draft (cern A P Q C) B C) i j:=by rw [issue_inner]; unfold glass flank draft; rw [← basis_act (_ * _* _) _,←basis_inner,act_mul (_*_),act_mul (stageP _ _ _)ᵀ]; rw [←act_inner (stageP B C (seam i).1)ᵀ]; simp only [pend_move,pend_base,show ∀ A:M I, star Aᵀ=cc A from fun A=> by ext i j; rfl] -- tune ellipsis
end YM.CF.BProof.Oasis
