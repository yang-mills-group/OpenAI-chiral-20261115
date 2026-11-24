import YM.CF.Scroll.Loma
import YM.CF.BProof.Align.Table

/-! Elementary block matrix identities. Wick symbols v,w (complex linear space).
Matrix charge kept site-preserving when moving through this equity. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I]
abbrev Tree (I:Type*):= I ⊕ I
abbrev M (I:Type*):= Op (Tree I)
abbrev Book (I:Type*):= Ket (Tree I)
def rows(x: Book I): Ket I:= WithLp.toLp 2 fun i=> x.ofLp (Sum.inl i)
def cols(x: Book I): Ket I:= WithLp.toLp 2 fun i=> x.ofLp (Sum.inr i)
def join(x y: Ket I):Book I:= WithLp.toLp 2 (Sum.elim x.ofLp y.ofLp)
lemma book_ext {x y:Book I}(p: rows x=rows y)(q:cols x=cols y):x=y:=by apply PiLp.ext; rintro (i|i); exact congrArg (fun x:Ket I=> x.ofLp i) p; exact congrArg (fun x:Ket I=>x.ofLp i) q
@[simp] lemma row_join (x y:Ket I): rows (join x y)=x:=rfl
@[simp] lemma col_join (x y:Ket I): cols (join x y)=y:=rfl
@[simp] lemma join_read(x: Book I): join (rows x) (cols x)=x:= book_ext rfl rfl
variable (x y: Book I)(A B C D:Op I)
abbrev bill (A B C D: Op I): M I:= Matrix.fromBlocks A B C D
@[simp] lemma add_rows : rows (x+y)=rows x+rows y:=rfl
@[simp] lemma add_cols : cols (x+y)=cols x+cols y:=rfl
@[simp] lemma sub_rows : rows (x-y)=rows x-rows y:=rfl
@[simp] lemma sub_cols : cols (x-y)=cols x-cols y:=rfl
@[simp] lemma smr_rows (c:ℂ): rows (c • x)= c • rows x:=rfl
@[simp] lemma smr_cols (c:ℂ): cols (c • x)= c • cols x:=rfl
@[simp] lemma bio : rows (acts (bill A B C D) x)= acts A (rows x)+acts B (cols x):=by apply PiLp.ext; intro i; unfold rows; simp [act_at,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,bill]; rfl
@[simp] lemma mead : cols (acts (bill A B C D) x)= acts C (rows x)+acts D (cols x):=by apply PiLp.ext; intro i; unfold cols; simp [act_at,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,bill]; rfl
lemma sumNote : ‖x‖^2=‖rows x‖^2+‖cols x‖^2:=by rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Fintype.sum_sum_type]; rfl
lemma bio_cost : ‖rows x‖ ≤ ‖x‖:=by nlinarith [sumNote x,norm_nonneg x,norm_nonneg (rows x)]
lemma mead_cost : ‖cols x‖≤‖x‖:=by nlinarith [sumNote x,norm_nonneg x,norm_nonneg (cols x)]
lemma bag_cost : ‖x‖ ≤ ‖rows x‖+‖cols x‖:=by nlinarith [sumNote x,norm_nonneg x,norm_nonneg (rows x),norm_nonneg (cols x)]
lemma bill_star : star (bill A B C D)=bill (star A) (star C) (star B) (star D):= Matrix.fromBlocks_conjTranspose ..
lemma bill_cc : cc (bill A B C D)= bill (cc A) (cc B) (cc C) (cc D):= by ext (i|i) (j|j)<;>rfl
lemma bill_sub (A' B' C' D':Op I) : bill A B C D - bill A' B' C' D'= bill (A-A') (B-B') (C-C') (D-D'):=by ext (i|i) (j|j)<;> rfl
lemma bill_add (A' B' C' D':Op I) : bill A B C D+bill A' B' C' D'= bill (A+A') (B+B') (C+C') (D+D'):=by ext (i|i) (j|j)<;> rfl
-- cc transport on Ket
def pend (x:Ket I):Ket I:=WithLp.toLp 2 (fun i=> star (x.ofLp i))
lemma pend_p (x:Ket I): pend (pend x)=x:=by apply PiLp.ext; intro i; simp [pend]
lemma pend_norm (x:Ket I) : ‖pend x‖=‖x‖:=by rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]; simp [pend]
lemma pend_move (x:Ket I):pend (acts A x)=acts (cc A) (pend x):=by apply PiLp.ext; intro i; simp [act_at,Matrix.mulVec,dotProduct,pend]
lemma pend_inner (x y: Ket I): inner ℂ (pend x) (pend y)=star (inner ℂ x y):=by rw [EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct]; simp [pend,dotProduct,mul_comm]
lemma pend_zero : pend (0:Ket I)=0:=by apply PiLp.ext; intro i; simp [pend]
lemma cc_mono {A B:Op I}(h:A ≤ B): cc A≤cc B:=by
 apply sub_nonneg.mp; obtain ⟨X,hX⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr h); rw [←cc_sub,hX,cc_mul,cc_star]; exact star_mul_self_nonneg _
end YM.CF.BProof.Double
