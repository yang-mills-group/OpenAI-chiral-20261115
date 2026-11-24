import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
open Function Finset Matrix
open scoped Topology BigOperators Matrix Classical

namespace YM.SU5.FiniteGaugeData.Drachma
/- operations on real counting measures -/
abbrev coin (ι:Type) := ι→ℝ
abbrev sp (ι:Type) := Matrix ι ι ℝ
variable {X W Y Z:Type}
variable [Fintype X][Fintype Y][Fintype Z][Fintype W][DecidableEq X][DecidableEq Y][DecidableEq Z][DecidableEq W]

abbrev prizes (T : Matrix Y X ℝ) : sp X := Tᵀ*T
abbrev boost (T : sp Y)(A : Matrix Y X ℝ) := Aᵀ*T*A
omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
lemma prize_sym (T : Matrix Y X ℝ): (prizes T).IsSymm:=by simp [Matrix.IsSymm,prizes]
omit [DecidableEq X] [DecidableEq Y] in
lemma prize_bill(A : Matrix Y X ℝ) (x y:coin X): dotProduct x (prizes A*ᵥ y)=dotProduct (A *ᵥ x) (A *ᵥ y):=by rw [prizes,← mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
omit [DecidableEq X] [DecidableEq Y] in
lemma boost_bill(A : Matrix Y X ℝ)(T:sp Y) (x y:coin X): dotProduct x (boost T A *ᵥ y)=dotProduct (A*ᵥ x) (T*ᵥ (A*ᵥ y)):=by rw [boost,←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
omit [DecidableEq X] [DecidableEq Y] in
lemma prize_nn(A:Matrix Y X ℝ)(x:coin X): 0≤dotProduct x (prizes A*ᵥ x):=by rw [prize_bill]; exact sum_nonneg fun i _=> mul_self_nonneg _
omit [DecidableEq Y] [DecidableEq X] in
lemma plus_bill(A B:Matrix Y X ℝ)(x:coin Y)(y:coin X):dotProduct x ((A+B)*ᵥ y)= dotProduct x (A*ᵥ y)+dotProduct x (B*ᵥ y):=by rw [add_mulVec,dotProduct_add]
lemma wager{T L:sp X} (h:∀ x y:coin X,dotProduct x (T*ᵥ y)=dotProduct x (L*ᵥ y)): T=L:=by ext i j; simpa using h (Pi.single i 1) (Pi.single j 1)
lemma wager_det(T:sp X)(S:sp X)(h: |S.det|=1): (boost T S).det=T.det:=by
 rw [boost,det_mul,det_mul,det_transpose]; rw [show S.det*T.det*S.det=S.det^2*T.det by ring, ← sq_abs,h]; ring

/-- Change of the null channel penalty (full matrix, not pseudo-det). E is a list of null directions. The integer estimate for trunks is separate. -/
lemma tally (T:sp X)(A B: Matrix Y X ℝ)(E:Matrix X Y ℝ)(he:A*E=1)(hl: T*E=0)(h:T.IsSymm) (v: |(B*E).det|=1):
 (T+prizes A).det=(T+prizes B).det:=by
 let S:=1+E*(B-A)
 have hq:A*S=B:=by unfold S; rw [Matrix.mul_add,← Matrix.mul_assoc,he]; simp
 have hp:T*S=T:=by unfold S; rw [Matrix.mul_add,← Matrix.mul_assoc,hl]; simp
 have hy:Sᵀ*T=T:= calc
    _=(T*S)ᵀ:=by rw [transpose_mul,h.eq]
    _=T:=by rw [hp,h.eq]
 have hv : |(S.det)|=1:=by unfold S; rw [det_one_add_mul_comm,Matrix.sub_mul,he]; simpa
 rw [←wager_det (T+prizes A) S hv]; congr 1
 unfold boost prizes; rw [Matrix.mul_add Sᵀ T ,Matrix.add_mul,hy,hp,←Matrix.mul_assoc Sᵀ Aᵀ A, ←transpose_mul,hq, Matrix.mul_assoc,hq]

/-- integral-change certificate for that determinant. maps all counting lattice points, and likewise a right inverse. -/
def integralMap (S:Matrix X Y ℝ) := ∀ x':Y→ℤ,∃ y':X→ℤ, S *ᵥ (fun i=> ↑(x' i))= fun i=> ↑(y' i)
lemma intact (T S:sp X)(h:T*S=1)(hT:integralMap T)(hS:integralMap S): |T.det|=1:=by
 let p:= Int.castRingHom ℝ
 have he(A:sp X)(hx:integralMap A): ∃ L: Matrix X X ℤ,L.map p=A:=by
    choose y hy using fun j=>hx (Pi.single j 1)
    refine ⟨Matrix.of fun i j=> y j i,?_⟩; ext i j; have hp:=hy j; rw [show (fun (k:X)=> (((Pi.single j 1:X→ℤ) k):ℝ))=Pi.single j (1:ℝ) from funext fun i=>by by_cases h:i=j <;>simp [h]] at hp
    change (y j i:ℝ)=_; simpa using (congr_fun hp i).symm
 obtain ⟨A,hA⟩:=he T hT; obtain ⟨B,hB⟩:=he S hS; rw [← hA,← hB,← RingHom.mapMatrix_apply,← RingHom.mapMatrix_apply] at h -- tune
 have hc:A*B=1:=by
    have he : p.mapMatrix (A*B)=p.mapMatrix 1:=by rw [map_mul,map_one,h]
    ext i j; apply Int.cast_injective (α:=ℝ); exact congr_fun (congr_fun he i) j
 rw [←hA,← RingHom.mapMatrix_apply,← p.map_det]; change |(A.det:ℝ)|=1; exact_mod_cast (Int.isUnit_iff_abs_eq.mp (Matrix.isUnit_det_of_right_inverse hc))

/-- joined operators and projections -/
abbrev ℓ(X Y:Type)(x:coin (X⊕Y)):coin X:=fun i=>x (.inl i)
abbrev ℜ(X Y:Type)(x:coin (X⊕Y)):coin Y:=fun i=>x (.inr i)
abbrev swapper (x:coin X)(y:coin Y):coin (X⊕Y):=Sum.elim x y
omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma born_l(x:coin X)(y:coin Y): ℓ X Y (swapper x y)=x:=rfl
omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma born_r(x:coin X)(y:coin Y): ℜ X Y (swapper x y)=y:=rfl
omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma born_two(x:coin (X⊕Y)): swapper (ℓ X Y x) (ℜ X Y x)=x:=by funext i; cases i <;> rfl
def fromCols(A:Matrix X Y ℝ)(B:Matrix X Z ℝ): Matrix X (Y⊕Z) ℝ:= .of fun i j=>j.elim (A i) (B i)
def fromRows(A:Matrix Y X ℝ)(B:Matrix Z X ℝ): Matrix (Y⊕Z) X ℝ:= .of (Sum.elim (fun i=>A i) (fun i=>B i))
omit [Fintype X][DecidableEq X][DecidableEq Y][DecidableEq Z] in
lemma onCols(A:Matrix X Y ℝ)(B:Matrix X Z ℝ)(x:coin (Y⊕Z)): fromCols A B*ᵥ x= A *ᵥ ℓ Y Z x+B *ᵥ ℜ Y Z x:= by
 ext i; exact Fintype.sum_sum_type (fun j : Y⊕Z=>fromCols A B i j * x j)
abbrev sty_l(X Y:Type)[DecidableEq X] : Matrix X (X⊕Y) ℝ:= fromCols 1 0
abbrev sty_r(X Y:Type)[DecidableEq Y] : Matrix Y (X⊕Y) ℝ:= fromCols 0 1
omit [DecidableEq Y] in
@[simp] lemma sty_l_bill(x:coin (X⊕Y)): sty_l X Y *ᵥ x=ℓ X Y x:=by
 rw [sty_l,onCols]; simp
omit [DecidableEq X] in
@[simp] lemma sty_r_bill(x:coin (X⊕Y)): sty_r X Y *ᵥ x=ℜ X Y x:=by
 rw [sty_r,onCols]; simp
omit [DecidableEq X][DecidableEq Y][Fintype X] [Fintype Z] [DecidableEq Z] in
lemma rband(A:Matrix X Y ℝ)(B:Matrix Z Y ℝ)(x:coin Y): fromRows A B*ᵥ x=swapper (A*ᵥ x) (B*ᵥ x):=by
 funext i; cases i <;> rfl
omit [DecidableEq X][DecidableEq Y] in
lemma bills(x y:coin (X⊕Y)):dotProduct x y=dotProduct (ℓ X Y x) (ℓ X Y y)+dotProduct (ℜ X Y x) (ℜ X Y y):= Fintype.sum_sum_type _
abbrev sided(A:sp X)(B:sp Y): sp (X⊕Y):= fromBlocks A 0 0 B
omit [DecidableEq X][DecidableEq Y] in
lemma sidedBill(A:sp X)(B:sp Y)(x y:coin (X⊕Y)):dotProduct x (sided A B*ᵥ y)=dotProduct (ℓ X Y x) (A*ᵥ ℓ X Y y)+dotProduct (ℜ X Y x) (B*ᵥ ℜ X Y y):=by
 rw [bills]
 have hp:sided A B *ᵥ y=swapper (A*ᵥ ℓ X Y y) (B*ᵥ ℜ X Y y):=by
    nth_rw 1 [←born_two y]; rw [sided, fromBlocks_mulVec]; simp
 rw [hp,born_l,born_r]
omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
lemma sidedSym(A:sp X)(B:sp Y)(he:A.IsSymm)(ht:B.IsSymm): (sided A B).IsSymm:=by
 unfold Matrix.IsSymm sided; rw [fromBlocks_transpose]; simp [he.eq,ht.eq]
lemma sided_det(A:sp X)(B:sp Y): (sided A B).det=A.det*B.det:= by rw [sided,det_fromBlocks_zero₂₁]

abbrev layer(A:Matrix Y X ℝ):sp (X⊕Y):= fromBlocks 1 0 A 1
abbrev spray(A:Matrix X Y ℝ):sp (X⊕Y):= fromBlocks 1 A 0 1
lemma layer_bill(A:Matrix Y X ℝ)(x:coin (X⊕Y)): layer A*ᵥ x=swapper (ℓ X Y x) ((A*ᵥ ℓ X Y x)+ℜ X Y x):= by nth_rw 1 [←born_two x]; rw [layer, fromBlocks_mulVec]; simp
lemma spray_bill(A:Matrix X Y ℝ)(x:coin (X⊕Y)): spray A*ᵥ x=swapper (ℓ X Y x + (A*ᵥ ℜ X Y x)) (ℜ X Y x):= by nth_rw 1 [←born_two x]; rw [spray, fromBlocks_mulVec]; simp
lemma layer_det(A:Matrix Y X ℝ): |(layer A).det|=1:=by rw [layer,det_fromBlocks_zero₁₂]; simp
lemma spray_det(A:Matrix X Y ℝ): |(spray A).det|=1:=by rw [spray,det_fromBlocks_zero₂₁]; simp
end YM.SU5.FiniteGaugeData.Drachma
