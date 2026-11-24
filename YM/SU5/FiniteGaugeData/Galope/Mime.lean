import YM.SU5.FiniteGaugeData.Drachma.Compa
import YM.SU5.FiniteGaugeData.Drachma.Gamut
import YM.Next.RANK.Axial
/-! # Determinant on omitted links: NO losses logarithmic in period. Need authenticated upper bound of restricted determinant, including with harmonic penalties. Here exploit deliberate choice of harmonic regulator!
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Drachma Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch CF.Font
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Classical
namespace Poeme
section
variable {n m r:Type}[Fintype n][Fintype m][Fintype r][DecidableEq n][DecidableEq m][DecidableEq r]
def foot(q : n→m): Matrix m n ℝ:= .of fun i j=> if i=q j then 1 else 0
lemma hold(q:n→m)(p:Injective q)(x:coin n)(j:n): (foot q*ᵥ x) (q j)=x j:=by unfold mulVec dotProduct; simp [foot, p.eq_iff] -- tune
lemma blankA(q:n→m)(v:m)(p: v∉ Set.range q)(x:coin n): (foot q *ᵥ x) v=0:=by
 have he(i:n): v≠q i:=fun h=> p ⟨i,h.symm⟩; unfold mulVec dotProduct; simp [foot,he] -- tune
lemma frameB(q:n→m)(x:coin m): (foot q)ᵀ *ᵥ x=x∘ q:=by ext i; simp [mulVec,dotProduct,foot]
lemma feet(A:sp m)(q:n→m):boost A (foot q)=A.submatrix q q:=by
 ext i j; simp [boost,foot,mul_apply] -- tune
lemma costsA(q:n→m)(A:sp m)(x y:coin n):dotProduct x (A.submatrix q q*ᵥ y)=dotProduct (foot q*ᵥ x) (A *ᵥ (foot q *ᵥ y)):= by rw [←feet,boost_bill]
lemma fee_v(q:n→m)(p:Injective q)(x y:coin n):dotProduct (foot q*ᵥ x) (foot q *ᵥ y)=dotProduct x y:=by
 let L:=foot q; rw [←prize_bill,show prizes (foot q)=(1:sp n) from ?_,one_mulVec]; rw [prizes, show (foot q)ᵀ*foot q=boost (1:sp m) (foot q) by simp [boost], feet]; ext i j; simp [Matrix.one_apply,p.eq_iff] -- tune
-- compare to any injected coordinate family. Schur w exact complement. Upper for excluded via full growth, could use price handles!
lemma blockcost (T: sp (n⊕m))(he:T.PosDef) (k:ℝ)(p:∀ x:coin (n⊕m), dotProduct x (T*ᵥ x)≤ k*dotProduct x x):T.det ≤ (T.submatrix Sum.inl Sum.inl).det*k^Fintype.card m:=by
 let A:=T.submatrix Sum.inl Sum.inl; let D:=T.submatrix Sum.inr Sum.inr; let B:=T.submatrix Sum.inl Sum.inr; have hA:=he.submatrix (show Injective (@Sum.inl n m) from Sum.inl_injective); change A.PosDef at hA; letI : Invertible A:= hA.isUnit.invertible
 have ht:T=fromBlocks A B Bᴴ D:=by
    ext i j; cases i <;> cases j <;> try rfl
    rename_i i j; simp only [fromBlocks_apply₂₁,conjTranspose_apply,star_trivial]; exact (Matrix.isHermitian_iff_isSymm.mp he.1).apply .. -- tune
 let P:=Bᴴ*A⁻¹*B; have hf:P.PosSemidef:= hA.posSemidef.inv.conjTranspose_mul_mul_same B -- tune
 have hQ:(D-P).PosSemidef:= (PosDef.fromBlocks₁₁ B D hA).1 (ht ▸ he.posSemidef)
 have hv:(D-P).det ≤ (k• (1:sp m)).det:= prosper hQ ((show Matrix.IsSymm (1:sp m) from ?_).smul _) (fun x=>by
    rw [sub_mulVec,dotProduct_sub,smid,one_mulVec]; apply sub_le_self _ (hf.dotProduct_mulVec_nonneg x) |>.trans -- star tune
    rw [show D=_ from rfl,costsA] -- tune
    exact (p (foot Sum.inr*ᵥ x)).trans_eq (by rw [fee_v _ Sum.inr_injective])) -- tune
 swap; · simp [Matrix.IsSymm]
 rw [det_smul,det_one,mul_one] at hv; change T.det≤ A.det*_; conv_lhs=> rw [ht,det_fromBlocks₁₁,invOf_eq_nonsing_inv] -- invInvert
 exact mul_le_mul_of_nonneg_left hv hA.det_pos.le

lemma compose_bill{n m:Type}[Fintype n][Fintype m](e:n≃m)(x y:coin m):dotProduct (x∘e) (y∘e)=dotProduct x y:= e.sum_comp (fun i=> x i*y i)
lemma det_fare(q:n→m)(h:Injective q)(T:sp m)(he:T.PosDef)(k:ℝ)(p:∀ x:coin m,dotProduct x (T*ᵥ x)≤ k*dotProduct x x): T.det≤ (T.submatrix q q).det*k^(Fintype.card m-Fintype.card n):=by
 let Y:= fun j:m=>j∈Set.range q; let V:=Subtype fun j:m=>¬ Y j
 let e:n⊕V≃m:= (Equiv.sumCongr ((Equiv.ofInjective q h)) (Equiv.refl _)).trans (Equiv.sumCompl Y)
 have hp:Fintype.card m-Fintype.card n=Fintype.card V:=by have hv:=Fintype.card_congr e; rw [Fintype.card_sum] at hv; omega
 have hq(i:n): e (.inl i)=q i:=by simp [e]; rfl -- tune
 let Z:= T.submatrix e e
 rw [←det_submatrix_equiv_self e]; change Z.det≤_; have hl:Z.submatrix Sum.inl Sum.inl=T.submatrix q q:=by ext i j; change T (e (.inl i)) (e (.inl j))=_; rw [hq,hq]; rfl
 rw [hp,← hl]; apply blockcost Z (he.submatrix e.injective); intro x; exact (p (foot e*ᵥ x)).trans' (costsA e T x x).le |>.trans_eq (by rw [fee_v _ e.injective]) -- tune
end
open Next.Rank.Axial
variable {n:Side}{P:Bed}{F:Clip}{a K:ℝ}
abbrev FreeA(n:Side):= (axle n).Free
abbrev slotZ(n:Side): FreeA n→LT n:=ηT (axle n)
lemma slot_ins: Injective (slotZ n) := fun i j h=>Subtype.ext (mark_ins h)
abbrev kindleG (P:Bed)(n:Side) := ((plaid P n+prizes (lasers n)).submatrix (slotZ n) (slotZ n))
lemma kindleSP(P:Bed)(n:Side): kindleG P n=(chips (axle n) P).submatrix (slotZ n) (slotZ n):=by
 have he:(prizes (tickets (axle n))).submatrix (slotZ n) (slotZ n)=0:=by
    have ht(i:stem (axle n))(j:FreeA n): tickets (axle n) i (slotZ n j)=0:=by
       apply one_apply_ne; exact fun h=> j.2 (mark_ins h ▸ i.2) -- tune
    ext i j; simp [prizes,mul_apply, ht]
 unfold chips kindleG; ext i j; have hh:prizes (tickets (axle n)) (slotZ n i) (slotZ n j)=0:=congr_fun (congr_fun he i) j; dsimp only [submatrix_apply,Matrix.add_apply]; rw [hh, _root_.add_zero]
lemma tight (x:coin (LT n))(i:Axis) (h:∀ e∈(axle n).trunks,x (markZ n e)=0): (lasers n *ᵥ x) i=x (markZ n (handle n i)):=by
 rw [loan]; let v:= (step i:Site n) -- syntax
 have he(k:ℕ)(j:ℕ)(p:k+j+1=n.val): linkSum (fun e=> x (markZ n e)) (k • v) (List.replicate (j+1) (posDir i))=x (markZ n (handle n i)) := by
    induction j generalizing k with
    | zero=>
       rw [List.replicate_one,linkSum,linkSum]; have hs : k • v= -v:=by
          apply eq_neg_of_add_eq_zero_left; rw [← succ_nsmul,show k+1=n.val by omega]; ext i; simp [nsmul_eq_mul] -- tune
       change (if false then -_ else _)+0=_; simp only [Bool.false_eq_true,↓reduceIte,add_zero]; rw [hs]; rfl
    | succ j ih=>
       have hy:k+1+(j+1)=n.val:=by omega
       have hx:(k•v,i)∈ (axle n).trunks:=by
          refine (trunk_here ..).2 ⟨?_,fun y ht=>by simp [v,ne_of_gt ht]⟩
          rw [show k•v+step i=(k+1) • v from (succ_nsmul ..).symm]; intro hw; have hz: ((k+1:ℕ):Per n)=0:=by simpa only [v,Pi.smul_apply,step_apply,↓reduceIte,nsmul_eq_mul,mul_one] using hw
          have h:=congr_arg ZMod.val hz; rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at h; omega
       rw [List.replicate_succ,linkSum]; change (if false then -_ else x (markZ n (k•v,i)))+linkSum _ (k•v+v) _=_; rw [show k•v+v=(k+1) • v from (succ_nsmul ..).symm,ih (k+1) (by omega), h _ hx]; simp only [Bool.false_eq_true,↓reduceIte,zero_add]
 change linkSum _ _ (List.replicate n.val _) = _
 have hz:=he 0 (n.val-1) (by rw [zero_add]; exact Nat.sub_add_cancel n.property); rw [zero_smul, show (n.val-1+1)=n.val from Nat.sub_add_cancel n.property] at hz; exact hz
abbrev sheetB(q:ℝ):= 4+16*(Fintype.card (TypeFace 2):ℝ)*|q|
lemma sheet_ok(q:ℝ):0<sheetB q:=by unfold sheetB; positivity
private lemma four_balance(x y z w:ℝ) : (x-y-(z-w))^2 ≤ 4*(x^2+y^2+z^2+w^2):=by
 nlinarith only [sq_nonneg (x+y),sq_nonneg (z+w),sq_nonneg (x+z),sq_nonneg (y+w),sq_nonneg (x-w),sq_nonneg (y-z)]
abbrev Account {m:Type}[Fintype m](x:coin m):= ∑ i,x i^2
lemma accountP{m:Type}[Fintype m](x:coin m): Account x=dotProduct x x:=sum_congr rfl fun _ _=>sq _
lemma upperA (x:coin (LT n))(i:TypeFace 2): Account (fun y:Site n=> (d 1 n*ᵥ x) (y,i)) ≤ 16* Account x:=by
 obtain ⟨p,rfl⟩:= plaqEquiv.surjective i
 let Y:= Account x; let b(i:Axis)(t:Site n):= fun y:Site n=>x (y+t,coord i)
 have he(i:Axis)(t:Site n):Account (b i t) ≤ Y:=by unfold Account b; rw [show (∑ y: Site n, x (y+t,coord i)^2)=_ from Equiv.sum_comp (Equiv.addRight t) (fun (y:Site n)=> x (y,coord i)^2)]; unfold Y Account; rw [Fintype.sum_prod_type]; exact (sum_le_sum (fun y _=> single_le_sum (fun i _=>sq_nonneg (x (y,i))) (mem_univ _))) -- tune
 let i:=p.val.1; let j:=p.val.2
 unfold Account; rw [plaq_map]; simp_rw [d_plaquettes]; refine (sum_le_sum (fun y (_ : y∈univ) => four_balance (x (y+step p.val.1,coord p.val.2)) _ _ _)).trans ?_
 rw [← mul_sum]; simp_rw [sum_add_distrib]; have hv(z): b z 0=fun y=>x (y,coord z):=by ext; simp [b]
 have hh:=he i 0; have hl:=he j 0; rw [hv] at hh hl
 linarith only [he j (step i), he i (step j), hh, hl] -- tune
lemma tightCap (f:Floor P F n a K)(x:coin (FreeA n)) : dotProduct x (kindleG P n*ᵥ x)≤ sheetB K*dotProduct x x:=by
 let X:=foot (slotZ n)*ᵥ x; let I:=d 1 n*ᵥ X; let Y:=dotProduct x x
 have hY: dotProduct X X=Y:=fee_v (slotZ n) slot_ins ..
 have he:dotProduct I I ≤ (Fintype.card (TypeFace 2):ℝ)*(16*Y):=by
    rw [← accountP, Account,Fintype.sum_prod_type,sum_comm,← hY, ← accountP]; exact ((sum_le_sum (fun y (_: y∈ univ)=> upperA X y)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])) -- tune
 have ht(i:Axis): (lasers n*ᵥ X) i = X (markZ n (handle n i)):= tight X i (fun i p=>blankA (slotZ n) (markZ n i) (by rintro ⟨j,q⟩; exact j.2 (mark_ins q |>.symm ▸ p)) x)
 have hm: dotProduct (lasers n *ᵥ X) (lasers n *ᵥ X)≤4*Y:=by
    rw [←accountP,Account,←hY,←accountP]; exact (sum_le_sum (s:=univ) (g:=fun i:Axis=> Account X) (fun i _=> by rw [ht]; exact single_le_sum (fun i _=>sq_nonneg (X i)) (mem_univ (markZ n (handle n i))))).trans_eq (by simp only [sum_const, card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat])
 unfold sheetB kindleG; rw [costsA,plus_bill,plaid_cost,prize_bill]; refine (add_le_add (le_trans ((f.uniform.1 I).2) (le_trans (mul_le_mul_of_nonneg_right (le_abs_self K) (flourish _)) (mul_le_mul_of_nonneg_left he (abs_nonneg K)))) hm).trans_eq ?_; unfold Y; ring
lemma paneBudget {m:Type}[Fintype m][DecidableEq m](q:m→FreeA n)(h:Injective q)(f:Floor P F n a K)(u:0<a): chassis P n≤ ((kindleG P n).submatrix q q).det* (sheetB K)^(3*Fintype.card (Site n)+1-Fintype.card m):=by
 rw [chassis,chips_p _ P f.symmetric.1, ← free_count]; refine det_fare q h (kindleG P n) ?_ (sheetB K) (tightCap f); rw [kindleSP]; exact (chips_live (axle n) f u).submatrix slot_ins
end Poeme
end YM.SU5.FiniteGaugeData.Galope
