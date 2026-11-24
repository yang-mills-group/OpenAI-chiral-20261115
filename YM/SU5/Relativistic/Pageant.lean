import Mathlib.Analysis.Matrix.Order
import YM.SU5.Relativistic.Kinetic
/-! # billboard splitting. determinants. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Pageant
open Function Finset Matrix Filter MeasureTheory GaugeFlux
open scoped Matrix BigOperators
variable {I J L : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype L][DecidableEq L]
lemma panel (T:Matrix (Sum I J) (Sum I J) ℝ)(p:T.PosDef): T.det≤ (T.submatrix Sum.inl Sum.inl).det*(T.submatrix Sum.inr Sum.inr).det:=by
 let A:= T.submatrix Sum.inl Sum.inl; let D:= T.submatrix Sum.inr Sum.inr; let B:=T.submatrix Sum.inl Sum.inr; have hA:A.PosDef:= p.submatrix Sum.inl_injective; haveI : Invertible A:= hA.isUnit.invertible; have hD:D.PosDef:=p.submatrix Sum.inr_injective
 have he:T= Matrix.fromBlocks A B Bᴴ D:= by
   ext i j; cases i with
   | inl=> cases j<;>rfl
   | inr i=> cases j with
             | inl j=> exact (congrFun (congrFun p.isHermitian _) _).symm -- tune
             | inr=> rfl
 let V:= Bᴴ*A⁻¹*B; let P:=D-V; have he': T.det=A.det*P.det:=by nth_rw 1 [he]; unfold P V; rw [det_fromBlocks₁₁,invOf_eq_nonsing_inv]
 have hx:P.PosSemidef:= (Matrix.PosDef.fromBlocks₁₁ _ _ hA).1 (he ▸ p.posSemidef) -- tune
 have hQ:P.det ≠0:=by intro g; have ht:= p.det_pos; rw [he',g,mul_zero] at ht; exact lt_irrefl _ ht
 have hp:= PosDef.inv hA; have ht: V.PosSemidef:= hp.posSemidef.conjTranspose_mul_mul_same B
 change T.det≤_; rw [he']; apply mul_le_mul_of_nonneg_left _ hA.det_pos.le
 apply det_hike (hx.posDef_iff_det_ne_zero.mpr hQ) hD; intro x; unfold P; rw [Matrix.sub_mulVec,dotProduct_sub]; exact sub_le_self _ (show 0≤dotProduct x (V*ᵥ x) from (by simpa using ht.dotProduct_mulVec_nonneg x))

def loadP (A : Matrix I I ℝ)(v : Finset I):= (A.submatrix ((↑) : v→I) ((↑) : v→I))
lemma included {A:Matrix I I ℝ}{v t:Finset I}(h:v⊆t)(p:(loadP A t).PosDef):(loadP A v).PosDef:= by
 let f(x:↥v):↥t:=⟨x.val,h x.property⟩; let h':(loadP A v)= (loadP A t).submatrix f f:= rfl; rw [h']; exact p.submatrix (by intro x y h; exact Subtype.ext (congrArg (fun i:↥t=>i.val) h)) -- tune
lemma cutBloc (T:Matrix I I ℝ)(v x y:Finset I) (w:v=x ∪ y)(g:Disjoint x y) (t:(loadP T v).PosDef): (loadP T v).det≤ (loadP T x).det*(loadP T y).det:=by
 let F: ↥x ⊕ ↥y→ ↥v:=Sum.elim (fun p=>⟨p.val,w.symm ▸ mem_union_left _ p.property⟩) (fun p=>⟨p.val,w.symm ▸ mem_union_right _ p.property⟩)
 have hf: Bijective F:=by
   constructor; swap; · rintro ⟨i,p⟩; rcases mem_union.mp (w ▸ p) with p|p; exact ⟨.inl ⟨i,p⟩,rfl⟩; exact ⟨.inr ⟨i,p⟩,rfl⟩
   intro i j h; have he:= congrArg (fun i:↥v=>i.val) h; have ht(i:↥x)(j:↥y): i.val≠j.val:=fun p=> Finset.disjoint_left.mp g i.property (p.symm ▸ j.property)
   cases i <;> cases j <;> first| exact congrArg _ (Subtype.ext he) | exact (ht _ _ he).elim| exact (ht _ _ he.symm).elim -- tune
 let k:= Equiv.ofBijective F hf; let P:=(loadP T v).submatrix k k; have hp :=panel P (t.submatrix k.injective); rw [←det_submatrix_equiv_self k (loadP T v)]; exact hp
lemma boardwalk (T:Matrix I I ℝ) (v:Finset I)(p:(loadP T v).PosDef) (x:Finset J)(f:J→Finset I)(h: (x:Set J).PairwiseDisjoint f)(g:x.biUnion f⊆v): (loadP T (x.biUnion f)).det≤∏ i∈x,(loadP T (f i)).det:=by
 induction x using Finset.induction_on with
 | empty => haveI:IsEmpty ↥((∅: Finset J).biUnion f):= ⟨fun i=>(by obtain ⟨i,h⟩:=i; simp at h)⟩; rw [Matrix.det_isEmpty,prod_empty]
 | @insert a s t ih=>
   have hp:a∈insert a s:= mem_insert_self ..
   have hs:s⊆insert a s:=subset_insert ..; have hx:= (subset_biUnion_of_mem f hp).trans g; have h':s.biUnion f⊆ v:=by rw [biUnion_insert] at g; exact subset_union_right.trans g
   have hz:= cutBloc T _ (f a) (s.biUnion f) (biUnion_insert ..) ?_ (included g p); swap
   · rw [Finset.disjoint_left]; intro i j t'; obtain ⟨b,p,hb⟩:=mem_biUnion.mp t'; exact Finset.disjoint_left.mp (h (show a∈ ((↑(insert a s)):Set J) from hp) (show b∈ ((↑(insert a s)):Set J) from hs p) (fun e=> t (e.symm ▸ p))) j hb -- tune
   rw [prod_insert t]; exact hz.trans (mul_le_mul_of_nonneg_left (ih (h.subset hs) h') (included hx p|>.det_pos.le))
lemma letter {S:Finset I}(A:Matrix I I ℝ)(f:J ↪ I)(h:∀ i,i∈ S↔∃ x,f x=i) : (loadP A S).det=(A.submatrix f f).det:=by
 let k(x:J):↥S:=⟨f x,(h _).mpr ⟨_,rfl⟩⟩; have he:Bijective k:= ⟨fun i j e=> f.injective (congrArg (fun x:↥S=>x.val) e),by rintro ⟨z,t⟩; obtain ⟨y,rfl⟩:=(h _).mp t; exact ⟨y,rfl⟩⟩
 exact (det_submatrix_equiv_self (Equiv.ofBijective k he) (loadP A S)).symm

variable (A:Matrix I I ℝ)
def spanD (A:Matrix I I ℝ) (q:ℝ):Prop:=∀ v,dotProduct v v*q ≤ dotProduct v (A*ᵥ v)
def plaque (S:Finset I)(r:ℝ):= diagonal (fun i=> if i∈ S then r else 0)
lemma packed(S: Finset I){r:ℝ}(p:0≤r): (plaque S r).PosSemidef:= PosSemidef.diagonal fun i=>by split; exact p; rfl
lemma plaque_p (S:Finset I)(v:I→ℝ)(r:ℝ): dotProduct v (plaque S r *ᵥ v)= (∑ i∈S,v i^2)*r:=by
 unfold plaque dotProduct; simp_rw [mulVec_diagonal]; rw [sum_mul, ← sum_subset (s₁:=S) (subset_univ S)]
 · exact sum_congr rfl fun x h=> by rw [if_pos h]; ring
 intro i x t; rw [if_neg t]; ring
lemma plaque_up{S:Finset I}(i:I)(p:i∉S)(r:ℝ) : plaque (insert i S) r=plaque S r+plaque {i} r:=by
 ext j k; by_cases g:k=j
 · subst k; by_cases h:j=i; subst j; simp [plaque,p]; simp [plaque,h]
 simp [plaque,Ne.symm g]
lemma one_panel (p:A.PosDef) {q r:ℝ}(u:0<q)(w:0≤r)(x:spanD A q)(i:I) : (A+plaque {i} r).det ≤ A.det * (1+r/q):=by
 let X:I→ℝ:= Pi.single i 1; let Y:I→ℝ:= Pi.single i r; let V:= replicateCol Unit X; let W:= replicateRow Unit Y; have hp:IsUnit A.det:= isUnit_iff_ne_zero.mpr p.det_pos.ne'
 have he: V*W= plaque {i} r:=by
    ext j k; change (∑ t:Unit,X j * Y k)=_; by_cases h:j=i <;> by_cases g:k=i <;> by_cases t:k=j<;> simp_all [plaque,X,Y,Pi.single_apply,Matrix.diagonal_apply] <;> grind -- tune
 let y:= A⁻¹ *ᵥ X
 have hx:0≤ y i:=by
    have h:0≤ dotProduct X y:=by simpa [y] using p.inv.posSemidef.dotProduct_mulVec_nonneg X
    simpa only [X,single_dotProduct,mul_one,one_mul] using h -- tune
 have ht:y i*(y i)*q≤y i:=by
    refine le_trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=fun i=> y i*y i) (fun i _=> mul_self_nonneg _) (mem_univ i)) u.le) ?_
    apply le_trans (x y); rw [show A*ᵥ y=X from (by unfold y; rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A hp,Matrix.one_mulVec])]; simp [X] -- tune
 have hr:y i ≤1/q:= (le_div_iff₀ u).mpr (by nlinarith)
 have H: (1+W*A⁻¹*V).det=1+r*y i:=by
    rw [det_unique]; change (1:Matrix Unit Unit ℝ) () ()+(W*A⁻¹*V) () () = _; rw [Matrix.one_apply_eq]; congr 1
    rw [Matrix.mul_assoc]; unfold V W; rw [← Matrix.replicateCol_mulVec,Matrix.replicateRow_mul_replicateCol_apply]; simp [Y,y] -- tune orientation
 rw [← he,det_add_mul V W hp,H]; exact mul_le_mul_of_nonneg_left (by nlinarith only [(mul_le_mul_of_nonneg_left hr w), show r*(1/q)=r/q by ring]) p.det_pos.le
lemma plaza (p:A.PosDef){q r:ℝ}(u:0<q)(w:0≤r)(x:spanD A q)(S:Finset I): (A+plaque S r).det≤ A.det*(1+r/q)^S.card:=by
 induction S using Finset.induction_on with
 | empty=> rw [show plaque (∅:Finset I) r=0 from by simp [plaque],add_zero,card_empty,pow_zero,mul_one]
 | @insert i s t ih=>
    let X:= plaque s r; have hf:spanD (A+X) q:= fun v=> by apply le_trans (x v); rw [add_mulVec,dotProduct_add,show dotProduct v (X*ᵥ v)= _ from plaque_p s v r]; exact le_add_of_nonneg_right (mul_nonneg (sum_nonneg fun _ _=> sq_nonneg _) w)
    rw [plaque_up _ t,← add_assoc,card_insert_of_notMem t, pow_succ, ← mul_assoc]; exact (one_panel (A+X) (p.add_posSemidef (packed s w)) u w hf i).trans (mul_le_mul_of_nonneg_right ih (by positivity)) -- tune
end YM.CF.Papyrus.Pageant
#print axioms YM.CF.Papyrus.Pageant.boardwalk
#print axioms YM.CF.Papyrus.Pageant.plaza
