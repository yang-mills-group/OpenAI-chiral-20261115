import YM.SU5.Fineness.TreeFrame
/-!
# Zero columns and the true invariant factor from harmonic rescaling
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Lattice RG Matrix Exterior Precision Tree Finset
open scoped Topology Matrix BigOperators
variable {f c:Side}(S:StepData c f)
variable (r: Ratio c f)
local notation "ρ"=> r.embed
@[simp] lemma post0 (r:Ratio c f): r.embed 0=0:= r.root.map_zero
lemma post_inj {x y}:ρ x= ρ y→ x=y := fun t=> by simpa [r.embed_parent] using congrArg r.parent t
abbrev conePosts (i : Puncture c): Puncture f := ⟨ρ i.val,fun t=> i.property (post_inj r (t.trans (post0 r).symm))⟩
abbrev coneStems (i: Shoot r) : Puncture f:=⟨i.val, fun x=> i.property (by rw [x,←post0 r,r.embed_parent])⟩
abbrev exhale : Shoot r⊕Puncture c→ Puncture f:= Sum.elim (coneStems r) (conePosts r)
def footCount : Shoot r⊕ Puncture c≃ Puncture f:= Equiv.ofBijective (exhale r) (by
 constructor
 · intro i j h; cases i with
   | inl i=> cases j with
     | inl j=> exact congrArg Sum.inl (Subtype.ext (congrArg (@Subtype.val _ fun a:Site f=> a ≠ 0) h))
     | inr j=>
        exfalso; apply i.property; rw [show i.val=ρ j.val from congrArg Subtype.val h,r.embed_parent]
   | inr i=> cases j with
     | inl j=> exfalso; apply j.property; rw [show j.val=ρ i.val from congrArg Subtype.val h.symm,r.embed_parent]
     | inr j=> exact congrArg Sum.inr (Subtype.ext (post_inj r (congrArg Subtype.val h)))
 rintro ⟨y,v⟩; by_cases h:leaf r y
 · exact ⟨Sum.inl ⟨y,h⟩,rfl⟩
 have he:y=ρ (r.parent y):= Classical.not_not.mp h
 exact ⟨Sum.inr ⟨r.parent y,fun e=> v (he.trans (e ▸ post0 r))⟩,Subtype.ext he.symm⟩) -- rw tune
abbrev dowel (n:Side) := Puncture n⊕ Axis
def agents := (rootGrad f).submatrix id (conePosts r)
def allocation := fromCols (agents r) (harmonic f)
lemma index_column {I J K L:Type*}[Fintype I][DecidableEq I] (A: Tab K I)(B:Tab I J) (y:L→J) : (A*B).submatrix id y=A*B.submatrix id y:=rfl
lemma page_splints : splints r=(switch f).submatrix id (coneStems r):=rfl
lemma spokes : let T:= fromCols (tagsZ r ℝ) (allocation r); T=(sightZero f).submatrix id ((Equiv.sumAssoc ..).symm.trans (Equiv.sumCongr (footCount r) (Equiv.refl Axis))):=by
 intro T; unfold T allocation; rw [← leaf_bright r, page_splints,← index_column]; ext x (s|(s|s))<;>rfl
variable {r}
local notation "r'"=> S.ratio
local notation "Cz"=>rootGrad c
lemma slope_zero : probe S * tagsZ S.ratio ℝ=0:=by
 rw [← leaf_bright]; apply Matrix.mulVec_injective; funext x
 rw [← Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,root_gradient,zero_mulVec,show centered S (splints r'*ᵥ x)=(0:form 0 c) from ?_,mulVec_zero]
 ext ⟨t,v⟩; unfold centered splints; unfold mulVec dotProduct; apply Finset.sum_eq_zero; intro i _; unfold FreeResolvent.insertion; change (if (i.val,vac)=(S.ratio.embed t,v) then 1 else 0)*x i=0; rw [if_neg,zero_mul]; intro h; apply i.property; have ht: i.val=S.ratio.embed t:= congrArg Prod.fst h; rw [ht,Ratio.embed_parent]
lemma root_light : probe S * agents S.ratio= rootGrad c:=by
 unfold agents rootGrad; rw [index_column]; apply Matrix.mulVec_injective; funext x; rw [←mulVec_mulVec,←mulVec_mulVec,root_gradient,←mulVec_mulVec]; apply congrArg ((d 0 c) *ᵥ ·)
 ext ⟨t,r⟩; rw [vac_only r]
 by_cases h:t=0
 · subst t; unfold centered; rw [switch_origin,post0]; unfold mulVec dotProduct; apply Finset.sum_eq_zero; intro i _; simp [switch,FreeResolvent.insertion,(conePosts r' i).property] -- tune
 let b:Puncture c:=⟨t,h⟩; rw [show (switch c*ᵥ x) (t,vac)=x b from switch_punct (n:=c) x b]
 unfold centered; unfold mulVec dotProduct
 have hx(i:Puncture c): S.ratio.embed i.val=S.ratio.embed t ↔ i=b:=by
    refine ⟨fun v=>?_,fun v=>v ▸ rfl⟩; exact Subtype.ext (post_inj _ v)
 simp only [submatrix_apply,id_eq,switch, FreeResolvent.insertion,Matrix.of_apply,Prod.mk.injEq,and_true, hx,ite_mul,one_mul,zero_mul]; rw [sum_ite_eq',if_pos (mem_univ _)]

local notation "X"=>allocation r'
local notation "L"=> (S.patch.L.val:ℝ)
def spill : Tab (Puncture c) Axis:=Matrix.of fun i j => let V:=fixRoot S* harmonic f; V (i.val,vac) j - V (0,vac) j
lemma spilled (u:Axis→ℝ) : spill S *ᵥ u=fun i=> (fixRoot S*ᵥ (harmonic f*ᵥ u)) (i.val,vac) - (fixRoot S *ᵥ (harmonic f*ᵥ u)) (0,vac):=by funext i; rw [mulVec_mulVec]; unfold spill; simp only [mulVec,dotProduct,Matrix.of_apply,_root_.sub_mul,sum_sub_distrib]
def projectionFrame : Sheet (dowel c) := fromBlocks 1 (spill S) 0 (L • 1)
local notation "T'"=> projectionFrame S
lemma frame_cost : (projectionFrame S).det=L^4:=by unfold projectionFrame; rw [det_fromBlocks_zero₂₁,det_one,det_smul,det_one]; simp [Axis]
lemma meeting : probe S* allocation r'= sightZero c*T':=by rw [allocation,mul_fromCols,root_light S,roots_flow S _ (spilled S),projectionFrame,sightZero,fromCols_mul_fromBlocks]; simp
lemma repayment (M:Sheet (Body 2 c))(h:Mᵀ=M): let A:= Precision.K M; let Tp:=L^8;
    torsion A (sightZero c)=Tp*torsion A (probe S*allocation r'):=by
 intro A Tg
 have hz:0<L:= by positivity
 have he:(T').det ≠0:=(frame_cost ..).symm ▸ pow_ne_zero _ hz.ne'
 rw [meeting,(lattice_null M h).basis_expense (Equiv.refl _) T' (T')⁻¹ (a:=rfl) (t:=?_) (v:=?_)] -- tune wrong field
 · rw [det_mul,det_transpose,frame_cost]; unfold Tg; ring
 all_goals first | exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr he) | exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr he)
end YM.Fineness
#print axioms YM.Fineness.repayment
#print axioms YM.Fineness.spokes
