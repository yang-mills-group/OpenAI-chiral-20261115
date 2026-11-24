import YM.CF.BProof.Dream.Guild
import YM.CF.BProof.Dream.Sub
import YM.CF.Matter.Pair
/-! Color seats, path on pairs H(e₀) to B. Third-generation copies identical. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Function SU Join Finset Pair
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker ContDiff
attribute [local instance] opCStarAlgebra
local notation "D"=>Matrix.diagonal
local notation "π"=>Real.pi
abbrev W := Fin 7 × Fin 2
abbrev Keys := W ⊕ Unit
def botX : Fin 7→Sheet:=![p 0 1,p 0 2,p 0 3,p 0 4,p 1 2,p 1 3,p 1 4]
def topX : Fin 7→Sheet:=![f 1,f 2,f 3,f 4,p 3 4,p 2 4,p 2 3]
def keyX : Keys→Sheet:= Sum.elim (fun i=>![botX i.1,topX i.1] i.2) (fun _=>f 0)
lemma keyX_b : Bijective keyX := by
 refine ⟨(by apply (show ∀ i j:Keys,keyX i=keyX j→i=j from (by decide))),?_⟩ -- tune
 exact (show ∀ y:Sheet, ∃ x:Keys,keyX x=y from (by decide))
def board : Keys≃Sheet:=Equiv.ofBijective keyX keyX_b
lemma atlasP (U: Op Keys)(i j : Keys): atlas board U (keyX i) (keyX j)=U i j:=by change U (board.symm (board i)) _= U i j; rw [board.symm_apply_apply,show board.symm (keyX j)=_ from board.symm_apply_apply j]

-- one signs test at H(e0)
def bottomAngle (i:Fin 7):ℝ:= if i=5 then -(π/2) else π/2
def topAngle : Fin 7→ℝ:=![π/2,π/2,π/2,π/4,0,0,0]
def cabinet (a:Fin 7→ℝ) : Op Keys:= both (choir fun i=>flect (a i)) (-1)
lemma cabinet_u (a:Fin 7→ℝ): cabinet a ∈ unitary _:= both_unitary (choirU _ (fun i=> flect_unit _)) (by constructor <;> simp)
lemma cabinet_tr (a:Fin 7→ℝ): (cabinet a)ᵀ=cabinet a:=by simp_rw [cabinet,both_trans,transpose_neg,transpose_one,choir_trans,flect_trans]
lemma cabinet_star (a:Fin 7→ℝ): star (cabinet a)= cabinet a:=by rw [cabinet,star_both,choir_star,star_neg,star_one]; congr 2; ext1 i; exact flect_self _
lemma cabinet_det (a:Fin 7→ℝ): (cabinet a).det=1:=by simp_rw [cabinet,both_det,choir_det,flect_det]; norm_num
lemma seats_sub (M N:Op Sheet) (h:∀ i j:Keys,M (keyX i) (keyX j)= N (keyX i) (keyX j)) : M=N:=by
 ext i j; obtain ⟨x,rfl⟩:= keyX_b.2 i; obtain ⟨y,rfl⟩:= keyX_b.2 j; exact h _ _
-- computable switch at bottom
private def dx : Equiv.Perm Keys:= Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)) (Equiv.refl _)
private def hue : Keys → ℤ:= Sum.elim (fun i=> if i.1=5 then -1 else 1) (fun _=> -1)
private lemma northTest : (∀ i:Keys, keyX (dx i)=northPerm (keyX i)) ∧ (∀ i,coloration (keyX i)=hue i) := by
 -- decide with noncomputable def? all except from proof
 decide
lemma flect_entry0 (i:Fin 7)(a b:Fin 2): flect (bottomAngle i) a b= if Equiv.swap 0 1 a=b then (if i=5 then -1 else 1) else 0:=by
 fin_cases a <;> fin_cases b <;> by_cases h:i=5 <;> simp [flect,bottomAngle,h]
lemma seatsAtNorth : pairM e0=atlas board (cabinet bottomAngle) :=by
 apply seats_sub; intro i j; simp only [atlasP,colorCase, ←northTest.1, keyX_b.1.eq_iff, northTest.2]; rcases i with ⟨i,b⟩|⟨⟩ <;> rcases j with ⟨j,c⟩|⟨⟩
 · let B: Fin 7→Duo:=fun i=> flect (bottomAngle i)
   simp only [dx, Equiv.sumCongr_apply, Equiv.prodCongr_apply,Equiv.refl_apply,Sum.map_inl, Sum.inl.injEq, Prod.mk.injEq,Prod.map_apply]; change (if i=j∧ Equiv.swap 0 1 b=c then _ else _)=(choir B) _ _
   by_cases h:i=j; subst j; by_cases e:i=5 <;> simp [B,choir,jump_apply,hue,flect_entry0,e]; simp [h,choir,jump_apply]
 all_goals simp [dx,cabinet,both,hue]

def shiftB (t:ℝ): Op Sheet:= atlas board (cabinet fun i=> t*topAngle i+(1-t)*bottomAngle i)
lemma shiftB_U (t:ℝ): shiftB t∈unitary _ := atlasU _ (cabinet_u _)
lemma shiftB_T (t:ℝ): (shiftB t)ᵀ= shiftB t:=by rw [shiftB,←atlas_trans,cabinet_tr]
lemma shiftB_D (t:ℝ): (shiftB t).det=1:= (atlas_det ..).trans (cabinet_det _)
lemma shiftB_star (t:ℝ): star (shiftB t)=shiftB t:=by rw [shiftB, ←atlas_star,cabinet_star]
lemma shiftB_p : shiftB 1= atlas board (cabinet topAngle):=by simp [shiftB]
lemma shiftB_0 : shiftB 0=pairM e0:=by simp only [shiftB,zero_mul,sub_zero,one_mul,zero_add,seatsAtNorth]
-- smooth entry helper
section
variable {I X:Type*}[Fintype I][DecidableEq I][NormedAddCommGroup X][NormedSpace ℝ X]
def smoothView : (I→ I→ℂ) →ₗ[ℝ] Op I where
 toFun:= Matrix.of
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma smoothM (f:X→ Op I)(h: ∀ i j,ContDiff ℝ ∞ (fun x=>f x i j)): ContDiff ℝ ∞ f := (smoothView (I:=I)).toContinuousLinearMap.contDiff.comp (contDiff_pi.mpr fun i=> contDiff_pi.mpr (h i))
end
lemma flectS : ContDiff ℝ ∞ flect:=by
 refine smoothM _ ?_; intro i j; let a:=Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin (n:=∞)); let b:= Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos (n:=∞)); fin_cases i <;> fin_cases j <;> first| exact a| exact b| exact b.neg
lemma shiftB_S: ContDiff ℝ ∞ shiftB:=by
 apply smoothM _ _; intro i j; obtain ⟨x,rfl⟩:=keyX_b.2 i; obtain ⟨y,rfl⟩:=keyX_b.2 j; simp_rw [shiftB,atlasP,cabinet]; rcases x with ⟨i,b⟩|⟨⟩ <;> rcases y with ⟨j,c⟩|⟨⟩
 · by_cases h:i=j; swap; · simp only [both,Matrix.fromBlocks_apply₁₁,choir,jump_apply,Equiv.refl_apply,h,↓reduceIte]; exact contDiff_const
   subst j; let L:Duo→ₗ[ℝ] ℂ:= ⟨⟨fun A=>A b c,fun _ _=>rfl⟩,fun _ _=>rfl⟩; simp only [both,Matrix.fromBlocks_apply₁₁,choir,jump_apply,Equiv.refl_apply,ite_true]; exact L.toContinuousLinearMap.contDiff.comp (flectS.comp ((contDiff_id.mul contDiff_const).add ((contDiff_const.sub contDiff_id).mul contDiff_const)))
 all_goals exact contDiff_const
end YM.CF.BProof.Dream
