import YM.CF.Levier.Ion
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
variable {I:Type*}(π:I→Bool→I)(T:Meter I G e)(l: ∀ i b c,π (π i b) c= π i (b.xor c))(p:∀ i,π i false=i)(t:Sweep N)
variable (X:Seal (Site (More P)))(x:cro G e)
include h
lemma toSpin_sum (s: Finset I)(F:I→Op κ): toSpin G k (∑ i∈s,F i) = ∑ i∈s,toSpin G k (F i):=by unfold toSpin steer; simp only [singT,win_sum,map_sum]
lemma kox :accent k⁻¹ = accent k:=by
 let v:=accent k⁻¹; let u:= accent k; have he(k t:Sweep N): accent (k*t)=(accent k).xor (accent t):= det_p _ _
 have hg:accent (N:=N) 1=false:=det_i; have ht:(accent k⁻¹).xor (accent k)=false:=by rw [←he,inv_mul_cancel,hg]
 simpa using ht
include l p
lemma overK(i:I):toSpin G k (modeT G e (k*t) π T i X x)= modeT G e t π T (π i (accent k)) (toRoar G k⁻¹ X) (toWish G e k x):=by
 unfold modeT coda perch; rw [l, ← shelf, swept]; -- sweep direction maybe
 rw [show accent (k*t)=(accent k).xor (accent t) from det_p ..]; rw [_root_.mul_inv_rev,skim G h, mul_assoc,inv_mul_cancel,mul_one]
set_option maxHeartbeats 860000 in
lemma shineB(i:I): toSpin G k (ced G e π T i X x)=ced G e π T (π i (accent k)) (toRoar G k⁻¹ X) (toWish G e k x):=by
 have he(B:Op κ): toSpin G k (pic (N:=N) • B)= pic (N:=N) • toSpin G k B:=by unfold toSpin steer; rw [singT,win_c,twist_scalar]; change _= pic (N:=N) • twist _ _; congr 1; unfold cSignX pic; split; simp; rfl
 unfold ced; rw [he,toSpin_sum _ h]; apply congrArg (fun W:Op κ=> pic (N:=N) • W)
 conv_lhs=>rw [← Equiv.sum_comp (Equiv.mulLeft k)]
 apply sum_congr rfl; intro j _; exact overK G h e k π T l p j X x i
variable (A:I→ Raw (cro G e) (Iota G))(Q: ∀ i d,∑ S:Seal (Site (More P)),T i S d=A i d)
include Q
lemma stellar(i:I)(H:∀ k:Sweep N,∀ i, toSpin G k (A i x) = A (π i (accent k)) (toWish G e k x)): ∑ S:Seal (Site (More P)),ced G e π T i S x=A i x:=by
 have he(k:Sweep N): ∑ S,modeT G e k π T i S x=A i x:=by
    unfold modeT coda perch; rw [←toSpin_sum _ h]; let j:=π i (accent k); change toSpin G k⁻¹ (∑ S,T j (weaveS G k⁻¹ S) (toWish G e k x))=A i x; rw [show ∑ S,T j (weaveS G k⁻¹ S) (toWish G e k x)= _ from Equiv.sum_comp (weaveS G k⁻¹) (fun i=> T j i (toWish G e k x)),Q,show A j _=toSpin G k _ from (H k i).symm,skim G h,mul_inv_cancel,skey _ h]
 unfold ced; rw [← Finset.smul_sum,sum_comm]; simp_rw [he]; rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℂ]; unfold pic; push_cast; rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=Sweep N)), one_smul]
end YM.CF.Levier
