import YM.SU5.May.TorqueCash
import YM.SU5.May.TorqueK
/-! Torque gains. actual Petri telescope L^-1/2 EXP, no link hypotheses! -/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent.Purchase
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
open NormedSpace
variable {N: Side}{b:Bool}{F:Op SU.Slot}
local notation "Ω"=> Op SU.Slot
variable {ι κ ν:Type*}[LinearOrder κ] [Fintype κ] [LinearOrder ι][Fintype ι][LinearOrder ν][Fintype ν]
open SU
variable {P:Side}(G:Ratio N P) (p:G.count=R.L) (u:Nom N P) {d:ℕ} (w:LaurentRadius R.J G.count d)
-- critical! path depends on BOTH k indices; we only care spine column at t=(0,η)
local notation "tok[" p "," r "," i "," v "]" => ((p,(r,i)),v)
noncomputable def guardU (r:Site G.count) (z:Cover)(o:Lattice.Order)(q:Site N)(i:SpinIdx): SU.E:= travel u.1 (touch G true (q,r,i)) (runD true false G.count (r,i) (0,i) z o)
include p
lemma brix_seed (r:Site G.count)(v: Cover)(i j:SpinIdx): tub (brix R.J G.count) v (r,i) (0,j) = if i=j then cash R (lift r) v else 0:= by revert r; rw [p]; exact fun _=> correspondent ..
local notation "M" => mosaic G true false (tub (brix R.J G.count)) (unionP u)
open scoped Classical
set_option maxHeartbeats 700000 in
private lemma priced (x y:Site N)(r:Site G.count)(i j:SpinIdx)(a b:SU.Slot)(f s:St G.count)(o:Lattice.Order)(z:Cover):
 drag G true false f s z (tub (brix R.J G.count) z f s) o (unionP u) (tok[x,r,i,a]: Iota G) ((patchQ G) ((y,j),b))=
 if ((r,i)=f ∧ (0,j)=s ∧ (i=j ∧ y=x+wrap N z)) then wind x z * cash R (lift r) z * (matter (guardU G u r z o x i)).val a b else 0:=by
 rw [drag_entry]; -- notation issue `tok[x` clash indexing
 change (if (r,i)=f ∧ (y,(0,j))=(x+wrap N z,s) then _ else 0)= _
 by_cases h:(r,i)=f∧(0,j)=s; swap;· push Not at h; aesop
 obtain ⟨rfl,rfl⟩:=h; rw [brix_seed R G p]; by_cases hy:y=x+wrap N z
 · subst y; by_cases he:i=j; · subst j; simp [guardU,show ∀ y:Site N,((patchQ G) ((y,i),b)).2=b from fun _=>rfl]
   simp [he]
 simp [hy]

private lemma stitch (x y:Site N)(r:Site G.count)(i j:SpinIdx)(a b:SU.Slot)(o:Lattice.Order)(z:Cover):
 (∑ f:St G.count,∑ t:St G.count,drag G true false f t z (tub (brix R.J G.count) z f t) o (unionP u) (tok[x,r,i,a]) ((patchQ G) ((y,j),b)))
 =if (i=j ∧ y=x+wrap N z) then wind x z * cash R (lift r) z * (matter (guardU G u r z o x i)).val a b else 0:=by 
    simp_rw [priced R G p u]; split
    next h=>
      simp only [h,and_true]; simp_rw [ite_and]; simp
    next h=> simp only [h,and_false, ↓reduceIte,sum_const_zero]
include w
lemma amount (x y:Site N)(r:Site G.count)(i j: SpinIdx)(a b:SU.Slot):
 M (tok[x,r,i,a]) ((patchQ G) ((y,j),b)) = (Fintype.card Lattice.Order:ℝ)⁻¹ • ∑ o:Lattice.Order,∑ z∈LabelSet d, (if i=j ∧ y=x+wrap N z then wind x z* cash R (lift r) z*(matter (guardU G u r z o x i)).val a b else 0):=by
 rw [mosaic_entry G R.J w]; apply congrArg; refine sum_congr rfl fun o _=>?_ ; let D(s f z):=drag G true false s f z (tub (brix R.J G.count) z s f) o (unionP u) (tok[x,r,i,a]) ((patchQ G) ((y,j),b)); change (∑ i,∑ j,∑ k∈_,D i j k)= _; simp_rw [sum_comm (t:=LabelSet d) (f:=fun j k=>D _ j k)]; rw [sum_comm]; exact sum_congr rfl fun z _=> stitch R G p u x y r i j a b o z
lemma margin (X Y:Site N)(r:Site G.count)(i j:SpinIdx)(a b:SU.Slot)(m: Male): Peaks.cloth R.J m G (unionP u) (tok[X,r,i,a]) ((patchQ G) ((Y,j),b))= M (tok[X,r,i,a]) ((patchQ G) ((Y,j),b)) := by
 rw [cloth_entry]; by_cases h:i=j
 · subst j; rw [show patchQ G ((Y,i),b)=tok[Y,0,i,b] from rfl]; simp_rw [lobe_fine]; by_cases g:i∈ plusHalf <;> simp [Fir.angle,Adef.trans raising.symm,cutM,g]
 rw [amount R G p u w]; simp [h]
end YM.CF.Buffered.Stent.Purchase
