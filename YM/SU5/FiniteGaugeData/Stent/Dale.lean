import YM.SU5.FiniteGaugeData.Stent.Quint
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent
set_option linter.unusedSimpArgs false
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
variable {N P:Side}(G:Ratio N P)(p:G.count=R.L)(h:4≤R.L.val) {d:ℕ} (q:LaurentRadius R.J G.count d) (t:2*d < N.val)
local notation "Ω"=> Op SU.Slot
variable (Q: Op SU.Slot)(M:Male)(u:Nom N P)(b:Bool)
abbrev IssueP(R:Patch)(Q: Op SU.Slot)(b:Bool)(i:SpinIdx)(W:LinksC): Op SU.Slot:= Bliss R • (Louvre R W*Lock Q b i)
include p h q t
lemma mirrorEntry(i:SpinIdx)(v w:SU.Slot) : (byMode G R.J Q M u b (basisC N 0 i v)).ofLp (Lifted.index P (specialM R.L) i w)= Lifted.winding N 0 * IssueP R Q b i (onC P u.1) w v:=by
 let A:=Yr G i; let Z:= Lifted.index P (specialM R.L) i w; have hg:4≤G.count.val:= p.symm ▸ h; let o:Odd G.count.val:=p.symm ▸ R.odd_side; have hz : Z=switchG G (A,w):=by unfold Z index; rw [←p,switched G hg o i w]
 rw [basisC,map_smul,show Lifted.index P (specialM R.L) i w= _ from hz]; change Lifted.winding N 0*(byMode G R.J Q M u b (basisKet (index N 0 i v))).ofLp ((switchG G) (Yr G i,w))=_; apply congrArg; rw [byMode_eq];  rw [seamK,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]; -- inspect step M
 simp_rw [show Lifted.index N 0 i v= ((0,i),v) from (by unfold index; rw [map_zero]), fee_work,map_sum,map_smul,basis_shell, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul]; unfold IssueP; rw [Matrix.smul_apply, Matrix.mul_apply,smul_eq_mul, mul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [basis_act]; rw [show (patchQ G) ((0,i),j)=(Yc G i,j) from rfl, clothZ R G p h q t u i i w j, if_pos rfl]; ring -- tune A
#print axioms mirrorEntry
end YM.CF.Buffered.Stent
