import YM.CF.Song.Jags
import YM.CF.Milo.Sucre
/-!
Basis reserve for the analytic procedure in VOLUME_ANALYTIC, Budget through match.
`Montage` is an explicit finite frame with unit-ball basis *and* dual, of ℓ¹ cost
fixed once, before patch L. `Poetic`/`Tempered` mean agrees on the whole closed Mind
ball with a real-linear map (ordinary real space of Mind). Stencils in the purchase below
are frozen once for all proposals in the step. We use notations `w v`/`v w` as in imports.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Haro
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
structure Montage (C:ℝ) where
 A : Module.Basis (Fin (Module.finrank ℝ SpaceM)) ℝ SpaceM
 leg : ∀ i, ‖A i‖≤1
 cost : ∀ x:SpaceM, ∑ i, ‖A.repr x i‖ ≤ C*‖x‖

lemma exists_montage : ∃ C:ℝ,1 ≤ C ∧ Nonempty (Montage C):=by
 let n:=Module.finrank ℝ SpaceM
 let B:= Module.finBasis ℝ SpaceM
 -- scaled basis `B i / ‖B i‖`
 let w (i:Fin n):= Units.mk0 ‖B i‖ (norm_ne_zero_iff.mpr (B.ne_zero i))
 let A:= B.unitsSMul (fun i=> (w i)⁻¹)
 have ht(i:Fin n): ‖A i‖≤1:=le_of_eq (by
    rw [show A i=(‖B i‖⁻¹) • B i from ?_, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (B.ne_zero i))]
    unfold A
    rw [Module.Basis.unitsSMul_apply]; rfl)
 let U (i:Fin n):SpaceM→L[ℝ]ℝ:=(A.coord i).toContinuousLinearMap
 let T:= ∑ i:Fin n, ‖U i‖
 exact ⟨max 1 T,le_max_left ..,⟨A,ht,fun x=>(sum_le_sum (fun i _=> U i|>.le_opNorm x)).trans ((le_of_eq (sum_mul ..).symm).trans (mul_le_mul_of_nonneg_right (le_max_right 1 T) (norm_nonneg x)))⟩⟩

section
variable {r:ℝ}{A B:Type*}[AddCommGroup A][AddCommGroup B][Module ℝ A][Module ℝ B]
def Poetic (f:ΘS r→ A) :Prop:=∃ L: SpaceM→ₗ[ℝ] A,∀ x, L x.val = f x
namespace Poetic
variable {f g:ΘS r→ A}
lemma by_lin(L:SpaceM→ₗ[ℝ]A):Poetic (fun x:ΘS r=>L x.val):=⟨L,fun _=>rfl⟩
lemma zero:Poetic (fun _:ΘS r=> (0:A)):=⟨0,fun _=>rfl⟩
lemma add (p:Poetic f)(q:Poetic g):Poetic (fun x=> f x+g x):=by obtain ⟨R,h⟩:=p; obtain ⟨P,i⟩:=q; exact ⟨R+P,fun x=>congrArg₂ (·+·) (h x) (i x)⟩
lemma neg (p:Poetic f):Poetic (fun x=>-f x):=by obtain ⟨R,h⟩:=p; exact ⟨-R,fun x=>congrArg Neg.neg (h x)⟩
lemma sub (p:Poetic f)(q:Poetic g):Poetic (fun x=>f x-g x):=by simp_rw [sub_eq_add_neg]; exact p.add q.neg
lemma comp (L:A→ₗ[ℝ]B)(p:Poetic f):Poetic (fun x=>L (f x)):=by obtain ⟨R,h⟩:=p; exact ⟨L.comp R,fun x=>congrArg L (h x)⟩
lemma c_lin (P:A→ B) (hp:∀ x y,P (x+y)=P x+P y)(ht:∀ (m:ℝ) (x:A),P (m • x)=m • P x)(q:Poetic f):Poetic (fun x=>P (f x)):=comp (f:=f) {toFun:=P,map_add':=hp,map_smul':=ht} q
lemma money {𝕜:Type*}[Monoid 𝕜][DistribMulAction 𝕜 A][SMulCommClass 𝕜 ℝ A](c:𝕜)(p:Poetic f):Poetic (fun x=>c • f x):=by
 exact c_lin (f:=f) (fun x=>c • x) (smul_add c) (fun r x=> smul_comm ..) p
lemma cogv {ι:Type*}(S:Finset ι)(P:ι→ΘS r→A)(h:∀ j∈S,Poetic (P j)):Poetic (fun x=>∑ j∈ S,P j x):=by
 induction S using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; exact Poetic.zero
 | insert i S hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun j p=>h j (mem_insert_of_mem p))
lemma assemble {J:Type*}{P:ΘS r→ J→A}(h:∀ j,Poetic (fun x=> P x j)):Poetic P := by
 choose L s using h
 exact ⟨LinearMap.pi L,fun x=>funext fun j=> s j x⟩
lemma readM : Poetic (riseV (r:=r)):=⟨SpaceM.subtype,fun _=>rfl⟩
end Poetic
end
end YM.CF.Haro
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{v a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
abbrev Tempered(E: Elm n (ΘS r) d a v):Prop:=∀ (S:Support (More n))(x:Openc (More n) d),Poetic (fun i=> E.F S i x)
variable (R:Montage C) (u:1 ≤ C){P0:Gem n (ΘS r)}
include R u
lemma flyer (tc:0<r)(X:Lawn n d P0 a b)(t:∀ x:Openc (More n) d,Poetic (fun i=>P0 i x.val)):∃ Y:Lawn n d P0 a (C*b),Tempered (hull Y):=by
 let m:= Module.finrank ℝ SpaceM; let A:=R.A
 let z (i:Fin m):ΘS r:=⟨r • A i,(le_of_eq (norm_smul ..)).trans (by rw [Real.norm_of_nonneg tc.le]; exact mul_le_of_le_one_right tc.le (R.leg i))⟩
 let k (i:Fin m) : SpaceM→ₗ[ℝ]ℝ:= r⁻¹ • A.coord i
 let Y0 (S:SO): ΘS r → Raw (Openc (More n) d) (Single n):= fun i x=>∑ j:Fin m,(k j i.val) • X.F S (z j) x
 have ht(S:SO)(x:Openc (More n) d):Poetic (fun i=>Y0 S i x):=by exact Poetic.cogv _ _ (fun i _=>Poetic.by_lin ((k i).smulRight (X.F S (z i) x)))
 have hu₀(i:ΘS r):∑ j:Fin m,‖k j i.val‖≤ C:=by
    have hh(j:Fin m):‖k j i.val‖=r⁻¹*‖A.repr i.val j‖:=(norm_smul (α:=ℝ) ..).trans (by rw [Real.norm_of_nonneg (by positivity)]; rfl)
    simp_rw [hh,←mul_sum]; refine ((mul_le_mul_of_nonneg_left ((R.cost i.val).trans (mul_le_mul_of_nonneg_left i.property (by linarith))) (by positivity : 0≤r⁻¹))).trans_eq ?_
    rw [mul_left_comm, inv_mul_cancel₀ tc.ne',mul_one]
 let B(S:SO)(i j: Single n):= C*X.W S i j
 refine ⟨⟨Y0,B,fun S=>⟨fun i=>?_,fun x=> continuous_finsetSum _ (fun j _=> ((k j).continuous_of_finiteDimensional.comp continuous_subtype_val).smul continuous_const)⟩,X.store.funds (by linarith),?_⟩,ht⟩
 · let L (j:Fin m):= k j i.val
   let Z' (j:Fin m): ℝ:=‖L j‖
   let Q (j:Fin m):Raw (Openc (More n) d) (Single n):= L j • X.F S (z j)
   let W (j:Fin m):Toll (Single n):=fun k l=> Z' j*X.W S k l
   have hp(j):Suite (badge _) (bail n d) (bail n d) S (W j) (Q j):=by
      change Suite _ _ _ _ _ (fun x=>k j i.val • X.F S (z j) x)
      simpa only [W,Z',Complex.coe_smul,Complex.norm_real] using ((X.coat S).1 (z j)).accel ((k j i.val:ℝ):ℂ)
   have hz:=Ticket.sumT (s:=bail n d) (t:=bail n d) univ W Q fun i _=>(hp i).toTicket
   refine ⟨⟨hz.frame,?_⟩,(badge _).suppose univ Q fun i _=> (hp i).fuel⟩
   intro j l; have xq:= hz.expo j l
   have hx: (∑ i:Fin m,W i j l) ≤ B S j l:=le_trans (le_of_eq (sum_mul ..).symm) (mul_le_mul_of_nonneg_right (hu₀ i) ((X.coat S|>.1 i).nonn j l))
   exact ⟨xq.positive.trans hx,fun e=> ((X.coat S|>.1 i).expo j l).triggered (right_ne_zero_of_mul e), fun d=>(xq.bounded _).trans hx, fun x y=>(xq.variation x y).trans (mul_le_mul_of_nonneg_right hx ((forum n _).pos ..)), xq.connected⟩
 intro i x; obtain ⟨H,h⟩:= t x; have hz (w:SpaceM): (∑ j,k j w • (z j).val) = w:=by
    have hp(j:Fin m): k j w*r=A.repr w j:=by change (r⁻¹*A.repr w j)*r=_; field
    change ∑ j:Fin m,k j w • (r • A j)=_
    simp_rw [smul_smul,hp]; exact A.sum_repr w
 dsimp only at h; unfold Y0; rw [sum_comm]; conv_lhs=>rw [←h i,←hz i.val, map_sum]
 apply sum_congr rfl; intro j _; rw [map_smul,h (z j),X.shape (z j),smul_sum]
end YM.CF.Sour
