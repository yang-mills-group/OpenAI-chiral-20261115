import YM.SU5.FiniteGaugeData.Concord.Charter
/-!
# Plate full OS-preform from one portfolio. Uses `level-0` plane
and its coordinates at ANY finer step. No unbuffered forms presumed.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale Style

namespace Consent
-- abstract Hermitian lemma
variable {G:Type*}[AddCommGroup G][Module ℂ G]
variable (P:G→ₗ⋆[ℂ] (G→ₗ[ℂ]ℂ))(h:∀ x,0 ≤ P x x)
include h
lemma herm (x y:G) : star (P x y)=P y x:=by
  have hv (x:G): (P x x).im=0:= ((Complex.le_def.mp (h x)).2).symm
  have a:=hv (x+y); have b:=hv (x + Complex.I • y)
  simp only [map_add,map_smulₛₗ,LinearMap.add_apply, LinearMap.smul_apply, Complex.add_im, RingHom.id_apply,
    starRingEnd_apply, smul_eq_mul,hv] at a b
  simp [hv,Complex.mul_re,Complex.mul_im] at a b
  apply Complex.ext <;> simp <;> linarith
lemma gram {I:Type*}[Fintype I] (f:I→ G): (Matrix.of fun i j=> P (f i) (f j)).PosSemidef:=by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
  · ext i j; exact herm P h (f j) (f i)
  intro x; have he:=h (∑ i,x i • f i); simp_rw [map_sum, LinearMap.sum_apply, map_smulₛₗ (f:=P)] at he -- tune
  change 0 ≤ ∑ i, star (x i)*∑ j,P (f i) (f j)*x j
  simp only [smul_eq_mul,starRingEnd_apply,map_smulₛₗ,LinearMap.smul_apply, RingHom.id_apply,Finset.mul_sum, mul_assoc,mul_comm,mul_left_comm] at he ⊢
  rwa [Finset.sum_comm] at he
end Consent

variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {i k:ℕ→ℕ}{s:ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "U"=> swept Λ l
variable (W:Traced Y H i k F E P) (a:Axis)(z:ℤ)

local notation "M"=> building (tent Y H)
local notation "PZ"=> haloRule Y H a z

lemma midway_one : midway Y H a z 1=1 := Subtype.ext (Style.inv_one _ (fun n=>turn_one ..))
lemma midway_prod (x y:M) : midway Y H a z (x*y)= midway Y H a z x * midway Y H a z y:= Subtype.ext (Style.inv_mul _ (fun n x y=>turn_mul ..) x.val y.val)
lemma midway_swap (x:M) : midway Y H a z (midway Y H a z x)=x:= Subtype.ext (Style.inv_inv _ (fun n=>turn_twice a _) x.val)
-- note: not assuming portfolio ◦ midway=star ◦ portfolio on full algebra; that is separately by covariance of Y reads etc if needed later.
lemma midway_sing (x:M)(p:x.val∈physical K): (midway Y H a z x).val∈physical K:= aloft Y H a z x.val p

def embedded : (physical (tent Y H))→ₐ[ℂ] building (tent Y H):= Subalgebra.inclusion (scent K)
lemma input_native (x:PZ): (input Y H a z x).val=x.val:=rfl
lemma outGrid_sum (f g:PZ): outGrid Y H a z (f+g)=outGrid Y H a z f+outGrid Y H a z g:=by unfold outGrid; rw [map_add,map_add]
lemma outGrid_smul (c:ℂ)(x:PZ): outGrid Y H a z (c • x)=star c • outGrid Y H a z x:=by unfold outGrid; rw [map_smul (input Y H a z), map_smulₛₗ]; rfl

local notation "Ψ"=> portfolio Y H W
include W
def formPanel : haloRule Y H a z→ₗ⋆[ℂ] (haloRule Y H a z →ₗ[ℂ]ℂ) where
  toFun f:= {
    toFun g:= portfolio Y H W (outGrid Y H a z f * input Y H a z g)
    map_add' x y:= by rw [map_add (input Y H a z), mul_add, map_add]
    map_smul' x y:= by rw [map_smul (input Y H a z), Algebra.mul_smul_comm,map_smul]; rfl
  }
  map_add' x y:= by
    apply LinearMap.ext; intro z;
    dsimp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply]
    rw [outGrid_sum,add_mul,map_add]
  map_smul' x y:=by
    apply LinearMap.ext; intro t; dsimp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply]; rw [outGrid_smul,Algebra.smul_mul_assoc,map_smul]; rfl

lemma consent {I:Type*}[Fintype I](x:I→ haloRule Y H a z) :
    Matrix.PosSemidef (Matrix.of fun i j=> portfolio Y H W (midway Y H a z (input Y H a z (x i))* input Y H a z (x j))) :=
  Consent.gram (formPanel Y H W a z) (fun x=> whole_positive Y H W a z x) x
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.consent
#print axioms YM.CF.Buffered.Concord.midway_swap
