import YM.SU5.Selected.Euro.Palate
import YM.SU5.Macro.Registration

/-!
# All-singlet implementation helper. A genuine gauge projection **in the same support**.

Keep costs on all genuine unit securities. Do not change the product. Gauge action Haar averaged
pointwise on the Wardrobe chart of this support. This lemma gives an inexpensive linear interface to
the corresponding release infrastructure.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
open Tower.PhaseChoice Tower.Selected Tower.Reconstruction CF.Pannier.Chancel Ether
namespace Monochrome
variable (K : Calibration)(S:Finset Cover)
abbrev Bay := bay K S true
/-- Gauge invariant on the given support (and honestly wide). -/
abbrev Spot := bay K S true ⊓ enclave K

def arrange : Swatch S →ₗ[ℂ] Bay K S where
 toFun f:= ⟨badge K S f,locatesBadge K S f⟩
 map_add' x y:= Subtype.ext (map_add _ x y)
 map_smul' z x:= Subtype.ext (map_smul _ z x)
def stocked : Swatch S≃ₗ[ℂ] Bay K S:= LinearEquiv.ofBijective (Monochrome.arrange K S)
 ⟨fun _ _ p=> badge_inj K S (congrArg Subtype.val p), fun u=>(accolade K S u.val u.property).imp
   (fun _ h=>Subtype.ext h)⟩
lemma stock_val(x:Swatch S): (stocked K S x).val=badge K S x:=rfl
variable (m:Side)(h:Hosp S (K.c m))
def hueMap : Swatch S→ₗ[ℂ] Swatch S where
 toFun x:= naturalHue K S m h x
 map_add' x y:= by
    funext q; apply daub_inj; funext X
    let d(z:Swatch S)(g: Zodiac (K.c m)) := daub S (ocelli K S (repeats (K.c m) g) z q) X
    have ht(z:Swatch S): Integrable (d z) (domeLaw (K.c m)):= Push.SectorMeasure.Env.integrableX
      (Push.SectorMeasure.Env.along (hue_cost K S m h z q) (measurable_id.prodMk measurable_const)) _
    let f(x: Swatch S):= ∫ u, d x u∂domeLaw (K.c m)
    let H(x: Swatch S):= naturalHue K S m h x
    have r(x): f x=daub S (H x q) X:= rfl
    have e(x y: Swatch S)(t: Zodiac (K.c m)) : d (x+y) t=d x t+d y t:=by
       unfold d; rw [map_add]; exact congrFun (daubL S|>.map_add _ _) X
    have he'(x y: Pigment S) : daub S (x+y) X=daub S x X+daub S y X:=congrFun (daubL S|>.map_add x y) X
    change daub S (H _ _) X=daub S (_+_) X; rw [he',←r _,←r _,←r _]; unfold f; simp_rw [e]; exact integral_add (ht _) (ht _)
 map_smul' z x:=by
    funext q; apply daub_inj; funext X
    let d(x:Swatch S)(g: Zodiac (K.c m)):= daub S (ocelli K S (repeats (K.c m) g) x q) X
    let f(x: Swatch S):=∫ u,d x u∂domeLaw (K.c m); let H(x:Swatch S):=naturalHue K S m h x
    have r(x:Swatch S): f x=daub S (H x q) X:= rfl
    have he'(y:Pigment S): daub S (z • y) X= z • daub S y X:=congrFun (map_smul (daubL S) z y) X
    have e(x:Swatch S)(t: Zodiac (K.c m)): d (z • x) t=z • d x t:=by unfold d; rw [map_smul]; exact he' _
    change daub S (H (z • x) q) X=daub S (z • _) X; rw [he',←r,←r]
    unfold f; simp_rw [e]; rw [integral_smul]
def reGauge : Bay K S →ₗ[ℂ] Bay K S :=
 (stocked K S).toLinearMap.comp ((hueMap K S m h).comp (stocked K S).symm.toLinearMap)
local notation "π"=> reGauge K S m h
lemma stocks(x:Swatch S): π (stocked K S x) = stocked K S (naturalHue K S m h x) :=by
  change stocked K S ((hueMap K S m h) ((stocked K S).symm (stocked K S x))) =_
  rw [LinearEquiv.symm_apply_apply]; rfl
lemma neutral (x:Bay K S) : (π x).val ∈ enclave K := by
  obtain ⟨x,rfl⟩:= (stocked K S).surjective x; rw [stocks]
  exact hue_neutral K S m h x
lemma legacy (x:Bay K S)(t:x.val∈ enclave K) : π x=x:=by
  obtain ⟨x,rfl⟩:= (stocked K S).surjective x; rw [stocks,Ether.after_hue K S m h x t]
-- P maps and dimensions
def fromSpot : Spot K S →ₐ[ℂ] Bay K S := Subalgebra.inclusion (show Spot K S≤Bay K S from inf_le_left) -- sub spot implicit
local notation "uₑ"=> fromSpot K S
def accessor : Bay K S →ₗ[ℂ] Spot K S where
 toFun x:= ⟨(π x).val,(π x).property,neutral K S m h x⟩
 map_add' x y:= Subtype.ext (congrArg (fun p:Bay K S=>p.val) (map_add π x y))
 map_smul' z x:= Subtype.ext (congrArg (fun p:Bay K S=>p.val) (map_smul π z x))
lemma renew (x: Bay K S) : fromSpot K S (accessor K S m h x)= π x:= rfl
lemma fixed (x: Spot K S) : accessor K S m h (fromSpot K S x)=x:= by
  have he:π (uₑ x)=uₑ x:= legacy K S m h (uₑ x) x.property.2
  exact Subtype.ext (congrArg (fun p:Bay K S=>p.val) he)

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
    {i k:ℕ→ℕ} {I:ℕ→ Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V : Universal Y H i k I E) (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H) (j:Axis)(C:Arena Y H G.history.circuit j 0 false)
    (s:ℕ)
local notation "K·"=> tent Y H
local notation "N" => liftCap Y H V G.history G.clipped j false C s
local notation "Θ" => bidding Y H
lemma settles (h: Hosp S ((tent Y H).c m)) (x: Bay (tent Y H) S) :
    N (Θ (reGauge (tent Y H) S m h x).val)=N (Θ x.val):=by
  obtain ⟨x,rfl⟩:= (stocked (tent Y H) S).surjective x; rw [stocks]
  exact (Palate.hue_cap Y H V G.history G.clipped j C s h x).symm
end Monochrome
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home.Monochrome
#print axioms accessor
#print axioms neutral
#print axioms settles
