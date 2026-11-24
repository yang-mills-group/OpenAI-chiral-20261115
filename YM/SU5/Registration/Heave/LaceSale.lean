import YM.SU5.Registration.Heave.LongSpin
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open Lamour.Bridge CF.Pannier.Chancel
variable {Z θ b v t ε R C ξ:ℝ} {n a y z' k:ℕ}
universe u0
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Lamour.Bridge.Celeste.Morn
open YM.CF.Lamour.Bridge YM.CF.Velvet

namespace LaceLayer
open Yoke Tower Tower.SlabMark Tower.SlabMark.ClockBooking Sonnet
variable {r p d:ℕ}{σ:ℝ}
set_option linter.unusedSectionVars true
variable (hp:Geometry P)(t₀:P.Attic)(w':∃ g,Procurement P.K.j g P.d)
variable (T:Finset Cover){f: Weaver}(g:0∈T)(vleg:Voice f T)(σsale:ℝ)(u:0<σsale) (hleg:Clarity f P.K.j (σsale/4))
include hp t₀ w' g vleg u hleg
lemma selling (j:Axis) :
    ∀ᶠ w:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,Ferry Y s i k → IcePlot Y s i k →
    ∀ n:ℕ,∀ b:ℤ, 0<n → 2*(ruler P.block*((w+w:ℕ):ℤ)*(n:ℤ)) ≤ (((side Y i s).val:ℕ):ℤ) → (((side Y i s).val:ℕ):ℤ) ≤ 4*(ruler P.block*((w+w:ℕ):ℤ)*(n:ℤ)) →
      ‖sharp Y H s i k (banner j ((w+w:ℕ):ℤ) (((w+w:ℕ):ℤ)*b) n (relocate (tent Y H) j (w:ℤ) (household (tent Y H) f)))‖ ≤ (3*(Real.exp 1*σsale))^(4*n):=by
 let d:= T.card; let r:= breadth 0 T; obtain ⟨C,b,v'⟩:= vleg.1.rent
 have hp':1≤ P.K.j:=by rw [P.kJ]; decide
 obtain ⟨n,k,g',σsale₀,θ₀,l,hK⟩:= choose_optic hp' (180*d) b u
 obtain ⟨ξ,cX,pX⟩:= ((vleg.1.fee _ hK.zephyr).and self_mem_nhdsWithin).exists
 filter_upwards [eventually_gt_atTop (0:ℕ),eventually_ge_atTop (2*(r+k)+(k+1))] with w H₁ H₂
 let Q:= costweight (tent Y H) r k w; let q:ℝ:= Q; have he: 0<q+1:=by unfold q; positivity
 let θ:ℝ:= (q+1)⁻¹; have hx:0 < θ:=inv_pos.mpr he; obtain ⟨z,hv,vz,F0,Hr⟩:= choose_floor P.K.j hp' (show 0<θ*(8/9) by positivity) hK.zephyr
 obtain ⟨v₀,w₀⟩:=w'; let V:Meringue.{0} Y k r (180*d) σsale₀ ξ C σsale θ:= salon Y hK hv vz w₀ F0 (by rw [show θ/9=θ*(8/9)/8 from by ring]; exact Hr) hx hp t₀ (show 0<ξ from pX) b u r
 refine please_leaf Y H b V j T f g rfl rfl u H₁ hx (show θ*q≤1 from ?_) (?_) vleg v' cX hleg
 · refine (mul_le_mul_of_nonneg_left (show q≤ q+1 from le_add_of_nonneg_right zero_le_one) hx.le).trans_eq (inv_mul_cancel₀ he.ne')
 have h'':(w:ℤ) ≤ ruler P.block * (w:ℤ):= le_mul_of_one_le_left (by positivity) (ruler_gene _)
 exact le_trans (Int.ofNat_le.mpr H₂) h''
end LaceLayer
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.LaceLayer
#print axioms selling
