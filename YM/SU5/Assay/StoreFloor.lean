import YM.SU5.Assay.Baluster
import YM.SU5.Assay.Bank
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Set Aria
variable (P:Spine)(s:ℕ)
local notation "K"=>P.calibration
local notation "Λ"=>P.par
local notation "b"=> ruler (Λ).block
local notation "τ"=> P.tock s
local notation "Φ"=> P.pinFoot s
variable {M:Set Vantage}{j:Axis} {Z:Finset Cover}{k:ℤ}{w:ℕ}
variable {P s}
/-- Caliper's physical footprint licence. Converse to `FrameFace.between`. -/
lemma Sleeve.inside (p:P.Sleeve j k w Z){y:Vantage}(t:y∈ Φ Z):τ k≤y j ∧ y j≤τ (k+w):=by
 obtain ⟨i,h,g⟩:=t
 let d:ℝ:=precisionAt (Λ) s
 have hd:0<d:=positiveScale ..
 have h₀:|(d)*(2*y j) - ↑(i j)|≤ (K).ℓ:=g j
 have h₁(m:ℤ):2*τ m=↑(b*m)/d:= Apron.distance_mark P ..
 obtain ⟨p₁,p₂⟩:=p.frame i h
 have q:((b*k:ℤ):ℝ)/d ≤ 2*y j:=by
    have u:((b*k:ℤ):ℝ)+ (K).ℓ ≤ (i j:ℝ):=by exact_mod_cast p₁
    apply (div_le_iff₀ hd).mpr; linarith only [u,(abs_le.mp h₀).1]
 have r: 2*y j≤((b*(k+w):ℤ):ℝ)/d:=by
    have u:(i j:ℝ)+ (K).ℓ ≤ ((b*(k+w):ℤ):ℝ):=by exact_mod_cast p₂
    apply (le_div_iff₀ hd).mpr; linarith only [u,(abs_le.mp h₀).2]
 rw [←h₁] at q r;constructor<;>linarith only [q,r]
lemma Balcony.space {a n:ℕ}{f:P.Test}{U D:Finset Cover}{d:ℝ}(p:P.Balcony j k w Z a n f U D d) :
    (∀y∈Φ U,y j≤τ k - τ n) ∧ (∀y∈Φ D,τ (k+w)+τ n≤y j):=by
 constructor
 · intro y h
   have u:=(p.pre.inside h).2
   rwa [sub_add_cancel,P.tock_sub] at u
 intro y h; rw [←P.tock_add];exact (p.post.inside h).1
/-- Tick faces in every direction. -/
def FrameFloor (P:Spine)(s:ℕ)(M:Set Vantage):Prop:=∀j,∃ q r k w, P.FrameFace j s M q r k w
variable {F:P.Test}
/-- This is a maximal permitted site bill at this price. -/
structure StoreFloor (P:Spine)(s:ℕ)(M:Set Vantage)(Z:Finset Cover):Prop where
 forward:P.pinFoot s Z⊆M
 back:∀Y:Finset Cover,P.pinFoot s Y⊆M→Y⊆Z
namespace StoreFloor
variable (p:StoreFloor P s M Z)
include p
lemma space {q r:ℝ}(h:P.FrameFace j s M q r k w):P.Sleeve j k w Z:=⟨h.width,h.between p.forward⟩
lemma auth : P.asked_at s F M ↔ F∈ bay K Z true:=by
 constructor
 · rintro ⟨Y,h,u⟩; exact tallerBay _ _ _ (p.back Y u) h
 exact fun h=>⟨_,h,p.forward⟩
end StoreFloor
lemma FrameFloor.stores (p:P.FrameFloor s M):∃Z,StoreFloor P s M Z:=by
 choose q t k w h using p
 let L:= Fintype.piFinset (fun i=>Finset.Icc (b*k i) (b*(k i + w i)))
 let Z:= L.filter (fun i:Cover=> Φ {i}⊆M)
 refine ⟨Z,?_,?_⟩
 · rintro y ⟨i,g,u⟩
   exact (show Φ {i}⊆M from (mem_filter.mp g).2) ⟨_,Finset.mem_singleton_self _,u⟩
 intro Y g i h'
 refine mem_filter.mpr ⟨Fintype.mem_piFinset.2 (fun j=>Finset.mem_Icc.mpr ?_), (P.pin_mono _ _ _ (Finset.singleton_subset_iff.mpr h')).trans g⟩
 obtain ⟨u,v⟩:=(h j).between g i h';constructor <;>omega
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
