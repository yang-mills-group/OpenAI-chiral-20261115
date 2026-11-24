import YM.SU5.Selected.Cor.Pent
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
open CF.Pannier.Chancel Tapestry Papal
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
attribute [local instance] opCStarAlgebra
namespace Fern
variable (s:ℕ)(A:Mezz)
local notation "Λ₀" => precisionAt Λ s
local notation "R"=> reserve Λ l
noncomputable def grates (Λ: Preparation)(l:ℕ)(s:ℕ)(X:Finset Cover) : Set RSpace:= {u|∃ x∈ X,u∈ Tapestry.shield Λ l s x}
structure GalleryG (Λ:Preparation)(l:ℕ)(s:ℕ)(c k:ℝ)(X Y:Finset Cover): Prop where
 detached : Detached Λ l X Y
 warm: 0 < k
 light: grates Λ l s X ⊆ cabin c
 dark: grates Λ l s Y ⊆ cabin c
 gap (x y: RSpace): x∈ grates Λ l s X→ y∈ grates Λ l s Y→ k ≤ dist x y
#print GalleryG.mk
namespace GalleryG
variable {X X':Finset Cover}{s}{c k:ℝ} (A' : GalleryG Λ l s c k X X') (n:ℕ)
local notation "V"=> volumeAround Λ l n
local notation "P"=> printedHere Λ l (s+n)
local notation "S"=> cabin c
private lemma st_i (X:Finset Cover): P (V X) (grates Λ l s X):= transport_location Λ l s n X _ (fun x h y v=>⟨_,h,v⟩)
include A'
lemma viewed : P (V X) (S) ∧ P (V X') (S) := ⟨ fun x h=> (st_i n X x h).trans A'.light, fun x h=> (st_i n X' x h).trans A'.dark⟩ -- syntax
lemma remains: ∀ x∈V X,∀ y∈ V X',∀ u∈ Tapestry.shield Λ l (s+n) x, ∀ v∈ Tapestry.shield Λ l (s+n) y, k≤ dist u v:= fun x t y e u p v q=> A'.gap _ _ (st_i n X x t p) (st_i n X' y e q)
lemma restrains: Detached Λ l (V X) (V X'):= Around_detaches Λ l A'.detached n -- binder order
omit A'
end GalleryG
variable (e:A.Legate)(p: addgap (tent Y H)≤ A.ℓ.val) -- dangerous notation K removed
-- guarantee at all Display n. Gap scale **10*reserve**? choose ≥ reserve/L (positive). widths shrink ≥ any fixed. orientation at Ward.
abbrev grate (Λ:Preparation)(l:ℕ)(s:ℕ): ℝ:= (reserve Λ l:ℝ)/precisionAt Λ s
private lemma sep_hall (Λ:Preparation) (l s:ℕ)(u v:RSpace)(x y:ℤ)(q:3*(reserve Λ l:ℤ)≤ y-x)(p:|precisionAt Λ s*u 3-x|≤(reserve Λ l:ℝ))(h:|precisionAt Λ s*v 3-y| ≤ (reserve Λ l:ℝ)): grate Λ l s ≤ dist u v := by
 obtain ⟨i,j⟩:= abs_le.mp p; obtain ⟨a,b⟩:=abs_le.mp h; apply le_trans _ (dist_le_pi_dist u v 3); rw [Real.dist_eq]; apply le_trans _ (neg_le_abs _); rw [grate,div_le_iff₀ (positiveScale Λ s)]; have hp:3*(reserve Λ l:ℝ) ≤ y-(x:ℝ):=by exact_mod_cast q
 linarith
variable {c:ℝ}
lemma shapeK (Λ:Preparation) (l s:ℕ) {Z X X':Finset Cover} (x:printedHere Λ l s Z (cabin c))(h:X ⊆ Z)(v:X' ⊆ Z)
    (e:∀ y∈X,∀ w∈ X', 3*reserve Λ l ≤ (y 3 - w 3).natAbs) : GalleryG Λ l s c (grate Λ l s) X X':= by
 let M:=(reserve Λ l:ℤ); have hv: 0 < reserve Λ l:= margin_good ..; refine ⟨?_, div_pos (by positivity) (positiveScale ..), fun a ⟨i,w,g⟩=> x i (h w) g, fun a ⟨i,w,g⟩=> x i (v w) g, fun u v' t z=>?_⟩
 · intro a k b r i; have hx:=e a k b r; obtain ⟨j,j'⟩:= box_test.mp i; specialize j 3; specialize j' 3; rw [Pi.sub_apply] at j j'; omega
 obtain ⟨i,u',t⟩:=t; obtain ⟨j,v,p⟩:=z; have hx:= e i u' j v; by_cases p':i 3≤ j 3; · exact sep_hall _ _ _ u v' (i 3) (j 3) (by omega) (t 3) (p 3)
 rw [dist_comm]; exact sep_hall _ _ _ v' u _ _ (by omega) (p 3) (t 3)
local notation "Θ" X:max X':max=> GalleryG Λ l s c (grate Λ l s) X X'
variable (t:printedHere Λ l s A.Broad (cabin c)) (i:A.BlockDay)
include p t Y H e
lemma pipes : Θ (A.coast_b true) (A.coast_b false):=by
 have he:(reserve Λ l) ≤ A.ℓ.val:= p.trans' (by unfold addgap stepgap; change _≤2*(reserve Λ l+_); omega); apply shapeK Λ l s t ((A.shore_rest true e).trans A.Core_subset) ((A.shore_rest false e).trans A.Core_subset); intro x h y v; have ht:=A.view_sea x y e h v; omega -- signature
local notation "N"=> Sermon.toyL A K i
local notation "M"=> Sermon.toyR A K i
lemma toys : Θ N M:=by
 have hx:(reserve Λ l) ≤ A.ℓ.val:= p.trans' (by unfold addgap stepgap; change _≤2*(reserve Λ l+_); omega); apply shapeK Λ l s t (filter_subset ..) (filter_subset ..); intro x h y v; have hu: x 3+10*(A.ℓ.val:ℤ) ≤ ruler (K).B*Sermon.declination A (K) i:= (mem_filter.mp h).2; have hp:ruler (K).B*Sermon.declination A (K) i+10*(A.ℓ.val:ℤ) ≤ y 3:= (mem_filter.mp v).2; omega
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern
#print axioms pipes
#print axioms GalleryG.remains
#print axioms toys
