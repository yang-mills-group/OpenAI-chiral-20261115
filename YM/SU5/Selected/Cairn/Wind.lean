import YM.SU5.Selected.Cairn.Stage
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
open CF.Pannier.Chancel.Attic.Cairn
variable (M:Giant){c:ℝ}(p:printedHere Λ l s M.Broad (cabin c))(t:addgap (tent Y H)≤ M.timeGap.val)
namespace Planet
local notation "Y₀"=> M.ascY
local notation "Y₁"=> M.ascX
local notation "P"=>volumeAround Λ l
local notation "ν" n:max=> grates Λ l n
-- physical plan all ℕ. Generic Permit for gap on every rank. layout only needed early. Also all seams by choosing clock separation v.
structure OrderedU (Λ:Preparation)(l:ℕ)(s:ℕ)(c k:ℝ)(S T:Finset Cover) : Prop where
 layout: GalleryG Λ l s c k S T
 ranked (j:Axis)(x y:RSpace) : x∈ grates Λ l s S→y∈grates Λ l s T→ x j+k ≤ y j
lemma grates_up (Λ:Preparation)(l s n:ℕ)(S:Finset Cover) : (grates Λ l (s+n) (volumeAround Λ l n S))⊆ (grates Λ l s S):= fun x ⟨a,p,t⟩=> transport_location Λ l s n S (grates Λ l s S) (fun x u y p=>⟨_,u,p⟩) _ p t
namespace OrderedU
variable {S T:Finset Cover}{k:ℝ}(h: OrderedU Λ l s c k S T)(n:ℕ)
include h
lemma prudence : OrderedU Λ l (s+n) c k ((P) n S) ((P) n T):=
 ⟨⟨h.layout.restrains n,h.layout.warm, (grates_up Λ l s n S).trans h.layout.light,(grates_up Λ l s n T).trans h.layout.dark,fun x y t p=> h.layout.gap x y (grates_up Λ l s n S t) (grates_up Λ l s n T p)⟩,fun j x y t p=> h.ranked j x y (grates_up Λ l s n S t) (grates_up Λ l s n T p)⟩
end OrderedU
include Y H t
variable (j:Axis)
lemma rapid(x y:Cover)(p:x∈ Y₀)(q:y∈ Y₁) :  (3:ℤ)*reserve Λ l≤ y j-x j := by have ht:= M.sorted x y p q j; have hp: (R)≤ M.timeGap.val:= le_trans (by unfold addgap stepgap; change _ ≤ 2*(reserve Λ l+_); omega) t; change _+ 2* ((100*M.timeGap.val:ℕ):ℤ) ≤ _ at ht; omega
include p
lemma layout : OrderedU Λ l s c (grate Λ l s) (Y₀) (Y₁):= by
 refine ⟨shapeK Λ l s p (M.nut.trans (M.portS.trans M.portT)) (M.nudge.trans (M.portS.trans M.portT)) (fun y t1 w b=> by have h' := rapid Y H M t 3 y w t1 b; omega),fun j u v h h' => ?_⟩
 obtain ⟨x,hx,z⟩:=h; obtain ⟨y,hy,p⟩:=h'; obtain ⟨a,b⟩:= abs_le.mp (z j); obtain ⟨j0,j'⟩:= abs_le.mp (p j)
 apply le_sub_iff_add_le'.1; unfold grate; apply (div_le_iff₀ (positiveScale Λ s)).mpr; have hp:(3:ℝ)*(R:ℝ)≤ (y j:ℝ)-(x j:ℝ):=by exact_mod_cast (rapid Y H M t j x y hx hy)
 linarith
omit p
local notation "ℓ₀"=> ruler (K).B
noncomputable def declination':ℤ:= (M.markY 0 j+(M.t:ℤ))/ruler (tent Y H).B
local notation "δ" j:max=> declination' Y H M j
lemma eminence (x y:Cover)(u:x∈ Y₀)(v:y∈ Y₁): x j +(K).ℓ≤ ℓ₀*(δ j) ∧ ℓ₀*(δ j)+ℓ₀+(K).ℓ ≤ y j:=by
 unfold declination'; have hu: x j≤ M.markY 0 j:= (Finset.mem_Icc.mp u).2 j; have ht: M.markY 0 j+ 2*(M.t:ℤ)≤ y j:= M.sorted _ _ (M.ascW _ (Nat.zero_le M.beams)) v j
 have hh: (tent Y H).ℓ + (ruler (tent Y H).B) ≤ (M.t:ℤ):= by change _ ≤ ((100*M.timeGap.val:ℕ):ℤ); unfold addgap stepgap at t; unfold ruler; omega
 have hz:= Int.emod_add_mul_ediv (M.markY 0 j+(M.t:ℤ)) (ℓ₀); have hw:= ruler_gene (K).B; have hp:= Int.emod_lt_of_pos (M.markY 0 j+(M.t:ℤ)) hw; have hi:= Int.emod_nonneg (M.markY 0 j+(M.t:ℤ)) hw.ne'; omega
lemma seam_cash (j:Axis) : (∀ x∈ Y₀,x j+(tent Y H).ℓ ≤ ℓ₀*δ j) ∧ (∀ y∈ Y₁, ℓ₀*δ j +ℓ₀+(K).ℓ ≤ y j):= ⟨fun x u=> (eminence Y H M t j x _ u (M.ascN _ (Nat.zero_le M.n))).1,fun y v=> (eminence Y H M t j _ y (M.ascW _ (Nat.zero_le _)) v).2⟩ -- notation parser `δ j +`
end Planet
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern.Planet
#print axioms seam_cash
#print axioms OrderedU.prudence
#print axioms layout
