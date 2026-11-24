import YM.SU5.Reconstruction.PilotLight.Position
import YM.SU5.Reconstruction.Crease.Thicket
/-! Geometry at fixed resolution sizes genuinely in spacetime physical metric. Not asserting fields of
bounded thickness F already analytically live in those regions spacelike in a reconstructed physical sense. -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5500
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Fock
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)
open BridgeClub
-- Use E4 coordinate transfer just for geometry. clocks separately paid in actual chosen world.
abbrev cartesian (x: Set RSpace): Set E4:= (WithLp.toLp 2 : RSpace→ E4) '' x
lemma reach_height (y:ℝ) : ∃ t : marks (timeMesh Λ),y<t.val:=by
 obtain ⟨x,a,b⟩:= ((daylight (timeMesh Λ)).exists_mem_open isOpen_Ioi (show (Ioi y).Nonempty from ⟨_,lt_add_one y⟩)); exact ⟨⟨x,a⟩,b⟩ -- tune order
structure StandingFree (δ R:ℝ)(p:placement Λ):Prop where
  gap : ∀ j:Axis, R + δ ≤ (p j:ℝ)
  separation : Disjoint (alcove R) (slides (coordinates Λ p) (alcove R))
  spatial : TicketSeparation j (cartesian (alcove R)) (cartesian (slides (coordinates Λ p) (alcove R)))
lemma spends (δ R:ℝ)(h:0<δ) : ∃ p:placement Λ, StandingFree j δ R p:= by
 obtain ⟨z,t⟩:= reach_height (Λ:=Λ) (R+δ); obtain ⟨u,w⟩:= reach_height (Λ:=Λ) (max (R+δ) ((z:ℝ)+R+R)); let p:placement Λ:=fun i=>if i=j then z else u
 have hp:p j=z:=if_pos rfl; have he(i:Axis):R+δ < (p i:ℝ):=by unfold p; split_ifs <;> first|exact t|exact (le_max_left ..).trans_lt w
 refine ⟨p,fun i=> (he i).le, alcove_separate R R (coordinates Λ p) (j:=j) ((lt_add_of_pos_right _ h).trans (he j)),?_⟩
 obtain ⟨a,d⟩:= exists_ne j
 rintro _ ⟨x,hx,rfl⟩ _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
 let V:= WithLp.toLp 2 (y+coordinates Λ p)- WithLp.toLp 2 x
 have ht:V j=y j+z.val-x j:=by change y j+(p j).val-x j=_; rw [hp]
 have hA:V a=y a+u.val-x a:=by change y a+(p a).val-x a=_; rw [show p a=u from if_neg d]
 have hz: 0 < V j:=by rw [ht]; linarith [(hx j).2,(hy j).1] -- std no unfold
 have hg: V j < V a:=by rw [ht,hA]; linarith [(hx j).1,(hx a).2,(hy j).2,(hy a).1, (le_max_right ..).trans_lt w] -- sum proof
 change Clearance j V; exact (pow_lt_pow_left₀ hg hz.le (by decide)).trans_le (Finset.single_le_sum (f:=fun i:Axis=> _) (fun i h=> sq_nonneg (V i)) (s:=Finset.univ.erase j) (a:=a) (by simp [d]))
lemma distance_mark {δ R:ℝ}{p:placement Λ} (h:StandingFree j δ R p) : ∀ i:Axis,∀ x∈ alcove R,∀ y∈ slides (coordinates Λ p) (alcove R),x i+δ ≤ y i:=by
 rintro i x t _ ⟨y,s,rfl⟩; change x i+δ ≤ y i + (p i:ℝ); linarith [(t i).2,(s i).1,h.gap i]
lemma signed_extent (c d:ℝ)(g:Set RSpace)(v:IsCompact g) : ∃ u:placement Λ, ∀ i:Axis,(c+d≤ (u i:ℝ))∧ ∀ x∈g,x i+d ≤ (u i:ℝ):=by
 have he(i:Axis): ∃ t:Gt,(c+d≤ (t:ℝ))∧∀ x∈g,x i+d ≤ t.val:= by
    obtain ⟨b,h⟩:= (v.image (continuous_apply i)).bddAbove
    obtain ⟨x,l⟩:= reach_height (Λ:=Λ) (max c b+d)
    exact ⟨x,by linarith [le_max_left c b],fun X hX=> (add_le_add_left (show X i≤ b from h ⟨X,hX,rfl⟩) d).trans (by linarith [le_max_right c b])⟩ -- add_le_add signature changed? earlier used add.le_add_left result x+d
 choose f hf using he; exact ⟨f,hf⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.spends
