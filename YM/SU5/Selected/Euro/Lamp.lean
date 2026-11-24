import YM.SU5.Selected.Euro.Plume

/-! # Cross-level lights: Euclidean covariance via all registered lamps 
Still discrete orientation/scale, earns translations explicitly. -/
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 240000
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
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)

open Tapestry
namespace Lamp
open YM.CF.Pannier.Chancel
open Altitude Exhibition
local notation "ℳ" => Dome (tent Y H)
local notation "pS" => Cloud (Dome (tent Y H))
local notation "Q₀" => FiniteGaugeDataPoly (tent Y H)
local notation "B" => groundAlgebra Y H V Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Only" => Vacancy.observable (tent Y H) true
variable (χ : CapCharacter Y H V Q Qc j false C)
local notation "f₀" χ:max s:max => marked Y H V Q Qc j false C χ s
variable {Z:Rack Λ l}{P:Clay Λ l}(U:Exhibition Y H i k I E Z P)
local notation "J_χ" => Selection.bill Y H V Q Qc j C U
local notation "uF" s:max=> vistaFinish Y H s U
variable (s:ℕ)
open PiTensorProduct (tprod)
local notation "Φ" => vistaDressing Y H U
local notation "F" i:max=> vistaFinish Y H i U
variable (a₀:Axis)(z:Sunlight Λ)
local notation "θ" => Sunlight.oppose Λ a₀ z K
local notation "Θ" => fun i=>aureole K a₀ (z.marks i)
local notation "PI" => z.arena Λ
variable (wide:Bool)(X:Set RSpace){S:Set ℕ}(hx:S⊆ z.arena Λ)
include hx
lemma crop_lights (u:z.start ≤ s) (x:pS)(p:x∈jetty Λ l K wide X (S ∩ Set.Iic s)) : (F s) (θ x)= (Θ) s ((F s) x):= by
 apply boarded (P:={f|Officer (S∩ Set.Iic s) (fun i=>keep Λ l i K wide X) f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ p -- need ∀ recurrence prove outside
 · intro f (g:Officer _ _ f); have t: Enough s f:= g.visible _ _ Set.inter_subset_right
   -- (Θ) s expansion parentheses, dsimp only correct.
   rw [show tprod ℂ f= pureShot K f from rfl]; rw [Sunlight.opposes]; unfold vistaFinish pureShot; rw [Decking.reckon_paid _ _ _ t, Decking.reckon_paid _ _ _ (z.opponentEnough Λ a₀ s K t)]; exact lightFinish f u (fun i j=> g.forbids _ (fun v=> j.not_ge (hx v.1)))
 · simp
 · intro i j w v x y; rw [map_add,map_add,x,y,map_add (F s),map_add]
 intro a i w x; change _= (aureole K a₀ (z.marks s)) _; rw [LinearMap.map_smulₛₗ,map_smul,map_smul (F s),LinearMap.map_smulₛₗ,x] -- could rw map_smul recognizes star? note `(Θ) s` notation issue
where
 lightFinish (f:ℕ→Dome (tent Y H))(pw:z.start ≤ s) (g:∀ i:ℕ, i<z.start→f i=1):
    (Φ).finish s (Sunlight.opponent Λ a₀ z K f)=aureole K a₀ (z.marks s) ((Φ).finish s f):=by
    clear u p
    induction s,pw using Nat.le_induction with
    | base =>
       rw [Decking.finish_alone Φ _ (Sunlight.opponent Λ a₀ z K f) (fun n k=> show aureole K a₀ (z.marks n) (f n) =1 from Eq.trans (congrArg _ (g _ k)) (aureoleUnit ..)),Decking.finish_alone Φ z.start _ g]; rfl
    | succ n v ih=>
       rw [Decking.finish,Decking.finish,ih]; change liftD Y H _ U (aureole K _ _ _) * _= _; rw [Breflect,aureoleProduct,z.aligned n v]; rfl

include V Q Qc C
lemma many_dawns (x:pS)(p:x∈jetty Λ l K wide X S) : J_χ χ (θ x)= star (J_χ χ x) := by
 obtain ⟨s,h⟩:= entrusted Λ l K wide X S p
 let n':=max s z.start; have a:z.start≤n':=le_max_right ..; have hv:x∈jetty Λ l K wide X (S∩Set.Iic n'):= admits Λ l K wide X X (S∩ Set.Iic s) (S ∩ Set.Iic n') (fun i p=> ⟨p.1,(show i ≤ s from p.2).trans (le_max_left ..)⟩) Set.Subset.rfl h
 rw [cardHeight Y H V Q Qc j C U χ n' (jettyBan Λ l K wide _ S n' (z.opposition Λ l a₀ K (Set.Subset.trans (Set.inter_subset_left) hx) X wide hv)), cardHeight Y H V Q Qc j C U χ n' (jettyBan Λ l K wide _ S n' hv), crop_lights Y H U n' a₀ z wide X hx a x hv] -- signature order
 obtain ⟨xₐ,t⟩:= z.shifted n' a; dsimp only; rw [t]; exact (all_together Y H V Q Qc j false C χ).flip _ a₀ xₐ (bidding Y H ((F n') x)) -- shadow x mark

variable (z' : Sunlight Λ)(v':S ⊆ z'.arena Λ)
-- composition translate: all.arena. express physically & hands
noncomputable def redShift := (Sunlight.oppose Λ a₀ z' K).comp (σ₁₃:=RingHom.id ℂ) (Sunlight.oppose Λ a₀ z K)
local notation "Δ" => redShift Y H a₀ z z'
def lantern (u:RSpace) : RSpace:= Pi.single a₀ (2*(z'.hinge Λ-z.hinge Λ))+u
local notation "ρE"=> lantern a₀ z z' -- Λ? arg infer
include v'
lemma lantern_up (x:pS)(p:x∈well Λ K l wide X S) : (Δ) x∈ well Λ K l wide ((ρE) '' X) S ∧ J_χ χ ((Δ) x)=J_χ χ x := by
 let k:= mirrorE a₀ (z.hinge Λ); let k':= mirrorE a₀ (z'.hinge Λ)
 have h:k' ∘ k=ρE:= funext fun i=>funext fun y=>by unfold lantern k k' mirrorE; simp only [Function.comp_apply, Pi.add_apply]; by_cases w:y=a₀ <;> simp [w]; ring
 rw [←h,Set.image_comp]; have hv:=flipWell Λ K l wide X S a₀ z hx p
 exact ⟨flipWell Λ K l wide (k '' X) S a₀ z' v' hv,by
    unfold redShift; rw [LinearMap.comp_apply,many_dawns Y H V Q Qc j C χ U a₀ z' wide (k '' X) v' _ ((well_spec ..).1 hv).1,many_dawns Y H V Q Qc j C χ U a₀ z wide X hx x ((well_spec ..).1 p).1,star_star]⟩

-- bary on multirank & axes decisions with symmetry, not unique J.result on other histories. FiniteGaugeData polys before unselected. maybe separate cp4.
end Lamp
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection
#print axioms Lamp.lantern_up
#print axioms Lamp.many_dawns
