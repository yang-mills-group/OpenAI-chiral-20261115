import YM.SU5.Relativistic.Panorama
import YM.SU5.Relativistic.PairedShelves
import YM.SU5.Relativistic.Straw
import YM.SU5.Relativistic.NoContact
import YM.SU5.Relativistic.Portfolio
import YM.SU5.Relativistic.NeedlePacket
/-!
# Geometry registration of local physical polynomials.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5500
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory Metric
open Lattice Wilson RG SU Lat Mir RP Reflect Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Py Py.Rate LocalLimit PhaseChoice Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)(G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis) (J: Arena Y H G.history.circuit j 0 false)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "D₀"=> Dome (tent Y H)
local notation "Τ"=> Cloud (Dome (tent Y H))
local notation "P₀" n:max=> vistaFinish Y H n D
local notation "d★" => vistaDressing Y H D
local notation "B₀" => driveAlgebra Y H D.univ_ G.history G.clipped j false J
local notation "Rg" t:max => Docked Y H D.univ_ t G.history G.clipped j J

local notation "ρ"=> D.univ_
local notation "reach" n:max f:max => reachMark (tent Y H) ((P₀ n) f)
section billing
variable (d:Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(χ : displayAlgebra Y H D.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "Χ"=> SameCharacter.resident Y H D.univ_ G d false (c d) χ
local notation "Ψ"=> onDrawing Y H D.univ_ G D d c Χ
local notation "Θ"=> procession Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "V"=>fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "p★"=>saunters Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "ω"=> vocation Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "A"=>ride Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ξ"=> peninsula Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j)
local notation "P□"=> mainsea Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "e□"=> follows_road Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "B□"=> docket Y H D G j (c j)
local notation "Φ"=> driveAlgebra Y H D.univ_ G.history G.clipped j false (c j)
local notation "dock" n:max => Docked Y H D.univ_ n G.history G.clipped j (c j)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

open Finset
open YM.CF.Pannier.Chancel
section pair
variable (δ:ℝ) (s:ℕ) (Z:Marks (tent Y H) true)(p q:Cover)(S:Finset Cover)
local notation "η₀"=> pinhole (Dome K) s (PhaseChoice.resolutionProbe Y H (mirrorInMarks Y H j true (relocateWorld Y H true p Z)))
local notation "η₁"=> pinhole (Dome K) s (PhaseChoice.resolutionProbe Y H (relocateWorld Y H true q Z))
def pattern : Bool→ Tapestry.Altitude.Cloud (Dome (tent Y H)) := fun i=> if i then η₁ else η₀
local notation "T₂"=> pattern Y H j s Z p q
local notation "U₁"=> footprint Λ l s (streetBox K q S)
local notation "U₀"=> footprint Λ l s (reflectedBox j 0 (streetBox K p S))
local notation "π₀"=> panorama Y H D G d c χ T₂ [false,true]
local notation "ω₀"=>windowPrice Y H D G
variable {w:ℝ}{t i:ℕ}{o:Cover}{z:SU.Slot}
lemma widerFoot (x:ℕ) {U:Set RSpace}{f:Cloud (Dome (tent Y H))} (h:f∈ circum Λ l K false U {x}): f∈ poet Y H x U:= by exact circum_widens Y H Set.Subset.rfl (Set.singleton_subset_iff.mpr (Set.mem_Iic.mpr (Nat.le_refl x))) (wellWider Λ K l false _ _ h)
section tested
variable (r:FocusMark Y H D G d j c χ s Z p q δ w t i o S z)
include r
local notation "f□"=> (pattern Y H j s Z p q)
lemma corridor_occurs (j':Axis) : ∃ (n:ℕ) (X V' : Bool → Slab (timeMesh Λ)), Corridor Y H j' (f□) (fun _=>n) X V' [false,true] (V' false).lower 0 ∧ (V' false).upper < (V' true).lower:=by
  apply pairShelf Y H j' (U:= U₀) (W:=U₁) -- defeq pattern perhaps high
  · exact widerFoot Y H s r.region₁
  · exact widerFoot Y H s r.region₂
  · exact footprint_compact ..
  · exact footprint_compact ..
  intro x u y v; linarith only [r.separatedNonzero j' x u y v, r.delta]
lemma contacts_deployed : panorama Y H D G d c χ (pattern Y H j s Z p q) [false,true] 0 = Ψ (η₀*η₁):= by
 obtain ⟨n,X,Q,u,t'⟩:= corridor_occurs Y H D G j d c χ _ _ _ _ _ _ r j
 let v:= (Q false).lower
 rw [panorama_price Y H D G j d c χ f□ (fun _=>n) X Q [false,true] v _ _ (.refl _) u]
 change windowPrice Y H D G j d c χ f□ (fun _=>n) X Q [false,true] (Q false).lower (integerRead (0 : Bool→Axis→Stamp M))=_
 rw [← material Y H D G j d c χ f□ (fun _=>n) X Q [false,true] (Q false).lower 0 u (by simp) ?_, fitCostZero Y H D G j d c χ f□ (fun _=>n) X Q [false,true] (Q false).lower u]
 · simp [pattern]
 intro k; obtain ⟨n',Y',Q',u',t'⟩:= corridor_occurs Y H D G j d c χ _ _ _ _ _ _ r k; exact ⟨[false,true],(Q' false).lower,_,Y',Q',u',List.Perm.refl _⟩
lemma displaced_test (v:Axis→ℝ):panorama Y H D G d c χ f□ [false,true] (fun _=>v)= Ψ (η₀*η₁) := by
 obtain ⟨n,X,Q,u,t'⟩:= corridor_occurs Y H D G j d c χ _ _ _ _ _ _ r j
 rw [← contacts_deployed Y H D G j d c χ δ s Z p q S r, show (fun _:Bool=> v)=tourShift (0:Bool→Axis→ℝ) v from funext (fun _=> (zero_add _).symm)]; exact flight_homogeneous Y H D G d c χ (pattern Y H j s Z p q) [false,true] 0 ⟨j,[false,true],.refl _,_,_,_,_,u⟩ v
lemma near_true : ∀ᶠ x : Bool→Axis→ℝ in 𝓝 0, x∈ journeying Y H (pattern Y H j s Z p q) [false,true] ∧
   1/33 < ‖panorama Y H D G d c χ (pattern Y H j s Z p q) [false,true] x‖ ∧ ∀ a∈ U₀, ∀ b∈U₁, ∀ j':Axis,
        (a j'+x false j') + δ/2 ≤ b j'+x true j':=by
 obtain ⟨n,X,Q,u,t'⟩:= corridor_occurs Y H D G j d c χ _ _ _ _ _ _ r j
 have h:(0:Bool→Axis→ℝ)∈journeying Y H f□ [false,true]:=⟨j,[false,true],.refl _,_,_,_,_,u⟩
 have he: 1/33 < ‖panorama Y H D G d c χ f□ [false,true] 0‖:=by rw [contacts_deployed Y H D G j d c χ _ _ _ _ _ _ r]; exact lt_of_lt_of_le (by norm_num) r.prices
 apply Filter.Eventually.and ((journeyOpen Y H f□ [false,true]).mem_nhds h); apply Filter.Eventually.and ((journeySmooth Y H D G d c χ _ [false,true] 0 h).norm.tendsto.eventually (lt_mem_nhds he))
 have hq (j:Axis): ∀ᶠ f: Bool→Axis→ℝ in 𝓝 0, f false j - f true j < δ/2 := by
    let F (x:Bool→Axis→ℝ):= x false j - x true j; have hm:Continuous F:=by unfold F; fun_prop
    apply (hm.tendsto 0).eventually (gt_mem_nhds (show F 0< δ/2 from (show 0 - 0<δ/2 from (by linarith only [r.delta]))))
 filter_upwards [eventually_all.mpr hq] with f ht a u b v k; linarith only [ht k,r.separatedNonzero k a u b v]
end tested
end pair
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.near_true
