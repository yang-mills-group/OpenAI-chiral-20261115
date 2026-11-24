import YM.SU5.Relativistic.Consist
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

section rays
variable (s w:ℕ) (x:Entry Y H s j true w) (h:0<w)
local notation "F"=> (futureMark Y H s j true x.val)
local notation "X₁"=> PhaseChoice.resolutionProbe Y H F
local notation "X"=> pinhole (Dome K) s X₁
local notation "Z"=>land Y H D.univ_ s G.history G.clipped j false (c j) (χ̂ j)
def shell (Λ:Preparation)(s w:ℕ)(h:0<w): Slab (timeMesh Λ):=⟨0, notch (timeMesh Λ) s (w:ℤ), (by rw [←notch_zero (timeMesh Λ) s]; exact (stamp_lt _ _ _ _).mpr (by exact_mod_cast h))⟩
local notation "T" h:max=> shell Λ s w h
local notation "T'"=> shell Λ s (w+1) (by omega)
local notation "ν" k:max=> nub (timeMesh Λ) 0 k
local notation "χ₁" x:max k:max=> earned Y H D G j d c χ s x (T h) T' (ν k)
lemma physicalAdmission : Carries Y H s X j (T h) := by
 obtain ⟨S,p,v⟩ := x.property
 have H₁:X₁∈ keep Λ l s K true (handstamp (footprint Λ l s S)):= ⟨S,(Tapestry.locates ..).mpr p,has_footprint Λ l s S⟩
 have hp:X ∈ poet Y H s (footprint Λ l s S):=oneSlotWell Λ K l true _ _ s (Set.mem_Iic.mpr (le_refl _)) H₁ ((enclave_spec ..).mpr ((marksSpec true F).2 rfl))
 refine ⟨⟨footprint Λ l s S,footprint_compact ..,hp,?_⟩,⟨⟨0,notch_zero M s⟩,w,rfl⟩⟩
 intro i a; obtain ⟨z,k⟩:=Set.mem_iUnion.mp a; obtain ⟨p,hx⟩:=Set.mem_iUnion.mp k
 change 0 ≤ i j ∧ i j≤ (N s (w:ℤ)).val; have hh :=v z p
 have he₁ := (show i ∈ collar Λ l s z from hx).1 j; have he₂ := (show i∈ collar Λ l s z from hx).2 j
 rw [precise_meters]
 rw [lower_gauge] at he₁; rw [upper_gauge] at he₂
 constructor
 · refine le_trans ?_ he₁; unfold gaugePosition; rw [←_root_.sub_mul]; apply mul_nonneg ?_ (gaugeMesh_pos ..).le; apply sub_nonneg.mpr
   have hx : (reserve Λ l:ℤ) ≤ z j:=by
      have he:=hh.1; rw [zero_add] at he; exact he
   exact_mod_cast hx
 refine le_trans he₂ ?_; unfold gaugePosition; rw [←_root_.add_mul]; apply mul_le_mul_of_nonneg_right ?_ (gaugeMesh_pos ..).le; exact_mod_cast (show z j+(reserve Λ l:ℤ) ≤ (ruler Λ.block)*(w:ℤ) from hh.2)

lemma decked : B□ s X (T h)= entrance Y H D.univ_ s G.history G.clipped j false (c j) (composer Y H s j x) h := by
 apply Docked.uniqueB Y H D.univ_ s G.history G.clipped j (c j) (docket_bound Y H D G j (c j) s X (T h) (physicalAdmission Y H j s w x h))
 refine ⟨0,w,notch_zero M s,by rw [zero_add]; rfl,h, composer Y H s j x,?_,rfl⟩
 rw [neg_zero,relocate_zero _ j ((marksSpec false _).1)]; change x.val.val= ((P₀ s) X).val
 unfold vistaFinish; rw [Decking.outcrop]; rfl
lemma scout_point : Tendsto (fun k:ℕ=> (χ₁ X k) ω) atTop (𝓝 (Z ((composer Y H s j x).val))) := by
 let K' (i:ℕ):= nub (timeMesh Λ) 0 i
 have hp:= collecting_point j (T h) T' K' 0 P□ A e□ (Θ (B□ s X (T h))) (by exact adjusts_mesh («M»:= timeMesh Λ) 0) ω -- tune
 have he : envelope P□ A e□ (Θ (B□ s X (T h))) (T h) T' 0 ω = Z ((composer Y H s j x).val):=by
    rw [envelope_zero]
    change (p★).orthogonalProjectionOnto ((encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j) (T h) T' (B□ s X (T h)) 0) ((ω).val:Ρ))= _
    have hu: heatGap (T').lower ((T h).lower+(0:Axis→ Stamp (timeMesh Λ)) j)=0:= by change heatGap (0:Stamp M) (0+0)=0; rw [add_zero,heatGap_zero]
    rw [encase, neg_zero,spacePos_origin,hu,(A).eZero,one_mul,mul_one, ContinuousLinearMap.mul_apply, scout Y H D.univ_ s G.history G.clipped j false (c j) (χ̂ j) (composer Y H s j x) h] -- direction? scout rewrite RHS forward.
    change (p★).orthogonalProjectionOnto (Θ _ ((A).E _ ((ω).val:Ρ)))= (p★).orthogonalProjectionOnto (Θ _ ((ω).val:Ρ))
    rw [vocate, heat_origin,decked]
 exact he ▸ hp
lemma soon_attach : ∀ᶠ i:ℕ in atTop,Served Y H j s X (T h) T' (ν i):=by
 let W(v:ℕ):= nub (timeMesh Λ) 0 v
 have ht:(T h).upper.val < (T').upper.val:=by refine (stamp_lt M s _ _).mpr ?_; omega
 have hm:∀ᶠ t:ℕ in atTop,(mill M t:ℝ)< (T').upper.val-(T h).upper.val := (NNReal.tendsto_coe.mpr (vanishes M)).eventually (gt_mem_nhds (show 0< _ from sub_pos.mpr ht))
 filter_upwards [hm] with k p; refine ⟨physicalAdmission Y H j s w x h,?_⟩
 intro i m; change (0:ℝ)≤ 0+(0+i j*(mill M k:ℝ)) ∧ (T h).upper.val + (0+i j*(mill M k:ℝ)) ≤ (T').upper.val
 simp only [zero_add]; refine ⟨mul_nonneg (show 0≤ i j from m.1 j) (mill M k).property,?_⟩ -- wrong
 have hp: i j*(mill M k:ℝ)≤ (mill M k:ℝ):= mul_le_of_le_one_left (by exact (mill M k).property) (m.2 j); linarith
end rays
-- density in one inserts
noncomputable def comet : Set ((fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)).space) :=
   {z|∃ (t:ℕ) (F:Cloud (Dome (tent Y H))) (S T:Slab (timeMesh Λ)) (Q:Packet (timeMesh Λ)), T.lower=0 ∧ Served Y H j t F S T Q ∧ earned Y H D G j d c χ t F S T Q ω=z}
lemma starstruck : Dense (comet Y H D G j d c χ):=by
 intro v; refine closure_minimal ?_ isClosed_closure (shore_dense Y H D.univ_ G.history G.clipped j (c j) (χ̂ j) v)
 intro x t
 obtain ⟨s,u⟩:= Set.mem_iUnion.mp t; obtain ⟨z,rfl⟩:= u; obtain ⟨w,p,e,rfl⟩:= artist_fits_slab Y H s j true z
 refine mem_closure_of_tendsto (scout_point Y H D G j d c χ s w e p) ?_
 exact (soon_attach Y H j s w e p).mono fun i t=> ⟨_,_,_,_,_,rfl,t,rfl⟩
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.starstruck
