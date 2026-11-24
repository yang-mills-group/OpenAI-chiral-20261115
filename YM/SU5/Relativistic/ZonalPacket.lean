import YM.SU5.Relativistic.Meets
import YM.SU5.Relativistic.Packet
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
local notation "μ" t:max z:max x:max=> migrate Y H D t z x
local notation "π" t:max z:max x:max=> signOver Y H D t z x
local notation "ι" s:max f:max => pinhole (Dome (tent Y H)) s (packMark _ f)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

lemma signed_shift (t:ℕ)(p:Cover)(X:Set RSpace) (S:Finset Cover)
  (u:SupportedPhysically Λ l t S X):
   footprint Λ l t (streetBox (tent Y H) p S) ⊆ (fun x:Axis→ℝ=>fun j=> x j+((notch (timeMesh Λ) t (p j)):ℝ)) '' X:= by
  intro x h; obtain ⟨a,h⟩:= mem_iUnion.mp h; obtain ⟨q,h⟩:= mem_iUnion.mp h
  obtain ⟨b,v,g⟩:= drives_shifted Y H p ordinate ordinate_one a (show a∈streetBox K p S from q)
  let V j:= (N t (p j)).val
  have he(j:Axis): gaugePosition Λ t a j= gaugePosition Λ t b j+ V j:=by
     unfold V; rw [precise_meters]; unfold gaugePosition; rw [g j,if_pos (ordinates j)]; push_cast; ring
  let y : Axis →ℝ:=x-V
  have h₁ := fun j:Axis=> (show _ from (h:x∈collar Λ l t a).1 j)
  have h₂ := fun j:Axis=> ((h:x∈collar Λ l t a).2 j)
  have hh : y∈collar Λ l t b:=by
     constructor
     · intro i; change collarLower Λ l t b i≤ x i-V i; rw [lower_gauge]; have hi:=h₁ i; rw [lower_gauge,he] at hi; linarith only [hi]
     intro i; change x i-V i≤ collarUpper Λ l t b i; rw [upper_gauge]; have hh :=h₂ i; rw [upper_gauge, he] at hh; linarith
  exact ⟨y, collar_inside u (Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨v,hh⟩⟩), by ext i; change x i- V i + V i=_; ring⟩

section rolling
variable (Q:Packet (timeMesh Λ)) (f:Tapestry.Altitude.Cloud (Dome (tent Y H))) (t:ℕ)
local notation "Qk"=> t-Q.size
noncomputable def district (Λ:Preparation) (Q:Packet (timeMesh Λ)) (U:Set RSpace) : Set RSpace:=(fun x:RSpace×RSpace=> x.1+x.2) '' (U ×ˢ (Q.region '' (UBox Axis)))
lemma districtCompact (U:Set RSpace) (p:IsCompact U): IsCompact (district Λ Q U):= (p.prod (isCompact_Icc.image (Packet.sweeps_cont Q))).image (continuous_fst.add continuous_snd)
noncomputable def navigateC (Λ:Preparation)(Q:Packet (timeMesh Λ))(t:ℕ) (x:Axis→Fin ((timeMesh Λ).L^(t-Q.size))) : Cover :=fun i=> tags t (Q.near (t-Q.size) x i)
local notation "up₀" x:max => navigateC Λ Q t x
structure PricedPacket (Λ:Preparation) (Q:Packet (timeMesh Λ)) (t:ℕ): Prop where
  size : Q.size ≤ t
  base : ∀ i:Axis,Precise t (Q.base i)
lemma readyPacket : ∀ᶠ t in atTop,PricedPacket Λ Q t := Q.eventually_grids.mono (fun _ ⟨a,b⟩=> ⟨a,b⟩)
lemma exactPacket (h: PricedPacket Λ Q t)(x: Axis→Fin ((timeMesh Λ).L^(t-Q.size)))(i:Axis):
    notch (timeMesh Λ) t (navigateC Λ Q t x i)= Q.near (t-Q.size) x i := by
  apply tags_on
  have hv:Q.size+(t-Q.size)=t:=Nat.add_sub_of_le h.size
  have he:=(Q.lines_near (t-Q.size) x i (by rw [hv]; exact h.base i)); rwa [hv] at he
-- literal polynomials purchased; not raw term of deck at contacts larger offsets. no representation changes per tile.
noncomputable def packetMark : Marks (tent Y H) false := ((Fintype.card (Zg (t-Q.size)):ℂ)⁻¹) • ∑ i:(Zg (t-Q.size)), Q.score (t-Q.size) i • μ t (up₀ i) f
noncomputable def packetPoly : Tapestry.Altitude.Cloud (Dome (tent Y H)) := pinhole (Dome (tent Y H)) t (packMark _ (packetMark Y H D Q f t))
lemma packet_sample : packetPoly Y H D Q f t = ((Fintype.card (Zg (t-Q.size)):ℂ)⁻¹) • ∑ i:(Zg (t-Q.size)), Q.score (t-Q.size) i • π t (navigateC Λ Q t i) f:=by
 unfold packetPoly packetMark signOver
 simp_rw [map_smul,map_sum,map_smul]
variable {X:Set RSpace}
lemma native_region (a:f∈ poet Y H t X) : ∃ S:Finset Cover, InTest K true S false ((P₀ t) f).val ∧ CovCover K ((P₀ t) f).val ∧ SupportedPhysically Λ l t S X:=by
 have p : f∈ circum Λ l K true X ( (Set.Iic t)∩ Set.Iic t):=by rw [inter_self]; exact a
 have ht:= gateIssued Λ (tent Y H) l true (handstamp X) (Set.Iic t) t p
 have hv: ((P₀ t) f)∈keep Λ l t K true (handstamp X):=crownShelter Λ l t d★ (auxiliaryPad K) (fun i x=>rfl) (handstamp X) (fun i g h=>roofline Λ l i true (handstamp X) D h) ((well_spec ..).1 p).1
 obtain ⟨S,u,v⟩:=hv
 exact ⟨S,(Tapestry.locates ..).1 u, (enclave_spec K).1 (D.finishCoherent Y H t f p ht),v⟩
lemma parcel_clears (h:PricedPacket Λ Q t) (a:f∈ poet Y H t X) : packetPoly Y H D Q f t ∈ poet Y H t (district Λ Q X):=by
 obtain ⟨S,v,u,g⟩:= native_region Y H D f t a
 rw [packet_sample]; let W(i:Zg (t-Q.size)):= Q.score (t-Q.size) i • π t (up₀ i) f
 apply Subalgebra.smul_mem _ ?_ _ -- order
 apply Subalgebra.sum_mem
 intro i _
 apply Subalgebra.smul_mem _ ?_ _
 let Z:= up₀ i; let f₀:Marks K true:= ⟨((P₀ t) f).val, (aux_test v),fun _=> u⟩
 let f':= relocateWorld Y H true Z f₀; let B':=streetBox K Z S
 have he: migrate Y H D t Z f = bosonLabel K f':=Subtype.ext (by unfold migrate; change (relocateWorld Y H false Z _).val=(relocateWorld Y H true Z f₀).val; rw [world_val,world_val]; rfl)
 have hp : footprint Λ l t B' ⊆ district Λ Q X:=by
    intro x h'; obtain ⟨y,p,rfl⟩:= signed_shift Y H t Z X S g h'
    let V:=smallCorner ((timeMesh Λ).L^(t-Q.size)) i; refine ⟨(y,Q.region V),⟨p,V,Packet.lives (t-Q.size) i,rfl⟩,?_⟩
    ext j; change y j+Q.region V j= y j+((N t ((up₀ i) j)):ℝ); rw [show notch M t _=_ from exactPacket Q t h i j]; exact congrArg (y j+·) (Q.points_near (t-Q.size) i j).symm -- tune
 have hx : InTest K true B' false f'.val:= by unfold f'; rw [world_val]; exact cadTestFull S Z _ _ _ v
 apply circum_widens Y H hp (by rfl: Set.Iic t ⊆ Set.Iic t)
 have ht: resolutionProbe Y H f'∈ keep Λ l t K true (handstamp (footprint Λ l t B')) := ⟨B', (Tapestry.locates ..).mpr hx,has_footprint Λ l t B'⟩
 change signOver Y H D t Z f ∈ _
 unfold signOver; rw [he]; exact oneSlotWell Λ K l true _ _ t (by exact Set.mem_Iic.mpr (le_refl _)) ht ((enclave_spec ..).mpr ((marksSpec true f').2 rfl))
end rolling
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.parcel_clears
