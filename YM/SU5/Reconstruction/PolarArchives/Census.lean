import YM.SU5.Reconstruction.Oblique.Announcer
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C j χ
local notation "au"=>move K
local notation "L" i:max=>located Y H V i G.history G.clipped j false (C j)
local notation "H₀"=> Ark.Ht Y H G.history.circuit j 0 false (C j)
local notation "A"=>Aurora Y H V G.history j false (C j)
local notation "P₀"=>displayAlgebra Y H V G.history G.clipped j false (C j)
local notation "Bx"=>seat0 Y H V G.history j false (C j)
local notation "px"=> (A).orthogonalProjectionOnto
variable {q:Bool}{U:Set RSpace}

/-- The reception's phase alarm on ALL permit-paid marks from CP1 era. -/
noncomputable def album: Domain Y H G false Set.univ→ₗ[ℂ] P₀:=
 assemble Y H G Set.univ false (fun s=>((L s).comp (asLoose (tent Y H)).toLinearMap).comp ((insideAt Λ l (tent Y H) false Set.univ s).toSubmodule.subtype))
  (fun s t h x=> Subtype.ext (cap_level (F:=asLoose K x.val) Y H V s G.history G.clipped j false (C j) t h))
local notation "C₀"=>album Y H V G C j
lemma atStamp(s:ℕ)(f:Dome (tent Y H))(h:ticket Y H G s f∈ Domain Y H G false univ): C₀ ⟨ticket Y H G s f,h⟩=(L s) (asLoose K f) :=
 by
 have t : f∈ insideAt Λ l K false Set.univ s:=by rw [insideAt_univ_loose]; exact Algebra.mem_top
 unfold album; exact assemble_enclose Y H G _ _ _ _ s ⟨f,t⟩

lemma at_origin {g:Sky (tent Y H)}(h:g∈Domain Y H G false (flank j 0))(t:g∈Domain Y H G false univ):
    px (LightBudget.prepaid Y H V G j (C j) ⟨g,h⟩)=(album Y H V G C j ⟨g,t⟩).val Bx:= by
 obtain ⟨s,b,z,rfl⟩:=h
 rw [atStamp,show (⟨ticket Y H G s b,_⟩ : D false (flank j 0)) = enclose Y H G (flank j 0) false s ⟨b,z⟩ from rfl,LightBudget.prepaid_enclose]; exact (cap_plant Y H V s G.history G.clipped j false (C j) (asField Y H j false s ⟨b,z⟩)).symm -- need prepaid_enclose
lemma at_op(s:ℕ)(t:ℕ)(x:Dome (tent Y H))(h:s≤t) : (L t) (asLoose K (spreadTo Y H G s t x))= (L s) (asLoose K x):= Subtype.ext (cap_level (F:=asLoose K x) Y H V s G.history G.clipped j false (C j) t h)

private lemma epoch_won (s:ℕ)(v:Cover)(p:Marks (tent Y H) false): (L s) (relocateWorld Y H false v p)= (L s) p := by
 unfold relocateWorld; generalize ordinate=A'; induction A' with
 | nil=>rfl
 | cons i a ih => rw [List.foldr_cons,show (L s) (moveMark Y H i false (v i) _)=(L s) (List.foldr (fun a t=> moveMark Y H a false (v a) t) p a) from Subtype.ext (PhaseChoice.cap_lattice Y H V G j false (C j) i _ _ s (v i) rfl), ih]
lemma moving_chime (p:placement Λ){f:Sky (tent Y H)} (t:f∈Domain Y H G false univ)(u:move (tent Y H) p f ∈ Domain Y H G false univ):
    C₀ ⟨move K p f,u⟩=C₀ ⟨f,t⟩:=by
 obtain ⟨s,⟨a,vz⟩,x,t,rfl⟩ := ((stamps_eventually p).and ((domain_eventually Y H G).1 t)).exists
 rw [show (⟨move K p _,u⟩:µ)= ⟨ticket Y H G s (reposition K a x),ticket_loose ..⟩ from Subtype.ext (move_at Y H V G p s x a vz), atStamp,atStamp]
 rw [show asLoose K (reposition K a x)= relocateWorld Y H false a (asLoose K x) from Subtype.ext (world_val Y H false a (asLoose K x)).symm, epoch_won]

lemma mirror_tone(i':Axis){f:Sky (tent Y H)}(t:f∈Domain Y H G false univ)(u:flipMark i' K f ∈ Domain Y H G false univ):
   C₀ ⟨flipMark i' K f,u⟩= star (C₀ ⟨f,t⟩):=by
 obtain ⟨s,x,w,rfl⟩:= t -- dep t binder in goal elim
 rw [show (⟨flipMark i' K _,u⟩:µ) = ⟨ticket Y H G s (aureole K i' 0 x),ticket_loose ..⟩ from Subtype.ext (flipMark_ticket Y H G i' s x), atStamp, atStamp]
 exact Subtype.ext (real_structure Y H V G.history G.clipped j false (C j) i' (C i') (s,asLoose K x))
lemma tier (x:Sky (tent Y H))(u:x∈ Domain Y H G false univ): χ (album Y H V G C j ⟨x,u⟩)=Ω x:=by
 rw [WindRose.funds_stamp Y H V G C j χ u]; obtain ⟨s,x,h,rfl⟩:=u; rw [os_ticket_val, atStamp]; rfl
lemma staff (P:Ramp){x:Sky (tent Y H)} (t:x∈Domain Y H G false univ)(u:gust P (tent Y H) x∈ Domain Y H G false univ):
    courseValue Y H V G ⟨gust P K x,u⟩=star (courseValue Y H V G ⟨x,t⟩):=by
 obtain ⟨s,b,h,rfl⟩:=t
 rw [course_ticket_val,show (⟨gust P K _,u⟩:µ)= ⟨ticket Y H G s (windTilt P K b), ticket_loose ..⟩ from Subtype.ext (gust_ticket Y H V G P s b),course_ticket_val]
 exact step_Price Y H P s V b.property
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
