import YM.SU5.Selected.Atelier
import YM.SU5.Selected.Parish
/-!
# A determining algebra in the selected resolution hierarchy

Atelier shows what readers to use. Verify property of determination of the
Hilbert system and the actual physical multi-resolution observable algebra.
Not discarding joint output-dependent covariant operators. All generated
from supported local polynomials in gauge and matter at all levels. Show the
actual interaction test is read at fixed physical footprint (from checkpoint)
in the algebra and that its continuation of the READ into upper stages still
applies in the same ground sector. At the origin-hinged plane, full identity of
selected positive-time Euclidean realizations across all heights. ONLY at reception
heights admitted; if already have f originally at k≤n can lift same vector in
selected reconstruction. Does not assert support may be made arbitrarily small
for density, but includes `Suite` simultaneous interaction result with readings
in this algebra. Buffered regions using our unit--level zero *matter* spacing--
(s Euclidean support statements in U). -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
open Set Theory MeshClock Tapestry Tapestry.Altitude Tapestry.Exhibition
variable {L:Rack Λ l}{B:Clay Λ l}(D:Exhibition Y H i k I E L B)
local notation "χ"=>Dome (tent Y H)
local notation "Cₚ"=>Cloud (Dome (tent Y H))
local notation "F₀"=>vistaDressing Y H D
local notation "P₀" n:max=>vistaFinish Y H n D
local notation "D₀" n:max=> Exhibition.liftD Y H n D
variable (d:Axis)(T:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "R"=>catalog Y H V G d false (T d)

variable (x:Resident (catalog Y H V G d false (T d)))
local notation "Mx"=>evaluate Y H V G d T x
local notation "Θ"=> onDrawing Y H V G D d T x
local notation "γ" s:max=>Acting.voice Y H V G j false (T j) (engaged Y H V G j false (T j) d (T d) x) s
local notation "A₀"=> (engaged Y H V G j false (T j) d (T d) x).space

-- for converting all Tapestry locations
noncomputable def handstamp (U:Set (Axis→ℝ)) : Set RSpace:= (fun z => fun i:Axis=> z i/2) ⁻¹' U
noncomputable def circum (Λ:Preparation)(l:ℕ)(Z:Calibration)(wide:Bool)(U:Set (Axis→ℝ))(a:Set ℕ) : Subalgebra ℂ (Cloud (Dome Z)):= well Λ Z l wide (handstamp U) a
local notation "ε"=>circum Λ l K
local notation "F₁" i:max=> Tower.Field Y H i j 0 false
lemma circum_widens {wide:Bool}{s t U W}(h:U⊆W)(p:s⊆t): ε wide U s≤ ε wide W t:=wellGrows Λ (tent Y H) l wide (handstamp U) (handstamp W) s t p (preimage_mono h)
lemma reader_ready {s:ℕ}{U:Set (Axis→ℝ)}{t:Set ℕ} {f:Cₚ}{wide:Bool} (p:f∈ ε wide U (t∩ Set.Iic s)) :
    Θ f=Mx s ((P₀ s) f).val ∧ ∃ S:Finset Cover, ((P₀ s) f).val∈ observ (tent Y H) S true ∧ SupportedPhysically Λ l s S U := by
  have h:= gateIssued Λ (tent Y H) l wide (handstamp U) t s p
  refine ⟨drawAt Y H V G D d T x h,?_⟩
  have a: ((P₀ s) f)∈keep Λ l s K true (handstamp U):=crownShelter Λ l s F₀ (auxiliaryPad K) (fun i x=>rfl) (handstamp U) (fun i g h=>roofline Λ l i true (handstamp U) D h) ((well_spec Λ K l true _ _).1 (wellWider Λ K l wide (handstamp U) (t∩ Set.Iic s) p)).1
  obtain ⟨S,u,v⟩:=a
  exact ⟨S, (obs_in ..).2 ⟨(Tapestry.locates ..).1 u, (enclave_spec K).1 (D.finishCoherent Y H s f p h)⟩,v⟩

noncomputable def atZero (Λ: Preparation) : Sunlight Λ:= glare Λ 0 0
local notation "O₀"=>atZero Λ
local notation "H₀"=>flank j 0
local notation "Rg"=> Sunlight.sanctum Λ l j O₀ K
local notation "Rz" s:max=> Sunlight.cloister Λ l j O₀ K s
local notation "θ"=>(O₀).oppose Λ j K
@[simp] lemma atZ (Λ:Preparation)(s:ℕ):(atZero Λ).marks s=0:=by simp [atZero,glare,Heat.gaugeShift]
@[simp] lemma hinge_zero (Λ:Preparation):(atZero Λ).hinge Λ=0:=by rw [Sunlight.hinge,atZ]; simp [markZ]
@[simp] lemma arena_all (Λ:Preparation): (atZero Λ).arena Λ=Set.univ:= by ext x; change (0 ≤ x) ↔ True; exact iff_true_intro x.zero_le
lemma stamp_flank : handstamp (flank j 0)= flank j 0:= by ext u; change 0≤ u j/2 ↔ 0 ≤ u j; constructor; all_goals intro p; linarith
lemma stamped {f:Cₚ}{a:Set ℕ}{U:Set RSpace}{wide:Bool}{s:ℕ}(v:f∈ ε wide U (a∩ Set.Iic s))(h:U⊆ H₀): f∈Rz s:=by
  unfold Sunlight.cloister; simp only [hinge_zero]
  have hx := ((well_spec ..).1 (wellWider Λ K l wide (handstamp U) (a∩ Set.Iic s) v)).1
  have Hx:(handstamp U) ⊆ H₀:=by rw [←stamp_flank]; exact preimage_mono h -- private statement scope
  exact admits Λ l K true _ _ _ _ (by rw [arena_all]; exact Set.inter_subset_inter_left _ (subset_univ _)) Hx hx

variable {s:ℕ}{f g:Altitude.Cloud (Dome (tent Y H))}
include V in
lemma practiced (p:f∈Rz s): ((P₀ s) f).val∈ purpose K (meshface (Λ:=Λ) 0 s) j false:=by
  have he:= D.glass Y H j O₀; obtain ⟨S,h,t⟩:= (show (P₀ s) f∈keep Λ l s K true (flank j ((O₀).hinge Λ)) from crownShelter Λ l s F₀ _ he.lantern _ he.onward p)
  have ht:Tower.region j ((O₀).marks s) (K).ℓ S := ((O₀).rents Λ l j s (by apply Nat.zero_le)).1 t
  rw [atZ] at ht; rw [area0]; exact (purpose_ok ..).2 ⟨⟨S,h,ht⟩,by simp⟩

noncomputable def declaim (p:f∈Sunlight.cloister Λ l j (atZero Λ) (tent Y H) s) : (engaged Y H V G j false (T j) d (T d) x).space :=
  (γ s) (⟨((P₀ s) f).val, practiced Y H V j D p⟩ : F₁ s)
local notation "Ω₁"=>declaim Y H V G j D d T x
lemma cabin_form {v:ℕ} (p:f∈Rz v)(q:g∈ Rz v):
   inner ℂ (Ω₁ p) (Ω₁ q)= Θ (θ f*g):=by
  rw [drawAt Y H V G D d T x ((shorter χ v).mul_mem ((O₀).respectsCut Λ l j K p) (jettyBan Λ l K true _ _ v q)),vistaFinish,reflectionHat Λ l j O₀ v (F₀) _ (D.glass Y H j O₀) v.zero_le p q,atZ]
  exact (voice_at Y H V G j d T x (⟨_,practiced Y H V j D p⟩ : F₁ v) (⟨_,practiced Y H V j D q⟩ : F₁ v)).symm
lemma spacing_stamp {z:ℕ} (p:s ≤ z)(h:f∈Rz s):f∈Rz z:= by
  apply admits Λ l K true _ _ ((O₀).arena Λ ∩ Set.Iic s) ((O₀).arena Λ∩ Set.Iic z) (fun i v=>⟨v.1,le_trans v.2 p⟩) Set.Subset.rfl h
lemma declaim_step (t:f∈Rz s) : let v : f ∈ Rz (s+1):=spacing_stamp Y H j (by omega) t; Ω₁ v=Ω₁ t:=by
 intro p; unfold declaim; rw [← Acting.climbs Y H V G j false (T j) (engaged Y H V G j false (T j) d (T d) x) (s:=s) (t:=s+1) (p:=by omega)]; apply congrArg _; apply Subtype.ext
 have he: (P₀ (s+1)) f = (D₀ s) ((P₀ s) f):=Decking.joins (F₀) s f (auxiliaryPad K) (jettyBan Λ l K true _ _ s t) -- order
 change ((P₀ (s+1)) f).val=stream Y H G.refine s _ _; rw [he,lifts_here Y H V, show s+1-s=1 by omega]; rfl
lemma declaim_all {u:ℕ}(p:s≤u)(q:f∈Rz s)(h:f∈Rz u): Ω₁ h= Ω₁ q:=by
 induction u,p using Nat.le_induction with | base=>rfl | succ u p ih=> exact (declaim_step Y H V G j D d T x (spacing_stamp Y H j p q)).trans (ih (spacing_stamp Y H j p q))

-- A full dense family in these linear OS readings (from local poly algebra)
noncomputable def showcase : Set (engaged Y H V G j false (T j) d (T d) x).space:={v|∃ (s:ℕ)(u:ℝ)(f:Cₚ),0<u∧ f∈ε true ((flank j 0) ∩ Tapestry.cabin u) (Set.Iic s) ∧ ∃ p:f∈Rz s,v=Ω₁ p}
include D in
lemma showcased : Dense (showcase Y H V G j D d T x):=by
  apply (Acting.drawnDensity Y H V G j (T j) _).mono
  intro u p; obtain ⟨s,w,x',a,b,t,rfl⟩:= (p: ∃_,_)
  obtain ⟨S,e,g⟩:=x'.property
  obtain ⟨q,hq,v⟩:=canBound Λ l s S
  let f:χ:=⟨x'.val.val,(aux_test e)⟩
  let h : Ledge Λ l S j 0:=fun x k=>(g x k).1
  have he: f∈keep Λ l s K true (flank j 0):= by
     apply (keeps ..).2; refine ⟨S,e,?_⟩; rw [show (0:ℝ)=markZ Λ s 0 by simp [markZ]]; exact brought Λ l s j 0 S h
  have pU: f∈keep Λ l s K true (handstamp ((flank j 0) ∩ Tapestry.cabin q)):=by
    unfold handstamp; rw [Set.preimage_inter]; change f∈ keep Λ l s K true (handstamp _∩ handstamp _); rw [stamp_flank]
    refine (keeps ..).2 ⟨S,e,fun i hv y u=>⟨?_, v i hv u⟩⟩; exact (show markZ Λ s 0 ≤ y j from (brought Λ l s j 0 S h i hv u)) |> fun h=>by simpa [flank,markZ] using h
  let x₀:= pinhole χ s f
  have p : x₀∈ ε true ((flank j 0)∩Tapestry.cabin q) (Set.Iic s):= oneSlotWell Λ K l true _ (Set.Iic s) s (Set.mem_Iic.mpr (le_refl s)) pU ((enclave_spec K).mpr b)
  have h₀:x₀∈ Rz s:= by unfold x₀ Sunlight.cloister; simp only [hinge_zero,arena_all]; exact pokes (Set.univ∩ Set.Iic s) _ (show s∈Set.univ ∩ Set.Iic s from ⟨Set.mem_univ _,Set.mem_Iic.mpr (le_refl s)⟩) he
  refine ⟨s,q,x₀,hq,p,h₀,?_⟩; symm; unfold declaim; apply congrArg _; apply Subtype.ext; change ((P₀ s) x₀).val=x'.val.val; unfold x₀ vistaFinish; rw [Decking.outcrop]; rfl
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.declaim_all
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.showcased
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.reader_ready
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.cabin_form
