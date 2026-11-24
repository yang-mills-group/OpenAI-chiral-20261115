import YM.SU5.Reconstruct.Domain
/-!
Full locally bounded and open-halfspace generator density. The maps to
positive test vectors use one polynomial charge (not separate cylindrical
completion axioms, or agreement almost everywhere). Use `saunters` and
projection explicitly to separate the cases of unprojected GNS and what can
already be moved continuously in space.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)
variable (C : ∀ j:Axis, Tower.Arena Y H G.history.circuit j 0 false)
local notation "𝔇" i:max => displayAlgebra Y H V Q Qt i false (C i)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
variable (j:Axis)
local notation "U₀" => flank j 0
local notation "u₀" => PhaseChoice.atZero Λ
local notation "𝜔" => (PhaseChoice.atZero Λ).oppose Λ j (tent Y H)
local notation "S★" => sch Y H D G C c
local notation "qA" i:max => inAxis Y H D G C c i
local notation "Rr" => upperRoom j
local notation "w₀" => G.history.circuit
local notation "H₀" => entire Y H D G C c j
local notation "HC" => continuousH Y H D G C c j
local notation "β" s:max => bud Y H V s Q Qt j false (C j) (qA j)
local notation "Π₀" s:max => land Y H V s Q Qt j false (C j) (qA j)
local notation "Ω" => doorstep Y H V Q Qt j false (C j) (qA j)
local notation "Ωc" => vocation Y H V Q Qt j false (C j) (qA j)
local notation "F₊" n:max => Tower.Field Y H n j 0 true
local notation "HF" n:max=> PolAt Y H n (upperRoom j)

-- arbitrary shape in the strictly-positive physical halfspace.
lemma clear_half {S:Finset Cover}{n:ℕ}
    (p:Tower.region j 0 ((K).ℓ+1) S) : SupportedPhysically Λ l n S (upperRoom j) := by
  intro x t y hy
  have he: (reserve Λ l:ℝ)+1 ≤ (x j:ℝ):= by exact_mod_cast (show (reserve Λ l:ℤ)+1≤ (x j) by have h:=p x t; change 0+↑(reserve Λ l+1)≤ x j at h; omega)
  have ht:= (abs_le.mp (hy j)).1
  have hp:0 < Tapestry.precisionAt Λ n:= positiveScale Λ n
  change 0 < y j / 2
  exact div_pos (pos_of_mul_pos_left (a:=y j) (b:=Tapestry.precisionAt Λ n) (by linarith only [ht,he]) hp.le) (by norm_num)

noncomputable def intoHalf (s:ℕ) : (PolAt Y H s (upperRoom j)) →ₗ[ℂ] PolAt Y H s U₀ :=
  Submodule.inclusion (show (PolAt Y H s (upperRoom j)).toSubmodule ≤ (PolAt Y H s U₀).toSubmodule from isotone Y H (upper_in j)) -- type mismatch? 

def openAt (s:ℕ) : PolAt Y H s (upperRoom j) →ₗ[ℂ] entire Y H D G C c j :=
    (locatePoly Y H D G C c j s).comp (intoHalf Y H j s)

noncomputable def viewProject : entire Y H D G C c j →L[ℂ] continuousH Y H D G C c j :=
  (saunters Y H V Q Qt j false (C j) (qA j)).orthogonalProjectionOnto
local notation "π" => viewProject Y H D G C c j

lemma open_realizes (s:ℕ) (x:F₊ s) :
    ∃ y:PolAt Y H (s+1) (upperRoom j),
       openAt Y H D G C c j (s+1) y=bud Y H V s Q Qt j false (C j) (qA j) (admit Y H s j x):= by
  let z:=Raise Y H G.history.circuit j 0 true s (s+1) (by omega) x
  obtain ⟨A,p,v⟩:=(show ∃ T : Finset Cover,InTest K true T false x.val∧ Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ T from ((purpose_ok ..).1 x.property).1)
  rw [area0] at v
  have pS:=Tower.strict_one Y H j (c:=0) (n:=0) (by simpa only [Nat.add_zero] using v)
  rw [mul_zero,Nat.add_zero] at pS
  have hZ : InTest K true (wingspan Λ l A) false z.val:=by change InTest _ _ _ _ (stream _ _ _ _ _ _); rw [show s+1-s=1 by omega]; exact (G.history.circuit.supports s p).1
  let a:χ:= ⟨z.val,aux_test hZ⟩
  have h:a∈ keep Λ l (s+1) K true (handstamp (upperRoom j)):=by apply (keeps ..).2; exact ⟨wingspan Λ l A,hZ,clear_half Y H j pS⟩
  have wa:a∈enclave K:= (enclave_spec ..).2 (((purpose_ok ..).1 z.property).2 rfl)
  let u: O:= pinhole χ (s+1) a
  have q:u∈ (HF (s+1)):=oneSlotWell Λ K l true (handstamp Rr) (Set.univ ∩ Set.Iic (s+1)) (s+1) (by simp) h wa
  let y: PolAt Y H (s+1) (upperRoom j) := ⟨u,q⟩
  let yg:= intoHalf Y H j (s+1) y
  refine ⟨y,?_⟩
  have h0:preparePoly Y H D j (s+1) yg = z:= by
    apply Subtype.ext; change ((P₀ (s+1)) u).val=z.val; unfold u vistaFinish; rw [Decking.outcrop]; rfl
  change (β (s+1)) (admit Y H _ _ (preparePoly Y H D j _ yg))=_
  rw [h0]; exact flourishes Y H V s Q Qt j false (C j) (qA j) (s+1) (by omega) (admit Y H s j x)

lemma realizes_compass (s:ℕ) (x:F₊ s) :
    ∃ y:PolAt Y H (s+1) (upperRoom j),
      viewProject Y H D G C c j (openAt Y H D G C c j (s+1) y)= land Y H V s Q Qt j false (C j) (qA j) (admit Y H s j x):=by
  obtain ⟨y,h⟩:= open_realizes Y H D G C c j s x
  rw [←show π ((β s) (admit Y H s j x))= land _ _ _ _ _ _ _ _ _ _ _ from rfl]
  exact ⟨y,congrArg (fun x=>π x) h⟩

lemma genuinely_dense : Dense (⋃ s:ℕ, Set.range (fun y:PolAt Y H s (upperRoom j)=>openAt Y H D G C c j s y)):=by
  apply (reserved_actor Y H V Q Qt j (C j) (qA j)).mono
  intro x v; obtain ⟨k,e⟩:= Set.mem_iUnion.mp v; obtain ⟨f,h⟩:=e
  subst x
  exact Set.mem_iUnion.mpr ⟨k+1,open_realizes Y H D G C c j k f⟩

lemma compass_dense : Dense (⋃ s:ℕ, Set.range (fun y:PolAt Y H s (upperRoom j)=>viewProject Y H D G C c j (openAt Y H D G C c j s y))) :=by
  refine Dense.mono ?_ (shore_dense Y H V Q Qt j (C j) (qA j))
  intro x v; obtain ⟨k,e⟩:= Set.mem_iUnion.mp v; obtain ⟨f,h⟩:=e
  subst x
  exact Set.mem_iUnion.mpr ⟨k+1, realizes_compass Y H D G C c j k f⟩

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
