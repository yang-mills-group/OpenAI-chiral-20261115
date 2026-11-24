import YM.SU5.Reconstruct.Domain
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
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
/-!
# The actual characters are determined by the physical polynomials

Use selected comparisons on all even calls but in the hypothesis no nonsinglet or
loose probes. `cap` was defined in the FULL display algebra. -/
local notation "A" => displayAlgebra Y H V Q Qt 0 false (C 0)
local notation "Ω" c:max s:max=> response Y H V s Q Qt 0 false (C 0) c

-- Loose one-stage call can be replaced already at next level, with a budget
-- for a bounded physical region, by a singlet POL entry giving the same receipt (every character).
lemma scrutinize (s:ℕ) (x:Marks (tent Y H) false) :
    ∃ R:ℝ,0 < R ∧ ∃ g: PolAt Y H (s+1) (Tapestry.cabin R), ∀ c: (displayAlgebra Y H V Q Qt 0 false (C 0)) →⋆ₐ[ℂ] ℂ,
      (Ω c s) x= sch Y H D G C c g.val := by
  obtain ⟨S,t⟩:= (marksSpec false x).1.paid
  obtain ⟨y,h,L⟩:= cap_in_common Y H V s Q Qt x t
  obtain ⟨b,v,a⟩:= canBound Λ l (s+1) (wingspan Λ l S)
  obtain ⟨g,q⟩:= (obs_in ..).1 h
  let f:χ:=⟨y.val,aux_test g⟩
  have he:pinhole (Dome (tent Y H)) (s+1) f∈PolAt Y H (s+1) (Tapestry.cabin b):=
    oneSlotWell Λ K l true _ (Set.univ ∩ Set.Iic (s+1)) (s+1) (by simp)
      (show f∈ keep Λ l (s+1) K true (handstamp (Tapestry.cabin b)) from ⟨_,g,a⟩) ((enclave_spec K).mpr q)
  refine ⟨b,v,⟨_,he⟩,fun c=>?_⟩
  change _= sch _ _ D _ _ _ (pinhole _ _ f)
  rw [sch_sample]
  exact congrArg c (L 0 _).symm

section algebra
open CStarAlgebra -- map_continuous
lemma polynomial_ext (u: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
    (h:∀ (s:ℕ)(R:ℝ),0 < R → ∀ x:PolAt Y H s (Tapestry.cabin R), sch Y H D G C c x.val = sch Y H D G C u x.val) : c=u:=by
  let F:= A
  have he(s:ℕ)(x:Marks K false): (Ω c s) x=(Ω u s) x:= by
     obtain ⟨R,t,f,h₀⟩:= scrutinize Y H D G C s x
     rw [h₀,h₀,h (s+1) R t f]
  let W:= StarAlgHom.equalizer c u; let B':=W.map (A).subtype
  have hp: A ≤ B' := by
    let Xt:=(groundRoom Y H V G.history 0 false (C 0)).Op
    have ht: IsClosed (W:Set (A)):= isClosed_eq (map_continuous c) (map_continuous u)
    have hv: IsClosed (B':Set Xt):= (displayClosed Y H V Q Qt 0 false (C 0)).isClosedEmbedding_subtypeVal.isClosedMap _ ht
    refine StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le ?_) hv
    rintro _ ⟨t,rfl⟩
    rcases t with ⟨s,x⟩ -- x : Marks? Beacon defeq?
    refine ⟨located Y H V s Q Qt 0 false (C 0) x, ?_,rfl⟩
    exact he s x
  ext1 x; obtain ⟨y,v,t⟩:= hp x.property
  have z:y=x:= Subtype.ext t; exact (z ▸ (show c y=u y from v))
end algebra
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
