import YM.SU5.Relativistic.Joint
import YM.SU5.Relativistic.Assay

/-!
# Same selected law with physical continuum-feet probes

Progress toward a full relativistic proof: these are genuine **Euclidean** tests.
The Gauge×matter obstruction at physical separation is from the second Glass
set (masked, so includes sensitivity to nonflat input gauges). Factorization
comparison theorem below applies directly to LINEAR predictions of this same
physical observable by reading products as independent, with precise means of
the prescribed charged marginals, not a Wick or no-clustering statement.
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 27000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Reliance ShortWave
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

section pricing
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (Q:Exhibition Y H i k I E L B)
local notation "V"=>Q.univ_
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (d j:Axis)(c:∀ j,Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H Q.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H V G.history G.clipped d false (c d) χ j (c j)
local notation "χ₁"=> SameCharacter.resident Y H V G d false (c d) χ
local notation "Φ" => onDrawing Y H V G Q d c χ₁
local notation "MX"=> evaluate Y H V G d c χ₁
local notation "Ω" => Dome (tent Y H)
variable (s : ℕ) {S: Finset Cover} {z:SU.Slot} {u v:ℕ} {o:Cover} {δ w:ℝ} (p q:Cover)
variable (f:Marks (tent Y H) true)
local notation "F₀"=> mirrorInMarks Y H j true (relocateWorld Y H true p f)
local notation "F₁"=> relocateWorld Y H true q f
local notation "μω"=> remotePair j (tent Y H) p q
local notation "F" s:max x:max=> pinhole Ω s (PhaseChoice.resolutionProbe Y H x)
local notation "Rxy" => (F s (F₀))*(F s (F₁))
local notation "Dx"=> Lode K (Window.family z) (booty o u v) S

structure Coupled : Prop where
  visibleTest : f.val∈ Filigree K (Window.family z) (booty o u v) S
  higher : Exceeds Y H V s G.history G.clipped j (c j) (χ̂ j) δ f z S o v u p q
  certified : FocusMark Y H Q G d j c χ s f p q δ w u v o S z
  absent (a b:Family (tent Y H))(h:a∈ Lode K (Window.family z) (booty o u v) S)(p₀:b∈ Lode K (Window.family z) (booty o u v) S): evaluate Y H V G d c χ₁ s (μω a b) = 0
  -- Ext prediction on Cloud ok. Needn't assign any values off supported subspaces for this question. Read predicts on **same** test.
  faces (t : Altitude.Cloud (Dome (tent Y H)) →ₗ[ℂ] ℂ)
    (cost : ∀ a∈ Lode K (Window.family z) (booty o u v) S,∀ b∈ Lode K (Window.family z) (booty o u v) S,
     ∀ x y : PairsC→ℂ,Coeff false S x → Coeff false S y→∀ r:Dome (tent Y H),
      r.val=μω (scalar K x*a) (scalar K y*b) → t (pinhole Ω s r)= evaluate Y H Q.univ_ G d c χ₁ s (μω (scalar K x) (scalar K y))* evaluate Y H Q.univ_ G d c χ₁ s (μω a b)):
    t ((F s (F₀))*(F s (F₁)))=0 ∧ 1/32 ≤ ‖t ((F s (F₀))*(F s (F₁))) - Φ ((F s (F₀))*(F s (F₁)))‖

lemma Coupled.jointly (b:f.val∈ Filigree K (Window.family z) (booty o u v) S)
    (r : Exceeds Y H V s G.history G.clipped j (c j) (χ̂ j) δ f z S o v u p q)
    (d₀:0<w)(g:probesGauge w f.val)(pX:Injective (booty o u v)) : Coupled Y H Q G d j c χ s (δ:=δ) (S:=S) (u:=u) (v:=v) (o:=o) (w:=w) (z:=z) p q f:=by
  let P:=reflectedBox j 0 (streetBox K p S); let U:= streetBox K q S
  have A:= enlivens Y H Q G d j c χ s f p q δ w b r.shelf d₀ g
  have he(a b)(p₀:a∈ Lode K (Window.family z) (booty o u v) S)(p₁:b∈ Lode K (Window.family z) (booty o u v) S) : MX s (μω a b)=0:=by
     rw [extended_pigment Y H Q G d j c χ s]
     exact Selected.remote_cold Y H V s G.history G.clipped j (c j) (χ̂ j) q P (detached_disjoint r.shelf.structured) _ (axial K j 0 (cadTestFull S p ordinate _ _ (Lode_test p₀|>.widen))) _ pX (Window.family z) b p₁
  refine ⟨b,r,A,he,?_⟩
  intro t e
  let h:= t.comp (pinhole Ω s).toLinearMap
  let x:= PhaseChoice.resolutionProbe Y H (show Marks K true from (F₀)*(F₁))
  have hx:x.val= μω f.val f.val:= A.basisUse
  have hv : Rxy = pinhole Ω s x := (map_mul (pinhole Ω s) (PhaseChoice.resolutionProbe Y H (F₀)) (PhaseChoice.resolutionProbe Y H F₁)).symm
  have hV : t (Rxy)=0:= by
    rw [hv]; exact mixedPredictor K j p q S (booty o u v) (Window.family z) (MX s) (fun f a g b=> he f g a b) h e f.val f.val b b x hx
  exact ⟨hV,by rw [hV,zero_sub,norm_neg]; exact A.prices⟩
end pricing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Coupled.jointly
