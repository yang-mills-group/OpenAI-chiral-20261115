import YM.SU5.Relativistic.Law
import YM.SU5.Relativistic.Sensitive
import YM.SU5.Relativistic.MultiSeparate
import YM.SU5.Relativistic.Box

/-! # One joint vacuum observable in this physical test system

This buys a mix across two regions in the explicit criterion of Glass (not saying
nonzero truncated correlation between regions-- the factorization being tested
is gauge times matter). The neutral test implicates those very (in envelope
even, not necessarily neutral) inputs for that charge assessment, not an
assumption about Minkowski fields. Estimate of resolution local interpretation
on precisely this Θ. Applies from `Election`, no comparison of choices of phases
or histories on different SU(5) calibrations.
-/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 26000
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

section structures
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (Q:Exhibition Y H i k I E L B)
local notation "V"=>Q.univ_
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (d j:Axis)(c:∀ j,Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H Q.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H Q.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "M" s:max F:max=> pigmentReading Y H Q.univ_ s G.history G.clipped j (c j) (χ̂ j) F
local notation "χ₁"=> SameCharacter.resident Y H V G d false (c d) χ
local notation "Φ" => onDrawing Y H V G Q d c χ₁
local notation "MX"=>evaluate Y H V G d c χ₁
local notation "φ" v:max=>response Y H V v G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω" => Dome (tent Y H)
variable (s : ℕ)
lemma selected_here (f : Marks K false) : (φ s) f= MX s f.val:=
  (across_response ..).trans ((evaluates Y H V G d c (χ₁) s f).trans (SameCharacter.sameReading ..)).symm
lemma costs_pinhole (f : Dome K) : Φ (pinhole (Dome K) s f)= MX s f.val:= plugged ..
lemma costs_basis (f : Marks K false)(b : Dome K)(p:b.val=f.val):
    Φ (pinhole (Dome K) s b)=(φ s) f:=by rw [costs_pinhole Y H Q G d c χ, p,selected_here Y H Q G d j c χ]

-- equality even off-test (both zero). onDrawing still uses `audition` on actual test.
lemma extended_pigment (x:Family K) : MX s x=M s x:= by
  by_cases h:TestFamily K true x
  · let f:Marks K false:=⟨x,h,nofun⟩
    change MX s f.val = M s ((x):Family K)
    rw [← selected_here Y H Q G d j c χ s f]
    exact (reads_color Y H V s G.history G.clipped j (c j) _ f).symm
  unfold evaluate pigmentReading
  rw [dif_neg h,dif_neg (show x ∉ marksAlgebra K false from fun u=> h (show TestFamily K true x ∧ (false=true → CovCover K x) from u).1)]

local notation "π" x:max => PhaseChoice.resolutionProbe Y H x
local notation "B₁" x:max => pinhole Ω s x
local notation "ξ" x:max p:max => relocateWorld Y H true p x
local notation "μ₀" x:max p:max=> mirrorInMarks Y H j true (ξ x p)
local notation "Υ" p:max S:max=> reflectedBox j 0 (streetBox K p S)
local notation "η" q:max S:max=> streetBox K q S

variable {t v:ℕ}{o:Cover}{S:Finset Cover}{z:SU.Slot}
variable (f:Marks (tent Y H) true) (p q:Cover) (δ w:ℝ)
local notation "η₀"=> B₁ (π (μ₀ f p))
local notation "η₁"=> B₁ (π (ξ f q))
local notation "Πρ" S:max=> footprint Λ l s (Υ p S)
local notation "Ξ" S:max=> footprint Λ l s (η q S)
local notation "F₀"=> (μ₀ f p)
local notation "F₁"=> (ξ f q)
local notation "δP"=> ((F₀)*(F₁))

lemma signature_root {S:Finset Cover} (u : Marks (tent Y H) true)(t: InTest K false S false u.val) :
    pinhole Ω s (π u)∈ circum Λ l K false (footprint Λ l s S) {s}:=by
  have ht : (π u)∈ keep Λ l s K false (handstamp (footprint Λ l s S)):= ⟨S,(Tapestry.locates ..).mpr t,has_footprint Λ l s S⟩
  exact oneSlotWell Λ K l false _ _ s (Set.mem_singleton _) ht ((enclave_spec ..).mpr ((marksSpec true u).2 rfl))

lemma signature_before (p₀: InTest K false S false f.val): InTest K false (Υ p S) false (F₀).val:=by
  change InTest K false _ false (mirror K j 0 ((ξ f p).val))
  rw [world_val]; exact axial K j 0 (cadTestFull S p ordinate false false p₀)
lemma signature_after (p₀: InTest K false S false f.val): InTest K false (η q S) false (F₁).val:=by rw [world_val]; exact cadTestFull S q _ _ _ p₀

/-- Actual instrument. ``gauge × matter'' reading test includes its cost on the fixed portable
(non-adaptive in s) observation even as the supports are seen on arbitrarily fine S. Keep probeGauge
at the measuring level where it is asserted (the top lift has a different operator profile). -/
structure FocusMark (t v : ℕ) (o:Cover) (S:Finset Cover) (z:SU.Slot) : Prop where
  region₁ : pinhole Ω s (π (μ₀ f p)) ∈ circum Λ l K false (footprint Λ l s (Υ p S)) {s}
  region₂ : pinhole Ω s (π (ξ f q)) ∈ circum Λ l K false (footprint Λ l s (η q S)) {s}
  separatedNonzero (i:Axis) (x:RSpace) (hx:x∈Πρ S) (y:RSpace) (hy:y∈ Ξ S): x i + δ ≤ y i
  delta : 0<δ
  basisUse : ((μ₀ f p)*(ξ f q)).val= remotePair j K p q f.val f.val
  prices : 1/32≤ ‖Φ (η₀ * η₁)‖
  failsFactorization : ¬ RemoteSplit j K p q S (booty o t v) (Window.family z) (evaluate Y H Q.univ_ G d c (SameCharacter.resident Y H Q.univ_ G d false (c d) χ) s)
  probes (m:Side) (h:Hosp (Υ p S∪η q S) ((K).c m)) :
    ∃ u:Pane ((K).c m), (∀ y, (δP).val m (1,y)=0 ∧ (δP).val m (u,y)≠0) ∧ 0<w ∧
      (∃ i:Face (Per (More ((K).c m))), w < SU.group.chord (faceValue u i)) ∧
      ∀ a:ℂ, (δP).val m (u,u)≠ a • (1:FC _)
  uplift_use : ∀ᶠ i in atTop,Host Y H i s (Υ p S∪η q S) ∧ ∀ (k n:ℕ), Tapestry.Pay Y (s+n) i k→
    let X:= attire (breathing Y H (s+n) i k η₀)
    let Z:= attire (breathing Y H (s+n) i k η₁)
    let R:= attire (breathing Y H (s+n) i k (η₀*η₁))
    AtSupport false (Satin.region (volumeAround Λ l n (Υ p S)) (side Y i (s+n))) X ∧
    AtSupport false (Satin.region (volumeAround Λ l n (η q S)) (side Y i (s+n))) Z ∧ R=X*Z ∧
    (∀ U, acts (R U) (Dial.mateK _)=0)

lemma enlivens (a:f.val∈ Filigree K (Window.family z) (booty o t v) S)
    (b : Ridge Y H Q.univ_ s G.history G.clipped j (c j) (χ̂ j) S p q f z o v t δ) (hw:0<w)
    (g:probesGauge w f.val) : FocusMark Y H Q G d j c χ s f p q δ w t v o S z:=by
  let P:= Υ p S; let X:= η q S
  have h:= FilTest a; have hp:= signature_before Y H j f p h; have hx:= signature_after Y H f q h
  have hS:InTest K false (P∪X) false (δP).val:= (hp.mono subset_union_left).mul (hx.mono subset_union_right)
  have ht: (η₀)*(η₁)=B₁ (π (δP)):= (map_mul (pinhole Ω s) (π (F₀)) (π (F₁))).symm
  have he:1/32≤‖Φ (η₀*η₁)‖:= ht.symm ▸ ((costs_basis Y H Q G d j c χ s (bosonLabel K (δP)) (π (δP)) rfl).symm ▸ b.consumption)
  have hv:(δP).val≠0:=by
    intro k; rw [ht,costs_pinhole Y H Q G d c χ,show (π (δP)).val=0 from k] at he
    have e: MX s 0=0:= (consistency Y H V G d c (χ₁) P s).nil_v
    rw [e,norm_zero] at he; norm_num at he
  have hq : probesGauge w ((δP).val) := by
      rw [b.whole_twin]
      exact probesGauge.mulG _ (g.relocatedGauge _ q)
  have hc : probesMatter ((δP).val) := by
      rw [b.whole_twin]
      exact probesMatter.mulM _ (relocatedMatter h.widen (probed_base a) _ _)
  have u:MX s=pigmentReading Y H Q.univ_ s G.history G.clipped j (c j) (χ̂ j):= funext (extended_pigment Y H Q G d j c χ s)
  refine ⟨signature_root Y H s (F₀) hp,signature_root Y H s (F₁) hx,
    fun i x h' y p=> footprint_separation Λ l s P X i δ (b.span_positions i) x y h' p,
    (b.span_positions j).1,b.whole_twin,he,u.symm ▸ b.paid,fun m β=> true_sensitivity hv m β hS hc hw hq, ?_⟩
  apply (eventually_host Y H s (P∪X)).mono; intro i k
  refine ⟨k,?_⟩; intro k' n y ζ ζ' γ
  have xh:= agrees_at_pin Y H s i k' (π (F₀)) (P) hp.widen (Host.shrink Y H subset_union_left k) n y
  have yh:= agrees_at_pin Y H s i k' (π (F₁)) (X) hx.widen (Host.shrink Y H subset_union_right k) n y
  have zh:= agrees_at_pin Y H s i k' (π (δP)) (P∪X) hS.widen k n y
  have hz:evanescent (attire (breathing Y H s i k' (η₀*η₁))):= by
      rw [ht]; change evanescent (attire (breathing Y H (s+0) i k' (B₁ (π (δP)))))
      rw [agrees_at_pin Y H s i k' (π (δP)) (P∪X) hS.widen k 0 ⟨y.1,(by have v:=y.2; omega)⟩]
      exact transmit _ _ (hc _)
  refine ⟨?_,?_,?_,fun U=> only_excited (N:=side Y i (s+n)) (keeps_degree Y H s i k' ⟨y.1,(by have v:=y.2; omega)⟩ (by rw [ht]; exact short_pinhole s _) hz n y.2) U⟩
  · unfold ζ; rw [xh]; exact stationed Y H _ _ i (prepared_train Y H s P n i k' hp.widen)
  · unfold ζ'; rw [yh]; exact stationed Y H _ _ i (prepared_train Y H s X n i k' hx.widen)
  unfold γ ζ ζ'; rw [ht,xh,yh,zh]; change distribute Y H _ _ (train Y H s n i k' (P∪X) ((F₀).val*(F₁).val))=_
  rw [through_product Y H s i k' b.structured k y.1 hp.widen hx.widen n y.2]; exact (distribute_arith Y H (s+n) i _ _ 0).2.1
where
 transmit {m n:Side} (e:m=n) (A:Mark m)(h : evanescent A): evanescent (ship e A):=by subst n; exact h
end structures
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.enlivens
