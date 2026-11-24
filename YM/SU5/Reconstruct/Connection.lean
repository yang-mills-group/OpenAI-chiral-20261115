import YM.SU5.Reconstruct.Determine
import YM.SU5.Reconstruct.Density
import YM.SU5.Reconstruct.Effective
/-!
# The actual mixed test at fixed nonzero physical separation

Use Selected's test ON THIS CHARACTER, any axis and room. Compute
on the dedicated part of the calibrated gauge-invariant polynomial algebra (not
claiming continuity of changing shapes). Field locations fixed, with disjoint
translated physical regions, not shoved to contact in cutoff limits. Includes
operator readings in the same appointed space and in the projection to
continuous spacetime translations with nonnegative time spectrum. Keeps all
of the original `Victory` data via `Exceeds`. The nonzero in this checkpoint
is not a statement on scattering, not a lower bound on a connected correlator
BETWEEN the two composite insertions, and uses the gauge-invariant state on
its whole domain (including extension to read the charged factors). The
nonfactorization states a failure of gauge / matter separation in precisely
the joint effective field sense specified by the input. The resolution
observables may (and do) mix the fields. No claims about real-time locality
of these operators yet.
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
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet

variable (j:Axis)
-- worker-independent phase functional on *all even* resolution polynomials (loose calls share s)
noncomputable def extension (s:ℕ) (f:Family K):ℂ:=
   if p : TestFamily K true f then sch Y H D G C c (pinhole (Dome K) s ⟨f,p⟩) else 0

lemma operational (s:ℕ) : extension Y H D G C c s = pigmentReading Y H D.univ_ s G.history G.clipped j (C j) (inAxis Y H D G C c j) := by
  funext f; unfold extension; by_cases p:TestFamily K true f
  · rw [dif_pos p]; let x:Marks K false:= PhaseChoice.observe p
    rw [sch_sample]; change response _ _ V _ Q Qt 0 false (C 0) c x=pigmentReading Y H V s Q Qt j (C j) (inAxis Y H D G C c j) x.val
    rw [reads_color]; exact (across_response Y H V s Q Qt 0 false (C 0) c x j (C j)).symm
  unfold pigmentReading; rw [dif_neg p,dif_neg]; exact fun h=> p ((marksSpec false (show Marks K false from ⟨_,h⟩)).1)

local notation "ρ" i:max => inAxis Y H D G C c i
local notation "R★" s:max=>response Y H D.univ_ s G.history G.clipped j false (C j) (inAxis Y H D G C c j)

variable (s:ℕ)
variable {z:SU.Slot} {o:Cover}{u d':ℕ}{S:Finset Cover}
-- strict=true means in the gauge invariant system (both links still allowed)
variable (f: Vacancy.observable (tent Y H) true)
local notation "U" => extension Y H D G C c s
local notation "λr" i:max => relocateWorld Y H true i f
local notation "θ₀" x:max => mirrorInMarks Y H j true x
local notation "ι" x:max => pinhole χ s (resolutionProbe Y H x)
local notation "F★" => sch Y H D G C c

lemma narrow_cad {S:Finset Cover}(i:Cover)(T: List Axis){x:Family K} (p:InTest K false S false x) : InTest K false (drivePlot i K T S) false (cad K T i x):=by induction T with | nil=> exact p | cons a v ih=> exact flow_port _ _ _ ih
lemma certificateAt {g : Vacancy.observable K true}(h:g.val∈ observ K S false) :
    pinhole (Dome (tent Y H)) s (resolutionProbe Y H g) ∈ PolAt Y H s (realChartFootprint Λ l s S) := by
  obtain ⟨p,t⟩:= (obs_in ..).1 h
  apply oneSlotWell Λ _ l true _ (Set.univ∩ Set.Iic s) s (by simp) _ (show resolutionProbe Y H g∈enclave K from (enclave_spec K).2 t)
  exact ⟨S,p.widen,foot_self Λ l s S⟩
local notation "X₀" p:max=> streetBox K p S
local notation "a₀" p:max=> reflectedBox j 0 (streetBox K p S)
local notation "π₀" x:max=> realChartFootprint Λ l s x
-- separate occurrences of f. in spin class assigned, refined supports stay in physically disjoint sets
def Placement (S:Finset Cover)(p q:Cover)(δ:ℝ) : Prop :=
    let A:= mirrorInMarks Y H j true (relocateWorld Y H true p f)
    let B:=relocateWorld Y H true q f
    let S':= reflectedBox j 0 (streetBox K p S); let T':= streetBox K q S
    let X:= realChartFootprint Λ l s S'; let Z:= realChartFootprint Λ l s T'
    let F:=pinhole χ s (resolutionProbe Y H A); let W:=pinhole χ s (resolutionProbe Y H B)
    f.val ∈ observ K S false ∧ (ι f) ∈ PolAt Y H s (π₀ S) ∧
    A.val ∈ observ K S' false ∧ B.val ∈ observ K T' false ∧
    F∈ PolAt Y H s X ∧ W ∈ PolAt Y H s Z ∧
    F * W∈PolAt Y H s (X∪ Z) ∧
    (∀ i:Axis,∀ x∈ X,∀ y∈ Z,x i+δ ≤ y i) ∧ Disjoint X Z ∧
    IsCompact X ∧ IsCompact Z ∧
    (ι (A*B : Marks K true))=F*W ∧
    (∀ᶠ i:ℕ in atTop,∀ (k:ℕ), Pay Y s i k → atCutoff Y H i k (F*W) = atCutoff Y H i k F*atCutoff Y H i k W)
set_option maxHeartbeats 500000 in
lemma placeConnection {p q:Cover} (δ:ℝ)(t:InTest K false S false f.val)
    (v:∀ i', PhysicalHush (Λ:=Λ) (l:=l) s i' (a₀ p) (X₀ q) δ) :
    Placement Y H j s f S p q δ:=by
  unfold Placement
  intro A B S' T' X Z F W
  have hf:InTest K false S false f.val:= t
  have hS(i:Cover):InTest K false (streetBox K i S) false (λr i).val:=by rw [world_val]; exact narrow_cad Y H i _ hf
  have x:A.val∈ observ K S' false:= ⟨axial K j 0 (hS p),(marksSpec true A).2 rfl⟩
  have y:B.val∈ observ K T' false:= ⟨hS q,(marksSpec true B).2 rfl⟩
  have hp:f.val∈ observ K S false:= ⟨hf,(marksSpec true (show Marks K true from f)).2 rfl⟩
  have e:F∈ PolAt Y H s X:= certificateAt Y H s (g:=(A: Vacancy.observable _ _)) x
  have g:W ∈ PolAt Y H s Z:= certificateAt Y H s (g:=(B:Vacancy.observable _ _)) y
  have Hx: ∀ i:Axis,∀ x∈ X,∀ y∈ Z,x i+δ ≤ y i:= fun i=>foot_separation Λ l s (v i)
  have Hz:Disjoint X Z:= by refine Set.disjoint_left.mpr (fun t a d=>?_); have ht:=Hx j t a t d; have he:0 < δ:= (v j).1; linarith
  have hw:(ι (A*B : Marks K true))=F*W:= map_mul (pinhole χ s) (resolutionProbe Y H A) (resolutionProbe Y H B)
  refine ⟨hp,certificateAt Y H s (g:=f) hp,x,y,e,g,(PolAt Y H s _).mul_mem ((isotone Y H Set.subset_union_left) e) ((isotone Y H Set.subset_union_right) g), Hx, Hz,foot_print Λ l s S',foot_print Λ l s T', hw, ?_⟩
  · obtain ⟨R,p,c₀⟩:= foot_cabin Λ l s S'; obtain ⟨R',a,c'⟩:=foot_cabin Λ l s T'
    have cm {a b:ℝ}(h:a≤b) : Tapestry.cabin a ⊆ Tapestry.cabin b:=fun x p i=>le_trans (p i) h -- type dispatch
    refine (wide_calendar Y (max R R')).mono fun i p k t=> pairAtCutoff Y H i k s p (Set.Subset.trans c₀ (cm (le_max_left ..))) (Set.Subset.trans c' (cm (le_max_right ..))) Hz Set.univ Set.univ ((well_spec ..).1 e).1 ((well_spec ..).1 g).1 t

set_option maxHeartbeats 730000 in
def CoupledHere (z:SU.Slot)(S:Finset Cover)(o:Cover)(u d':ℕ)(p q:Cover) : Prop :=
    let A:= mirrorInMarks Y H j true (relocateWorld Y H true p f)
    let B:=relocateWorld Y H true q f
    let F:=pinhole χ s (resolutionProbe Y H A); let W:=pinhole χ s (resolutionProbe Y H B)
    1/4 ≤ ‖F★ (ι f)‖ ∧
    1/32 ≤ ‖F★ (F* W)‖ ∧
    ¬CF.Pannier.Chancel.Parcel K (Window.family z) (booty o d' u) S (extension Y H D G C c s) ∧
    ¬RemoteSplit j K p q S (booty o d' u) (Window.family z) (extension Y H D G C c s) ∧
    (∃ x y:Tower.Field Y H s j 0 true,
      x.val=(relocateWorld Y H true p f).val ∧ y.val=B.val ∧
      let x':= admit Y H s j x; let y':=admit Y H s j y
      F★ (F*W) = scene Y H V s Q Qt j false (C j) (ρ j) x' y' (0:Axis → ℝ) ∧
      ∀ᶠ v: (Axis→ℝ) in 𝓝 0, 1/33 ≤ ‖scene Y H V s Q Qt j false (C j) (ρ j) x' y' v‖)
set_option maxHeartbeats 650000 in
lemma couplingConnection {p q:Cover} (δ:ℝ)
    (hsurv: Survivor Y H D.univ_ s G.history G.clipped j (C j) z o u d' S f (inAxis Y H D G C c j))
    (v: Exceeds Y H D.univ_ s G.history G.clipped j (C j) (inAxis Y H D G C c j) δ f z S o u d' p q) :
    CoupledHere Y H D G C c j s f z S o u d' p q:=by
  unfold CoupledHere
  intro A B F W
  have hw:(ι (A*B : Marks K true))=F*W:= map_mul (pinhole χ s) (resolutionProbe Y H A) (resolutionProbe Y H B)
  have hD(d:Marks K true): sch Y H D G C c (ι d)=(R★ s) (bosonLabel K d) := (sch_sample Y H D G C c s (resolutionProbe Y H d)).trans ((across_response Y H V s Q Qt 0 false (C 0) c (fieldArg Y H (resolutionProbe Y H d)) j (C j)).symm)
  have HE:F★ (F*W)=(R★ s) (bosonLabel K (A*B : Marks K true)):=by rw [←hw,hD]
  have cost : 1/32≤ ‖(R★ s) (bosonLabel K (A*B : Marks K true))‖:= v.shelf.consumption
  have hread: F★ (ι f)= _ := hD (show Marks K true from f)
  have fare: 1/4≤ ‖(R★ s) (bosonLabel K f)‖:= hsurv.responds
  refine ⟨fare.trans_eq (congrArg norm hread).symm,cost.trans_eq (congrArg norm HE).symm,?_,?_,?_⟩
  · rw [operational Y H D G C c j s]; exact hsurv.factor_failure
  · rw [operational Y H D G C c j s]; exact v.shelf.paid
  obtain ⟨x',y',u0,v0,e',hvx,r,_⟩:= v.extendsTo
  let T: Tower.Field Y H s j 0 true:= ⟨x'.val,(purpose_ok ..).2 ⟨((purpose_ok ..).1 x'.property).1,fun _=>u0.symm ▸ ((marksSpec true (λr p)).2 rfl)⟩⟩
  let L: Tower.Field Y H s j 0 true:= ⟨y'.val,(purpose_ok ..).2 ⟨((purpose_ok ..).1 y'.property).1,fun _=>v0.symm ▸ ((marksSpec true (λr q)).2 rfl)⟩⟩
  exact ⟨T,L,u0,v0,HE.trans r.symm,hvx⟩
def PhysicalPair (z:SU.Slot)(S:Finset Cover)(o:Cover)(u d':ℕ)(p q:Cover)(δ:ℝ) : Prop := Placement Y H j s f S p q δ ∧ CoupledHere Y H D G C c j s f z S o u d' p q

lemma connection {p q:Cover} (δ:ℝ)
    (hsurv: Survivor Y H D.univ_ s G.history G.clipped j (C j) z o u d' S f (inAxis Y H D G C c j))
    (v: Exceeds Y H D.univ_ s G.history G.clipped j (C j) (inAxis Y H D G C c j) δ f z S o u d' p q) :
    PhysicalPair Y H D G C c j s f z S o u d' p q δ:= by
  refine ⟨placeConnection Y H j s f δ (FilTest hsurv.link.mark_mem) (fun i' => v.shelf.span_positions i'), couplingConnection Y H D G C c j s f δ hsurv v⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
