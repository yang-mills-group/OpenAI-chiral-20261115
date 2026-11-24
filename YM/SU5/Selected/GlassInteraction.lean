import VerifiedSatinGroundInteraction
import YM.SU5.Selected.AllGap
import YM.SU5.Selected.Transit
/-! # CP4. Keep true fully-spatial cells, exact reading survives, extends along Euclidean charts.

Full translation rep & Fourier convention ℂ-argument of E and positive energy on fort.
Note `E4` shifts are Mink time-real and space-real in Spec.Orit, **not** Euclidean. Distinguish
from shift cost in the continuum charts bought using them. Only assert axes (phase); no boost
or microscopic locality result. Also no *extension of all unprojected shifts* asserted!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 310000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (C : Arena Y H Q.circuit j 0 false)
open Tapestry CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
variable {S : Finset Cover}
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "E'" => pigmentReading Y H V s Q Qt j C c
local notation "D₀" => indoor Y H V Q Qt j false C c
local notation "Χ" n:max => response Y H V n Q Qt j false C c

open SelectionAnalysis Spectral Germ
local notation "M"=> timeMesh Λ
local notation "R" => ride Y H V Q Qt j false C c
local notation "π"=> (saunters Y H V Q Qt j false C c).orthogonalProjectionOnto
local notation "L"=> fort Y H V Q Qt j false C c
local notation "P₀" v:max f:max=> relocateWorld Y H true v f
local notation "W" x:max=> mirrorInMarks Y H j true x
local notation "tw" p:max q:max f:max => ((mirrorInMarks Y H j true (P₀ p f))*(P₀ q f))
local notation "f∝" x:max=>show Marks K false from bosonLabel K x
local notation "Ω"=> vocation Y H V Q Qt j false C c
local notation "Ξ"=> peninsula Y H V Q Qt j false C c
local notation "Ψ" s:max=> scene Y H V s Q Qt j false C c
local notation "Z" s:max=> land Y H V s Q Qt j false C c
local notation "B"=> driveAlgebra Y H V Q Qt j false C
local notation "A" x:max=> narrowOrt Y H V Q Qt j false C c x
local notation "E★" u:max => (Ξ).E u

structure Live : Prop where
 true_vac : Victory Y H V Q Qt false j C c
 place : ‖vocation Y H V Q Qt j false C c‖=1 ∧ ∀ t:E4, (Ξ).unit.translation t Ω=Ω
 select (x:L) (h:∀ t:E4,(Ξ).unit.translation t x=x) : ∃ z:ℂ,z•Ω=x
 spectrum : (Ξ).unit.Spectrum (Ξ).ℚmeasure
 nonneg_energy (x: L) : ∀ᵐ z:E4 ∂(Ξ).ℚmeasure.diagonal x,0≤z j
 orbits (k:ℂ)(h:0<k.im)(x u:L) : Paley.Air ((Ξ).J 0 x u) (‖x‖*‖u‖) ∧
   (Ξ).J 0 x u k=inner ℂ x ((Ξ).F (-Complex.I*k) u) -- shifted ray general via OS.*
 links (s:ℕ)(x y:Tower.Field Y H s j 0 false)(u:Axis→ℝ): inner ℂ ((Z s) x) ((Ξ).E (u j).toNNReal ((Ξ).U (diameter u) ((Z s) y)))=(Ψ s) x y u
 transitions (x: List B) : ∃ g:ℕ→ℂ,(∀ i, Tendsto (fun t=>atCharacter Y H V Q Qt j false C c (labored Y H V Q Qt j false C x i t)) atTop (𝓝 (g i))) ∧ Tendsto g atTop (𝓝 (inner ℂ Ω ((paidRanks Y H V Q Qt j false C c x) Ω)))
 fills : Dense (⋃ s,range (fun x: Tower.Field Y H s j 0 true=> land Y H V s Q Qt j false C c (admit Y H s j x)))

lemma alive (h: Victory Y H V Q Qt false j C c) : Live Y H V Q Qt j C c := by
 refine ⟨h,⟨vocation_norm ..,compass_origin Y H V Q Qt j false C c⟩,compass_invariant Y H V Q Qt j false C c h,(Ξ).joint,(Ξ).bright,fun k h x u=>⟨(Ξ).altitude ..,?_⟩,fun s x y u=>(peninsula_window Y H V s Q Qt j false C c x y u).symm,ranks_contract Y H V Q Qt j false C c,shore_dense Y H V Q Qt j C c⟩
 unfold OS.Semigroup.J; rw [(Ξ).lift_ray u h,(Ξ).unit.origin]; rfl

variable (δ:ℝ) {o: Cover}{u d : ℕ}{f: Marks (tent Y H) true}{z:SU.Slot}
structure Exceeds (f:Marks (tent Y H) true) (z:SU.Slot) (V': Finset Cover)(o:Cover)(u d:ℕ)(p q:Cover): Prop where
  live : Live Y H V Q Qt j C c
  shelf : Ridge Y H V s Q Qt j C c V' p q f z o u d δ
  persisting : ∀ n:ℕ, stream Y H D s n ((tw p q f).val)=
       stream Y H D s n (W (P₀ p f)).val * stream Y H D s n (P₀ q f).val ∧
     (Χ (s+n)) (upward Y H Q false (f∝ (tw p q f)) s n)=(Χ s) (f∝ (tw p q f))
  extendsTo : ∃ x y: Tower.Field Y H s j 0 false,x.val=(relocateWorld Y H true p f).val ∧ y.val=(relocateWorld Y H true q f).val ∧
     Continuous (scene Y H V s Q Qt j false C c x y) ∧
     (∀ᶠ v : (Axis→ℝ) in 𝓝 0,1/33 ≤‖(Ψ s) x y v‖) ∧
     ((Ψ s) x y 0)=(Χ s) (f∝ (tw p q f)) ∧
     ∀ v : placement Λ,(∀ i:Axis,uptown i v)→ scene Y H V s Q Qt j false C c x y (fun i=>(v i:ℝ))=Visits Y H V s Q Qt j false C c x y v

lemma showcase (V': Finset Cover) (h: Survivor Y H V s Q Qt j C z o u d V' f c) (p0:0 < δ) :
    ∃ p q:Cover, Exceeds Y H V s Q Qt j C c δ f z V' o u d p q:=by
 obtain ⟨p,q,hp⟩:= high_paired Y H V s Q Qt j C c δ V' z f h p0
 refine ⟨p,q,alive Y H V Q Qt j C c h.victory,hp,fun n=> ⟨?_,moves_up ..⟩,?_⟩
 · have x:= (FilTest h.link.mark_mem).widen; have hu(q:Cover) : InTest K true (streetBox K q V') false (P₀ q f).val:=by rw [world_val]; exact cad_test q _ x
   exact woven_product Y H Q.circuit s n (axial K j 0 (hu p)) (hu q) hp.structured
 obtain ⟨x,y,ht,hz,ax,_⟩:= hp.zones
 have e : (Ψ s) x y 0=(Χ s) (f∝ (tw p q f)):= by
    rw [show (0:Axis→ℝ)=(fun i:Axis=> ((0:placement Λ) i:ℝ)) from rfl, ax 0 (by simp [uptown]),blankZero,earns]
    apply congrArg ((Χ s)); exact Subtype.ext (congrArg₂ (fun a b=>mirror (tent Y H) j 0 a*b) ht hz)
 refine ⟨x,y,ht,hz,scene_cont ..,?_, e,ax⟩
 apply (Metric.tendsto_nhds.mp ((scene_cont Y H V s Q Qt j false C c x y).norm.tendsto 0) (1/1056) (by norm_num)).mono
 intro z h; have he:dist ‖(Ψ s) x y z‖ ‖(Ψ s) x y (0:Axis→ℝ)‖ < 1/1056:= h; rw [Real.dist_eq] at he; have hq: 1/32≤ ‖(Ψ s) x y (0:Axis→ℝ)‖:= by rw [e]; exact hp.consumption
 linarith only [(abs_lt.mp he).1,hq]

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.showcase
