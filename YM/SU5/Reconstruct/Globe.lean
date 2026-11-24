import YM.SU5.Reconstruct.Slides
import YM.SU5.Reconstruct.Tresh
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 470000
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
open SelectionAnalysis Vacancy.Average
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

section here
variable (C : ∀ i: Axis, Tower.Arena Y H G.history.circuit i 0 false)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
variable {s:ℕ}{j:Axis}{σ:Type} {U:σ→ Set RSpace}{x:∀ i,Pol Y H (U i)}
variable (F:Board Y H D s j U x)
local notation "M"=> timeMesh Λ
local notation "Rr" i:max=> inAxis Y H D G C c i
local notation "L₀" i:max => indoor Y H V Q Qt i false (C i) (Rr i)
local notation "Op" a:max => procession Y H V Q Qt j false (C j) (Rr j) a
local notation "p₀" i:max=> doorstep Y H V Q Qt i false (C i) (Rr i)
open StripCard
local notation "ζ₀" i:max z:max=> atEstate Y H V Q Qt i false (C i) (Rr i) z
local notation "B₀"=>hallCall Y H D G C F
local notation "μ"=>physPos Λ
local notation "pF"=>navFilm Y H D G C c F
local notation "m₀"=>meshPos Λ s
local notation "Z₀"=> Marks (tent Y H) false
local notation "η₀" v:max=> relocateWorld Y H false v
/-! # Physical broad Euclidean relaxation is ONE chart. -/
open SelectionAnalysis.Regularizing
local notation "ρʰ" i:max=> fort Y H V Q Qt i false (C i) (Rr i)
local notation "χʰ" i:max=>vocation Y H V Q Qt i false (C i) (Rr i)
local notation "V₀"=>procession Y H V Q Qt j false (C j) (Rr j)
local notation "G₀" i:max=>peninsula Y H V Q Qt i false (C i) (Rr i)
local notation "ιC" i:max=> narrowOrt Y H V Q Qt j false (C j) (Rr j) (B₀ i)
local notation "Sʰ" i:max=>saunters Y H V Q Qt i false (C i) (Rr i)

noncomputable def roundTrip (w:σ→RSpace)(z:List σ) (v:RSpace) : fort Y H V Q Qt j false (C j) (inAxis Y H D G C c j):= parkFilm (plain (timeMesh Λ) ∘ bottomPlay Y H D F) (plain M ∘ widthPlaying Y H D F) w
   (fun i=> ιC i) (moor (G₀ j)) (vocation Y H V Q Qt j false (C j) (Rr j)) z v
noncomputable def crossBill (p:List σ)(v:σ→RSpace):ℂ:= inner ℂ (χʰ j) (roundTrip Y H D G C c F v p 0)
local notation "T'" v:max p:max u:max=>roundTrip Y H D G C c F v p u
local notation "B★"=>crossBill Y H D G C c F
section
variable [Fintype σ][DecidableEq σ]
variable (P:List σ) (v:σ → RSpace)
variable {S:Type}(l':Filter S)(X:S→FrameRef)(r: S→ σ→ placement Λ)
variable (g:Tendsto X l' zoom)(w : Tendsto (fun i=>fun y=> physPos Λ (r i y)) l' (𝓝 v))
local notation "Ψ" i:max=> Dress (timeMesh Λ) σ (X i)
include w g
lemma navigator (q:P.Nodup)(y:S→placement Λ)(ψ :RSpace)(t:Tendsto (fun i=> physPos Λ (y i)) l' (𝓝 ψ)):
    Tendsto (fun n=>Average.center (fun z: Dress (timeMesh Λ) σ (X n)=> pF (plotted (timeMesh Λ) (X n) (r n) z) P (y n))) l' (𝓝 ((T' v P ψ).val:L₀ j)) := by
 let X':= mainsea Y H V Q Qt j false (C j) (Rr j)
 let h : doorstep Y H V Q Qt j false (C j) (Rr j)∈Sʰ j:= occupant_compass Y H V Q Qt j false (C j) (Rr j)
 let x := (χʰ j)
 let y₀ : ρʰ j:= ⟨p₀ j, h⟩
 have hs:roundTrip Y H D G C c F v P ψ = parkFilm (plain (timeMesh Λ) ∘ bottomPlay Y H D F) (plain M ∘ widthPlaying Y H D F) v (fun i=>ιC i) (moor (G₀ j)) y₀ P ψ:=by unfold roundTrip; rw [show y₀=χʰ j from Subtype.ext (vocate Y H V Q Qt j false (C j) (Rr j)).symm]
 rw [hs]
 have he := apertureFilm M (X') (ride Y H V Q Qt j false (C j) (Rr j)) rfl (follows_road Y H V Q Qt j false (C j) (Rr j)) y₀ (bottomPlay Y H D F) (widthPlaying Y H D F) (fun i=> V₀ (B₀ i)) v ψ P q l' X g y r (tendsto_pi_nhds.mp w) t
 exact he

local notation "Dₛ"=>Sigma (fun n=> Dress (timeMesh Λ) σ (X n))
local notation "μg"=>uniform l' (fun n=>Dress (timeMesh Λ) σ (X n))
lemma ready_plot : Tendsto (fun i:Sigma (fun n=>Dress (timeMesh Λ) σ (X n))=> fun k=> physPos Λ (plotted (timeMesh Λ) (X i.1) (r i.1) i.2 k)) (uniform l' (fun n=>Dress (timeMesh Λ) σ (X n))) (𝓝 v):=by
 refine tendsto_pi_nhds.mpr fun a=> ?_
 have he := pellet_moves M μg (fun i:Dₛ=> X i.1) (g.comp (at_uniform l')) (fun i:Dₛ=> i.2 a)
 have hx:= ((tendsto_pi_nhds.mp w a).comp (at_uniform (A:=fun n=> Dress M σ (X n)) l')).add he
 unfold plotted; simp_rw [map_add]; rw [←add_zero (v a)]; exact hx

/-- For every real chart event restore ONE value by universal offsets,
    on ONE selected response in absolute physical units. Thus no reassignment
    of meanings at overlaps. -/
lemma worldly (p:P.Nodup)(d:OfferedOn Y H D P F v): Tendsto (fun n=> Average.center (fun z:Dress (timeMesh Λ) σ (X n)=> poseValue Y H D G C c U x P (plotted (timeMesh Λ) (X n) (r n) z))) l' (𝓝 (crossBill Y H D G C c F P v)) := by
 let e:= (0:RSpace)
 let J:= fun _:S=> (0:placement Λ)
 have hk := (tendsto_const_nhds (x:=p₀ j)).inner (𝕜:=ℂ) (navigator Y H D G C c F P v l' X r g w p J 0 tendsto_const_nhds)
 have he : ∀ᶠ n in l',∀ i:Dress M σ (X n), OfferedOn Y H D P F (fun k=> (physPos Λ) (plotted M _ (r n) i k)):= (uniform_event l').mp ((ready_plot (Λ:=Λ) v l' X r g w).eventually ((chart_open Y H D P F).mem_nhds d)) -- arguments inspect
 have hy: (B★ P v)=inner ℂ (p₀ j) ((T' v P e).val:L₀ j):=by unfold crossBill; change inner ℂ ((χʰ j).val:L₀ j) _=_; rw [vocate]; rfl
 rw [hy]
 apply hk.congr'
 filter_upwards [he] with i p
 rw [show inner ℂ (p₀ j) (Average.center _) = _ from (Average.natural (fun z:Dress M σ (X i)=>pF (plotted _ _ (r i) z) P (J i)) (innerSL ℂ (p₀ j))).symm]
 exact Average.eq_of _ _ fun z=>frame_update Y H D G C c F P _ _ (p z)
omit w g
lemma locating_real (R:Mesh){y:σ→ RSpace}: ∃ r:ℕ→σ→SceneGrid R,Tendsto (fun i=>fun k=>plain R (r i k)) atTop (𝓝 y):=by
 -- shadow R notation remove
 have hv: DenseRange (fun p:σ→SceneGrid R=> fun i=>plain R (p i)):= DenseRange.piMap fun i=> DenseRange.piMap fun j:Axis=> (daylight R).denseRange_val
 obtain ⟨r,h,t⟩:= mem_closure_iff_seq_limit.mp (hv y)
 choose f hf using h
 exact ⟨f,t.congr fun i=> (hf i).symm⟩
lemma any_world (p:P.Nodup)(h:OfferedOn Y H D P F v){Z:List σ}(g:P.Perm Z){u:Axis}{t:ℕ}(b:Board Y H D t u U x)(r:OfferedOn Y H D Z b v):
    crossBill Y H D G C c F P v=crossBill Y H D G C c b Z v := by
 obtain ⟨r',hr⟩:=locating_real (y:=v) M
 let X:FrameRef→σ→placement Λ:= fun i=> r' i.1
 have he := hr.comp zoom_out; have hs:= worldly Y H D G C c F P v zoom _root_.id X tendsto_id he p h
 refine tendsto_nhds_unique hs ((worldly Y H D G C c b Z v zoom _root_.id X tendsto_id he (g.nodup_iff.mp p) r).congr (fun i=>?_)) -- tune
 exact Average.eq_of _ _ fun z => (poses_order Y H D G C c U x _ P g).symm
end -- sections
end here
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
