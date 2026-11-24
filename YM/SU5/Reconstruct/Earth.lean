import YM.SU5.Reconstruct.Cont
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

section atlas
-- ground and origin questions (no time validity assumptions: vacuum ignores first clamp)
local notation "W₀"=>G₀ j
local notation "Ωc"=>χʰ j
local notation "Ρ"=>ρʰ j
local notation "T'"=> roundTrip Y H D G C c F
local notation "B★"=>crossBill Y H D G C c F
lemma moor_left (w:RSpace)(v:Ρ): inner ℂ Ωc (moor (G₀ j) w v)=inner ℂ Ωc v:=by
 let f:=fun w:RSpace=>inner ℂ Ωc (moor (G₀ j) w v)
 have h : Continuous f:=continuous_const.inner (moor_visit (G₀ j) v)
 suffices p:f=(fun _=>inner ℂ Ωc v) from congrFun p w
 apply (everywhere_pos Λ).equalizer h continuous_const; funext i
 let z : ρʰ j:= moor (G₀ j) (physPos Λ i) v
 have he : z.val= (ζ₀ j i) v.val := (plane_edit M (mainsea Y H V Q Qt j false (C j) (Rr j)) (ride Y H V Q Qt j false (C j) (Rr j)) rfl (follows_road Y H V Q Qt j false (C j) (Rr j)) i v).symm
 change inner ℂ ((χʰ j).val:L₀ j) z.val = inner ℂ ((χʰ j).val:L₀ j) v.val; rw [vocate,he,ground_pad]
variable (P:List σ)(v:σ→RSpace)
lemma changes_horizon (a:RSpace) : B★ P v=inner ℂ (χʰ j) (roundTrip Y H D G C c F v P a):=by
 cases P with
 | nil=> rfl
 | cons i t => unfold crossBill roundTrip; rw [film_step,moor_left,film_step,moor_left]
lemma bill_ready (w:RSpace) : B★ P v=B★ P (fun i=>w+v i):=by
 rw [changes_horizon Y H D G C c F P (fun i=>w+v i) w]; exact congrArg _ (trail P 0 |>.trans (by rw [add_zero]))
where
 trail (p:List σ)(a:RSpace): (T' v p a) = (T' (fun i=>w+v i) p (w+a)) := by
   unfold roundTrip; induction p generalizing a with
   | nil=>rfl
   | cons i p ih =>
     rw [film_step,film_step,ih]; have he (p q:RSpace): p+ (w+q)-(w+a)=p+q-a:=by abel
     have h(p q:RSpace):p+(w+q)=w+(p+q):=by abel
     rw [he,h]
end atlas
section earth
variable [Fintype σ][DecidableEq σ]
variable (U:σ→ Set RSpace)
-- binder shadow x F move separate
/-- All configurations admitting a strict temporal coordinate in one of the four.
    Permute the points in seeking ordering. -/
def Formed (P:List σ)(v:σ→ RSpace):Prop:= ∃ (j:Axis)(Z:List σ), P.Perm Z ∧ AxisAperture j U v Z
lemma formed_here (v:σ→RSpace){P Z:List σ}(p:P.Perm Z) (x:∀i,Pol Y H (U i))(F:Board Y H D s j U x)(h:OfferedOn Y H D Z F v) : Formed U P v:=⟨j,Z,p,open_only Y H D s j U v Z F h⟩
include D in -- open_order uses
lemma forms_open (P:List σ): IsOpen (setOf (Formed U P)) := by
 rw [isOpen_iff_mem_nhds]; intro i h
 obtain ⟨j,q,t,k⟩:=h; let S:={v|AxisAperture j U v q}; have hx : S∈𝓝 i:= (open_order Y H D j U q).mem_nhds k
 exact Filter.mem_of_superset hx (by intro z p; exact ⟨j,q,t,p⟩) -- fun z p=> ⟨j,q,t,p⟩
variable (X:∀ i,Pol Y H (U i))
lemma formed_pages (P:List σ)(v:σ→RSpace)(p:Formed U P v): ∃ (s:ℕ)(j:Axis)(Z:List σ)(L:Board Y H D s j U X), P.Perm Z ∧ OfferedOn Y H D Z L v:= by
 obtain ⟨j,q,t,k⟩:=p; obtain ⟨s,q',h⟩:= (eventual_pages Y H D j U v q X k).exists; exact ⟨s,j,q,q',t,h⟩

lemma billboard (P:List σ)(v:σ→RSpace)(p:Formed U P v)(t:P.Nodup): ∃ y:ℂ, ∀ (s:ℕ)(j:Axis)(Z:List σ)(L:Board Y H D s j U X), P.Perm Z → OfferedOn Y H D Z L v → y=crossBill Y H D G C c L Z v:=by
 obtain ⟨s,j,q,h,Q',H'⟩:= formed_pages Y H D U X P v p
 refine ⟨crossBill Y H D G C c h q v,fun s v' p' y ε k=>?_⟩
 exact any_world Y H D G C c h q v (Q'.nodup_iff.mp t) H' (Q'.symm.trans ε) y k

noncomputable def responseAtlas (P:List σ)(u:σ→RSpace):ℂ:= if h : Formed U P u ∧ P.Nodup then (billboard Y H D G C c U X P u h.1 h.2).choose else 0 -- outside undefined
local notation "qv" p:max v:max=> responseAtlas Y H D G C c U X p v
lemma area (P:List σ)(u:σ→RSpace){p:List σ}(g:P.Perm p)(t:P.Nodup)(F:Board Y H D s j U X)(h:OfferedOn Y H D p F u): responseAtlas Y H D G C c U X P u=crossBill Y H D G C c F p u := by
 have he:= formed_here Y H D U u g X F h; rw [responseAtlas,dif_pos (And.intro he t)]; exact (billboard Y H D G C c U X P u he t).choose_spec s j p F g h
lemma sphere_value (P:List σ)(u:σ→RSpace)(p: P.Nodup) (t:Formed U P u): ContinuousAt (responseAtlas Y H D G C c U X P) u:=by
 obtain ⟨s,j,z,q,h,b⟩:= formed_pages Y H D U X P u t
 refine ((realistic Y H D G C c q z).continuousAt).congr ?_
 filter_upwards [(chart_open Y H D z q).mem_nhds b] with i p'; exact (area Y H D G C c U X P i h p q p').symm
lemma atlas_symmetric (P Q':List σ)(n:P.Perm Q')(t:P.Nodup)(v:σ→RSpace)(h:Formed U P v) : responseAtlas Y H D G C c U X P v=responseAtlas Y H D G C c U X Q' v:=by
 obtain ⟨s,j,z,q,p,k⟩:=formed_pages Y H D U X P v h
 exact (area Y H D G C c U X P v p t q k).trans (area Y H D G C c U X Q' v (n.symm.trans p) (n.nodup_iff.mp t) q k).symm
lemma atlas_shifts (P:List σ)(w:σ→RSpace)(h:Formed U P w)(t:P.Nodup)(u:RSpace): Formed U P (fun i=> w i+u) ∧ responseAtlas Y H D G C c U X P (fun i=> w i+u)= responseAtlas Y H D G C c U X P w:=by
 obtain ⟨s,j,z,F,p,k⟩:= formed_pages Y H D U X P w h
 have hz := (OfferedOn_plus Y H D z F w u).2 k
 refine ⟨formed_here Y H D U _ p X F hz,?_⟩
 rw [area Y H D G C c U X P w p t F k,area Y H D G C c U X P _ p t F hz,bill_ready Y H D G C c F z w u]; simp only [add_comm u]

lemma one_mesh (P:List σ)(p:P.Nodup)(u:σ→placement Λ)(e:ShowsEvery P U (fun i=> physPos Λ (u i))):
    poseValue Y H D G C c U X P u=responseAtlas Y H D G C c U X P (fun i=> physPos Λ (u i)):=by
 let U':= fun i=>physPos Λ (u i)
 have h: Formed U P U' := ⟨0, e 0⟩
 obtain ⟨s,j,z,F,t,p'⟩:= formed_pages Y H D U X P U' h
 have he : ShowsEvery z U U':=by intro j; obtain ⟨u,n,g⟩:=e j; exact ⟨u,t.symm.trans n,g⟩
 exact (poses_order Y H D G C c U X u P t).trans ((chart_brilliant Y H D G C c F z (t.nodup_iff.mp p) u he p').trans (area Y H D G C c U X P U' t p F p').symm)
/-- Limit of the original full pose descriptor (no projection) at all-axis
    positions. `one_mesh` identity buys true interpretation here. -/
lemma unwrapped_chart (P:List σ)(p:P.Nodup)(v:σ→RSpace){T':Type}(l':Filter T')(y:T'→σ→placement Λ)(h:Tendsto (fun i k=>physPos Λ (y i k)) l' (𝓝 v))(e:ShowsEvery P U v):
    Tendsto (fun i=>poseValue Y H D G C c U X P (y i)) l' (𝓝 (responseAtlas Y H D G C c U X P v)) := by
 let f:= responseAtlas Y H D G C c U X P
 have he: Formed U P v:= ⟨0,e 0⟩
 refine Tendsto.congr' ?_ ((sphere_value Y H D G C c U X P v p he).tendsto.comp h)
 choose Z k g using e
 have ht(a:Axis): ∀ᶠ i in l', AxisAperture a U (fun k=>physPos Λ (y i k)) (Z a) := h.eventually ((open_order Y H D a U (Z a)).mem_nhds (g a))
 filter_upwards [Filter.eventually_all.mpr ht] with i e'; exact (one_mesh Y H D G C c U X P p _ (fun j=> ⟨Z j,k j,e' j⟩)).symm
lemma at_world (P:List σ)(p:P.Nodup)(v:σ→RSpace){T':Type}(l':Filter T')(n:T'→FrameRef)(b:Tendsto n l' zoom)(y:T'→σ→placement Λ)(h:Tendsto (fun i k=>physPos Λ (y i k)) l' (𝓝 v))(e:Formed U P v):
    Tendsto (fun i=> Average.center (fun z:Dress (timeMesh Λ) σ (n i)=> poseValue Y H D G C c U X P (plotted (timeMesh Λ) (n i) (y i) z))) l' (𝓝 (responseAtlas Y H D G C c U X P v)) := by
 obtain ⟨s,j,z,F,t,p'⟩:= formed_pages Y H D U X P v e
 rw [area Y H D G C c U X P v t p F p']; exact (worldly Y H D G C c F z v l' n y b h (t.nodup_iff.mp p) p').congr fun i=>Average.eq_of _ _ fun z=> (poses_order Y H D G C c U X _ P t).symm
end earth
end here
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
