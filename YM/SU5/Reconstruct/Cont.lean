import YM.SU5.Reconstruct.Globe
import YM.SU5.Reconstruct.Metro
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

-- arbitrary arity analytic work isolated from setup
private lemma blanket_cont {A:Hilbert}{D P:Type}[TopologicalSpace D]{a:Axis}(S:OS.Semigroup A a) (u w: P→RSpace)(x:D→P→RSpace)(q:∀ i: P, Continuous (fun y=> x y i))(X:P→A.Op)(y:A)(t:List P) (z:D→RSpace)(h:Continuous z) : Continuous (fun d=> parkFilm u w (x d) X (moor S) y t (z d)) := by
 induction t generalizing z with
 | nil=> exact continuous_const
 | cons i t ih=>
   let C'(d:D):= X i (parkFilm u w (x d) X (moor S) y t (u i+w i + x d i)); let p(d:D):= u i+x d i - z d
   have ht:Continuous C':= (X i).continuous.comp (ih (fun d=> u i+w i + x d i) (continuous_const.add (q i)))
   have hp:Continuous p:= (continuous_const.add (q i)).sub h
   refine continuous_iff_continuousAt.mpr fun v=> ?_
   change Tendsto (fun u:D=> moor S (p u) (C' u)) (𝓝 v) (𝓝 (moor S (p v) (C' v)))
   apply tendsto_of_tendsto_of_dist (((moor_visit S (C' v)).comp hp).tendsto v)
   apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ (tendsto_iff_dist_tendsto_zero.mp (ht.tendsto v))
   exact Eventually.of_forall fun i=> by change dist (moor S (p i) _) (moor S (p i) _) ≤_; rw [dist_comm (moor S _ _),dist_eq_norm,dist_eq_norm,←map_sub]; exact moor_cost S ..
local notation "T'" v:max p:max u:max=>roundTrip Y H D G C c F v p u
local notation "B★"=>crossBill Y H D G C c F
lemma realistic (t:List σ) : Continuous (B★ t):=continuous_const.inner (blanket_cont (G₀ j) _ _ (fun y=> y) (fun i=> continuous_apply i) _ _ _ (fun _=> 0) continuous_const)

section wide
variable [Fintype σ][DecidableEq σ]
variable (P:List σ)(v:σ→RSpace)
-- infinite threshold if no labels
lemma lower_earlier (z:σ→ℝ):∃ i:placement Λ,∀ s∈P, physPos Λ i j < z s:=by
  induction P with
  | nil=>exact ⟨0,by simp⟩
  | cons i t ih =>
    obtain ⟨y,p⟩:=ih
    obtain ⟨x,h,b⟩:= (daylight M).inter_open_nonempty _ isOpen_Iio (show (Set.Iio (min (physPos Λ y j) (z i))).Nonempty from Set.nonempty_Iio)
    let v:placement Λ:=fun i=> ⟨x,b⟩
    refine ⟨v,?_⟩; intro a v
    obtain rfl|v:= List.mem_cons.mp v
    · exact h.trans_le (min_le_right ..)
    exact (lt_of_lt_of_le h (min_le_left ..)).trans (p _ v) -- shadow

lemma at_separator {D':Type} (L':Filter D') (a b : D'→σ→placement Λ) (m:Tendsto (fun i k=> physPos Λ (a i k)) L' (𝓝 v))(n:Tendsto (fun i k=> physPos Λ (b i k)) L' (𝓝 v))(h: OfferedOn Y H D P F v) (q:∀ i k,∀ l:Axis,l≠j → a i k l = b i k l):
    Tendsto (fun i=> dist (poseValue Y H D G C c U x P (a i)) (poseValue Y H D G C c U x P (b i))) L' (𝓝 0) := by
 let s:= mainsea Y H V Q Qt j false (C j) (Rr j)
 obtain ⟨k,p⟩:=lower_earlier (j:=j) P (fun i=> plain (timeMesh Λ) (bottomPlay Y H D F i) j+v i j)
 have hu : OrderedP M (bottomPlay Y H D F) (widthPlaying Y H D F) v P (j:=j) := h.imp (by
    intro a b h; change StripCard.ends _ _ _ _ _ j < _ at h; unfold StripCard.ends StripCard.finishBit at h; rw [map_add] at h; exact h)
 let A₁(i:D'):= pF (a i) P k; let A₂(i:D'):= pF (b i) P k
 have hx:Tendsto (fun i=> dist (A₁ i) (A₂ i)) L' (𝓝 0) :=
    film_axis M s (ride Y H V Q Qt j false (C j) (Rr j)) rfl (p₀ j) (bottomPlay Y H D F) (widthPlaying Y H D F) (fun i=> procession Y H V Q Qt j false (C j) (Rr j) (B₀ i)) v (physPos Λ k) P L' a b (fun _=>k) (fun _=>k) (tendsto_pi_nhds.mp m) (tendsto_pi_nhds.mp n) tendsto_const_nhds tendsto_const_nhds (fun y i=>q i y) (fun _ _ _=>rfl) p hu
 refine squeeze_zero' (Eventually.of_forall fun i=> dist_nonneg) ?_ hx
 have Hu : setOf (OfferedOn Y H D P F)∈𝓝 v:= (chart_open Y H D P F).mem_nhds h
 filter_upwards [m.eventually Hu,n.eventually Hu] with i p q
 rw [←frame_update Y H D G C c F P _ k p,←frame_update Y H D G C c F P _ k q,dist_eq_norm,dist_eq_norm,←inner_sub_right]; exact (norm_inner_le_norm (𝕜:=ℂ) _ _).trans_eq (by rw [Tower.Selected.ready,one_mul])
-- a common 4-coordinate aperture. second form allows W permutations
abbrev ShowsEvery {σ:Type} (P:List σ) (u:σ→ Set RSpace)(v:σ→RSpace) := ∀ j:Axis, ∃ p:List σ, P.Perm p ∧ AxisAperture j u v p
lemma raw_contour {v:σ→RSpace}(t: ShowsEvery P U v)(c₀ : List Axis)
    {A':Type}(l':Filter A')(d d':A'→σ→placement Λ)(w:Tendsto (fun a i=>physPos Λ (d a i)) l' (𝓝 v))(b:Tendsto (fun a i=>physPos Λ (d' a i)) l' (𝓝 v))(g:∀ i∉c₀, ∀ a k,d a k i=d' a k i) : Tendsto (fun i=>dist (poseValue Y H D G C c U x P (d i)) (poseValue Y H D G C c U x P (d' i))) l' (𝓝 0):=by
 induction c₀ generalizing d d' with
 | nil=>
    have he : d=d':=funext (fun a=>funext (fun i=>funext (fun b=> g b List.not_mem_nil a i)))
    simp_rw [he,dist_self]; exact tendsto_const_nhds
 | cons i l ih=>
    obtain ⟨Z,n,h⟩:= t i
    obtain ⟨z,F,h⟩:= (eventual_pages Y H D i U v Z x h).exists
    let f(a:A')(s:σ) : placement Λ:= Function.update (d a s) i (d' a s i)
    have hf:Tendsto (fun a s=>physPos Λ (f a s)) l' (𝓝 v):=by
       refine tendsto_pi_nhds.mpr fun s=> tendsto_pi_nhds.mpr fun k=>?_
       by_cases h:k=i
       · subst k; have hz(a:A'): physPos Λ (f a s) i=physPos Λ (d' a s) i:= by change (Function.update (d a s) i (d' a s i) i:↥(marks M)).val=_;
                                                                                  rw [Function.update_self]; rfl
         simp_rw [hz]; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp b s) i
       have hz(a:A'): physPos Λ (f a s) k=physPos Λ (d a s) k:=by unfold f; change (Function.update (d a s) i (d' a s i) k : ↥(marks M)).val=_; rw [Function.update_of_ne h]; rfl
       simp_rw [hz]; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp w s) k
    have he := ih f d' hf b (show ∀ a∉l, ∀ y k, f y k a=d' y k a from fun a p y k=> by
       rcases eq_or_ne a i with k|e
       · subst a; unfold f; rw [Function.update_self]
       unfold f; rw [Function.update_of_ne e,g a (by simpa [e] using p)])
    let B(y):=poseValue Y H D G C c U x P y
    have h' i': B i'= poseValue Y H D G C c U x Z i':= poses_order _ _ _ _ _ _ _ _ _ P n
    have hx : Tendsto (fun a=> dist (B (d a)) (B (f a))) l' (𝓝 0):= by
      simp_rw [h']; exact at_separator Y H D G C c F Z v l' d f w hf h (fun a k l p=> (Function.update_of_ne p ..).symm)
    refine squeeze_zero' (Eventually.of_forall fun i=>dist_nonneg) (Eventually.of_forall fun i=> dist_triangle _ (B (f i)) _) (by simpa only [add_zero] using hx.add he)
lemma chart_brilliant (p:P.Nodup)(u:σ→placement Λ)(w:ShowsEvery P U (fun i=> physPos Λ (u i)))(d:OfferedOn Y H D P F (fun i=> physPos Λ (u i))): poseValue Y H D G C c U x P u=crossBill Y H D G C c F P (fun i=> physPos Λ (u i)):=by
 let Ω:= fun i=>physPos Λ (u i)
 let D':= fun i:FrameRef=>Dress M σ i; let A:=Sigma D'; let l:=uniform zoom D'
 let r(a:A):= plotted M a.1 u a.2; let X(i) := poseValue Y H D G C c U x P i
 have hv:Tendsto (fun a:A=> X (r a)) l (𝓝 (X u)):=tendsto_iff_dist_tendsto_zero.mpr
    (raw_contour Y H D G C c P w ordinate l r (fun _=>u) (ready_plot Ω zoom _root_.id (fun _=>u) tendsto_id tendsto_const_nhds) tendsto_const_nhds (fun i h=> (h (ordinates i)).elim)) -- X implicit missing from target
 exact tendsto_nhds_unique (avg_move zoom (A:=D') (fun a:A=>X (r a)) _ hv) (worldly Y H D G C c F P Ω zoom _root_.id (fun _=>u) tendsto_id tendsto_const_nhds p d)
end wide
end here
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
