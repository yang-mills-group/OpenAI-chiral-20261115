import YM.SU5.Reconstruction.Cross.Acquisition
import YM.SU5.Reconstruction.Cross.Passage
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
/-!
# Coherent real-time content from the chart O, before Lorentz/locality

On a **same axis only** Mink time contour. All allocations/orders inducing this same Euclidean function on open neighborhood give same values at imaginary positions arbitrarily chosen.
Proof: continuation along complex rays from the real Euclidean atlas (one point at a time all independent coordinates together). This doesn't assume continuation to other-axis imaginary contours: not yet a relativistic representation. -/
variable {ι:Type*}[Fintype ι] (f : ι →Marks (tent Y H) false) (x: List ι)
section complex
open _root_.YM.SelectionAnalysis Vacancy.Average
local notation "Ξ" t:max => electedAtlas Y H V Q Qt t j C c
local notation "Ψ" t:max => arrived Y H V Q Qt t j C c
local notation "Ξi" t:max => requested Y H V Q Qt t j C c
local notation "Ωt" t:max x:max=> upGrade Y H s Q false (f x) t
local notation "X" k:max=> AcceptFrom Y H Q s k f x
local notation "Ρt"=> ι→ℝ
local notation "F" t:max=> fun i:ι=> upGrade Y H s Q false (f i) t
variable (A: AcceptFrom Y H Q s j f x)
variable (k₁ : ι→ℝ)
def slideR (z:ℂ):ι→ℂ:= fun i=> z * (k₁ i:ℂ)
lemma ticket_real (v:ι→RSpace): (fun z:ℝ=> realContour j v (z • k₁)) 0=v:=by simp only [zero_smul]; unfold realContour stepDrift; simp
lemma cont_real (v:ι→RSpace): Continuous (fun z:ℝ=> realContour j v (z • k₁)):=by
 apply continuous_pi; intro i; apply continuous_pi; intro k; unfold realContour stepDrift; by_cases h:k=j; · simp only [h,Function.update_self,Pi.smul_apply]; exact continuous_const.add (continuous_id.smul continuous_const)
 simp only [Function.update_of_ne h]; exact continuous_const
lemma re_ticket (v:ι→RSpace){z:ℂ}{t:ℕ}{g:∀ i,Gate Y H t j (upGrade Y H s Q false (f i) t)} (p:∀ i∈x,(g i).within_ (realContour j v (z.re • k₁) i)) : viewing Y H t j (F t) g x v (slideR k₁ z):=by
 rw [show z.re • k₁=(fun i=> z.re*k₁ i) from rfl] at p; rw [contour_ready]; simpa [slideR,Complex.mul_re] using! p
local notation "F₁"=> upGrade Y H s Q false
-- analytic along this ray, equivalence
lemma connected_across (B : AcceptFrom Y H Q s j f x) (p : x.Nodup) (v : ι→ Axis→ℝ) (q : v∈A.domain) (w : v∈B.domain) :
  (Ψ A.stage) (F A.stage) A.gate A.order v k₁=(Ψ B.stage) (F B.stage) B.gate B.order v k₁:=by
 let η(z:ℝ):ι→Axis→ℝ:= realContour j v (z • k₁)
 let T' (k:ℝ):Prop:=η k∈ A.domain ∩ B.domain
 have ht : 0∈ {k:ℝ|T' k}:= by change η 0 ∈ A.domain ∩ B.domain; rw [show η 0=v from ticket_real j ..]; exact ⟨q,w⟩
 obtain ⟨d,r,h⟩ := Metric.mem_nhds_iff.mp ((((A.isOpen.inter B.isOpen).preimage (cont_real j k₁ v))).mem_nhds ht)
 let S: Set ℂ:= {z| |z.re| < d}
 let C' (U: AcceptFrom Y H Q s j f x) (z:ℂ) := (Ξi U.stage) (F U.stage) U.gate U.order v (slideR k₁ z)
 have e: IsPreconnected S:=by
    have hs:S= Complex.reCLM ⁻¹' Ioo (-d) d:= Set.ext fun i=> (show |i.re| < _ ↔ -d < i.re ∧ i.re< d from abs_lt)
    rw [hs]; exact ((convex_Ioo _ _).linear_preimage _).isPreconnected -- tune
 have j0(z:ℂ)(l:z∈S) : z.re∈Metric.ball 0 d:=by change |z.re| < d at l; simpa [Metric.mem_ball,Real.dist_eq] using l
 have fE(U: AcceptFrom Y H Q s j f x)(p:A.domain ∩ B.domain ⊆ U.domain) : AnalyticOnNhd ℂ (C' U) S:=by
    intro z hz; have h' : ∀ i∈U.order,(U.gate i).within_ (η z.re i):= p (h (j0 _ hz)); let y₀:= slideR k₁ z
    refine (window_complex Y H V Q Qt U.stage j C c (F U.stage) U.gate U.order v (slideR k₁ z) ?_).comp (analyticAt_pi_iff.mpr (fun i : ι=> ?_))
    · exact re_ticket Y H Q s j f U.order k₁ v h'
    exact analyticAt_id.mul analyticAt_const
 have fU(z:ℝ)(hz:(z:ℂ)∈ S): C' A (z:ℂ) = C' B (z:ℂ):=by
   let t:= η z
   have hw : t∈ A.domain ∩ B.domain := h (j0 (z:ℂ) hz)
   unfold C'; rw [show slideR k₁ (z:ℂ)=(fun i=>(↑((z • k₁) i):ℂ)) by ext1 i; simp [slideR]]
   rw [euclidean_time Y H V Q Qt A.stage j C c _ A.gate A.order v _ hw.1, euclidean_time Y H V Q Qt B.stage j C c _ B.gate B.order v _ hw.2]
   exact differentRungs Y H V Q Qt s j C c f C c A.gate B.gate (A.schedule.trans B.schedule.symm) (A.schedule.nodup_iff.mpr p) (fun _ _=>rfl) A.large B.large A.travel B.travel hw.1 hw.2
 let t:=sideways 1
 have hz:t∈ S:=by simpa [S,t] using r
 rw [Mink_full Y H V Q Qt A.stage j C c (F A.stage) A.gate A.order v k₁ q, Mink_full Y H V Q Qt B.stage j C c (F B.stage) B.gate B.order v k₁ w]
 rw [show (fun i:ι=> sideways (k₁ i))=slideR k₁ t from funext fun i=> (by unfold t sideways slideR; rw [Complex.ofReal_one]; ring)]
 refine (fE A inter_subset_left).eqOn_of_preconnected_of_frequently_eq (fE B inter_subset_right) e (show (0:ℂ)∈S by simpa [S] using r) ?_ hz
 intro u
 have he: Tendsto ((↑) : ℝ→ℂ) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; · simpa only [Complex.ofReal_zero] using ((Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s:= Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with x (hx:0<x); exact Complex.ofReal_ne_zero.mpr hx.ne'
 obtain ⟨z,hz',a,vL⟩:= ((he.eventually u).and ((Filter.Eventually.and (p:=fun i:ℝ=> i>0) self_mem_nhdsWithin (q:=fun i:ℝ=>i<d) (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds r))))).exists -- eventually.
 exact hz' (fU z (show |(z:ℂ).re|< d by change |z| < d; rw [abs_of_pos a]; exact vL))
end complex
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.connected_across
