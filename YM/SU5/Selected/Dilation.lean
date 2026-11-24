import YM.SU5.Selected.Sealing
/-!
# Pointwise continuity of the interlevel maps into the final norm system

Dominated convergence against the *actual predecessor* measures under
`Coupon` at any paid entry in the history. Consequently against history
operator estimates. Qualify `ae` carefully: pair input field includes
SAME Cape output as before; no fake Lebesgue measure there. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Haro

section trans
variable {N P:Side}(G:Ratio N P)(A:StepData (More N) (More P))(j:ℕ)
variable (Q:Haro.SpaceM)(M:Male)(ho:Odd G.count.val)(q:Chi)(d β:ℝ)(l : Loom N)
local notation "Ψ" =>gathered G j Q.val M ho q d
variable {R:ℕ}(p:LaurentRadius j G.count R)(t:Measurable l)(a:0<d)(b:2*d< firstRadius SU.group) (g:A.patch.Branches A.kernel SU.group)
include ho

lemma collectPointwise (U : Fields P) (V: Fields N) : ∃ L : FC (Single N) →L[ℂ] FC (Single P), ∀ f:Mark N, (Ψ f U V)=L (f V) := by
  let D := ∑ F:Forest (ratio G), (subF G j Q.val M ho (middle G q d F U V)).toContinuousLinearMap
  let r:ℝ:=(Fintype.card (Forest (ratio G)):ℝ)⁻¹
  refine ⟨(r • D),fun f=>?_⟩
  rw [_root_.smul_apply]; unfold D; rw [ContinuousLinearMap.sum_apply]; rfl

include p
lemma gatherCost2 : ∃ C:ℝ,0<C∧∀ U (V:Fields N) (f:Mark N), ‖Ψ f U V‖ ≤ C*‖f V‖:=by
  obtain ⟨Z,c,h⟩:= subBill G j M ho p Q
  refine ⟨Z,c,fun u v f=>?_⟩
  letI : Nonempty (Forest (ratio G)):= Tree.select (ratio G) ho
  refine tollMean (u:=fun i=> before G j Q.val M ho q d f i u v) ?_
  intro i
  let A:= (middle G q d i u v); let L:= (subF G j Q.val M ho A).toContinuousLinearMap
  change ‖L (f v)‖ ≤_ ; apply (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ContinuousLinearMap.opNorm_le_of_unit_norm (𝕜:=ℂ) c.le fun x t=> h A x t.le

include t a b g
lemma pushPointwise {f : ℕ→Mark N} (h: ∀ i, Envelope (f i)) (C:ℝ)(hc:0 ≤ C)
    (p₀:∀ i, ∀ᵐ x:Orbit N ∂city N, ‖f i (drawn l x)‖≤C)
    (p₁:∀ᵐ x:Orbit N ∂city N,Tendsto (fun i=> f i (drawn l x)) atTop (𝓝 0)) (u:Fields P):
    Tendsto (fun i:ℕ=> pushMark G A j Q.val M ho q d β l (f i) u) atTop (𝓝 0) := by
  let DX(x: Orbit N):= A.density β u.1 x.1
  let L(i:ℕ)(x:Orbit N):= DX x • Ψ (f i) u (drawn l x)
  have he:Integrable DX (city N):= Env.integrableX (Env.along (g:=Prod.fst) (slice_env A β g u.1) measurable_fst) _
  obtain ⟨k,v,K⟩:=gatherCost2 G j Q M ho q d p
  have ht : Tendsto (fun i=> ∫ x, L i x ∂city N) atTop (𝓝 (∫ _x:Orbit N,(0 : FC (Single P)) ∂city N)):= by
    apply tendsto_integral_of_dominated_convergence (bound:=fun x=> ‖DX x‖*(k*C))
    · intro i; exact (pushIntegrable G A j Q.val M ho q d β l (f i) p t g a b (h i) u u.1).aestronglyMeasurable
    · exact he.norm.mul_const _
    · intro i; filter_upwards [p₀ i] with x p; unfold L; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((K u (drawn l x) (f i)).trans (mul_le_mul_of_nonneg_left p v.le)) (norm_nonneg (DX x))
    filter_upwards [p₁] with x px
    obtain ⟨L',Q'⟩:=collectPointwise G j Q M ho q d u (drawn l x)
    simp_rw [L,Q']; simpa using! (show Tendsto (fun i=>DX x • L' (f i (drawn l x))) atTop (𝓝 (DX x • L' 0)) from Tendsto.smul (tendsto_const_nhds) (L'.continuous.continuousAt.tendsto.comp px))
  simp only [integral_zero] at ht; exact ht.congr (fun i=> (outright G A j Q.val M ho q d β l p t g a b (f i) (h i) u).symm)
end trans

section settings
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable (S:Finset Cover)(s i k:ℕ)
local notation "Ω" i:max s:max=> side Y i s
local notation "Jm" m:max x:max=> drawn ((Y.voyage m).CapeT s) x
local notation "r"=>followBox (Λ:=Λ) (l:=l) S

include H
lemma dilationFixed (p:Spanned Y S s i k){f : ℕ→Swatch S}(C:ℝ)(hc:∀ i,‖f i‖≤C)
    (h:∀ᵐ x:Orbit (side Y i s) ∂city (side Y i s), Tendsto (fun k'=>present Y H s i S (f k') (Jm i x)) atTop (𝓝 0)):
    Tendsto (fun n=> coupon Y H S s i k (f n)) atTop (𝓝 0):=by
  let Q:=coupon Y H S s i k; let m:=momentm Y i (s+1); let Cape:= (Y.voyage i).CapeT s
  let X':=Λ.Ctor (Y.ir i); let Z:= (Ω i (s+1))
  have he:= (compact_coupon Y H S s i k); let T:= closure ( (Q:Swatch S →L[ℂ]Swatch (r)) '' (Metric.closedBall 0 C))
  have ht:IsCompact T:= he.isCompact_closure_image_closedBall _
  have h₁(n): Q (f n) ∈ T:= subset_closure ⟨_,mem_closedBall_zero_iff.mpr (hc n),rfl⟩ -- need existential hint
  have hp(x:Fields Z): Tendsto (fun n=>present Y H (s+1) i (r) (Q (f n)) x) atTop (𝓝 0):=by
    unfold Q; simp_rw [onSpanned Y H S s i k p]
    refine pushPointwise (apt (Y.ir i) Λ.block Λ.R.L s) _ _ (patternQ Y s i k) (( (Y.voyage i).X (Y.uv k)).gram (s+1)).J.M _ _ _ _ _ (Journey.legal _) ((Y.voyage i).ownership s).paid.bill (threshold Y).1 (threshold Y).2 ((Y.pilot_steps s i k).2.2) (fun a=> (presented Y H s i S (f a)).env) (spread S*C) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hc 0))) ?_ h x
    intro t; apply Filter.Eventually.of_forall; intro x; exact (present_bound ..).trans (mul_le_mul_of_nonneg_left (hc t) (Nat.cast_nonneg _))
  by_contra v
  rw [Metric.tendsto_nhds] at v; push Not at v
  obtain ⟨ε,e,q⟩:= v
  have hh: ∃ᶠ n in atTop,ε≤ ‖Q (f n)‖:=by simpa [Q] using q
  obtain ⟨ψ,u,w⟩:=extraction_of_frequently_atTop hh
  obtain ⟨z,g,e',t,hw⟩:=ht.tendsto_subseq (fun j=>h₁ (ψ j))
  have hk:z=0:=by
    apply present_inj Y H (s+1) i (r) (Roomy.seats p.2.2)
    funext i'; let L': Swatch (r) →L[ℂ] FC (Single (Ω i (s+1))):= ((LinearMap.proj i').comp (present Y H (s+1) i (r))).mkContinuous (spread (r)) (fun _=> present_bound ..)
    have z₀:= L'.continuous.continuousAt.tendsto (x:=z)|>.comp hw
    have zi: L' z=0:=tendsto_nhds_unique z₀ ((hp i').comp (u.comp t).tendsto_atTop)
    exact zi.trans (map_zero L').symm
  have hn: ε≤ ‖z‖:=ge_of_tendsto' hw.norm (fun i=> w (e' i))
  rw [hk,norm_zero] at hn; exact hn.not_gt e
end settings
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.pushPointwise
#print axioms YM.CF.Buffered.Afterglow.Tapestry.dilationFixed
