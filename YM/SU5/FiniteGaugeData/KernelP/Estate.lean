import YM.SU5.FiniteGaugeData.KernelP.Masque
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace KernelP
section dct
open MeasureTheory Measure Filter
variable {I:Type*}[MeasurableSpace I]{μ:Measure I}
-- package limit payment for levels first.
lemma budget_dct (f:ℕ→ I→ ℝ) {B F:I→ℝ}(B':Integrable B μ) {G:ℕ→ℝ}{Z:ℝ} (d:∀ n,∫ i, f n i ∂ μ=G n)(V:∀ n,Integrable (f n) μ)(H:∀ n i, ‖f n i‖≤ B i)(p:∀ i,Tendsto (fun n=>f n i) atTop (𝓝 (F i)))(v:Tendsto G atTop (𝓝 Z)): Integrable F μ ∧ ∫ i,F i∂ μ=Z:=by
 have a:= fun i=>(V i).aestronglyMeasurable; have ht:= fun n=> Eventually.of_forall (f:=ae μ) (H n); have b:= Eventually.of_forall (f:=ae μ) p; refine ⟨⟨aestronglyMeasurable_of_tendsto_ae _ a b,hasFiniteIntegral_of_dominated_convergence B'.2 ht b⟩,?_⟩; have he:=tendsto_integral_of_dominated_convergence B a B' ht b; simp_rw [d] at he; exact tendsto_nhds_unique he v
end dct
end KernelP
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
variable (H:Harbor Y h W' R Φ a)(X:Engine Y h W' R a H)(x:Decko Y h a)
abbrev flashH := (Φ s (helve Kₜ a x.val x.val)).re
local notation "C"=> flashH Y h s Φ a x
include H
lemma flash_metric : ‖H.leaf s x‖^2=flashH Y h s (Φ:=Φ) a x:=by rw [flashH,← H.measure]; exact InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ) _
include X
local notation "f" n:max i:max=> Φ (s+n) (planned Y h W' R a i n s x)
lemma flash_bound (k:ℕ): 0≤ (Φ (s+n) (planned Y h W' R a k n s x)).re ∧ (Φ (s+n) (planned Y h W' R a k n s x)).re≤ flashH Y h s (Φ:=Φ) a x:= by
 rw [← boasts Y h s W' R a n H X,← flash_metric Y h s W' R a H]; exact ⟨sq_nonneg _,pow_le_pow_left₀ (norm_nonneg _) (((unityAvg X.val (s+n) k).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (meanB ..))) _⟩
omit H X
variable (a₀:Axis)(p:Actors Y h a₀ W' R (A a₀))
local notation "U" => p.val.X
local notation "Σ"=> coronet Y h a₀ W' R A p
-- ANY assignment of Engines (not assuming continuity).
variable (V:∀ α:p.val.X, Harbor Y h W' R (coronet Y h a₀ W' R A p α) a)(Ξ:∀ α:p.val.X,Engine Y h W' R a (V α))
variable (α:p.val.X)
local notation "P'" i:max n:max=> issueH Y h n a₀ W' R (A a₀) p i
local notation "M"=> p.val.μ
include p
lemma integrated (s':ℕ)(k':W Kₜ) : Integrable (fun α:U=>(issueH Y h s' a₀ W' R (A a₀) p α k').re) p.val.μ ∧ ∫ α, (issueH Y h s' a₀ W' R (A a₀) p α k').re ∂ p.val.μ=(E s' k'.val).re:= by
 let f':= fun α:U=> issueH Y h s' a₀ W' R (A a₀) p α k'; haveI := p.property.normalized; have he:Continuous f':= vote_civil ..; have h': ∫ α,f' α ∂ M= E s' k'.val:= vote_pearl ..; refine ⟨(Complex.continuous_re.comp he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩; rw [← h']; exact integral_re (he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) -- field `Complex`? use binder `μ:=M`
local notation "C'" i:max n:max=> levelMass Y h s W' R a n (V i) (Ξ i) x
local notation "H₁"=> OriginalH Y h W' R A a
local notation "X₁"=>legacyEngine Y h W' R A a
include V Ξ
lemma momentBudget : ‖levelMass Y h s W' R a n (V α) (Ξ α) x‖≤flashH Y h s (Φ:=(Σ) α) a x:= by
 let D:= (Ξ α).val.GalleryH (s+n); let y:= (V α).leaf s x; unfold levelMass; rw [← flash_metric Y h s W' R a (V α), Real.norm_eq_abs,abs_of_nonneg (by positivity)]; change ‖planeP D y‖^2≤ ‖y‖^2; rw [← castC, Hills.yen]; exact pow_le_pow_left₀ (norm_nonneg _) (restrict_deflect y) _
lemma integrate_l : Integrable (fun α:U=>levelMass Y h s W' R a n (V α) (Ξ α) x) (M) ∧
    ∫ α:p.val.X,levelMass Y h s W' R a n (V α) (Ξ α) x ∂ M=levelMass Y h s W' R a n (OriginalH Y h W' R A a) (legacyEngine Y h W' R A a) x:= by
 let g:U→ ℝ:= fun α=>flashH Y h s (Φ:=(Σ) α) a x; let F (k:ℕ)(v:U):= ((P' v (s+n)) (planned Y h W' R a k n s x)).re
 refine budget_dct F (B:=g) ((integrated Y h W' R A a₀ p s (helve Kₜ a x.val x.val)).1) (fun n'=> (integrated Y h W' R A a₀ p (s+n) (planned Y h W' R a n' n s x)).2) (fun n'=> (integrated Y h W' R A a₀ p (s+n) (planned Y h W' R a n' n s x)).1) (fun k i=> ?_) (fun α=> plate_limit Y h s W' R a n (V α) (Ξ α) x) (plate_limit Y h s W' R a n (H₁) (X₁) x)
 rw [Real.norm_eq_abs,abs_of_nonneg]; exact (flash_bound Y h s W' R a n (V i) (Ξ i) x k).2; exact (flash_bound Y h s W' R a n (V i) (Ξ i) x k).1
lemma beloved : Integrable (fun α:U=> royalMass Y h s W' R a (V α) (Ξ α) x) (M) ∧ ∫ α,royalMass Y h s W' R a (V α) (Ξ α) x ∂ M= royalMass Y h s W' R a H₁ X₁ x := budget_dct (fun n i=> C' i n) (B:=fun α=>flashH Y h s (Φ:=(Σ) α) a x) ((integrated Y h W' R A a₀ p s (helve Kₜ a x.val x.val)).1) (fun i=>(integrate_l Y h s W' R A a i x a₀ p V Ξ).2) (fun i=>(integrate_l Y h s W' R A a i x a₀ p V Ξ).1) (fun i α=>momentBudget Y h s W' R A a i x a₀ p V Ξ α) (fun α=> much_power Y h s W' R a (V α) (Ξ α) x) (much_power Y h s W' R a H₁ X₁ x)
#print axioms beloved
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
