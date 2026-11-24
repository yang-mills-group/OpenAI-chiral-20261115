import YM.SU5.Reconstruction.Sleet.Iolite
/-! # The Compass transfer of the interaction through full-power Wick aperture. NOT Mink analytic claim outside this budget. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5200
set_option synthInstance.maxSize 33000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers LightBudget Storm
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
local notation "W" => placement Λ
local notation "L" j:max=> lowland j 0
local notation "N" j:max=> flank j 0
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier Fock Lat Lifted Peaks Spire Tenant Vale
  SlabMark MeshClock Tapestry.Exhibition Tapestry.Altitude Metric
attribute [local instance] opCStarAlgebra
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker

variable (i₀ j b:Axis)(p:b≠j) (t:ℕ) {δ:ℝ} {r:Shard (marks (timeMesh Λ))} (q:thermal r<δ)
variable (B J:Cover) -- namespace tune
local notation "Ξ"=> ticket Y H G t
local notation "Ω"=>Soaring Y H V G C a χ j b
local notation "κ"=> sameRead Y H V G i₀ (C i₀) (wk i₀) t
local notation "V₀" A:max=> (Ξ (leg i₀ B A))
local notation "V₁" A:max=> (Ξ (reposition (tent Y H) J A))
local notation "R₁"=> Metric.ball 0 (thermal r)
variable {P:Set RSpace}
variable {S:Finset Cover}{z:SU.Slot}{o:Cover}{u d:ℕ}{f: Marks (tent Y H) true}
local notation "Mh" => bufferedHull Λ l t
local notation "D₀" => Mh (reflectedBox i₀ 0 (streetBox (tent Y H) B S))
local notation "D₁" => Mh (streetBox (tent Y H) J S)
local notation "χ'" => fromStrict f
variable (g:LinkCheck Y H V G i₀ (C i₀) (displacement Y H V G.history G.clipped a false (C a) χ i₀ (C i₀)) t B J S z o u d f δ)

private lemma atReceipt (x y: Dome (tent Y H))(p':ticket Y H G t (twin i₀ B J x y)= V₀ x * V₁ y):
    whiff Y H V G C a χ (V₀ x * V₁ y) = sameRead Y H V G i₀ (C i₀) (wk i₀) t (twin i₀ B J x y):= by
 rw [← p']; exact whiff_turn Y H V G C a χ i₀ (ticket Y H G t _) (ticket_loose ..)

variable {H₁ M P₁ P₂:ℂ→ℂ}
private lemma spots {r:Shard Gt} (h:AnalyticOnNhd ℂ M (Metric.ball 0 (thermal r)))(g: M 0≠0): ∀ w∈ Metric.ball 0 (thermal r),∀ᶠ z in 𝓝[≠] w,0<‖M z‖:=by
 intro z Z; simp_rw [norm_pos_iff]; by_contra! v
 apply g; apply h.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball ..|>.isPreconnected) Z v (Metric.mem_ball_self (thermal_pos r)) -- tune Convex 𝕜?

noncomputable abbrev entryFirst (t:ℕ)(i₀:Axis)(B:Cover)(x:Dome (tent Y H)):=ticket Y H G t (leg i₀ B x)
noncomputable abbrev entryThen (t:ℕ)(J:Cover)(x:Dome (tent Y H)):=ticket Y H G t (reposition (tent Y H) J x)
structure TraceSignal (i₀ j b:Axis)(z:SU.Slot)(t u d:ℕ)(S:Finset Cover)(o B J:Cover)(r:Shard (marks (timeMesh Λ)))(f:Marks (tent Y H) true) : Prop where
  captures : ∃ (x y a' b':Dome (tent Y H)) (F M M₁ G₁ : ℂ→ℂ),
     NoDecompose Y H V G i₀ (C i₀) (displacement Y H V G.history G.clipped a false (C a) χ i₀ (C i₀)) t B J z u d S o x y a' b' ∧
     Soaring Y H V G C a χ j b (entryFirst Y H G t i₀ B (fromStrict f)) (entryThen Y H G t J (fromStrict f)) r F ∧
     Soaring Y H V G C a χ j b (entryFirst Y H G t i₀ B (a'*x)) (entryThen Y H G t J (b'*y)) r M ∧
     Soaring Y H V G C a χ j b (entryFirst Y H G t i₀ B x) (entryThen Y H G t J y) r M₁ ∧ Soaring Y H V G C a χ j b (entryFirst Y H G t i₀ B a') (entryThen Y H G t J b') r G₁ ∧
       M₁ 0=0 ∧ 1/32≤ ‖F 0‖ ∧ 0<‖M 0-M₁ 0*G₁ 0‖∧
         -- at every point throughout the Ap. Isolated zeros not excluded.
         (∀ z'∈ Metric.ball 0 (thermal r),∀ᶠ z in 𝓝[≠] z',0<‖F z‖ ∧ 0<‖M z-M₁ z*G₁ z‖) ∧
         ∃ e:ℝ, 0<e ∧ ∀ᶠ z in 𝓝 (0:ℂ), (1/33:ℝ) ≤ ‖F z‖ ∧ e ≤ ‖M z-M₁ z*G₁ z‖

include g q p
lemma ReceiptLift: TraceSignal Y H V G C a χ i₀ j b z t u d S o B J r f:= by
 have h(x y)(p₁:x∈D D₀)(p₂:y∈D D₁):∃ F, Ω x y r F:=full_power Y H V G C a χ j b p (show allLift D₀ D₁ δ from g.spacing) g.coveredRegions.1 g.coveredRegions.2 r q p₁ p₂
 obtain ⟨x,y,a',b',l⟩:=g.see_basis
 obtain ⟨h0,h1,h2⟩:= witness_charge Y H V G i₀ (C i₀) (wk i₀) t B J l g.apart
 obtain ⟨F,F₀⟩:=h _ _ (domain_loose Y H G _ (ticket_mem Y H G g.first)) (domain_loose Y H G _ (ticket_mem Y H G g.second))
 obtain ⟨M,T₀⟩:=h _ _ (ticket_mem Y H G h2.left) (ticket_mem Y H G h2.right)
 obtain ⟨N',T₁⟩:=h _ _ (ticket_mem Y H G h0.left) (ticket_mem Y H G h0.right)
 obtain ⟨G',T₂⟩:=h _ _ (ticket_mem Y H G h1.left) (ticket_mem Y H G h1.right)
 let A(x:ℂ):= M x-N' x*G' x
 have hA:AnalyticOnNhd ℂ A R₁ := fun z Z=> (T₀.analytic _ Z).sub ((T₁.analytic _ Z).mul (T₂.analytic _ Z))
 have ht: (0:ℂ)∈ R₁:=mem_ball_self (thermal_pos _)
 have hF:1/32 ≤ ‖F 0‖:= by rw [Soaring.origin Y H V G C a χ j b p F₀, atReceipt Y H V G C a χ i₀ t B J _ _ g.paid]; exact g.answer -- tune
 have hm: N' 0=0 := by rw [Soaring.origin Y H V G C a χ j b p T₁,atReceipt Y H V G C a χ i₀ t B J _ _ h0.pair]; exact l.matterKernels
 have he: 0<‖A 0‖:=by
    unfold A; rw [Soaring.origin Y H V G C a χ j b p T₀,Soaring.origin Y H V G C a χ j b p T₁,Soaring.origin Y H V G C a χ j b p T₂]
    rw [atReceipt Y H V G C a χ i₀ t B J (a'*x) (b'*y) h2.pair,atReceipt Y H V G C a χ i₀ t B J x y h0.pair,atReceipt Y H V G C a χ i₀ t B J _ _ h1.pair]; exact l.operational
 refine ⟨x,y,a',b',F,M,N',G',l,F₀,T₀,T₁,T₂, hm,hF,he, fun z Z=> (spots F₀.analytic (norm_pos_iff.mp ((by norm_num:(0:ℝ)<1/32).trans_le hF)) z Z).and (spots hA (norm_pos_iff.mp he) z Z), ‖A 0‖/2,half_pos he,?_⟩ -- nesting flatten
 have hv:1/33< ‖F 0‖:=lt_of_lt_of_le (by norm_num) hF
 exact (((F₀.analytic 0 ht).continuousAt.norm.tendsto).eventually (le_mem_nhds hv)).and (((hA 0 ht).continuousAt.norm.tendsto).eventually (le_mem_nhds (by linarith:‖A 0‖/2 < ‖A 0‖))) -- orientation le_nhds tune
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
