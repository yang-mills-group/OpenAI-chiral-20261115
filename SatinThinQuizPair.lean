import SatinFixedContrastNovember4
import SatinThinQuizLounge
/-!
# Milestone 15.IV. The actual and raw split prices for all these separated measurements.

We will keep (*even simultaneously*) width and grid limits on these fields, and compare
in the same CHIRAL dictionary (see `-FixedContrast`). And prove the result
is truly **not a product-of-means experiment either** if any matrix entry is
nonzero-- the one-point answers are zero. Include costs of the total-to-raw-marginal-comparison,
used here. `X` in the notation below is **projected packet
at finite width**, `X!` limiting *readPrism* and `χ'`
is a t-regulator reading, not to confuse with `P.chi` (equalities below). We have not
changed the state.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "λ'"=> P.enter 3 ξ
local notation "ℒ"=> Lead.Clan
local notation "k'"=> P.calibration
local notation "p[" t "]"=> P.singleState 3 t x
local notation "σ[" t "]"=> P.thinSplit x t
variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "W"=> P.soldTrumpet A c r n w
variable (T:P.HandleWith x c r A n)
local notation "B[" z "," i "]"=> P.sold_birth x A c r n w z i T
local notation "l₀" => ([false,true]:List Bool)
local notation "I₁" a:max i:max => ((W a i).kiss P 3)
variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x) (μ:ℝ)(a b:Lead.Clan)
variable (F U: SampleDose)
local notation "Φ" a:max t:max i:max=> P.prepared t (I₁ a i) F
local notation "Ψ" b:max t:max i:max=> P.prepared t (W b i) U
local notation "X" i:max a:max=> P.thinKet x (W a i) B[a,i] (flipDose F 3)
local notation "Y" i:max a:max=> P.thinKet x (W a i) B[a,i] U
local notation "X'" t:max i:max a:max=> P.thinGridKet x t (W a i) B[a,i] (flipDose F 3)
local notation "Y'" t:max i:max a:max=> P.thinGridKet x t (W a i) B[a,i] U
local notation "R₁" a:max=> DoseTravel.beam (G) F (P.earlierProfile x V w μ a)
local notation "R₂" a:max=> DoseTravel.beam (G) U (P.laterProfile x V w μ a)
local notation "X!" => P.readPrism x V w μ F U
local notation "X△" p:max q:max=> P.pointPrism x V w (q-p)
variable (t i:ℕ)
-- Both probes at heights c(n(i)) share all choices independent of query grid t≥ c(n(i)).
-- The painted entries price these SAME two independent smooth sweeps with the prescribed
-- mesh normalizations; they can be compared with the posed old experiment at each sufficiently large implementing height. The two kinds of experiments differ in their input reference stencils and birth heights, not in the posing protocol or consulting dictionary.

def reportPrism (i t:ℕ)(U':P.Test→ₗ[ℂ]ℂ): CrossRead:= Matrix.of (fun a b:ℒ => U' ((Φ a t i)*(Ψ b t i)))
local notation "χ'"=> P.reportPrism A c r n w F U

def thinJournal : CrossRead:= matchRoles (G) (fun a=>X i a) (fun b=>Y i b)
local notation "X☷"=> P.thinJournal x A c r n w T F U
local notation "t!" i:max => c (n i)
lemma report_regulator (K:P.Register) : χ' i t p[t] a b=
   P.spirits K 3 x (P.paintPair (I₁ a i) (W b i) t F.val U.val) :=by
 rw [P.paintPair_here]; unfold markPair; rw [← P.reviewWardPaint,← P.reviewWardPaint]; rfl
lemma report_scanned (V':P.Test→ₗ[ℂ]ℂ) : χ' i t V' a b= V' (P.markPair (I₁ a i) (W b i) t F.val U.val):=by
 unfold markPair; rw [← P.reviewWardPaint,← P.reviewWardPaint]; rfl
variable (u:0<μ)(v:backwardSite F μ)(p:forwardSite U μ)
-- Quantize and take grid limit within the authorized measurements. Also simultaneously.
structure AuthorizedPair : Prop where
 -- the exact seam and support at every ordered price. eventually reads also include
 -- continuity transfer on this very Session, to yield `commonWell` integrals (ThinSeam).
 epoch : ∀ᶠ i in atTop,∀ a b:ℒ,P.ThinSeam x (W a i) (W b i) B[a,i] B[b,i] F U
 widths (ε:ℝ)(p:0<ε) : ∀ᶠ i in atTop,∀ a:ℒ,P.ThinFootprints (fun j=> I₁ a j) i ε ∧ P.ThinFootprints (W a) i ε
 grid : ∀ᶠ i:ℕ in atTop,Tendsto (fun t=> χ' i t p[t]) atTop (𝓝 (X☷ i))
 width : Tendsto X☷ atTop (𝓝 X!)
 during (t:ℕ→ℕ)(u:∀ᶠ i in atTop,t! i ≤ t i) : Tendsto (fun i=> χ' i (t i) p[t i]) atTop (𝓝 X!)
 -- smeared fields
 leftM (a:ℒ) : Tendsto (fun i=> X i a) atTop (𝓝 (R₁ a))
 rightM (a:ℒ) : Tendsto (fun i=> Y i a) atTop (𝓝 (R₂ a))
 bothM (a:ℒ)(t:ℕ→ℕ)(u:∀ᶠ i in atTop,t! i ≤ t i): Tendsto (fun i=> X' (t i) i a) atTop (𝓝 (λ' (R₁ a))) ∧ Tendsto (fun i=> Y' (t i) i a) atTop (𝓝 (λ' (R₂ a)))
 -- centered=0 explicitly. Comparison single in `epoch`. Not a factorized
 -- *spatial* criterion! The comparison returns both same one-body zeros and zero throughout paired prices.
 bothZero (a:ℒ)(i t:ℕ)(h:t! i≤t): p[t] (Φ a t i)=0 ∧ p[t] (Ψ a t i)=0
 ward : ∀ᶠ i in atTop,∀ t:ℕ, t! i ≤ t → ∀ (M:P.Test→ₗ[ℂ]ℂ), Factors k' M→MatterWard k' M∨GaugeWard k' M→ (∀ a:ℒ, M (Φ a t i)=0 ∧ M (Ψ a t i)=0) ∧ χ' i t M=0
 comparison : ∀ᶠ i in atTop,∀ t:ℕ, t! i ≤ t → (∀ a:ℒ,σ[t] (Φ a t i)=0 ∧ σ[t] (Ψ a t i)=0)∧ χ' i t σ[t]=0
 -- Actual single on projected packets also zero. This registers a CONNECTED price if price≠0.
 centered_seams (a:ℒ) : ∀ᶠ i in atTop, star (inner ℂ Ω (X i a))=0 ∧ inner ℂ Ω (Y i a)=0
 centered (a:ℒ) : star (inner ℂ Ω (R₁ a))=0 ∧ inner ℂ Ω (R₂ a)=0
 -- actual plus-order kernel prices
 kernel (a b:ℒ) (p q:ℕ→ Vantage)(f g:Vantage)(u:Tendsto p atTop (𝓝 f))(v:Tendsto q atTop (𝓝 g))(e:f 3<g 3):
   Tendsto (fun i=> P.commonWell 3 x (usher (I₁ a i) (W b i)) (usher (p i) (q i)) l₀) atTop (𝓝 ((X△ f g) a b))
 integral (a b:ℒ) : X! a b = ∫ p:Vantage,∫ q:Vantage,(F.val p:ℂ)*(U.val q:ℂ)*(X△ p q) a b
 high : Tendsto (fun i=>t! i) atTop atTop

include R J u v p
private lemma allEpoch : ∀ᶠ i in atTop,∀ a b:ℒ,P.ThinSeam x (W a i) (W b i) B[a,i] B[b,i] F U:= eventually_all.mpr fun a=> eventually_all.mpr fun b=> P.illuminate_seam x A c r n w V g h T R J μ a b F U u v p

private lemma soonerVictory (t:ℕ→ℕ)(q:∀ᶠ i in atTop,t! i ≤ t i) : Tendsto (fun i=> χ' i (t i) p[t i]) atTop (𝓝 X!):= by
 have e:Tendsto t atTop atTop:= tendsto_atTop_mono' _ q R.fusion.high.tendsto_atTop
 refine tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=>?_
 have hp:= (((P.illuminate_backward x A c r n w V g h T R J μ a F u v).2 t e).inner (𝕜:=ℂ) ((P.illuminate_forward x A c r n w V g h T R J μ b U u p).2 t e)); rw [(λ').inner_map_map] at hp
 exact hp.congr' (((P.illuminate_seam x A c r n w V g h T R J μ a b F U u v p).and q).mono fun i y=> (y.1.raw (t i) y.2 y.2).symm)
omit J u v p in
private lemma soldZero(a:ℒ)(i t:ℕ)(p:t! i≤t): p[t] (Φ a t i)=0 ∧ p[t] (Ψ a t i)=0:=
 ⟨(P.illuminate_zero x A c r n w V g h T R a F i t p).2,(P.illuminate_zero x A c r n w V g h T R a U i t p).1⟩
private lemma gone (a:ℒ) : ∀ᶠ i in atTop, star (inner ℂ Ω (X i a))=0 ∧ inner ℂ Ω (Y i a)=0 := by
 filter_upwards [allEpoch P x A c r n w V g h T R J μ F U u v p] with i t'
 let q:= (t' a a).single; have hz:= (eventually_ge_atTop (t! i)).mono (fun t h=> P.soldZero x A c r n w V g _ T R F U a i t h)
 exact ⟨tendsto_nhds_unique q.1 (tendsto_const_nhds.congr' (hz.mono fun i h=> h.1.symm)), tendsto_nhds_unique q.2 (tendsto_const_nhds.congr' (hz.mono fun i h=> h.2.symm))⟩
private lemma blocked : ∀ᶠ i in atTop,∀ t:ℕ,t! i ≤ t → ∀ M:P.Test→ₗ[ℂ]ℂ, Factors k' M→MatterWard k' M∨GaugeWard k' M→(∀ a:ℒ, M (Φ a t i)=0 ∧ M (Ψ a t i)=0) ∧ χ' i t M=0:= by
 filter_upwards [allEpoch P x A c r n w V g h T R J μ F U u v p] with i u t y M w l
 refine ⟨fun a=> ⟨((u a a).split t y y M w l).1,((u a a).split t y y M w l).2.1⟩,?_⟩; ext1 a b; exact ((u a b).split t y y M w l).2.2
omit R J u v p in
lemma invertWidth (A:ℕ→P.Apron)(e:P.thicknessZero A):P.thicknessZero (fun i=> (A i).kiss P 3):= e
lemma authorizePair : P.AuthorizedPair x A c r n w V T μ F U:= by
 let f(a):=P.illuminate_backward x A c r n w V g h T R J μ a F u v
 let q(a):=P.illuminate_forward x A c r n w V g h T R J μ a U u p
 let e:= allEpoch P x A c r n w V g h T R J μ F U u v p
 have hg:= R.fusion.high.tendsto_atTop; have hw:=blocked P x A c r n w V g h T R J μ F U u v p
 refine ⟨e,?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · intro ε u; refine eventually_all.mpr fun a:ℒ=> (P.thin_qualify (fun i=> I₁ a i) (P.invertWidth _ (R.slender a)) ε u).and (P.thin_qualify _ (R.slender a) ε u)
 · exact e.mono fun i h=> tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> (h a b).price
 · exact tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> (f a).1.inner (𝕜:=ℂ) (q b).1
 · exact P.soonerVictory x A c r n w V g h T R J μ F U u v p
 · exact fun a=>(f a).1
 · exact fun a=>(q a).1
 · exact fun a t y=> ⟨(f a).2 t (tendsto_atTop_mono' _ y hg), (q a).2 t (tendsto_atTop_mono' _ y hg)⟩
 · exact P.soldZero x A c r n w V g h T R F U
 · exact hw
 · exact hw.mono (fun i z t v=> z t v σ[t] (P.thin_comparator_LocalFieldBounds x t).1.factors (Or.inr (P.thin_comparator_LocalFieldBounds x t).2.2.1))
 · exact P.gone x A c r n w V g h T R J μ F U u v p
 · exact fun a=> by
      have hj:= P.gone x A c r n w V g h T R J μ F U u v p a
      have hu:Tendsto (fun i:ℕ=>Ω) atTop (𝓝 Ω):= tendsto_const_nhds
      exact ⟨tendsto_nhds_unique ((hu.inner (f a).1).star) (tendsto_const_nhds.congr' (hj.mono fun i z=> z.1.symm)), tendsto_nhds_unique (hu.inner (q a).1) (tendsto_const_nhds.congr' (hj.mono fun i z=> z.2.symm))⟩
 · exact fun a b _ _ _ _=> P.illuminate_curve x A c r n w V g h T R J a b
 · exact fun a b=> P.illuminate_price x A c r n w V g h T R μ a b F U u v p
 · exact hg
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.report_regulator
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.authorizePair
