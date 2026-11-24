import ForceSatin.Pocket
import ForceSatin.ChannelPrice
import ForceSatin.Coupon
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- on Board ledger, authority can be Stamp.growth from `Credential` & Theta copies. RootGauge only used on wash, not intended when composing with another root transaction without checking.
structure Milage (s i k:ℕ)(rate gust F:ℝ) {c:Side}{r:Lattice.Ratio c (More (count Y s i))}(T:Tiling c (count Y s i) r) (Φ:Pane (count Y s i)→ℝ):Prop where
 carries: RG.Envelope Φ
 cold: RootGauge r Φ
 price: ∃ U V F1 F2:ℝ,U+V+trend*F2^2≤ F ∧
   ∃ W:Support c→Finset (Cell (More (count Y s i)))→ Altar SU.group (More (count Y s i))→ℝ,
    (∀ A D,ContDiff ℝ 1 (W A D)) ∧ (∀ A D x, |W A D x|≤F1) ∧ (∀ A D x, ‖fderiv ℝ (W A D) x‖ ≤ F2) ∧
    (∀ A D,TreeLease (P.V.L.mood (Y.uv k - s)) (P.V.L.tied (Y.uv k - s)) (Uₛ s i k).p T.forest (radiusB (ℶ s)) rate (Uₛ s i k).beta (tuition pio (ℶ s)) (U+snags r (radiusB (ℶ s)) A D+gust*D.card) (sax (ℶ s)) A D Φ (W A D)) ∧
    (∀ A D,plumeCost (P.V.L.mood (Y.uv k - s)) (P.V.L.tied (Y.uv k - s)) (W A D) 1 ≤ V)
variable {s i k:ℕ}(rate fee:ℝ)(K:ℝ→ℝ)(p0:0<rate)(g0:rate≤1)(hK:PL K)
include p0 g0 hK
def mountain (s i k:ℕ) (U:Pane (count Y s i)):= let A:=gram Y s i k
   Real.exp (-A.path.inChannels A.funds A.p A.beta U+greyFee Y fee s i k U)
abbrev lodgeView (s i k:ℕ):= goods (P.V.L.path (Y.uv k-s)) π₀ (Uₛ s i k).p (Uₛ s i k).beta (flagCup (Uₛ s i k).p π₀ (Uₛ s i k).beta) (fee*((walls pio (ℶ s):ℕ):ℝ)^4) (sax (ℶ s)) (n:=More (count Y s i))
abbrev grassClear (s i k:ℕ):= Fineness.gaugedBase P.L (Uₛ s i k).beta (More (count Y s i)) (P.V.L.H (Y.uv k-s))+(ℶ s)^(-yieldA) *sites (nₛ s i)

omit p0 g0 hK
lemma mountainLease (v:s≤Y.uv k) : Envelope (mountain Y fee s i k):=by
 let U:=gram Y s i k; let V:=prices_plot Y s i k v; unfold mountain; dsimp only; rw [V.2.2.1,V.2.1]; exact env_reg (P.V.L.mood (Y.uv k - s)) -- GramM yy notations

include p0 g0 hK in
lemma hollowBank : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤ Y.uv k → ∀c:Side,∀ r:Lattice.Ratio c (More (nₛ s i)),coveredWidth pio (ℶ s) r→ ∀ (T:Tiling c (count Y s i) r)(F:ℝ)(Φ:Pane (count Y s i) → ℝ), Milage Y s i k rate (K (ℶ s)) F T Φ →
    (∫ U:Pane (count Y s i),(lodgeView Y fee s i k U)*(Real.exp (Φ U))∂prior SU.group _) ≤ Real.exp (grassClear Y s i k+F):=by
 let I:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let T₀:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a:=|T₀|
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le
 filter_upwards [(stage_slope P.V P.x).eventually (Gentle.offering P.K.top.clip R' P.L P.chart a P.R.L (V.L.mood 0).width hv V.W.bar (abs_nonneg T₀) rate p0 g0 K hK fee 1 zero_le_one)] with s q i k ht c r e T F Φ hp
 let N:= count Y s i; let G:=More N; let t:= Y.uv k-s; let A:= gram Y s i k; let Z:= P.V.L.H t; let Hm:=V.L.roof t
 obtain ⟨he,hT,hJ,f,_⟩:= prices_plot Y s i k ht
 have hV: A.p.threshold=temp (hat P.R.L P.x s):= he ▸ (Y.meter.boot s).1
 obtain ⟨U,U0,P₁,P₂,E,f0,v0,p1,p2,e0,w⟩:=hp.price
 apply (q r.count T.odd_width e.1 e.2 A.p A.beta f hV G c r T.fit rfl (V.L.tied t) (V.L.mood t) (Hm.2.1 G) V.W.reserve (fun i=> (YM.Fineness.stairEstimate Z P.K.width.le Hm.1.2.1 i).trans (le_abs_self T₀)) hp.carries hp.cold T.forest U U0 P₁ P₂ f0 v0 p1 p2 (by simpa only [one_mul] using e0) w).trans
 apply Real.exp_monotone; unfold grassClear Gleam.Roof Fineness.gaugedBase; rw [Pannier.shadowLie,sites_as_price]; linarith only [E]
-- use lemma `min` Envelope on cut costs keyed by pull. charge actual integrand via pointwise holds at every contender
variable {N:Side}
private lemma minEnv {F G:Pane N→ℝ}(h:Envelope F)(p:Envelope G): Envelope (fun v=> min (F v) (G v)):= _root_.YM.CF.Girt.kitE F G min (by fun_prop) h p -- namespace
-- avoid Lean min' notation. nonempty Index from Signed
lemma minimumView (Φ:Signed→Pane N→ℝ)(h:∀ s,Envelope (Φ s)) : ∃ Y:Pane N→ℝ,Envelope Y ∧ ∀ x, (∀ σ, Y x≤Φ σ (silhouette σ x)) ∧ (∃ σ,Y x=Φ σ (silhouette σ x)):=by
 let f(s:Signed)(x:Pane N):= Φ s (silhouette s x)
 have hf(a):Envelope (f a):=by obtain ⟨p,c,v⟩:=h a; exact ⟨p.comp (Wilson.continuous_pull ..).measurable,c,fun x=> v _⟩
 suffices E : ∀ L:Finset Signed,∃ Z:Pane N→ℝ, Envelope Z ∧ ∀ x, (∀ σ∈L,Z x≤ f σ x) ∧ (∃ σ,Z x=f σ x) by obtain ⟨Z,e,p⟩:= E univ; exact ⟨Z,e,fun x=>⟨fun i=>(p x).1 i (mem_univ i),(p x).2⟩⟩
 intro L; induction L using Finset.induction_on with
 | empty=> exact ⟨f 1,hf 1,fun _=>⟨by simp,1,rfl⟩⟩
 | @insert i L e ih=>
    obtain ⟨Z,h,p⟩:=ih
    refine ⟨fun x=> min (f i x) (Z x),minEnv (hf i) h,fun x=>⟨fun j v =>?_,?_⟩⟩
    · exact (mem_insert.mp v).elim (fun w=>w.symm ▸ min_le_left ..) ((min_le_right ..).trans ∘ (p x).1 j)
    rcases le_total (f i x) (Z x) with h|h; exact ⟨i,min_eq_left h⟩; dsimp only; rw [min_eq_right h]; exact (p x).2
include p0 g0 hK in
lemma lake_credit : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤ Y.uv k → ∀c:Side,∀ r:Lattice.Ratio c (More (nₛ s i)),coveredWidth pio (ℶ s) r→ ∀ (T:Tiling c (count Y s i) r)(F:ℝ)(Φ:Signed→Pane (count Y s i) → ℝ), (∀ σ,Milage Y s i k rate (K (ℶ s)) F T (Φ σ)) → ∀ (Z:Orbit (count Y s i)→ℝ) (W:ℝ), AEStronglyMeasurable Z (city (nₛ s i)) →
    (∀ᵐ x ∂city (nₛ s i), 0≤ Z x ∧ ∀ σ:Signed,Z x ≤ (mountain Y fee s i k x.1)*Real.exp (W+Φ σ (silhouette σ x.1))) →
    Integrable Z (city (nₛ s i)) ∧ (∫ U:Orbit (count Y s i), Z U∂city (count Y s i)) ≤ Real.exp (grassClear Y s i k+F+W):=by
 filter_upwards [hollowBank Y rate fee K p0 g0 hK] with s h i k u c r e T B Φ v Z W ht E
 let N:=nₛ s i; let H:=mountain Y fee s i k; let f:= lodgeView Y fee s i k; let μ:=city N; let ξ:= prior G5 (More N); let V:= grassClear Y s i k+B
 obtain ⟨g,hg,hI⟩:= minimumView Φ (fun i=>(v i).carries); let F(u):=H u*Real.exp (g u); let X(x:Orbit N):=F x.1 * Real.exp W
 have he(p:Pane N→ℝ)(u:Envelope p):Envelope (Real.exp ∘ p) := u.exp
 have hF: Envelope F:= (mountainLease Y fee u).mul (he g hg)
 have hv:AEStronglyMeasurable (fun x:Orbit N=>F x.1) μ:= (hF.meas.comp measurable_fst).aestronglyMeasurable
 have hx:Integrable X μ:= ((measurePreserving_fst (μ:=ξ) (ν:=depot N)).integrable_comp_of_integrable (hF.integrable ξ)).mul_const _
 have hh : Z ≤ᵐ[μ] X:= E.mono fun i h=>by obtain ⟨σ,t⟩:= (hI i.1).2; unfold X F; rw [t]; exact (h.2 σ).trans_eq (by rw [Real.exp_add]; ring) -- may need H
 have hZ: Integrable Z μ:=hx.mono ht (by filter_upwards [hh,E] with i g e; rw [Real.norm_of_nonneg e.1,Real.norm_of_nonneg (e.1.trans g)]; exact g)
 refine ⟨hZ,(integral_mono_ae hZ hx hh).trans ?_⟩ -- tune
 unfold X; rw [integral_mul_const, usesPrior _ (hF.integrable ξ), Real.exp_add (grassClear .. + B)]
 apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
 let Z':= prices_plot Y s i k u
 let R:=gram Y s i k; let P0:= P.V.L.path (Y.uv k-s); let Q:= regenerate P0 π₀ R.p R.beta (flagCup R.p π₀ R.beta) (fee*((walls pio (ℶ s):ℕ):ℝ)^4) (sax (ℶ s)) (n:=More (count Y s i))
 have hX : H= Q:=by unfold H Q mountain greyFee; dsimp only; rw [Z'.2.1,Z'.2.2.1]
 change (∫ x:Pane N,H x*Real.exp (g x) ∂ ξ)≤ _; rw [hX]
 apply le_trans (le_of_eq (Eq.symm ?_)) (forWind (p:=R.p) (fuel:=(fee*((walls pio (ℶ s):ℕ):ℝ)^4)) (κ:=flagCup R.p π₀ R.beta) (β:=R.beta) (v':=sax (ℶ s)) (P.V.L.mood (Y.uv k - s)) hg (Real.exp V) 1 ?_)
 · apply integral_congr_ae; filter_upwards with t; change Q _*Real.exp (1*g t)=_; rw [one_mul]
 intro σ; have hf:Envelope f:= env_grow (P.V.L.mood _)
 apply (integral_mono_of_nonneg (Eventually.of_forall (fun x=>mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) ((hf.mul (he _ (v σ).carries)).integrable _) (Eventually.of_forall fun x=>?_)).trans
      (h i k u c r e T B (Φ σ) (v σ))
 change f x* _ ≤ f x*_; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
 apply Real.exp_monotone; rw [one_mul]; have hy:= (hI (pull σ 0 x)).1 σ; rw [silhouette,pull_pull,mul_inv_cancel,affine,Signed.act_zero, add_zero,pull_id] at hy; exact hy
#print axioms lake_credit
end Papal
end LocalLimit
end Rate
end YM.CF.Py
