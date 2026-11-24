import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Bless
import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Shire

/-! # Buffered gauge probes can use translations compatible with the donor
of the paired period. (No claim about translation equivariance of an arbitrary
Pv929 Cape.)
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
local notation "Ω" => cell m B R.L
local notation "kT" => trunkY n b
local notation "kS" => buoy n
local notation "B'" => ActualSpine T ht W0 f kT
local notation "BT" => Actual T ht W0 f kT
local notation "Yb" i:max => dleaf R.L (hat R.L x i)
local notation "Γ" => StarPS kT
local notation "Φ" i:max => wage_B n b i R.L x
open Brace

namespace Donor
variable {F0:Scrolls B} (Y:Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0)
open Period Window
open scoped ComplexOrder
include ht
local notation "Tr" => Y.carnival ht

open Mir Mir.Trip Reflect Spark
variable {A r v:ℝ} (hp:∀ m,ScaleK A r (F0 m)) (hw:Budget B d v)
local notation "M_" => Vale.mesh m R.L (trunkY n b)
local notation "ξ" => cell m B R.L
local notation "Z₊" j:max => partitionZ (Y.gram j) U (W0 j)
local notation "T…" => RP.Str.shireF K.top.clip (T.a kT).threshold (Y.gram kT).beta (F0 M_) d 0 (↑(radiusB (hat R.L x kT)):ℝ) 1 (Brace.northZ M_ B)
local notation "Φ…" => probe ht Y
include hp hw

local notation "Xj" => Vale.mesh m R.L
lemma top_gauge(X: Pane (ξ kT)→ℂ)(v:Envelope X) :
    Φ… kT (bosonic _ X) = T… (Chaff.leer M_ B (bosonic (ξ kT) X)) / Z₊ kT := by
 let F:= bosonic (ξ kT) X; let Hp:=T.a kT
 unfold probe; rw [by_denominator]; apply congrArg (· / Z₊ kT)
 let β:= (Y.gram kT).beta; let u:ℝ:= radiusB (hat R.L x kT)
 let Z := RP.Str.hoistF K.top.clip (T.a kT).threshold β (F0 M_) d 0 u 1 (Brace.northZ M_ B) (Chaff.leer M_ B F)
 let g:=fun i:Orbit (ξ kT)=> inner ℂ (mateK (ξ kT)) (acts (F i.1) (denZ (Y.gram kT) U (W0 kT) i))
 have hz: Integrable Z (wheel M_ B):= scalar_of_interest _ _ _ _ _ _ _ _ _ X v (hp _) hw
 apply feastL (m:=M_) (T.a kT) (Y.rare kT) g Z hz; intro i hi
 unfold g; rw [Y.pull.boot, hue_top]; exact (Y.lives.eyes β i hi (F i.1)).trans (Chaff.clock_ix _ F K.top.clip (T.a kT) β _ _ _)

omit hp hw ht
lemma torScale (m B:Side)(χ:Cover) : torShift B (northTrip m ((wrap (More m)) χ)) = wrap (Domain m B) ((2*B.val) • χ) := by
 unfold torShift paneShift northTrip; rw [Ratio.root_embed, Ratio.root_embed, Ratio.embed_wrap, Ratio.embed_wrap,smul_smul]; change wrap (Domain m B) ((B.val*2) • χ) = _; rw [Nat.mul_comm B.val 2]
abbrev traceOfWalk (B N:Side) (χ:Cover) : Pane N→Pane N:= Lattice.pull 1 (wrap _ ((2*B.val) • χ))
include hp hw ht
open Carousel Push.GridApprox
private lemma start (X: Pane (ξ kT)→ℂ) (x':Cover) (v:Envelope X) : Φ… kT (bosonic _ (X ∘ traceOfWalk B _ x'))= Φ… kT (bosonic _ X) := by
 let ψ:= traceOfWalk B (ξ kT) x'; let q:= northTrip M_ (wrap _ x')
 have hψ: ψ =through B q:=by change _= Lattice.pull 1 _; rw [torScale M_ B]
 rw [Y.top_gauge ht hp hw (X ∘ ψ) (v.comp_env (continuous_pull ..).measurable),Y.top_gauge ht hp hw X v]; change T… (Chaff.leer M_ B (bosonic (ξ kT) (X ∘ ψ)))/ Z₊ kT= _; rw [hψ, translate_shire_scalar]

local notation "bu" j:max => buoyG V 1 2 6 N0 J q h Q D Tr j
local notation "Ga" j:max => garner V 1 2 6 N0 J q h Q D Tr j
omit hp hw in
private lemma step_translate (j:ℕ) (X: Pane (ξ j)→ℂ)(x':Cover)(v:Envelope X) :
    (Ga j) (X ∘ traceOfWalk B _ x') = (Ga j) X ∘ traceOfWalk B _ ((bu j).ratio.count.val • x') := by
 let b:= wrap (More (ξ j)) ((2*B.val) • x')
 let I:= (bu j)
 have ht:= actualG V 1 2 6 N0 J q h Q D Tr j; have h := I.isKernel ht.2.2 (Y.gram (j+1)).beta
 let y:= I.ratio.embed b
 have hp:traceOfWalk B _ (I.ratio.count.val • x')=Lattice.pull 1 y (K:=SU.group.El) := by unfold traceOfWalk; apply congrArg; unfold y b; rw [Ratio.embed_wrap, smul_comm]
 change back _ _ _= back _ _ _ ∘ traceOfWalk B _ (I.ratio.count.val • x'); rw [hp]; exact back_natural h v _ _ (prior_pull (G:=SU.group) 1 b) fun X W=> I.channel ht.2.2 1 b _ X W
lemma stroll (j:ℕ) (hj:j ≤ kT)(x':Cover) (X: Pane (ξ j)→ℂ)(v:Envelope X) :
    Φ… j (bosonic _ (X ∘ traceOfWalk B _ x'))= Φ… j (bosonic _ X) := by
 induction hj using Nat.decreasingInduction generalizing x' with
 | self => exact start ht Y hp hw X x' v
 | of_succ j p ih=>
  let F:= X ∘ traceOfWalk B (ξ j) x'; let g:=(bu j).ratio.count.val
  have he:= actualG V 1 2 6 N0 J q h Q D Tr j; have H:= (bu j).isKernel he.2.2 (Y.gram (j+1)).beta; let W:=Ga j
  change Φ… j (bosonic _ F)=_
  have ha(Z: Pane (ξ j)→ℂ)(v:Envelope Z) : Φ… j (bosonic _ Z)= Φ… (j+1) (bosonic _ (W Z)) := hhgo V 1 2 6 N0 J q h Q D Tr j p _ v
  rw [ha F (v.comp_env (continuous_pull ..).measurable), ha X v]; rw [show W F=(W X) ∘ traceOfWalk B _ (g • x') from step_translate ht Y j X x' v]
  exact ih (g • x') (W X) (back_env H v)
end Donor
end LocalLimit
end YM.CF.Py.Rate
