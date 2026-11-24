import SatinThinPanther
import SatinThinBeaconPath
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/
variable {z A c:ℝ}




open Regis Head.Garland Head.Etch Lamour.Bridge Celeste Clock Hookah Hookah.Blaze

open Papal -- needed addgap namespace
set_option linter.unusedVariables false
-- probes fare template incumbent
variable (z:PlaqAxes→ℝ) {I:Type}[Fintype I]
local notation "xθ" s:max=>hat P.R.L P.x s
local notation "ρ" s:max=>Real.sqrt (hat P.R.L P.x s)
local notation "ℰ" s:max=> meterC (xθ s)
variable {A B b:ℝ} (E':Trip I)(K H:ℕ→ℕ) (P_ :Real.exp 1≤ P.x)
variable (a:ℝ)
variable {K H} {T:ℕ→Buffered.Family (tent Y P_)→ℕ→ℂ}{E:ℕ→ Buffered.Family (tent Y P_) →ℂ}(V:Universal Y P_ K H T E)
open Regis Circuit Head.Brecht
open YM.Stationary (Gaia)
namespace Travel
abbrev turnoverX (t:Trip I)(s:Signed)(b:Cover):Trip I:=⟨fun i=> affine s b (t.loc i),fun i=> s * t.orient i⟩
def playback (t:Trip I) (u:Axis)(b:ℤ): Trip I:= turnoverX t (Signed.mirror u) (2 • (b • step u))
abbrev hopping (t:Trip I)(b:Cover):Trip I:= turnoverX t 1 b
lemma turn_twice (T:Trip I)(s u:Signed)(b c:Cover): turnoverX (turnoverX T s b) u c=turnoverX T (u*s) (affine u c b):=by
 cases T; unfold turnoverX; congr 1; · ext i; simp [affine,Signed.act_mul]; try ring
 simp [mul_assoc]
lemma play_hopping (t:Trip I) (u:Axis)(b:ℤ): playback (playback t u 0) u b=hopping t (2 • (b • step u)):=by
 unfold playback hopping; rw [turn_twice,show Signed.mirror u * Signed.mirror u=1 from (by nth_rw 2 [← Signed.mirror_inv u]; rw [mul_inv_cancel])]; rw [zero_smul,smul_zero,affine,Signed.act_zero,zero_add]
lemma mapped_at (t:Trip I)(s:Signed)(b:Cover): (turnoverX t s b).tryN n=(t.tryN n).moves s (wrap n b):=by
 unfold turnoverX Trip.tryN Tour.moves; congr 1; funext j; simp [affine,wrap_signed]
lemma both_at {F:Trip I}(S:Trip I): (tapeBoth F S).tryN n=(F.tryN n).addStack (S.tryN n):=by unfold tapeBoth Trip.tryN Tour.addStack; congr 1; funext i; cases i <;> rfl
include V
lemma carried_vision (u:ℕ)(p:0 < hat P.R.L P.x u){W:Type}[Fintype W][Nonempty W](Q W':W→Trip I)
 (h:∀ i:I,Injective fun j=> (Q j).loc i)(f:∀ i:I,Injective fun j=> (W' j).loc i)
 (Yα:∀ i,∃ s t, Q i=turnoverX E' s t)(Yβ:∀ i,∃ s t, W' i=turnoverX E' s t) :
   |(∑ i:W, ∑ j:W, ultimate Y z (tapeBoth (Q i) (W' j)) K H A u) - ((Fintype.card W)*(ultimate Y z E' K H A u))^2| ≤ Fintype.card W* sunRank P.K.top.clip (padC z SU.group A (hat P.R.L P.x u)) (Fintype.card I):=by
 let P':=sunRank P.K.top.clip (padC z SU.group A (xθ u)) (Fintype.card I)
 let U(i j:W):= tapeBoth (Q i) (W' j); let N:ℝ:= Fintype.card W
 apply le_of_tendsto (((tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun j _=> (ultimate_guess Y z (U i j) K H A u).2).sub (((ultimate_guess Y z E' K H A u).2.const_mul N).pow 2)).abs)
 apply Nat.hyperfilter_le_atTop; let E:= (count_la Y u).comp V.pick.grow_i.tendsto_atTop
 filter_upwards [E.eventually (Filter.eventually_all.mpr fun i:I=> panel_spread (fun j:W=> (Q j).loc i) (h i)), E.eventually (Filter.eventually_all.mpr fun i:I=> panel_spread (fun j:W=> (W' j).loc i) (f i))] with i h1 h2
 apply le_of_tendsto (((tendsto_finsetSum _ fun i' _=> tendsto_finsetSum _ fun j _=> (scribe_here Y z (U i' j) H A u (K i)).2).sub (((scribe_here Y z E' H A u (K i)).2.const_mul N).pow 2)).abs)
 apply Nat.hyperfilter_le_atTop; filter_upwards [V.pick.grow_k.tendsto_atTop.eventually (ferry_later Y u (K i))] with k uK
 let n:= More (count Y u (K i)); let G:=RootBook Y (K i) (H k) u; let d:= Y.uv (H k)-u; obtain ⟨_,_,_,v,l⟩:=prices_plot Y u (K i) (H k) uK.enters
 let S:=P.V.L; let B:= S.mood d; let P'':= S.tied d; -- ensure no duplicate P'
 let Y':= padC z SU.group A (xθ u); let q:=Real.sqrt (xθ u)*coupling G.beta
 have hi:|q|≤ 2:= by
    have h:= Regis.Head.Etch.railB (β:=G.beta) v.1 v.2 p; rw [abs_of_nonneg (by have hh: (1:ℝ)/2 ≤ q:= h.1; linarith only [hh])]; exact h.2
 let M:=S.roof d
 have hv(T:W→Trip I)(t:∀ i,∃ s t,T i=turnoverX E' s t): Copied (E'.tryN n) (fun i=>(T i).tryN n):=by refine ⟨fun i=>?_⟩; obtain ⟨s,b,v⟩:=t i; rw [v]; exact ⟨s,(wrap n b), mapped_at E' s b⟩
 change |(∑ i, ∑ j, visionCost B P'' ((tapeBoth (Q i) (W' j)).tryN n) Y' q) - (N*visionCost B P'' _ Y' q)^2|≤ _; simp_rw [both_at]; exact increase_vision B P'' (M.2.1 n) (E'.tryN n) Y' _ q _ (M.2.2 n) hi (show Stationed (fun i=>(Q i).tryN n) from h1) (show Stationed (fun i=>(W' i).tryN n) from h2) (hv Q Yα) (hv W' Yβ)
end Travel
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Travel.carried_vision
