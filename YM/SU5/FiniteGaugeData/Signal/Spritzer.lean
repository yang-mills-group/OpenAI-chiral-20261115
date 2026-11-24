import YM.SU5.FiniteGaugeData.Signal.VolumePower
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake

/-! # Temperature charge. Convert absolute basis to `Gross` invoice.

 Keep β and common Ω in actual arrays and their comparison donor. All estimates on `Cashbox`
 election by the new stronger tariff. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
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

open FullBill Window Marks
open Pyx
open Girt

open Window Graph Period Jade.Earn Buffered.Reliance
namespace Preparation
local notation "q₀" => Chi.canonical
variable (P:Preparation)

open Signal.Kinetic Buffered Buffered.Afterglow Buffered.Afterglow.Journey
namespace Skyscraper
variable (P:Preparation){l:ℕ}{n:Side}(Y : Carousel P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.x n l)
variable (W:Cashbox P){A H C:ℝ}{S':Support (More n)}{j k d:ℕ}(s:j ≤ l)
local notation "O"=> Classical.choice (YM.Next.Rank.exists_budget SU.group)
local notation "S"=> Y.Y j
local notation "Z"=> Y.E j
local notation "m"=> Vale.mesh n P.R.L j
local notation "N"=> P.Ctor n j
local notation "x"=> hat P.R.L P.x j
local notation "T·" a:max=> Tableau (mesh n P.R.L j) (Y.E j) (Y.Y j) P.U (soaked (hat P.R.L P.x j)) a
local notation "R↑" σ v:max f:max=> Booted P.K.j (Y.E j) (Y.Y j) C H σ v f
variable (b:Tableau (mesh n P.R.L j) (Y.E j) (Y.Y j) P.U (soaked (hat P.R.L P.x j)) A)
variable (hp:1 ≤ H)(u:H ≤ P.h)(h:0 ≤ C)
include W b h hp u s
private lemma hot_inner (T:Support (More N))(f:Mark N) (w: Booted P.K.j (Y.E j) (Y.Y j) C H T k f): ‖markedRead f S (denZ Z P.U S)/partitionZ Z P.U S‖ ≤ C^k * Real.exp ((Universum.surcharge P + A)*sites N):= by
 let B:= soaked x; let g:= soaked (Y.E j).beta
 obtain ⟨e,wE⟩:= Universum.above_zone P j W; let V:= flagBill N (dleaf P.R.L x) (dleaf P.R.L x) (cashU P.W.C)
 obtain ⟨_,t0,tq,_,_⟩:= e.budget ((Y.E j).beta) (Y.sift j (s.trans Y.probed)); obtain ⟨-,_,hg,hg'⟩:= amplifier _ tq; let o:=Y.owns j (s.trans Y.probed); have hZ: (Y.E j).p.threshold=temp (hat P.R.L P.x j):=show _ from o.width ▸ (Y.val.boot j).1
 have he: ‖num0 P.U (Y.E j) S f‖ ≤ C^k *(Real.exp (V + (Fintype.card (Face (Per (More N))):ℝ)/2) * fullRate O (Y.E j) P.K.top.paths P.V.W.bar g):= Signal.Kinetic.charge (Carousel.loomActs P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Y j) (P.J.gran.trans (Y.roof j).size) (Carousel.expense P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Y j s P.height) (level_p ..|>.le) (cash_v _) hp u O (Carousel.footprint_B P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Y j s) hg hg' (hZ ▸ t0) f T w h
 let l:=vac0 P.U Z S; let Tr:= Real.exp (budgetCharge Z B (-A)); have hv:Tr≤‖l‖:= b.lowB
 rw [←Buffered.same_ratio,norm_div]; apply (div_le_iff₀ ((Real.exp_pos _).trans_le hv)).mpr; apply (he.trans (mul_le_mul_of_nonneg_left (Universum.raw_cap P j Y W s) (pow_nonneg h _))).trans
 apply le_trans _ (mul_le_mul_of_nonneg_left hv (mul_nonneg (pow_nonneg h _) (Real.exp_pos _).le)); unfold Tr; apply le_of_eq; rw [mul_assoc,←Real.exp_add]; congr 2; unfold B budgetCharge; rw [Universum.metric_mass]; ring

-- transfer widths pack from actor to tent stencils at μ, equation with physical dimensions.
omit W b h hp u s
-- specialize generically to native dimensions F not definitionally `K.c`.
def Narrowed {n:Side} (T:Support (More n))(d:ℕ):= ∀ i:Axis,∃ b:ℤ,∀ x'∈T,Afterglow.Chord b d (x' i)
lemma widen {n:Side} {a b:Support (More n)}(h:a⊆b)(v:Narrowed b d): Narrowed a d:= fun i=> by obtain ⟨c,hc⟩:= v i; exact ⟨c,fun k t=> hc k (h t)⟩

private lemma hoisted {a n':Side} (K:Calibration) (e:K.c a=n') (Q:Loom n') (X:Mark n'→ℂ) {b d:ℕ}{W:Support (More n')→ℕ→Mark n'→Prop}{C D A:ℝ} (pC:0 ≤ C)(pA:0 ≤ A)(T: Metered K a (e.symm ▸ Q) (fun v=> X (e ▸ v)) D)
    (g:∀ S':Support (More n'),∀ k f,W S' k f → ‖X f‖ ≤ C^k*Real.exp (A*(a.val:ℝ)^4))
    (h:∀ i:Axis, ∀ z:ℤ, ∀ S'⊆ band n' i z K.ℓ,∀ f:Mark n',∀ k,W S' k f→ AtSupport false S' f → W (S'.image ((plane i z).anon n')∪S') (k*2) (reflMark i z f*f))
    {S':Support (More n')}{f:Mark n'}(p:W S' b f)(u:AtSupport false S' f)(v:Narrowed S' d): ‖X f‖ ≤ C^b*magnified K A d:=by
 subst n'; exact VolumePower.shelter T h pC pA g v p u -- transports trivial
-- no margin binder needed, K always has it

-- notation for gross exponent determine. He in N/4 costs.
def gaugePrice (P:Preparation)(A:ℝ):= |Universum.surcharge P + A| * (4*(P.block.val:ℝ))^4
lemma gross_plan (A:ℝ): Real.exp ((Universum.surcharge P + A)*sites (P.Ctor n j)) ≤ Real.exp (gaugePrice P A * ((mesh n P.R.L j).val:ℝ)^4):= by
 apply Real.exp_monotone; apply (mul_le_mul_of_nonneg_right (le_abs_self _) (show 0 ≤ sites _ from by unfold sites; positivity)).trans_eq; unfold gaugePrice sites Preparation.Ctor cell CSide More; push_cast; ring -- mesh val_r unfolded?
include W b h hp u s
local notation "κcost"=> magnified
local notation "X" f=> markedRead f (Y.Y j) (denZ (Y.E j) P.U (Y.Y j)) / partitionZ (Y.E j) P.U (Y.Y j)
-- cast calibration costs from μ
lemma tipped {D:ℝ} (K:Calibration)(e:K.c m=N)(T: Metered K (mesh n P.R.L j) (e.symm ▸ S) (fun f=> (X ((e ▸ f): Mark N))) D){k d:ℕ} (T':Support (More N))(f:Mark N)(u': Booted P.K.j (Y.E j) (Y.Y j) C H T' k f)(p:AtSupport false T' f) (v:Narrowed T' d):
    ‖markedRead f S (denZ Z P.U S)/partitionZ Z P.U S‖ ≤ C^k * κcost K (gaugePrice P A) d := by
 -- use packing of NOR (moment.u)
 apply hoisted K e (Y.Y j) (fun f=> X f) h (show 0 ≤ gaugePrice P A by unfold gaugePrice; positivity) T ?_ ?_ u' p v
 · intro s' j' f g; exact (hot_inner P Y W s b hp u h s' f g).trans (mul_le_mul_of_nonneg_left (gross_plan P A) (pow_nonneg h _))
 intro i z s' a f k w t; rw [mul_two]; apply boots_merge (boots_reflection P.W.C (Carousel.credit_rule P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Y j s) (P.J.gran.trans (Y.roof j).size) (Carousel.loomActs P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Y j) (by rw [P.kJ]; omega) P.V.note w z i (zero_lt_one.trans_le hp)) (t.refl i z) w t
 exact Finset.disjoint_left.mpr (fun y a' b => Nat.not_lt_zero _ ((margin_separate i z K.buffer y y (image_subset_image a a') (a b)).trans_le (by rw [separation_self])))

omit P Y W h hp u s b
-- syntax retirement. add specialization `Course`
end Skyscraper
end Preparation
end LocalLimit
end YM.CF.Py.Rate

#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Skyscraper.tipped
