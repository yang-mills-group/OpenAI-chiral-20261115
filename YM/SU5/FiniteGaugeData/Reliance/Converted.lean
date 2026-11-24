import YM.SU5.FiniteGaugeData.Reliance.Transfer
import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Bless
/-! # Convert heat comparison to strong high-level volume bills.

Sharp certificate throughout. Heat certificate s late uniformly on Y.Price cone (threshold UV
depends on s, and cone at row starts when kick paid); no new diagonal coupled with aperture claims.
Useful to transfer local sup & flag-weight budgets using this VERY partner (without its own election).
Heat beta at s is not sharp, but donor still has `Y.heatGap` `priceH.compare_density` etc and
has own raw `owns` and matching to x as used. -/
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

namespace Preparation
local notation "q₀" => Chi.canonical
variable {P : Preparation} {F : (s:Side)→ Scree.Loom s → Prop} (Y:Course P F)

namespace Course
variable (i k j : ℕ)
local notation "Ξ" => Y.voyage i
local notation "U₀" => P.U
local notation "N₀" => (Ξ).funds
local notation "m₀" => Y.ir i
local notation "CS" => P.Ctor (Y.ir i)
local notation "kt" => Y.uv k
local notation "Xv" => (Ξ).X (Y.uv k)
local notation "Χ" j => (Xv).gram j
local notation "Qv" => (Ξ).CapeT
local notation "T" => Y.meter
local notation "Yr" => Vale.mesh m₀ P.R.L

open Window Graph Period Jade.Earn

variable (W:Cashbox P)
local notation "Ψ" k:max p:max=> (Y.voyage i).Q k p
local notation "Z" j:max p:max=> ((Y.voyage i).Q k p).gram j
local notation "X'" i:max=> hat P.R.L P.x i
-- decay with arbitrary s threshold
lemma near_room (V:ℝ) :
    ∀ᶠ k:ℕ in atTop,∀ i (p:(Y.voyage i).kick ≤ k),
        Donor.outage Y.meter j (Y.ivory k) (Y.ir i) ≤ Real.exp (budgetCharge (((Y.voyage i).X (Y.uv k)).gram j) (soaked (hat P.R.L P.x j)) (-V))/2 :=by
 let z:= 3*strengthLog (soaked (hat P.R.L P.x j))-V
 let v:= -z*postage P.block P.R.L j; let Q:= Y.meter; let V' := Donor.volumePrice Q j + 1
 let f:=Donor.horizontalPrice Q j -- Hor binder dims
 filter_upwards [Y.UV.tendsto_atTop.eventually (collapse P.b (Real.log_pos (by norm_num : (1:ℝ) < 2)) (by norm_num : (0:ℝ) < 1/2) f (V'+v))] with k h i t
 specialize h (Y.ir i) ((Y.voyage i).domain k t)
 let m:= (Y.ir i); let I:=Y.ivory k; let G:= ((Y.voyage i).X (Y.uv k)).gram j
 have he : budgetCharge G (soaked (X' j)) (-V) = -(v*game m):=by
    have he : massMeter (P.Ctor m j)=sites (P.Ctor m j):=by unfold massMeter sizes sites; rw [Nat.cast_pow]
    change massMeter (P.Ctor m j)*(3*_+-V)=_; rw [he,sites_postage]; unfold v z; ring
 unfold Donor.outage; rw [he]; change f * decay I _ * Real.exp (V'*game m) ≤ _
 rw [add_mul,Real.exp_add] at h
 have hh: f * decay I (Real.log 2) * Real.exp (V'*game m)* Real.exp (v*game m)≤ (1:ℝ)/2:= by rwa [mul_assoc (_*_)] -- tune
 apply le_trans ((le_div_iff₀ (Real.exp_pos _)).mpr hh); rw [Real.exp_neg, ←one_div]; exact le_of_eq (by ring) -- 1 ÷ etc

lemma diffuser (g v:ℝ)(A B:GramM (cell (Y.ir i) P.block P.R.L j)) : Real.exp (budgetCharge A g (-(v+1)))≤ Real.exp (budgetCharge B g (-v))/2:=by
 let N:= massMeter (P.Ctor (Y.ir i) j); let b:=v-3* strengthLog g; have h:= exp_half_extra b (show 1≤N from money_pos _)
 let y:=3*strengthLog g
 rw [show budgetCharge A g (-(v+1))=-(b+1)*N from ?_, show budgetCharge B g (-v)= -b*N from ?_]; exact h
 all_goals unfold budgetCharge; unfold b N; ring -- defeq K.Ctor vs cell

local notation "O"=> Classical.choice (YM.Next.Rank.exists_budget SU.group)

include W
lemma passing : ∃ A:ℝ,0 < A ∧
    (∀ i k,(Y.voyage i).kick ≤ k → ∀ j ≤ Y.uv k, Tableau (mesh (Y.ir i) P.R.L j) (((Y.voyage i).X (Y.uv k)).gram j) ((Y.voyage i).CapeT j) P.U (soaked (X' j)) A) ∧
    ∀ j:ℕ,∀ᶠ k:ℕ in atTop,j<buoy (Y.ivory k) ∧ ∀ i:ℕ,∀ p:(Y.voyage i).kick ≤ k,
        Tableau (mesh (Y.ir i) P.R.L j) (((Y.voyage i).Q k p).gram j) ((Y.voyage i).CapeT j) P.U (soaked (X' j)) A:=by
 obtain ⟨A,hz,v⟩:= Y.solvent W; let B := Carousel.costPlan P.V (cashU P.W.C) O; let C:=max (A+1) B; have hC:A+1 ≤ C:= le_max_left ..; have hc:A ≤ C:= by linarith
 refine ⟨C,hz.trans_le hc, fun i k p j t=>?_, fun j =>?_⟩
 · let e:= v i k p j t
   let X:=((Y.voyage i).X (Y.uv k)).gram j; let d:=soaked (hat P.R.L P.x j)
   exact ⟨e.isPay,(Real.exp_monotone (budgetLe X _ _ d (neg_le_neg hc))).trans e.lowB,e.highB.trans (Real.exp_monotone (budgetLe X _ _ d hc))⟩
 filter_upwards [near_room Y j A,Y.heatGap j] with k u hz
 refine ⟨hz.1,fun i p=>?_⟩; let H:= ((Y.voyage i).Q k p); let m:=Y.ir i; let k':=Y.ivory k
 let Vc:= H.carnival ((Y.voyage i).funds); let V:=Vc.E j; let z:=Vc.Y j; let x:= ((Y.voyage i).X (Y.uv k)).gram j; let y:=hat P.R.L P.x j; let d:= soaked y
 have ht:j ≤ Y.uv k:=(hz.1.trans (deeper ..)).le
 let G:=hz.2 i p; have hP:= v i k p j ht; have hpr:= W.choose_spec.2 y (Vale.crown ..)
 let Zx:=compensated P.U x z; let Zy:=compensated P.U V z
 have he: ‖Zx-Zy‖ ≤ Real.exp (budgetCharge x d (-A))/2:= (vacuum_compare P.V G.priceA (G.priceH.permits) G.compare_density).trans (u i p)
 refine ⟨?_,?_,?_⟩
 · exact Carousel.sailed P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ Vc j hz.1.le
 · have hh:Real.exp (budgetCharge x d (-A)) ≤ ‖Zx‖:= hP.lowB
   change Real.exp (budgetCharge V d (-C)) ≤ ‖Zy‖; refine (Real.exp_monotone (budgetLe V _ _ d (neg_le_neg hC))).trans ?_; apply le_trans (diffuser Y i j d A V x); linarith [norm_sub_norm_le Zx Zy]
 exact (Carousel.toils_κ P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.height Vc O j hz.1.le hpr.2.1 hpr.2.2).trans (Real.exp_monotone (budgetLe V _ _ d (show B≤ C from le_max_right ..)))
omit W
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Course.passing
