import Risa.SeedBox
import Risa.Warehouse
import Rods.Sport
import YM.SU5.Regis.Visitations
import Risa.Hosted
import CellQ.Delight
set_option autoImplicit false
set_option maxHeartbeats 320000
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
open BProof CF.Refrain _root_.YM.Gleam.Luster.Risa
open _root_.YM.CF.Lamour.Bridge.Celeste Clock Afterglow Journey
set_option linter.unusedVariables false
variable {n m:Side}{I:Type}[Fintype I] (p:BudgetPoint) (y a d:ℝ)(n₀:Bool)(v:Bool→Seat n)(t:Bool→Signed)
variable {p y a d n₀ v t} (E:Seed I p y a d n₀ v t)
def expHeightα (C:ℝ):ℝ:=Fintype.card I*|a| * ((max 1 (gradM p y))^2+C)
lemma sway_fee{C:ℝ}(l:|d|≤C): ∀ i:Fields n,‖Sway E i‖ ≤ Real.exp (expHeightα (I:=I) (a:=a) (p:=p) (y:=y) C):=by
 intro i; unfold Sway CalendarQ' sampleZ; rw [norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_eq_abs]
 let M:= max 1 (gradM p y); let F(i':I)(k:Bool):= solicit SU.group p y (E.ort i' k) (E.spa i' k) i.1
 let T:= expHeightα (I:=I) (a:=a) (p:=p) (y:=y) C; change |∑ j:I,a*(loader n₀ (F j)-d)| ≤ Real.exp T
 have hk(j):|loader n₀ (F j)|≤ M^2:= Risa.grainD (le_max_left ..) (fun k=> (launchQ ..).trans (le_max_right ..))
 refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>|a| * (M^2+C)) (fun j _=>by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hk j) l)) (abs_nonneg _))).trans ?_)
 rw [sum_const,card_univ,nsmul_eq_mul,←mul_assoc]; exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp T)
lemma portraitν{T:ℝ}{K:Calibration} {v:Bool→Seat (K.c m)} (L:List (Seed I p y a d n₀ v t))(l:|d|≤T) : let F:= Sport.film (bandSeat K) L;Envelope F ∧ ∀ i, ‖F i‖≤Real.exp (expHeightα (I:=I) (a:=a) (p:=p) (y:=y) T *L.length) :=by
 intro F; let b:=expHeightα (I:=I) (a:=a) (p:=p) (y:=y) T
 have he :AtSupport false (Sport.hopit (bandSeat K) L) F:=by
    unfold F Sport.film; induction L with
    | nil=>exact AtSupport.oneM _
    | cons k L ih=>exact (k.covers.mono subset_union_left).mulM (ih.mono subset_union_right)
 refine ⟨he.env,fun i=>?_⟩
 clear he
 unfold F Sport.film; induction L with
 | nil=> simp
 | cons k L ih=> rw [List.map_cons,List.prod_cons,Pi.mul_apply,List.length_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one,Real.exp_add,mul_comm _ (Real.exp _)]; exact (norm_mul_le ..).trans (mul_le_mul (sway_fee k l i) ih (norm_nonneg _) (Real.exp_pos _).le)
variable {K:Calibration} {m:Side}
local notation "Sx"=> K.c m
local notation "D"=>sites (Sx)
lemma portrait_pos (C:ℝ)(h:0 ≤ C) : 0 ≤ expHeightα (I:=I) (a:=a) (p:=p) (y:=y) C:=by unfold expHeightα; positivity
-- uniform analytic. let employer parameter.X. exact list=2. bM.F.
open Sport
lemma proms {v:Bool→Seat (K.c m)}(R Q:Mark (K.c m)→ℂ){κ C:ℝ}(h:0≤κ)(e:Twosome K (K.c m) R)(l:|d|≤C)
 (hp:∀ F:Mark (K.c m),Envelope F → (∀ i,‖F i‖≤Real.exp (expHeightα (I:=I) (a:=a) (y:=y) (p:=p) C * (2*D)))→ ‖Q F-R F‖≤1)
 (hz:∀ L:List (Seed I p y a d n₀ v t), race (bandSeat K) L→ ‖Q (film (bandSeat K) L)‖ ≤ Real.exp (κ*D +4*(L.length:ℝ)))
 (L: List (Seed I p y a d n₀ v t))(cxt:L.length=2){B:ℕ}(c:B+addgap K ≤ (K.c m).val)(x:∀i,rest K m (hopit (bandSeat K) L) i B)(pX:race (bandSeat K) L): ‖R (film (bandSeat K) L)‖ ≤ Real.exp (κ*(4*(((B:ℕ)+addgap K:ℕ):ℝ))^4+9):=by
 obtain ⟨k,Lq,hk,hM,hS,W,g⟩:= Sport.team _ R e L c x pX
 let n:= (2^k)^4; have hn:1 ≤n:= one_le_pow₀ (one_le_pow₀ (by norm_num:(1:ℕ)≤2));
 let V:=expHeightα (I:=I) (a:=a) (y:=y) (p:=p) C; let T:=film (bandSeat K) Lq
 have hfL: (Lq.length:ℝ)=(n:ℝ)*2:= congrArg (Nat.cast (R:=ℝ)) (W.trans (congrArg _ cxt))|>.trans (by unfold n; push_cast; rfl)
 have hpR:(n:ℝ)≤D:=by unfold sites; exact_mod_cast hk
 have hpM:D ≤ (n:ℝ)*(4*(((B:ℕ)+addgap K:ℕ):ℝ))^4:=by unfold sites; exact_mod_cast hM
 have hQ: ‖Q T-R T‖≤1:= hp _ (portraitν Lq l).1 (fun i=> ((portraitν Lq l).2 i).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by rw [hfL]; linarith only [hpR]) (portrait_pos C ((abs_nonneg _).trans l)))))
 let H:=κ* (4*(((B:ℕ)+addgap K:ℕ):ℝ))^4
 let W':=(n:ℝ)*(H+8); have hW':0≤W':=by unfold W' H; positivity
 have hs:‖Q T‖≤ Real.exp W':=(hz _ hS).trans (Real.exp_monotone (by rw [hfL]; unfold W' H; nlinarith only [mul_le_mul_of_nonneg_left hpM h]))
 refine le_of_pow_le_pow_left₀ (n:=n) (by omega) (by positivity) (g.trans ?_)
 rw [←Real.exp_nat_mul,show (n:ℝ)*(κ*_+9)=W'+(n:ℝ) from (by unfold W' H; ring),Real.exp_add]
 refine ((norm_le_norm_sub_add (R T) (Q T)).trans (add_le_add ((norm_sub_rev ..).trans_le hQ) hs)).trans ?_
 have hM: (2:ℝ) ≤ Real.exp n:=by linarith only [(Real.add_one_le_exp (n:ℝ)),show (1:ℝ) ≤n from (by exact_mod_cast hn)]
 nlinarith only [Real.one_le_exp hW',mul_le_mul_of_nonneg_left hM (Real.exp_pos W'|>.le)]
#print axioms proms
end Papal
end LocalLimit
end Rate
end YM.CF.Py
