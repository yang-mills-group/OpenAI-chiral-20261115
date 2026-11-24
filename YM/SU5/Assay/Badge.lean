import YM.SU5.Assay.Punch
import YM.SU5.Assay.Medal
import YM.SU5.Assay.TollBelt
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
open Ballad Glaze
variable {P}
local notation "𝔏"=>Lead.Clan
local notation "τ"=>P.tock
local notation "δ"=>P.macroStep
/-! Single-sticker purchase. For owner sequence A, width is synchronized across labels.
 Include inactive stages explicitly. -/
def badgeSum (M:P.Menagerie):ℕ:=∑ Z,(M Z).bright.w
lemma badge_small (M:P.Menagerie)(Z:𝔏):(M Z).bright.w≤badgeSum M:=Finset.single_le_sum (f:=fun z=>(M z).bright.w) (fun _ _=>Nat.zero_le _) (Finset.mem_univ Z)
variable (P)(A:ℕ→P.Glaze)(M:P.Menagerie)(I:Set P.Court)
local notation "m"=>P.scrap A M I
def topFare (s:ℕ):ℕ:=⌈m s/δ s⌉₊
def ferry (s:ℕ):ℕ:=(A s).w+badgeSum M+ P.topFare A M I s
local notation "w"=>P.ferry A M I
lemma ferry_own (s:ℕ):(A s).w≤w s:=by unfold ferry;omega
lemma ferry_guest (s:ℕ)(Z:𝔏):(M Z).bright.w≤w s:= (badge_small M Z).trans (by unfold ferry; omega)
lemma ferry_room (s:ℕ):m s ≤ τ s (w s):=by
 let g:= P.topFare A M I s
 have t:m s / δ s≤g:=Nat.le_ceil _
 have v: g≤ w s:=by unfold ferry;omega
 rw [P.tock_price,Int.cast_natCast]
 exact (div_le_iff₀ (P.macroStep_pos s)).mp (t.trans (by exact_mod_cast v))

def badge (Z:𝔏)(s:ℕ): P.Glaze:=Glaze.belt (P.ferry_own A M I s) (P.ferry_guest A M I s Z)
def badgeBook (l:ℕ→P.Folio)(Z:𝔏)(s:ℕ):P.Folio:=beltBook (w s) (l s) (M Z).shine
local notation "D"=>P.badge A M I
lemma badge_first {l:ℕ→P.Folio}(u:∀s,P.Wove none (A s).S (A s).F (l s))(Z:𝔏)(s:ℕ): P.FirstDress (serial (D Z) s) Z.2 (P.badgeBook A M I l Z s):=
 Glaze.belt_first (l:=l s) (k:=(M Z).shine) _ _ (u s) ((M Z).first s)
lemma badgeBook_length (l:ℕ→P.Folio)(Z:𝔏)(s:ℕ): (P.badgeBook A M I l Z s).length=(M Z).shine.length*(l s).length:=by unfold badgeBook beltBook;rw [Folio.crossPrint_length,Folio.transcribe_length]
lemma badge_literal (Z:𝔏)(s:ℕ):
 (D Z s).F=(A s).F*P.chartAll (fun _=>(↑(w s)+w s+1)) ((M Z).y⁻¹•P.defaultR Z (M Z).n):=by
 show _*P.chartAll (pinDiagonal (w s)) _=_;apply congrArg ((A s).F *·)
 exact congrArg (fun t=> P.chartAll t _) (by funext i; unfold pinDiagonal pinOut;push_cast; rfl)

variable {P A I}
lemma scrap_pos (P:Spine)(A:ℕ→P.Glaze)(M:P.Menagerie)(I:Set P.Court)(s:ℕ):0<P.scrap A M I s:=slat_pos _
lemma Clutch.fare (h:P.Clutch I A):Tendsto (fun s=>τ s (P.topFare A M I s)) atTop (𝓝 0):=by
 have h₁: Tendsto (fun s=>m s+δ s) atTop (𝓝 0):=by simpa using (h.scraps M).add P.macroStep_zero
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h₁ (fun n=> P.tock_nonneg _ _) (fun s=>?_)
 rw [P.tock_price,Int.cast_natCast]
 have u:=P.macroStep_pos s; have k:=scrap_pos P A M I s
 exact ((mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_pos k u).le).le u.le)).trans_eq (by rw [add_mul,div_mul_cancel₀ _ u.ne',one_mul])
lemma Clutch.ferry_shrinks (h:P.Clutch I A): Tendsto (fun s=>τ s (w s)) atTop (𝓝 0):=by
 have u:Tendsto (fun s=>τ s (A s).w) atTop (𝓝 0):=h.1.fades 3
 have y:=(u.add (P.tock_fades (badgeSum M))).add (h.fare M)
 simpa only [add_zero,ferry,Nat.cast_add,tock_add] using y
lemma Clutch.badge_tiny (h:P.Clutch I A)(Z:𝔏): Tiny (D Z):=by
 let t:=h.ferry_shrinks M
 have y:=(((t.add t).add (P.tock_fades 1)).add t)
 simp only [add_zero] at y
 refine y.congr (fun s=>?_)
 change _=((w s+w s+1+w s:ℕ):ℝ)*δ s
 simp only [tock_price,Int.cast_natCast,Nat.cast_add,Nat.cast_one,add_mul]; norm_num
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
