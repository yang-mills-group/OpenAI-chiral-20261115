import SatinThinNeat
import SatinThinCardiff
import YM.SU5.Regis.Legend
import YM.SU5.Hiro.Ladles
import YM.SU5.Regis.Voyance
import YM.SU5.Celeste.Custodian

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
variable (z:PlaqAxes→ℝ) {I U:Type} [Fintype I] [Fintype U] (T:Trip I)(s:ℕ)(b:U→ ℕ)
local notation "xθ"=> hat P.par.R.L P.par.x s
/-! # affine pose bill and count. -/
variable (A:ℝ)
abbrev parish := ultimate P.run z T P.period P.cutoff A s
local notation "M"=> P.par
open BProof Py.Rate.Pannier Py.Rate.LocalLimit.Papal
open Signal.Interval (separationCost)
open Lattice
lemma rover_injective (h:Injective b)(c:I) : Injective (fun i:U=> (P.rover j T b i).loc c) :=by intro i k y; apply h; apply P.stretchO_inj j; change affine 1 _ _=affine 1 _ _ at y; unfold affine at y; exact add_left_cancel y
lemma rover'_inj(h:Injective b)(c:I): Injective (fun i:U=> (P.rover' j T b i).loc c):=by intro i k y; apply P.rover_injective j T b h c; exact (Signed.mirror j).act_injective (add_right_cancel y)
lemma duelCapital [Nonempty U] (h:Injective b) : let N:ℝ:=Fintype.card U; |(∑ i:U,∑ k:U,(P.parish z (P.win_stack j T b i k) s A))-(N* P.parish z T s A)^2|≤N * sunRank P.par.K.top.clip (padC z SU.group A xθ) (Fintype.card I):= by
 intro N; apply carried_vision P.run z T P.large P.law s (((Real.exp_pos 1).trans_le P.large).trans_le (Vale.crown ..)) _ _ (P.rover'_inj j T b h) (P.rover_injective j T b h); swap; · exact fun _=> ⟨1,_,rfl⟩ -- existential missing term
 intro i; unfold rover' playback rover hopping; rw [Yoke.Travel.turn_twice]; exact ⟨_,_,rfl⟩
variable (i n:ℕ)
omit [Fintype I] in
private lemma roverBound (i:U)(c:I)(a:Axis): ((P.rover j T b i).loc c a).natAbs ≤ (T.loc c a).natAbs + 8*P.par.block.val*b i:=by
 -- P.lineup implicit Fintype? MirrorLine section auto not include? likely Fintype J omitted
 change (Signed.act 1 (T.loc c) a+(P.stretchO j (b i)) a).natAbs ≤_
 have ht(i:Cover):Signed.act 1 i=i:=by simp
 rw [ht]; apply (Int.natAbs_add_le ..).trans; gcongr; change ((2 • (gaugeShift _ (↑(b i)) • (step j:Cover))) a).natAbs ≤ _; by_cases h:a=j<;> simp [h,gaugeShift]; norm_cast; ring_nf; (try simp); apply le_of_eq; ring
omit [Fintype I] in
private lemma roamBound (i:U)(c:I)(a:Axis): ((P.rover' j T b i).loc c a).natAbs ≤ (T.loc c a).natAbs + 8*P.par.block.val*b i:=by
 apply le_trans ?_ (P.roverBound j T b i c a); apply le_of_eq; change ((plane j 0).motion _ a).natAbs=_; by_cases h:j=a<;> simp_rw [fling_move, h]; all_goals simp
abbrev mCount (n:ℕ)(k:ℕ) : Fin n→ℕ:=fun i=>k+i.val
local notation "φq"=> Lamour.Bridge.Celeste.breadth
local notation "νW"=>φq 0 noonFrame
def CoversT (g:ℕ): Prop:=∀ i v, (T.loc i v).natAbs ≤ g
lemma staff_cover (t:CoversT T i)(h:∀ j,b j≤ n)(k c:U): CoversT (P.win_stack j T b k c) (i+8*P.par.block.val*n):=by
 intro a v; cases a with | inl a=> exact (P.roamBound j T b k a v).trans (add_le_add (t a v) (Nat.mul_le_mul_left _ (h k)))| inr a=>exact (P.roverBound j T b c a v).trans (add_le_add (t a v) (Nat.mul_le_mul_left _ (h c)))
lemma tile_budget [Nonempty I](h: CoversT T i): ∃ c:Finset Cover,c.Nonempty ∧ φq 0 c * 2 ≤ (i+νW)*2 ∧ T.canvasC ⊆ c:=by
 refine ⟨_,⟨_,T.touchedC (Classical.arbitrary I) (loc_frame _)⟩,Nat.mul_le_mul_right 2 ?_, subset_refl T.canvasC⟩
 unfold Lamour.Bridge.Celeste.breadth; apply Finset.sup_le; intro x hx; obtain ⟨j,k,v⟩:= mem_biUnion.mp hx; unfold separationCost; apply Finset.sup_le; intro a _; change ((0-x) a).natAbs ≤ i+νW; simpa using (rangeFrame x (T.loc j) v a).trans (Nat.add_le_add_right (h j a) νW)
abbrev numU := P.calibration.ℓ+i+νW
abbrev priceIncrease:= mCount n (P.numU i)
lemma expenseLimit (x:Fin n): P.priceIncrease i n x ≤ P.numU i+n:= Nat.add_le_add_left x.isLt.le _
lemma expenseInjective : Injective (P.priceIncrease i n):=by intro a b h; exact Fin.val_injective (Nat.add_left_cancel h)
lemma clearGrade (h:CoversT T i)(x:Fin n): Tower.region j 0 P.calibration.ℓ (onFlight P.par.block T.canvasC j (P.priceIncrease i n x)):=by
 intro a v; obtain ⟨y,u,rfl⟩:=mem_image.mp v; rw [SlabMark.moves j j,if_pos rfl,zero_add]; let m:= P.priceIncrease i n x; obtain ⟨z,h1,h2⟩:= mem_biUnion.mp u; have he:= (rangeFrame y (T.loc z) h2 j).trans (Nat.add_le_add_right (h z j) νW); have hφ: P.numU i ≤ m:= Nat.le_add_right ..; unfold numU at hφ; change _ ≤ _ + 2* Heat.gaugeShift P.par.block (↑m); have hv:= stab_hold P.par.block 0 m; omega
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.duelCapital
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.staff_cover
