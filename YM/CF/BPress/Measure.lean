import YM.CF.BPress.Calendar.Instrument
/-!
 # B pressure theorem (uniform version)

 including reading on any true trajectory at arbitrarily large admissible periods (_not_ windows increasing with x). Implement the B estimator at every `Rented` & `Seat`; no projective-limit clause. Here x is the **terminal** coupling (pivot), as opposed to pricing files in Calendar where it's y. Remaining prechoice/existence assertions packaged in BPress.Season. Particular true trajectory matching for asymptotic reflection considered separately. Theorem is independent of that stronger choice.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BPress
open Function Finset Set MeasureTheory Filter Lattice RG Precision Pressure Push.SectorMeasure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson Locale Calendar Calendar.Around
open Engine Before Between LocalH Next.SectorChange Hazel Net Honey
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p c:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n}{E:Earning X}
-- hypothesis Height protocol.Praise keep.
structure Sage (D:Day E)(h x:ℝ): Prop where
 stop : d ≤ P.dcap
 fern : p≤ W.pearl.q
 height : Between.height E≤h
 delay : 2<x
 dawn : ∀ y:ℝ,x≤y→ Time D.curb D.gain y
variable (D: Day E) {q:Chi}{N0:ℕ} {R0 δ:ℝ→ℝ}
lemma purchase_day (a:d ≤ P.dcap)(b:p≤ W.pearl.q)(k:Between.height E≤h) : ∀ᶠ x:ℝ in atTop,Sage D h x:=by
 obtain ⟨i,v⟩:=eventually_atTop.1 D.time; filter_upwards [eventually_ge_atTop i,eventually_gt_atTop (2:ℝ)] with x p e; exact ⟨a,b,k,e,fun m q=>v _ (p.trans q)⟩
private abbrev y := hat R.L x -- not Binder? tune
variable {M: Side}{n:ℕ}{j:ℕ}
namespace Sage
open Currencies
variable {D}
variable {H:History V N0 J q h R0 δ x M n}
variable (v:Sage D h x)(T: j ≤ n)(A:Bands (More (cell M B R.L j)) (era X (hat R.L x j)))(P':D.Appear _ A)
local notation "K₁"=> More (cell M B R.L j)
local notation "r"=>hat R.L x j -- tune binder annotations
include v
lemma hatTime : Time D.curb D.gain (hat R.L x j):= v.dawn _ (Vale.crown ..)
abbrev design(H:History V N0 J q h R0 δ x M n) := Instrument (mantel H T) v.hatTime P' -- tune binder H shadow
lemma tall(H:History V N0 J q h R0 δ x M n) : Nonempty (Instrument (mantel H T) v.hatTime P'):= by
 let Y:= history_prices H T; exact instrument (mantel H T) v.hatTime P' v.stop v.fern v.height Y.2.2.2.2.1 Y.2.2.2.2.2.1
lemma scope (H:Month x 1 6 2 N0 V W) (g:Side)(j n:ℕ): ∃ M:Side,n≤ M.val∧Admit V N0 J H M ∧ g.val∣ (More (cell (M*Mstar) B R.L j)).val∧∃ A: Bands (More (cell (M*Mstar) B R.L j)) (era X (hat R.L x j)), D.Appear _ A:=Day.parade D v.hatTime n g
variable {A}
local notation "CC"=> D.gain * (hat R.L x j)^2
variable (Z:Instrument (mantel H T) v.hatTime P')
lemma Pencil (i:A.Index) : IsMark (A.band i) (Z.pencil i) (Real.exp ((D.gain*(hat R.L x j)^2)*((More (cell M B R.L j)).val:ℝ)^3)):= Z.shapes i -- tune Order.Power.PL
/-- **The signed B-hit/W relation on the actual FiniteGaugeData reading.** Uniform constants for all y, x. Test equality with all Marks. For clarity every list order admitted. In particular test can vary with history and horizon. -/
theorem B_hit (p:List A.Index)(g:p.Nodup)(t:∀ i,i∈p) : Real.exp (-(D.gain*(hat R.L x j)^2)*((More (cell M B R.L j)).val:ℝ)^4)≤ ‖reading U (H.E j) (H.Y j) ((p.map Z.pencil).prod)‖ := by
 let h':= v.hatTime (j:=j); let H':= h'.stamp.high.pace.age; let z:= Cue (mantel H T) h' P'; -- tune cue signature
 have ht:= gate_history H T X.toGapSize A H'.yPos H'.plenty.plenty.Xi H'.plenty.plenty.coast z.Z p Z.wreath (fun i=>cashmark Z.gas (D.angel.k (hat R.L x j)) (value E) (Between.stipend E (hat R.L x j)) i) Z.marks g t; change _ ≤ ‖reading U (H.E j) (H.Y j) (shows A z.Z p Z.wreath)‖; exact (Z.lower v.fern p g t).trans_eq (congrArg (‖·‖) ht.2.2.symm) -- tune includes arguments
lemma TelescopePlanner(H:History V N0 J q h R0 δ x M n) (A: Bands (More (cell M B R.L j)) (era X (hat R.L x j)))(t:D.Appear _ A): ∃ Z:Instrument (mantel H T) v.hatTime t,
   (∀ i, IsMark (A.band i) (Z.pencil i) (Real.exp ((D.gain*(hat R.L x j)^2)*((More (cell M B R.L j)).val:ℝ)^3))) ∧
     ∀ p:List A.Index,p.Nodup→ (∀ i,i∈p)→Real.exp (-(D.gain*(hat R.L x j)^2)*((More (cell M B R.L j)).val:ℝ)^4)≤ ‖reading U (H.E j) (H.Y j) ((p.map Z.pencil).prod)‖:=by
 obtain ⟨Z⟩:=v.tall T A t H; exact ⟨Z,v.Pencil T t Z,v.B_hit T t Z⟩ -- note binder P' args
end Sage

/-- Theorem B-main, uniform power asserted (writing y² instead of raising to the possibly much larger power C; gain≥2). Issued on all these histories; includes non-ambiguity of exact offset removal. See `main_prechoices` for extractor schedule. Height is issued on long funds and angular method. Does not require the rotor bound be sizeK etc (but those apply on true MeterQ choice). -/
theorem B_main (v:Sage D h x)(H:History V N0 J q h R0 δ x M n)(t:j ≤ n) (A:Bands (More (cell M B R.L j)) (era X (hat R.L x j))) (g:D.Appear (hat R.L x j) A):
   ∃ Z:Instrument (mantel H t) v.hatTime g,
   (∀ i, IsMark (A.band i) (Z.pencil i) (Real.exp ((D.gain*(hat R.L x j)^2)*((More (cell M B R.L j)).val:ℝ)^3))) ∧
     ∀ p:List A.Index,p.Nodup→ (∀ i,i∈p)→Real.exp (-(D.gain*(hat R.L x j)^2)*((More (cell M B R.L j)).val:ℝ)^4)≤ ‖reading U (H.E j) (H.Y j) ((p.map Z.pencil).prod)‖:= Sage.TelescopePlanner v t H A g -- tune
end YM.CF.BPress
#print axioms YM.CF.BPress.B_main
#print axioms YM.CF.BPress.Sage.scope
