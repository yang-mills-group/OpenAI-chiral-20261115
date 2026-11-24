import YM.SU5.CompassRose.Phlox

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open WakeInvestment Gleam Gleam.Wake
open Lamour.Bridge.Celeste.Clock
variable (P : Spine) (v : ℕ→ℕ) (β : ℕ→ℝ) {E w : ℝ}
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
local notation "Y" => P.run
local notation "R" s:max A:max => sPow P.par s A
local notation "τ" s:max => hat P.par.R.L P.par.x s
local notation "K" s:max => κFix β s
variable {I:Type*} [Fintype I] (V : I→ℕ→Staff) (x:I→Gaia)
variable (r W : I→ℕ→ℕ) (p: Pools P v β)
local notation "G" => SU.group

def cargoShip (z : ℕ × ℕ) : Vessel SU.group (More (O z)) (I × SU.group.ColorIndex) where
  view i := ((V i.1 z.1).localFace (O z),i.2)
def carrier (a : ℕ × ℕ → ℕ) : Foyer P v where
  faces _:= I × SU.group.ColorIndex
  finite _ := inferInstance
  anchor _ := 0
  B z := BlockP (a z) 0
  ship := cargoShip P v V
  width z:=2*a z
  pedestal z:= K z.1
  threshold:=1/2

def Porches (b : ℕ×ℕ→ℕ) (i : I) : Prop :=
  ∀ᶠ z in bobbin, (V i z.1).tenancy (O z) (r i z.1) Staff.clearance (b z) 0 ∧
    (V i z.1).Pays (r i z.1) (W i z.1)
variable {b : ℕ×ℕ→ℕ}
local notation "D" => carrier P v β V b

include p
lemma launchFee_many (e:Easy P fun z=>(b z:ℝ))(a:∀ i,Porches P v V r W b i) : LaunchFee P v D := by
  have h : Easy P (fun z => (2*(b z:ℝ))) := Easy.mul (Loan.constant 2 P) e
  have hc : Easy P (fun z => (2*b z:ℕ)) := by -- casts inference
    convert h using 1; ext; norm_cast
  refine ⟨Loan.constant (Fintype.card (I × SU.group.ColorIndex)) P,?_,hc,by change 0<(1:ℝ)/2; norm_num,by change (1:ℝ)/2≤1; norm_num,?_⟩
  · refine Loan.of_felt (Loan.pow (Loan.add (Loan.add e e) (Loan.constant 1 P)) 4) (Eventually.of_forall fun i=> Nat.cast_nonneg _) (Eventually.of_forall fun i=>?_)
    let a:=b i; change ((BlockP (n:=O i) a 0).card:ℝ) ≤ ((a:ℝ)+(a:ℝ)+1)^4
    exact_mod_cast (show (BlockP (n:=O i) a 0).card ≤ (a+a+1)^4 from by simpa only [BlockP,card_singleton,one_mul] using Corona.halo_size {(0:Seat (O i))} a)
  filter_upwards [Filter.eventually_all.mpr a,Rose.runway.eventually ((turnover P.par).eventually (Work.E08.eventual_radiusB Staff.clearance))] with z t g; let n:=O z; let Z:= (cargoShip P v V z); let B:=BlockP (n:=n) (b z) 0
  let hA (i:I × SU.group.ColorIndex) (v : Signed) (w : Seat n) := (V i.1 z.1).withinShip Z i rfl (t i.1).2 (t i.1).1 v w
  have hQ : Z.Ship B Staff.clearance := ⟨fun i=>(hA i 1 0).1,fun i d z=>(hA i d z).2.2,fun i j=>(hA i j 0).2.1⟩
  exact ⟨hQ.raise _ _ (Subset.refl _) g, blocks_rest (n:=n) (0:Seat n) (b z), range_paid P p z.1⟩
-- etc
variable {A : ℝ} (h : 0<A) {F : I → PlaqAxes} {L : I→DirSpin}
local notation "Cf" => I × SU.group.ColorIndex
def mStone (s : ℕ) (A : ℝ) (i : I) : Papal.Weaver := (winding P A s:ℂ) • (V i s).rungWeave (κFix β s) (r i s) (temp (τ s))
def mPaint (A : ℝ) (i : I) (z : ℕ × ℕ) (x : Cf → ℝ) := (winding P A z.1:ℂ) • trailer (V i z.1) (O z) (Prod.mk i) x

include h
lemma snapshot (t : ∀ i, LayoutBudget P A (x i) (V i) (r i) (W i) (F i) (L i)) :
    ∃ b : ℕ × ℕ → ℕ, let S:=carrier P v β V b; Easy P (fun z=> (b z:ℝ)) ∧ LaunchFee P v S ∧ ∀ i, Board P v S
       (F := fun z x => mPaint P v V A i z x) (X :=fun z=>mStone P β V r z.1 A i (O z)) 2 1 := by
  choose m hm using fun i=> (t i).approved (A+1) (lt_add_one A); let b(s:ℕ) := ∑ i:I,m i s; let B(z:ℕ×ℕ):= b z.1; let S:= carrier P v β V B
  have hx(i:I): Easy P (fun z=> (m i z.1:ℝ)) ∧ Easy P (fun z=> (W i z.1:ℝ)) := by
    have he := Rose.runway.eventually (hm i)
    have hg := Easy.rungs (P:=P) (A+1)
    exact ⟨Loan.of_felt hg (Eventually.of_forall fun _=>Nat.cast_nonneg _) (he.mono fun _ p => p.1), Loan.of_felt hg (Eventually.of_forall fun _=>Nat.cast_nonneg _) (he.mono fun _ p=>p.2.1)⟩
  have hB : Easy P (fun z=> (B z:ℝ)) := by
    convert Loan.summing _ Finset.univ (fun (i:I) _=> (hx i).1) using 1; ext u; unfold B b; rw [Finset.sum_apply, Nat.cast_sum]
  have hv(i:I) : Porches P v V r W B i:= by
    filter_upwards [Rose.runway.eventually (hm i)] with z q; exact ⟨tenancy_inc _ _ _ _ _ _ (single_le_sum (f:=fun i=>m i z.1) (fun _ _=>Nat.zero_le _) (mem_univ i)) (q.2.2 _),(t i).credentials z.1⟩
  have hg := launchFee_many P v β V r W p hB hv
  refine ⟨B,hB,hg,fun i=> ?_⟩ -- let reduction
  have hp := launch_granted (W:=fun z=> V i z.1) (U := fun z j=> (show S.faces z from Prod.mk i j)) (r := fun z=>r i z.1) P v S p B (fun z=> W i z.1) hB (hx i).2 hg (show (1:ℝ)/2 < 1 by norm_num) ((hv i).mono fun z e=> ⟨fun _=>rfl,rfl,e.2,e.1⟩)
  exact hp.smul (chromatic_bills P h) -- defeq

omit h p in
lemma walk_apply {α:Type*}{Grp:α→Type*}[∀ a,Monoid (Grp a)]{X:Type*}(f : X → ∀ a,Grp a)(L:List X)(a:α) : (L.map f).prod a=(L.map fun i=>f i a).prod:=by induction L with |nil=> rfl|cons i L ih=> rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,Pi.mul_apply,ih]

/-- observation level high-body mixed probe. preserves representation by the Weavers even when
 budgets purchased directly on `Fields` instruments at every inspected torus. -/
abbrev clusterW (l : List I) (A : ℝ) (s : ℕ) : Papal.Weaver:= (l.map (mStone P β V r s A)).prod
abbrev checkBy (l : List I) (A : ℝ) (z : ℕ × ℕ) (x : Cf → ℝ) : ℂ:= (ζbank P v z) (l.map (fun i => mPaint P v V A i z x)).prod
lemma many_compass (L' : List I) (a : Investment P.par E w) (u : Dispatchers P.par) (k : Meritorious P.par)
    (t : ∀ i, LayoutBudget P A (x i) (V i) (r i) (W i) (F i) (L i)) :
    ∀ᶠ z in bobbin, ‖Journey.sharp Y P.large z.1 (pᵥ z) (cᵥ z) (Papal.household P.calibration (clusterW P β V r L' A z.1)) -
      seatT Y z.1 (pᵥ z) (cᵥ z) (cargoShip P v V z) (checkBy P v V L' A z) (κFix β z.1)‖ ≤ chip (hat P.par.R.L P.par.x z.1) (-3) := by
  obtain ⟨b,q,hS,qt⟩ := snapshot P v β V x r W p h t
  let S:=carrier P v β V b
  let F i z := (show panelVal P v S z from mPaint P v V A i z)
  let X i (z:ℕ×ℕ):= mStone P β V r z.1 A i (O z)
  let U:∀ z,panelVal P v S z:= (L'.map F).prod; let X':∀ z,Mark (O z):=(L'.map X).prod
  let μ i:= clusterW P β V r L' A i
  filter_upwards [Board.purchase (F:=U) (X:=X') P v S hS a u k p.up (Board.walks F X L' (fun i _=> qt i))] with z f
  let Φ:= checkBy P v V L' A z; let T:= ζbank P v z
  have hz : Φ=T ∘ (U z):= by
    funext i; unfold Function.comp; apply congrArg T; dsimp only [U]; rw [walk_apply,walk_apply]
  change ‖Journey.compass Y _ _ _ (expSrc Y z.1 (pᵥ z) P.large (Papal.household _ (μ z.1))) - seatT _ _ _ _ _ Φ _‖≤_
  rw [lift_book,hz, show μ z.1 (O z)=X' z from ?_]; exact f
  unfold μ X' clusterW; rw [walk_apply,walk_apply]
#print axioms many_compass
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
