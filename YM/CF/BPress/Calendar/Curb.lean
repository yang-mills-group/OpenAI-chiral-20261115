import YM.CF.BPress.Calendar.Atoll
import YM.CF.BPress.Manna.Packet
/-! geometry schedule grants. Pre-user projection height.Keeper.Assembler.Lc may use arbitrary PL demands, never has to dominate itself. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange -- tune
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} (f: Angel X)(E:Earning X)
-- PL heights. common factor.
namespace Around
open Mosaic Peel Spine
def small(y:ℝ):ℕ:=1+radiusB y -- tune text allows all choices after PL
lemma small_l (x:ℝ): (small x:ℝ)=lscale x:=by simp only [small,lscale,Nat.cast_add,Nat.cast_one]
lemma small_PL : PL fun i=> (small i:ℝ):=by simp only [small_l]; exact PL.scale
abbrev zMx : ℕ := 9*P.tone'.val+1 -- not involving X! `P` implicit? includes V
abbrev zX :ℕ:=9*P.tone.val+X.z.T.val+1 -- no f
def Fspan(X:P.Between d J.n):= zX (X:=X) + zMx (P:=P)
def spanN (X:P.Between d J.n)(x:ℝ):= X.z.M + ((small x)+ Fspan X)
lemma span_pl : PL fun i=>(spanN X i:ℝ):=by unfold spanN; simp only [Nat.cast_add]; exact (PL.const _).add (small_PL.add (PL.const _))
def μMode (x:ℝ):= min (min (limit E x) (f.a x)) (min (f.P_.jrate x/2) ((value E).rate /2))
lemma μMode_p(x:ℝ):0< μMode f E x:= lt_min (lt_min (rate_pos E x) (f.living x)) (lt_min (half_pos (half_pos (f.P_.gg x))) (half_pos ((value E).pos)))
private lemma plcmin (p q:ℝ→ℝ)(h:∀ i,0<p i)(t:∀ i,0<q i)(v:PL fun i=>(p i)⁻¹)(u:PL fun i=>(q i)⁻¹): PL fun i=>(min (p i) (q i))⁻¹:= (v.add u).mono (Eventually.of_forall (fun i=>by
 have ht:=h i; have hv:=t i; rw [abs_of_nonneg (inv_pos.mpr (lt_min ht hv)).le]; apply le_trans _ (le_abs_self _); rcases le_total (p i) (q i) with e|e; rw [min_eq_left e]; exact le_add_of_nonneg_right (by positivity); rw [min_eq_right e]; exact le_add_of_nonneg_left (by positivity)))
lemma core_pl : PL fun i=> (μMode f E i)⁻¹:=by
 let V:=limit E; let Z:=value E; let p(x:ℝ):= f.P_.jrate x/2; exact plcmin (fun i=> min (V i) (f.a i)) (fun i=>min (p i) (Z.rate/2)) (fun i=> lt_min (rate_pos E i) (f.living i)) (fun i=>lt_min (half_pos (half_pos (f.P_.gg i))) (half_pos Z.pos)) (plcmin V f.a (rate_pos E) f.living (broad E).2.2 f.PLb) (plcmin p (fun _=>Z.rate/2) (fun i=>half_pos (half_pos (f.P_.gg i))) (fun _=> half_pos Z.pos) (Weave.Budget.half_pl (Weave.Budget.half_pl f.P_.buy_ig)) (PL.const _))
abbrev Yagg(X:P.Between d J.n):= Fspan X+Fspan X+1
abbrev Fcap(x:ℝ):ℕ:= estate 40*(pacer f.steps f.F x * Yagg X^4)
lemma f_PL : PL fun i=>(Fcap f i:ℝ):=by
 have he:=lPL X.toGapSize _ 40 f.steps (zero_lt_one.trans_le f.oneF); unfold Lcharge at he; unfold Fcap; simp_rw [← mul_assoc (estate 40) _ (Yagg X^4)]; -- tune unfold Fcap
 simp only [Nat.cast_mul]; -- issue he match
 simp_rw [Nat.cast_mul] at he; exact he.mul (PL.const _)
abbrev κTown(X:P.Between d J.n) :ℕ:=X.z.M+(2*J.n+20)+4 -- local
abbrev hunger (x:ℝ):= Wander (f.P_.reach x) (6*f.r x)
lemma hu_pl : PL fun i=> (hunger f i:ℝ):=by unfold hunger Wander; push_cast; exact (f.P_.r_PL.add ((PL.const _).mul f.broad)).add f.P_.r_PL
def grant(x:ℝ) (S:Side): Prop := Even S.val∧S.val≤ umbra (era X x) ∧ spanN X x + hunger f x + f.P_.heightClose x + κTown X ≤ S.val ∧ courant S.val (Fcap f x) 4 (μMode f E x)
structure Curb where
 width : ℝ→ Side
 PL : PL fun i=>((width i).val:ℝ)
 bill : ∀ᶠ x:ℝ in atTop, grant f E x (width x)
lemma curb : Nonempty (Curb f E):= by
 let y(x):= spanN X x + hunger f x + f.P_.heightClose x+ κTown X; have ht:PL fun i=> (y i:ℝ):=by unfold y; push_cast; exact (((span_pl.add (hu_pl f)).add f.P_.h_PL).add (PL.const _)); -- tune binder order
 obtain ⟨s,h,v⟩:=Fits X.toGapSize _ y (μMode f E) (f_PL f) ht (core_pl f E) (Eventually.of_forall (μMode_p f E)) _ (by norm_num : (0:ℝ)≤4); exact ⟨⟨s,h,v.mono (fun i t=>⟨t.1,t.2.2.2,t.2.1,t.2.2.1⟩)⟩⟩
namespace Curb
variable {f E}
end Curb
end Around
end YM.CF.BPress.Calendar
