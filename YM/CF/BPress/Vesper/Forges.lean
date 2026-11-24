import YM.CF.BPress.Vesper.Forge
/-! eq:B-Oexpect exact polynomial input at permissible data. story built with Probe charge; output PMS.`math`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Cube Lat SU Spin Spin.Paint Chalk Lily Skye Scree Branch Tenant DoughBag Tulip Dial Spin.Cellar --
variable {Y B :Type}[Fintype Y][Fintype B][DecidableEq Y][DecidableEq B]{S:Branch.Field Y}
variable {N:Side}
abbrev Heat(N:Side):= WantJ N⊕ WantR N
abbrev LensStory(N:Side):= joinZ (aug N) (ore_full N)
variable (R:GramM N)(v:Orbit N)(g:ℂ)(Z: Force N→ℂ)(K U:Paint (More N)) (A: Op (Single N))(Yv: Site N→ℂ) (O:Support N){℘:Support N}
abbrev issue_spin : Heat N→ℂ:= Sum.elim (optionW K U Yv O) (termsO R v g Z)
abbrev holdα (℘:Support N)(K:Paint (More N)): Phys N := braC (Spin.Stride.Locks ℘ true) (Spin.Stride.Locks ℘ false) (coupling K)
variable {E : EdgeD (TripC (Single N)) B Y S} (T: Story (Heat N) E)
structure Born: Prop where
 law:T.rule=(LensStory N).rule
 grain:T.word=(LensStory N).band
variable {L:Op (Single N)}(f:B→ℂ)(ω: Wave (Single N))
abbrev opus : FC (Single N):= tomes univ (oceans K U Yv O) * strength R v g Z A
abbrev wickO(℘: Support N):=wick (holdα ℘ K) ω (opus R v g Z K U A Yv O)
lemma phaseO (u:Prom R)(k:MatPlan K)(a: IsStarProjection A)(p:Born T)(h:pays (E:=E) f (holdα ℘ K) ω (sneak (coupling K) (Paint.skew _ k)) (nursery A a)):
 wickO R v g Z K U A Yv O ω ℘= Complex.exp (originS R v.1 g)* T.table f (issue_spin R v g Z K U Yv O) :=by
 unfold wickO opus; rw [pantry_p R v g Z A u a,vacation K U Yv k O, Algebra.mul_smul_comm, wick.termScale]; exact congrArg _ (total_duet _ _ _ _ _ T p.law p.grain h) -- tune
end YM.CF.BPress.Vesper
