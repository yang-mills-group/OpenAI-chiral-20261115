import YM.CF.BPress.Vesper.Field
import YM.CF.Graph.Sore
import YM.CF.Graph.Dray
/-! VolumeB-phase. Second-species coefficients in *true* polynomial. Slip paid. Coil & repair use OF THE TRUE Gauge Field. Optional Flag colour kept. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Cube Lat SU Spin Spin.Paint Chalk Lily Skye Scree Lute Branch Tenant DoughBag Tulip Dial -- verify names
variable {N:Side} (R:GramM N)
abbrev kin (X:Hub N) := X.val.2
abbrev LocB(N:Side):=Bool × Hub N
abbrev earth (x: LocB N):= kin x.2
def βReg(z:Bool) : RegBudget N:= if z then R.slip else R.F
abbrev harbor (x:Force N):= kin x.val.1
abbrev forcePart (x:Force N):= x.val.2
def OreS : Force N→Force N→Prop := fun x y=>¬Disjoint (harbor x) (harbor y)
variable (u:Pane N)(v:Orbit N)(g:ℂ)(Z:Force N→ℂ)
abbrev u_budget (x:LocB N):=numbE R.p.threshold (earth x) (βReg R x.1 x.2) u
abbrev uB(x: LocB N):= weft g (u_budget R u x)
abbrev f_budget (x: Force N):=Scree.clamp R.p x (R.K x) v
abbrev fB(x:Force N):= weft (Z x) (f_budget R v x)
abbrev redP {N:Side}:LocB N→Finset (LeanV (Single N)):=camp ∘ earth
abbrev furnaceP {N:Side}:Force N→Finset (LeanV (Single N)):= camp ∘ harbor
abbrev MReg(N:Side):= Sparklers (redP (N:=N)) -- tune explicit!
abbrev MFuel(N:Side):=TreesF (furnaceP (N:=N))
abbrev WantR(N:Side):= MReg N⊕ MFuel N
def ore_heat (N:Side): Leaves (LeanV (Single N)) (MReg N):= heat redP
def ore_kind (N:Side): Leaves (LeanV (Single N)) (MFuel N):= kindle furnaceP OreS
def ore_full (N:Side): Leaves (LeanV (Single N)) (WantR N):= marital (ore_heat N) (ore_kind N)
-- functions used exposed independent of Z
abbrev regVal (u:Pane N)(g:ℂ): MReg N→ℂ:= pickStone redP (uB R u g)
abbrev fuelVal (f:Orbit N)(u:Force N→ℂ): MFuel N→ℂ:= pickLeaf furnaceP (fB R f u)
abbrev originS (u:Pane N)(g:ℂ):= Vesper.origin (uB R u g)
abbrev termsO := Sum.elim (regVal R v.1 g) (fuelVal R v Z)
structure Prom (R:GramM N): Prop where
 warm:∀ u i,Flour (redP i) (u_budget R u i).val
 hot:∀ v i,Flour (furnaceP i) (f_budget R v i).val
variable (A : Op (Single N))
def office := exponentL R.p R.F u+ exponentL R.p R.slip u
def pantry : Cipher N:= exp (weft g (office R v.1))* box OreS (fB R v Z)
def strength : FC (Single N):= tank A (pantry R v g Z)
lemma warmth {a b c d e:ℝ}(X:YM.CF.Graph.Ledger a b c d e R) : Prom R:=by
 refine ⟨fun u i=>?_ ,fun v i=>?_ ⟩
 · change Flour _ (Set.indicator {U|pingS R.p.threshold _ U} _ u : Cipher N).val; rw [Set.indicator_apply]; split; swap; · exact Flour.trivial
   rcases i with ⟨(_|_),x⟩; exact (X.reg.weight.choose_spec.1 x).fitted u; exact (X.slip.weight.choose_spec.1 x).fitted u
 unfold f_budget Scree.clamp; split; exact (X.force.weight.choose_spec.1 _).fitted _; exact Flour.trivial
lemma eraser : ∑ i:LocB N,uB R u g i=weft g (office R u):=by rw [Fintype.sum_prod_type,Fintype.sum_bool]; unfold office exponentL uB weft u_budget; rw [mul_add,mul_sum,mul_sum]; exact add_comm _ _
lemma pantry_p (p:Prom R) (t:IsStarProjection A) : strength R v g Z A= Complex.exp (originS R v.1 g) • (nursery A t).cook ((ore_full N).snow (termsO R v g Z)):=by
 unfold strength pantry; rw [←eraser, tank_eq (h:=t),kind_raw furnaceP (fB R v Z),heat_raw redP, mul_assoc,ardent, cTask] -- tune syntax
 · simp [originS,termsO,ore_full,ore_heat,ore_kind,regVal,fuelVal]
 · intro i; unfold uB; rw [weft_u]; exact (p.warm ..).smul _
 intro i; unfold fB; rw [weft_u]; exact (p.hot ..).smul _
end YM.CF.BPress.Vesper
