import Gingham.Ruff.Pulse
import Gingham.Ruff.Dab

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]


/-! The exact dΓ-source output on denZ:
  Y°ρ = e^χ
      (Reg-response * dressed-board
       +Reg-exp       * dressed-Force-response)|S⟩
      + (masked & truncated − full)ρ
 "dressed-" here means multiply and then evaluate on dressed ket.
 This is pointwise before pricing, including with flags. Note in
 particular which Reg incidence it is that needs paying. -/
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye

variable {N : Side}

abbrev fuelNeed (p:RG.BudgetPoint) (X:Finset (Force N)) (v:Orbit N) :=
    coverF p X v.1 ∧ Set.PairwiseDisjoint (X:Set (Force N)) (fun x=> x.val.1.val.2)
def greenfire (E:Op (LeanV (Single N))) (p:RG.BudgetPoint)
    (K:ForceBudget N) (v:Orbit N) : Cipher N := by
  classical
  exact ∑ s:Finset (Force N),
    if fuelNeed p s v then
      ∑ i∈s,
        (jolt E (clamp p i (K i) v)) * (∏ j∈s.erase i,clamp p j (K j) v)
    else 0
lemma jolt_prod {ι : Type*} [DecidableEq ι] (s: Finset ι) (f:ι→Dough n) (E:Op n) :
    jolt E (∏ i∈s, f i) =
    ∑ i∈s, jolt E (f i) * ∏ j∈s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty=> rw [prod_empty,sum_empty,jolt_one]

  | insert i s h ih=>
     rw [sum_insert h,erase_insert h,prod_insert h,jolt_mul,ih,mul_sum]
     congr 1
     apply sum_congr rfl
     intro k hk
     have w : i∉s.erase k := fun t=>h (mem_of_mem_erase t)
     rw [show (insert i s).erase k = insert i (s.erase k) by
           ext a; have y : i≠k := ne_of_mem_of_not_mem hk h |>.symm
           simp only [mem_erase,mem_insert]; grind,
         prod_insert w, mul_left_comm]

lemma jolt_fueled (E:Op (LeanV (Single N))) (p:RG.BudgetPoint)
    (K:ForceBudget N) (v:Orbit N) :
    jolt E (fueled p K v) = greenfire E p K v := by
  classical
  unfold fueled greenfire fuelNeed
  rw [map_sum]
  apply sum_congr rfl
  intro s _
  by_cases k:fuelNeed p s v
  · rw [if_pos k,if_pos k,jolt_prod]
  rw [if_neg k,if_neg k,map_zero]
lemma greenfire_zero (E:Op (LeanV (Single N))) (p:RG.BudgetPoint)
    (K:ForceBudget N) (v:Orbit N) (nf : RG.flags p.threshold v.1=∅) :
    greenfire E p K v = 0 := by rw [←jolt_fueled,fuel_one p K v nf,jolt_one]


def flicks (F:RegBudget N) : RegBudget N :=
  fun i z => Pastry.cloudless (F i z)
lemma lamp_flicks (E:Op (LeanV (Single N))) (p:RG.BudgetPoint)
    (F:RegBudget N) (v:Pane N) :
    jolt E (exponentL p (flicks F) v) = jolt E (exponentL p F v) := by
  classical
  rw [exponentL,exponentL,map_sum,map_sum]
  refine sum_congr rfl fun i _=>?_
  unfold numbE
  by_cases h:pingS p.threshold i.val.2 v
  · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]
    rw [flicks,cloudless,map_sub,jolt_hollow,sub_zero]
  rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h]

def regShock (R:GramM N) (v: Orbit N) (E:Op (LeanV (Single N))) : Cipher N :=
    jolt E (exponentL R.p (flicks R.F) v.1) +
      jolt E (exponentL R.p (flicks R.slip) v.1)
def shockBoard (R:GramM N) (v: Orbit N) (E:Op (LeanV (Single N))) : Cipher N :=
    regShock R v E * R.board v +
       exp (exponentL R.p R.F v.1+exponentL R.p R.slip v.1) *
       greenfire E R.p R.K v
lemma jolt_board (R:GramM N) (v: Orbit N) (E:Op (LeanV (Single N))) :
    jolt E (R.board v) = shockBoard R v E := by
  unfold shockBoard regShock GramM.board
  rw [jolt_mul,jolt_fueled,jolt_exp,map_add,mul_assoc,
     lamp_flicks,lamp_flicks]


variable {m B L:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e:ℝ}
         (P:Grasp Y B e) (R:GramM (mid m B)) (A:Loom (mid m B)) (v:Orbit (mid m B))

def flightKet : Cipher (mid m B) → Phys (mid m B) :=
  fun r =>
    Complex.exp (R.betaL A v) •
      acts (tank (spar j R.J.M (A v)) r) (relV P R.J (A v))

/-- Before truncation and masks, exact algebraic errors in inserting Y°.
 The equation applies in particular WITH arbitrary Force flags. Can use
 as is where v passed all the genuine qualifications even for copies;
 alternately no smoothness or Mask knowledge required. -/
theorem birdcall (h : P.roundZ ≤ (mid m B).val) (g:Guard (A v) e)
    (W:Op (Single (mid m B))) :
    let S := spar j R.J.M (A v)
    let T := R.J.P.den (A v)
    acts (𝒵 S T W) (denZ R P A v) = flightKet P R A v (shockBoard R v (hitch S W)) := by
  intro S T
  let z := changeM P (A v) R.J.M
  have s : Sea S z := Spire.sea_g h (A v) g R.J.M
  have p : IsStarProjection S := (P.broadness _ h R.J.M).projection _ g
  have y : relV P R.J (A v) = acts (quant (𝒞 S T)) z := by rw [𝒞_quant p]; rfl
  rw [flightKet,denZ,map_smul,y,striking (𝒵 S T W) _ _
    (voiceless p z s _ _),stir_tank p,jolt_board]


lemma facade_tail (S T W A W' L : Op n) (a : ℂ) :
    facade A W' a L =
      𝒵 S T W +
      facade A (W'-W) (a-𝒜 S A W) (L-𝒪 S T W) := by
  rw [←facade_eq S T W A]
  unfold facade gable
  rw [dg_sub L, dg_sub W', sub_smul,mul_sub,Matrix.trace_sub,sub_smul]
  abel
theorem birdcall_tail (h : P.roundZ ≤ (mid m B).val) (g:Guard (A v) e)
    (W D W' M:Op (Single (mid m B))) (a:ℂ) :
    let S := spar j R.J.M (A v)
    let T := R.J.P.den (A v)
    let y := denZ R P A v
    acts (facade D W' a M) y =
      flightKet P R A v (shockBoard R v (hitch S W))
      + acts (facade D (W'-W) (a-𝒜 S D W) (M-𝒪 S T W)) y := by
  intro S T y
  have z := birdcall P R A v h g W
  rw [facade_tail S T W D W' M a,act_add]
  exact congrArg₂ (·+·) z rfl

