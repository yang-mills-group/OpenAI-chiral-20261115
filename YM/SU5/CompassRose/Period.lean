import YM.SU5.CompassRose.Quay

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

-- Costs permitting operation under many funded stencils, still at every sufficiently
-- late height/ground extension. Track two parameters so that work with tests whose costs
-- grow with s (poly-leg counts/coefficients, cutoff tests) doesn't consume the power saving.
variable (P : Spine)
abbrev Threading := ℕ × ℕ → ℝ
local notation "τ" s:max => hat P.par.R.L P.par.x s
local notation "R" A:max z:max => sPow P.par ((z:ℕ×ℕ).1) A
local notation "χ" A:max z:max => WakeInvestment.chip (τ ((z:ℕ×ℕ).1)) A
abbrev book (P : Spine) (a b : ℝ) (z : ℕ × ℕ) : ℝ :=
  BProof.coin (hat P.par.R.L P.par.x z.1) (a/400000) b 0
lemma book_eq (x y : ℝ) (z : ℕ × ℕ) : book P x y z = χ x z * R y z := by
  rw [WakeInvestment.chip,sPow,BProof.coin_mul]; simp [book]
lemma book_mul (x y a b : ℝ) (z : ℕ × ℕ) : book P x a z * book P y b z=book P (x+y) (a+b) z := by
  rw [book_eq,book_eq,book_eq,mul_mul_mul_comm,← WakeInvestment.chip_add,sPow,sPow,BProof.coin_mul]; norm_num [sPow]
lemma book_pos (a b : ℝ) (z : ℕ × ℕ) : 0 < book P a b z := BProof.coin_pos ..
lemma book_price (a a' b b' : ℝ) (h : a < a' ∨ a=a' ∧ b < b') (r : ℝ) :
    ∀ᶠ z in bobbin, r * book P a b z ≤ book P a' b' z := by
  have v := BProof.coin_budget (a:=a/400000) (b:=b) (c:=0)
        (d:=a'/400000) (e:=b') (f:=0) (by
    rcases h with p|⟨rfl,p⟩
    · exact Or.inl (div_lt_div_of_pos_right p (by norm_num))
    exact Or.inr (Or.inl ⟨rfl,p⟩)) r 1 zero_lt_one
  filter_upwards [Rose.runway.eventually ((turnover P.par).eventually v)] with z u
  simpa only [one_mul] using u.le
structure Loan (x : Threading) (a : ℝ) : Prop where
  price : ∃ A : ℝ, ∀ᶠ z in bobbin, |x z| ≤ book P a A z
abbrev Easy (x : Threading) := Loan P x 0
abbrev Deep (x : Threading) := Loan P x (-8) -- scratch = chip(-7)
namespace Loan
variable {P} {a a' A : ℝ} {x y z : Threading}
lemma fixed (b c : ℝ) : Loan P (book P b c) b := ⟨⟨c,Eventually.of_forall fun i=>(abs_of_pos (book_pos P b c i)).le⟩⟩
lemma of_coat (t : Loan P y a) (p : ∀ᶠ z in bobbin, |x z| ≤ |y z|) : Loan P x a := by
  obtain ⟨A,h⟩:=t.price; exact ⟨A,p.mp (by filter_upwards [h] with z h p; exact p.trans h)⟩
lemma of_felt (t : Loan P y a) (q : ∀ᶠ z in bobbin,0≤x z) (p : ∀ᶠ z in bobbin,x z≤y z) : Loan P x a := by
  apply t.of_coat; filter_upwards [q,p] with z q p; simpa only [abs_of_nonneg q,abs_of_nonneg (q.trans p)] using p
lemma turns (p : a ≤ a') (t : Loan P x a) : Loan P x a' := by
  rcases p.eq_or_lt with rfl | p; exact t
  obtain ⟨A,h⟩:=t.price; refine ⟨0,?_⟩; filter_upwards [h,book_price P a a' A 0 (Or.inl p) 1] with z h t; rw [one_mul] at t; exact h.trans t
lemma secondary (t : Easy P x) : ∀ᶠ A in atTop, ∀ᶠ z in bobbin, x z ≤ R A z := by
  obtain ⟨A,h⟩:=t.price
  filter_upwards [eventually_gt_atTop A] with B b
  filter_upwards [h,book_price P 0 0 A B (Or.inr ⟨rfl,b⟩) 1] with z q w
  simp only [one_mul,book,zero_div] at w q
  exact (le_abs_self (x z)).trans (q.trans w)
lemma constant (x : ℝ) (P : Spine) : Easy P fun _ => x := by
  refine ⟨1,?_⟩
  filter_upwards [book_price P 0 0 0 1 (Or.inr ⟨rfl,zero_lt_one⟩) |x|] with i t
  simpa only [book,zero_div,BProof.coin_zero,mul_one] using t
lemma add (p : Loan P x a) (q : Loan P y a) : Loan P (x+y) a := by
  obtain ⟨A,h⟩:=p.price; obtain ⟨B,q⟩:=q.price; let I:=max A B+1; refine ⟨I,?_⟩
  have he:A<I:=(le_max_left ..).trans_lt (lt_add_one _); have hx:B<I:=(le_max_right ..).trans_lt (lt_add_one _)
  filter_upwards [h,q,book_price P a a A I (Or.inr ⟨rfl,he⟩) 2,book_price P a a B I (Or.inr ⟨rfl,hx⟩) 2] with z p t q h
  apply (abs_add_le ..).trans; linarith only [p,t,q,h]
lemma mul (p : Loan P x a) (q : Loan P y a') : Loan P (x*y) (a+a') := by
  obtain ⟨A,h⟩:=p.price; obtain ⟨B,g⟩:=q.price; refine ⟨A+B,?_⟩
  filter_upwards [h,g] with z h p; rw [Pi.mul_apply, abs_mul, ←book_mul]; exact mul_le_mul h p (abs_nonneg _) (book_pos ..|>.le)
lemma pow (p : Easy P x) (m : ℕ) : Easy P (x^m) := by
  induction m with|zero=> rw [pow_zero]; exact constant 1 P| succ n h=> rw [pow_succ]; exact (h.mul p).turns (by norm_num)
lemma summing {I : Type*} (X : I → Threading) (s : Finset I) (p : ∀ i∈s, Loan P (X i) a) : Loan P (∑ i∈s,X i) a := by
  induction s using Finset.induction_on with
  | empty=> rw [sum_empty]; exact ⟨0,Eventually.of_forall (fun i=> (abs_zero.le.trans (book_pos P a 0 i).le))⟩
  | insert i S e ih=> rw [sum_insert e]; exact (p i (mem_insert_self ..)).add (ih (fun i e=>p i (mem_insert_of_mem e)))
lemma scratched (p : Deep P x) : ∀ᶠ z in bobbin, x z ≤ scratch (τ z.1) := by
  obtain ⟨A,h⟩:=p.price; filter_upwards [h,book_price P (-8) (-7) A 0 (Or.inl (by norm_num)) 1] with z h p
  rw [one_mul] at p; exact (le_abs_self ..).trans (h.trans p)
end Loan
namespace Easy
-- dot notation short forms (abbrev may unfold sometimes)
variable {P} {f g : Threading}
lemma mul (a : Easy P f) (b : Easy P g) : Easy P (f*g) := (Loan.mul a b).turns (by norm_num)
lemma deep (a : Easy P f) (b : Deep P g) : Deep P (f*g) := (Loan.mul a b).turns (by norm_num)
lemma deep' (a : Easy P f) (b : Deep P g) : Deep P (g*f) := (Loan.mul b a).turns (by norm_num)
lemma rungs (a : ℝ) : Easy P (fun z=>R a z) := by
  have h:= Loan.fixed (P:=P) 0 a
  convert h using 1
  ext z
  simp only [sPow,book,zero_div]
lemma zoom {A : ℝ} (p : 0<A) : Easy P fun z=> (zoomR P.par A z.1:ℝ) := by
  apply Loan.of_felt (P:=P) (y:=fun z=>R A z) (rungs A) (Eventually.of_forall fun i=> by positivity)
  filter_upwards [Rose.runway.eventually ((sPower_pay P.par p).eventually_ge_atTop 2)] with z q
  have hx : (zoomR P.par A z.1:ℝ) < R A z /2+1:=Nat.ceil_lt_add_one (half_pos (rungs_pos P z.1)).le
  linarith
end Easy

end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
