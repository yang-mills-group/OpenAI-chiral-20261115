import YM.CF.Fock.Semig
import YM.CF.Support.Pulse
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Complex reflection cone over arbitrary (bounded, continuous) side parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reflect
open Fock Finset Function Filter NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction
attribute [local instance] opCStarAlgebra
variable {D n : Type*} [TopologicalSpace D] [LinearOrder n] [Fintype n]
abbrev CBox (D n : Type*) [TopologicalSpace D] [LinearOrder n] [Fintype n] := D →ᵇ FC n
abbrev CSeat (D n : Type*) [TopologicalSpace D] [LinearOrder n] [Fintype n] := CBox (D×D) n
def Theta (U : UNI n) : FC n →L[ℝ] FC n where
  toFun := theta U
  map_add' := theta_add U
  map_smul' := fun c a=> theta_rsmul U a c
  cont := theta_cont _
def direct (f : CBox D n) : CSeat D n := f.compContinuous (⟨Prod.fst,continuous_fst⟩)
def opposite (U : UNI n) (f : CBox D n) : CSeat D n := (Theta U).compLeftContinuousBounded (D×D) (f.compContinuous (⟨Prod.snd,continuous_snd⟩)) -- tune
lemma rightU (U : UNI n) (f : CBox D n) (x : D×D) : opposite U f x=theta U (f x.2) := rfl
def chord (b : Bool) : ℂ := if b then Complex.I else 1
def tile (U : UNI n) (b : Bool) (f : CBox D n) : CSeat D n := chord b • (opposite U f*direct f)
lemma brick (U : UNI n) (b : Bool) (f : CBox D n) (x:D×D) : tile U b f x= chord b • (theta U (f x.2) * f x.1) := rfl
lemma grade_phase (a b) : chord b * chord a * Sector.grainB a b = chord (a.xor b) := by cases a <;> cases b <;> simp [chord,Sector.grainB]
def Hut (S : Finset n) (b : Bool) (f : CBox D n) := ∀ x, Sector S b (f x)
variable (U : UNI n) (S : Finset n)
lemma multiplied {a b} {f g:CBox D n} (h : Hut S a f) (k : Hut S b g) (e : twist U (cutM S)=cutM Sᶜ) : tile U a f * tile U b g=tile U (a.xor b) (f*g) := by
  ext x : 1; let X := f x.1; let A := theta U (f x.2); let Y := g x.1; let B := theta U (g x.2)
  change (tile U a f x)*(tile U b g x)= _; rw [brick,brick,brick]
  change (chord a • (A*X))*(chord b • (B*Y))=chord (a.xor b) • (theta U (f x.2*g x.2)*(X*Y)); rw [theta_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc];
  have he : X*B=Sector.grainB a b • (B*X) := Sector.apart (h x.1) (theta_carries U (k x.2) e) disjoint_compl_right
  rw [←mul_assoc (A*X), mul_assoc A,he, Algebra.mul_smul_comm,Algebra.smul_mul_assoc, smul_smul, smul_smul,grade_phase]; unfold A B; simp only [mul_assoc]

inductive Faced (U : UNI n) (S : Finset n) : CSeat D n→Prop
  | zero : Faced U S 0
  | square (b) (f : CBox D n) : Hut S b f → Faced U S (tile U b f)
  | raise (a : ℝ) : 0≤a→∀ {f}, Faced U S f → Faced U S (a • f)
  | plus {f g} : Faced U S f→Faced U S g→Faced U S (f+g)
lemma Faced.unit : Faced U S (1:CSeat D n) := by
  have he : (1:CSeat D n)= tile U false 1 := by
    ext x : 1; rw [brick, chord]; change (1:FC n) = (1:ℂ) • (theta U 1 * 1); rw [theta_one,one_mul,one_smul]
  rw [he]; exact Faced.square _ _ fun _=> Sector.one
variable {S U}
lemma Faced.layer {f g:CSeat D n} (h : Faced U S f) (e : Faced U S g) (k : twist U (cutM S)=cutM Sᶜ) : Faced U S (f*g) := by
  induction h with
  | zero => rw [zero_mul]; apply Faced.zero
  | raise a p h ih=> rw [Algebra.smul_mul_assoc]; exact raise a p ih
  | plus h g ih it=> rw [add_mul]; exact ih.plus it
  | square b f h =>
    induction e with
    | zero=> rw [mul_zero]; apply Faced.zero
    | square a g e => rw [multiplied U S h e k]; exact Faced.square _ _ (fun x=>(h x).mul (e x))
    | plus h g ih it => rw [mul_add]; exact ih.plus it
    | raise a p h ih=> rw [Algebra.mul_smul_comm]; exact raise a p ih
lemma Faced.powered {f:CSeat D n} (h : Faced U S f) (k : twist U (cutM S)=cutM Sᶜ) (i : ℕ) : Faced U S (f^i) := by induction i with | zero=> rw [pow_zero]; exact Faced.unit U S | succ i ih => rw [pow_succ]; exact ih.layer h k
lemma Faced.sumX {P : Type*} (s : Finset P) (x : P→CSeat D n) (h : ∀ i∈s, Faced U S (x i)) : Faced U S (∑ i∈s,x i) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp; exact Faced.zero
  | insert i s g ih=> rw [sum_insert g]; exact (h i (mem_insert_self ..)).plus (ih (fun i hi=> h _ (mem_insert_of_mem hi)))

def Cloud (U : UNI n) (S : Finset n) (D : Type*) [TopologicalSpace D] := closure {f:CSeat D n| Faced U S f}
lemma rain_mul {f g:CSeat D n} (h:f∈Cloud U S D) (e:g∈Cloud U S D) (k:twist U (cutM S)=cutM Sᶜ) : f*g∈Cloud U S D := by
  let A : Submonoid (CSeat D n) := ⟨⟨{f | Faced U S f},fun h e=> Faced.layer h e k⟩,Faced.unit U S⟩
  exact (A.topologicalClosure).mul_mem h e
lemma Faced.run {f:CSeat D n} (p : Faced U S f) : f∈Cloud U S D := subset_closure p
lemma attendsCone [Nonempty D] (F:CBox D n) (A:CSeat D n) (e : Hut S false F) (h : Faced U S A) (k:twist U (cutM S)=cutM Sᶜ) : exp (opposite U F+direct F+A)∈Cloud U S D := by
  let B := tile U false F; let G := opposite U F+direct F+A
  let t := fun i:ℕ=>(i+1:ℝ)⁻¹
  have hp v (u:0≤v) : Faced U S (stampE G B v) := by
    let f : CBox D n := 1+v • F
    have hf : Hut S false f := fun x=> Sector.add Sector.one (show Sector S false (v • F x) from by
      rw [←show (v:ℂ) • F x=v • F x by ext i j; simp [Complex.real_smul]]; exact Sector.scale (e x) (v:ℂ))
    have He : tile U false f=1+v • (opposite U F+direct F)+v^2 • tile U false F := by
      ext x : 1; rw [brick]; change (1:ℂ) • (theta U (1+v • F x.2)*(1+v • F x.1))=1+v • (theta U (F x.2)+ F x.1)+v^2 • (tile U false F x); rw [one_smul,theta_add,theta_one,theta_rsmul,add_mul,one_mul,mul_add,mul_one, Algebra.mul_smul_comm,Algebra.smul_mul_assoc, smul_smul, ←pow_two,smul_add,brick]; change _=_+_ • ((1:ℂ) • _); rw [one_smul]; abel
    have hw : stampE G B v=tile U false f+v • A := by rw [He]; unfold stampE G B; rw [smul_add]; abel
    rw [hw]; exact (Faced.square _ _ hf).plus (h.raise v u)
  apply isClosed_closure.mem_of_tendsto (euler G B) (Eventually.of_forall (fun i=> Faced.run ((hp _ (show 0≤ t i by unfold t; positivity)).powered k _))) -- need closed
lemma eval_exp {X : Type*} [TopologicalSpace X] (f : CBox X n) (x : X) : exp f x=exp (f x) := by
  letI : NormedAlgebra ℚ (CBox X n) := NormedAlgebra.restrictScalars ℚ ℝ (CBox X n)
  let g : CBox X n →+* FC n :=
    { toFun := fun f=> f x
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _=>rfl
      map_mul' := fun _ _=>rfl }
  have hg : Continuous g := by
    change Continuous (fun i:CBox X n => i x)
    fun_prop
  exact map_exp g hg f
end YM.CF.Reflect
