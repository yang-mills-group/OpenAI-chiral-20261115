import YM.SU5.CompassRose.Period

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
open WakeInvestment Gleam.Wake Regis.Wake
open Lamour (alleyR)
open CF.Pannier.Chancel.Rous

/-! # Receipts on a single support. Schedules for prices in `Shelves`.
 A W-visible piece has three different evaluations. Keep them DISTINCT.
 * The `Mark n` passed to the actual finite normalized functional. Requires support & gauge invariance.
 * An auxiliary, **global**-color covariant (at a COMMON rendezvous o, not each factor's site!)
   Fock-operator-valued function of ONE pane, `D`. Its flat `noble` price is gauge invariant
   because of that global-color rule, and hence usable as `φ`. Pointwise-close to the first item
   only in the specified good layout, with a Cadre norm which permits costing products.
 * Transfer `F`. Fock operator on the FLAT realization, depending on selected real face variables;
   required only ContDiff and a polynomial cost. This evaluation is what we integrate against
   the Gaussian.
-/
open scoped ContDiff
variable {I : Type*} [Fintype I] {n : Side} {m d : ℕ} {c e mu δ : ℝ} {o : Seat n}
local notation "ℱ" => FC (Single n)

structure Flora (s : Finset (Single n)) (c : ℝ) (d m : ℕ) (F : (I→ℝ) → ℱ) : Prop where
  bright : ContDiff ℝ 1 F
  worth : ∀ K ≥ (1:ℝ), ∀ x, ‖x‖ ≤ K → Cadre s d (c*K^m) (F x)
  price : ∀ K ≥ (1:ℝ), ∀ x y, ‖x‖ ≤ K → ‖y‖ ≤ K → Cadre s d (c*K^m*‖x-y‖) (F x-F y)

structure Hatch (B : Support (More n)) (o : Seat n) (Y : Pane n → Prop) (U : Pane n → (I→ℝ))
    (V : Mark n) (F : (I→ℝ) → ℱ) (D : Pane n → ℱ)
    (c e : ℝ) (d m : ℕ) : Prop where
  first : AtSupport false B V
  bonds : covariant V
  full : ∀ x, Cadre (modesIn _ B) d c (V x)
  texture : Measurable D
  global : ∀ (g : Seat n → SU.E) x, D (gauge g x)=twist (quantU (tradew n fun _ => g o)) (D x)
  sample : ∀ x, Cadre (modesIn _ B) d c (D x)
  promise : Flora (modesIn n B) c d m F
  mantle : ∀ x, Y x → Cadre (modesIn n B) d c (F (U x))
  crop : ∀ x : Fields n, Y x.1 → Cadre (modesIn n B) d e (V x-D x.1)
  ends : ∀ x, Y x → Cadre (modesIn n B) d e (D x - F (U x))

lemma pamphlet {s : Finset (Single n)} {A : ℱ} (p : Cadre s d c A) : 0 ≤ c := (norm_nonneg _).trans p.price
variable {xboard yboard : (I → ℝ) → FC (Single n)} {s : Finset (Single n)}
variable {m' d' : ℕ} {V W : Mark n} {C D : Pane n → FC (Single n)} {Y : Pane n → Prop} {U : Pane n → (I → ℝ)} {B : Support (More n)}

lemma leaf_product {A A' B B' : ℱ}
    (p : Cadre s d c A') (p' : Cadre s d' e B) (x : Cadre s d mu (A-A')) (y : Cadre s d' δ (B-B')) :
    Cadre s (d+d') (mu*e+c*δ) (A*B-A'*B') := by
  convert (x.and_ p').add (p.and_ y) using 1; noncomm_ring

lemma Flora.scale_nonneg (p : Rose.Flora s c d m xboard) : 0≤ c := by simpa only [one_pow,mul_one] using pamphlet (p.worth 1 le_rfl 0 (by simp))
lemma Flora.extra (p : Rose.Flora s c d m xboard) (a : c ≤ e) : Rose.Flora s e d m xboard := by
  refine ⟨p.bright,fun K v x t=> (p.worth K v x t).buy le_rfl ?_,fun K v x y t t'=> (p.price K v x y t t').buy le_rfl ?_⟩
  all_goals have hv := zero_le_one.trans v; gcongr
lemma Flora.more (p : Rose.Flora s c d m xboard) (k : m ≤ m') (h : d ≤ d') : Rose.Flora s c d' m' xboard:=by
  refine ⟨p.bright,fun K v x t=> (p.worth K v x t).buy h ?_,fun K v x y t t'=> (p.price K v x y t t').buy h ?_⟩
  all_goals have hv:= p.scale_nonneg; gcongr
lemma Flora.mul (p : Rose.Flora s c d m xboard) (q : Rose.Flora s e d' m' yboard) : Rose.Flora s (2*(c*e)) (d+d') (m+m') (xboard*yboard):=by
  have h : c*e≤2*(c*e):=le_mul_of_one_le_left (mul_nonneg p.scale_nonneg q.scale_nonneg) one_le_two
  refine ⟨p.bright.mul q.bright,fun K v x t=> ?_,fun K v x y t t'=>?_⟩
  · refine ((p.worth K v x t).and_ (q.worth K v x t)).buy le_rfl ?_
    have hv : 0 ≤ K := zero_le_one.trans v; apply le_trans (b:= c*e*K^(m+m')) _ (mul_le_mul_of_nonneg_right h (by positivity)); exact le_of_eq (by rw [pow_add]; ring)
  · refine (leaf_product (p.worth K v y t') (q.worth K v x t) (p.price K v x y t t') (q.price K v x y t t')).buy le_rfl (le_of_eq ?_); rw [pow_add]; ring
lemma Flora.smul (p : Rose.Flora s c d m xboard) (z : ℂ) : Rose.Flora s (‖z‖*c) d m (z • xboard) := by
  refine ⟨by have t:=p.bright; fun_prop,fun K v x t => by rw [mul_assoc]; exact (p.worth K v x t).scale z, fun K v x y t t'=>?_⟩
  rw [Pi.smul_apply,Pi.smul_apply,←smul_sub]; exact ((p.price K v x y t t').scale z).buy le_rfl (le_of_eq (by ring))

namespace Hatch
variable (p : Hatch B o Y U V xboard C c e d m) (q : Hatch B o Y U W yboard D mu δ d' m')
include p
lemma scale_nonneg : 0 ≤ c := p.promise.scale_nonneg
lemma extra (h : c ≤ mu) (l : e ≤ δ) : Hatch B o Y U V xboard C mu δ d m :=
 ⟨p.first,p.bonds,fun x=>(p.full x).buy le_rfl h, p.texture,p.global,fun x=>(p.sample x).buy le_rfl h,p.promise.extra h,
  fun x t=>(p.mantle x t).buy le_rfl h, fun x t=>(p.crop x t).buy le_rfl l, fun x t=>(p.ends x t).buy le_rfl l ⟩
lemma more (k : m ≤ m') (h : d ≤ d') : Hatch B o Y U V xboard C c e d' m' :=
 ⟨p.first,p.bonds,fun x=>(p.full x).buy h le_rfl, p.texture,p.global,fun x=>(p.sample x).buy h le_rfl,p.promise.more k h,
  fun x t=>(p.mantle x t).buy h le_rfl, fun x t=>(p.crop x t).buy h le_rfl, fun x t=>(p.ends x t).buy h le_rfl ⟩
include q in
lemma mul : Hatch B o Y U (V*W) (xboard*yboard) (C*D) (2*(c*mu)) (e*mu+c*δ) (d+d') (m+m') := by
  have h : c*mu ≤ 2*(c*mu):=le_mul_of_one_le_left (mul_nonneg p.scale_nonneg q.scale_nonneg) one_le_two
  refine ⟨p.first.mulM q.first,?_,fun x=> ((p.full x).and_ (q.full x)).buy le_rfl h,
    p.texture.mul q.texture, ?_, fun x=> ((p.sample x).and_ (q.sample x)).buy le_rfl h,
    p.promise.mul q.promise, fun x t=> ((p.mantle x t).and_ (q.mantle x t)).buy le_rfl h,fun x t=> leaf_product (p.sample x.1) (q.full x) (p.crop x t) (q.crop x t),fun x t=>leaf_product (p.mantle x t) (q.sample x) (p.ends x t) (q.ends x t)⟩
  · intro g x; rw [Pi.mul_apply,Pi.mul_apply,map_mul,p.bonds g x,q.bonds g x]
  · intro g x; rw [Pi.mul_apply,Pi.mul_apply,map_mul,p.global g x,q.global g x]
lemma smul (z : ℂ) : Hatch B o Y U (z • V) (z • xboard) (z • C) (‖z‖*c) (‖z‖*e) d m := by
  refine ⟨?_, ?_,fun x=>(p.full x).scale z,?_,?_,fun x=>(p.sample x).scale z,p.promise.smul z,
    fun x t=>(p.mantle x t).scale z,fun x t=>?_,fun x t=>?_⟩
  · exact p.first.smulM ..
  · intro g x; rw [Pi.smul_apply,Pi.smul_apply,twist_scalar,p.bonds g x]
  · exact Measurable.const_smul p.texture z
  · intro g x; rw [Pi.smul_apply,Pi.smul_apply,twist_scalar,p.global g x]
  · rw [Pi.smul_apply,Pi.smul_apply,←smul_sub]; exact (p.crop x t).scale z
  rw [Pi.smul_apply,Pi.smul_apply,←smul_sub]; exact (p.ends x t).scale z
omit p in
lemma unit (U : Pane n → (I→ℝ)) (Y) : Hatch B o Y U 1 1 1 1 0 0 0 := by
  refine ⟨AtSupport.oneM _,fun _ _=> (map_one _).symm,fun _=>Cadre.unit, measurable_const,fun _ _=>(map_one _).symm,
    fun _=>Cadre.unit,⟨contDiff_const,?_,?_⟩,fun _ _=> Cadre.unit,fun x _=>?_,fun x _=>?_⟩
  · intro K _ x _; rw [pow_zero,mul_one]; exact Cadre.unit
  · intro K h x y _ _; simp only [Pi.one_apply,pow_zero,mul_one,sub_self,one_mul]; exact ((Cadre.zero _).buy le_rfl (norm_nonneg _))
  all_goals simp only [Pi.one_apply,sub_self]; exact Cadre.zero _
end Hatch
-- usage & proof from Chapter-Wake budgets next.
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
