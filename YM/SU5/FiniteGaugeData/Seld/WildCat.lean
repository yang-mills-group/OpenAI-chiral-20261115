import YM.SU5.FiniteGaugeData.Seld.Murmur
import YM.SU5.FiniteGaugeData.Seld.DeltaK
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
open Spectral Boundary Probe
local notation "V"=> S.unit
local notation "U"=> M S
variable (A B: H.Op)(p:E4)(g h: Test4)(c:ℂ)
lemma timeD(s:ℝ): U (-(p+s • basis a))= U (-p)*S.edge (-s) := by rw [← timeslot S, tgo]; unfold M; rw [neg_add,← neg_smul] -- tune sign
lemma routeD : HasDerivAt (fun s:ℝ=> U (-(p+s • basis a)) (R x)) (-I • U (-p) (x-R x)) 0:=by
 have hv: HasDerivAt (fun s:ℝ=> S.edge (-s) (R x)) (-I • (x-R x)) 0:=by
    have ht:= (fanfare S x (-0)).scomp (0:ℝ) ((hasDerivAt_id' (0:ℝ)).neg); simpa [Function.comp_def,parade,S.birth,neg_smul,show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl] using ht
 simp_rw [timeD]; convert ((U (-p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ hv using 1 <;> (first|rfl|simp)
def lucent(p:E4):= inner ℂ x (optx S A p y)
local notation "D₀" x:max y:max=> lucent S x y A
lemma Lucent : (D₀ x y) p= inner ℂ (U (-p) x) (A (U (-p) y)):=tboth S _ _ p
abbrev rum(p:E4):= I *( (D₀ x (R y)) p - (D₀ (R x) y) p)
lemma lucD : HasLineDerivAt ℝ (D₀ (R x) (R y)) (rum S x y A p) p (basis a):=by
 unfold HasLineDerivAt; simp_rw [Lucent]; convert (routeD S x p).inner ℂ ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ (routeD S y p)) using 1 <;> (first|rfl|skip); unfold rum; rw [Lucent, Lucent]; simp [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right]; ring
lemma sell : Integrable (fun p=>g p * (D₀ x y) p):=by
 let L:H→L[ℂ]ℂ:=innerSL ℂ x; have h: (fun p=> g p * (D₀ x y) p)=(fun p=> L (g p • optx S A p y)):= funext fun i=> (inner_smul_right ..).symm; rw [h]; exact L.integrable_comp (emberI S y A g)
lemma sell_in : (∫ p,g p* (D₀ x y) p) = inner ℂ x (valise S A g y):= by rw [vmap,← integral_inner (emberI ..)]; simp_rw [lucent,inner_smul_right]
open LineDeriv
abbrev shade(x:E4):= lineDerivOpCLM ℂ Test4 x
lemma shadeD(y:E4) : HasLineDerivAt ℝ g (shade p g y) y p:= (g.hasFDerivAt y).hasLineDerivAt _ -- any
#print axioms lucD
def εpref (a:Axis): Test4 →L[ℂ] Test4:= I • shade (basis a)
local notation "ε∂"=> shade (basis a)
local notation "Ψ" f:max=> valise S A f
lemma room : let g':=ε∂ g; I*(inner ℂ x ((Ψ g) (R y))-inner ℂ (R x) ((Ψ g) y)) = -inner ℂ (R x) ((Ψ g') (R y)) := by
 let L (p:E4) := (D₀ (R x) (R y)) p; let D:= rum S x y A
 let f:= ε∂ g
 have he : (fun p=>g p * D p) = (fun p=> I * (g p * (D₀ x (R y)) p - g p * (D₀ (R x) y) p)):= funext fun i=> by unfold D rum; ring
 have hf : Integrable (fun p=> g p * D p):= by rw [he]; exact ((sell S x (R y) A g).sub (sell S (R x) y A g)).const_mul _
 -- ∫ by parts
 have hv : (∫ p, g p * D p)= -(∫ p, f p * L p):= integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B:=ContinuousLinearMap.mul ℝ ℂ) (sell S (R x) (R y) A f) hf (sell S (R x) (R y) A g) (fun p _=>shadeD (basis a) g p) (fun p _=> lucD S x y A p) -- check binder
 unfold L at hv; rw [he,integral_const_mul,integral_sub (sell ..) (sell ..)] at hv; simp_rw [sell_in S] at hv; exact hv -- let
lemma orion : (Ψ g) * R = R*( Ψ g ) + R*( Ψ (εpref a g) )*R:=by
 have h(v:H) (w:H) : inner ℂ v ((Ψ g) (R w))-inner ℂ (R v) ((Ψ g) w)=I*inner ℂ (R v) ((Ψ (ε∂ g)) (R w)):=by
       apply mul_left_cancel₀ (show I≠0 from I_ne_zero); rw [room S v w A g,← mul_assoc,I_mul_I]; simp
 ext1 x; apply ext_inner_left ℂ; intro y; let F:=Ψ g; let t:=ε∂ g; let G:= Ψ t
 have he: valise S A (εpref a g)=I • G:= by change barren S A (_)= _; rw [show εpref a g= I • t from rfl, map_smul]; rfl
 have h1(z:H) : inner ℂ y (R z)=inner ℂ (R y) z:= by simpa only [show (saucer S).adjoint=R from saucer_sym S] using ContinuousLinearMap.adjoint_inner_right R y z -- syntax R.adj
 rw [he]; change inner ℂ y (F (R x))=inner ℂ y (R (F x)+R (I • (G (R x)))); rw [inner_add_right,h1,h1,inner_smul_right]; exact (sub_eq_iff_eq_add'.mp (h y x)) -- maybe prime direction
#print axioms room
#print axioms orion
def brochure : ℕ → Test4 → H.Op
 | 0=>valise S A
 | n+1=> fun g=> brochure n g + brochure n (εpref a g)*R
local notation "B"=> brochure S A
variable (n:ℕ)
lemma brochure_eq : valise S A g* Cache S n= Cache S n * B n g:=by
 induction n generalizing g with
 | zero=> simp [brochure, Cache]
 | succ n ih =>
    let f:= εpref a g; let J:=Cache S n; let Z:= Ψ g; let Q:= Ψ f
    calc
     _= (Z*R)*Cache S n:=by unfold Cache; rw [pow_succ', mul_assoc]
     _= (R*Z+ R*Q*R)*J:= congrArg (·*J) (orion S A g)
     _= R*(Z*J)+R*(Q*J)*R:=by rw [add_mul, mul_assoc,mul_assoc _ R,(Commute.self_pow R n).eq,mul_assoc,←mul_assoc _ J]; simp only [mul_assoc]
     _ = _:=by rw [show Z*J=_ from ih g,show Q*J=_ from ih f,brochure, mul_add]; dsimp only [J,Z,f,Cache]; rw [pow_succ']; simp only [mul_assoc]
-- invoice used for WOT approximants
lemma initialized (u:ℕ): pays S u (valise S A g):=⟨ B u g, brochure_eq S A g u⟩
lemma BroCt : Continuous (B n):= by induction n with
 | zero=> exact (apron S A).continuous
 | succ n ih=> exact ih.add ((ih.comp (εpref a).continuous).mul continuous_const) -- tune
abbrev dollycoin (a:Axis): ℕ → Test4→ℝ
 | 0=> vial
 | n+1=>fun g=>dollycoin a n g+dollycoin a n (εpref a g)
lemma dollyC : Continuous (dollycoin a n):=by induction n with
 | zero=> exact vialC
 | succ n ih=> exact ih.add (ih.comp (εpref a).continuous)
lemma dollyZ (a:Axis): dollycoin a n 0=0 := by induction n with | zero=> unfold dollycoin vial; rw [map_zero,norm_zero] | succ n ih=> simp only [dollycoin,map_zero,ih,add_zero]
lemma dollyP : ‖B n g‖ ≤ dollycoin a n g*‖A‖:= by induction n generalizing g with
 | zero=>exact vnorm S A g
 | succ n ih=>
    rw [dollycoin,add_mul]; exact (norm_add_le ..).trans (add_le_add (ih g) (((norm_mul_le _ R).trans (mul_le_of_le_one_right (norm_nonneg _) (pot S))).trans (ih _)))
#print axioms dollyP
#print axioms initialized
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
