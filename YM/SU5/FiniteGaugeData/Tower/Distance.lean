import YM.SU5.FiniteGaugeData.Tower.Pairs
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Corr-R at elected hierarchy

Period threshold depends on diameter of each of the two stencils on the
observing lattice, not separation (can move translations after all
thresholds). This is a BOUND (not distance-uniform convergence). Same-draw
product and same signed physical denominator on all these entries.
-/
section sizes
variable (S:Finset Cover)
def CompactArc (S:Finset Cover)(d:ℕ):Prop:=∀i:Axis, ∃b:ℤ,∀x∈S,b ≤ x i∧x i≤b+d
lemma torus_arc (Z:Calibration)(n:Side){d:ℕ}(t:CompactArc S d)(i:Axis): rest Z n (Satin.region S (Z.c n)) i d:=by
 obtain ⟨b,w⟩:=t i; refine ⟨b,fun x hx=>?_⟩; obtain ⟨i',v,rfl⟩:=mem_image.mp hx; exact ⟨i' i,(w _ v).1,(w _ v).2,rfl⟩
lemma CompactArc.up {d f:ℕ}(h:CompactArc S d)(z:d≤f): CompactArc S f:=by intro i; obtain ⟨b,u⟩:=h i; refine ⟨b,fun x p=> ?_⟩; specialize u x p; omega
lemma CompactArc.reflBox {d}(h:CompactArc S d)(a:Axis)(s:ℤ):CompactArc (reflectedBox a s S) d:=by
 intro i; obtain ⟨b,t⟩:=h i
 by_cases w:a=i
 · subst a; refine ⟨2*s-b-d,fun x v=>?_⟩; obtain ⟨x,u,rfl⟩:=mem_image.mp v; specialize t x u; rw [reflected_coord]; omega
 refine ⟨b,fun x v=>?_⟩; obtain ⟨x,u,rfl⟩:=mem_image.mp v; rw [fling_move,if_neg w]; exact t x u
lemma sizes :∃ d:ℕ,CompactArc S d:=by
 let r:=S.sup (fun x=>univ.sup (fun i:Axis=>(x i).natAbs))
 refine ⟨2*r,fun i=>⟨-(r:ℤ),fun y v=>?_⟩⟩
 have he : (y i).natAbs ≤ r:= (le_sup (f:=fun i:Axis=> (y i).natAbs) (mem_univ i)).trans (le_sup (f:=fun y=>univ.sup (fun i:Axis=>(y i).natAbs)) v)
 omega
end sizes

local notation "K₀"=>tent Y H
local notation "A"=> Journey.duetCharge Y s
noncomputable def Grip (d:ℕ):=closefare (tent Y H) (A) d
local notation "C₀" d:max=>Grip Y H s d
-- native lease rates for both. warmth sufficient (UV) controls I. sharpened consumer can use on moving pairs too.
local notation "Φ" i:max k:max F:max=>hot Y H s i k F
lemma tandem(d:ℕ):∀ᶠ i in atTop,∀ (k:ℕ), Ferry Y s i k→
 ∀ {S T:Finset Cover}{f g:Family (tent Y H)},InTest (tent Y H) true S false f→ InTest (tent Y H) true T false g→ CompactArc S d→ CompactArc T d→∀ a b:ℝ,pay f a→pay g b→ ‖Φ i k (f*g)‖≤ C₀ d*(a*b) := by
 filter_upwards [(momentum Y s).eventually ((c_grows (K₀)).eventually_ge_atTop (widthPair K₀ d+addgap K₀))] with i h k q S T f g a b c t A₁ B t₀ w
 unfold hot; rw [dif_pos q.depth]; exact all_pair (boxprice Y H i k q.depth s q.fire q.enters) d h (a.support _) (b.support _) (torus_arc S K₀ _ c) (torus_arc T K₀ _ t) A₁ B (t₀ _) (w _)

-- also at normalized sharp at finite stages, keeping actual transaction.
lemma transfers (e:ℝ)(z:0<e): ∀ᶠ k:ℕ in atTop,∀ i, Ferry Y s i k→
 ∀ (S T:Finset Cover)(f g:Family (tent Y H)),InTest K true S false f→ InTest K true T false g → ∀a b:ℝ,pay f a→pay g b→
 ‖sharp Y H s i k (f*g)-Φ i k (f*g)‖ ≤ e*(a*b):=by
 filter_upwards [Y.UV.tendsto_atTop.eventually (LocalLimit.Donor.shrinks (T:=Y.meter) (C:=Λ.C) («τ»:=Y.τ) s Λ.b z)] with k H' i P
 intro S T f g pf pg r v hm hp
 let f':=(f*g)
 let m:=momentm Y i s; let L:=deltaL Y H i s; let F:= f' m
 have v0 : cash L F≤r*v:= (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (integrable_const _) (Filter.Eventually.of_forall (fun i=>pay_mul hm hp ..))).trans_eq (by simp)
 unfold hot; rw [dif_pos P.depth]
 exact (awaken Y H s P F ((((pf.support m).mono (subset_univ _)).mulM ((pg.support m).mono (subset_univ _))).env)).trans (mul_le_mul (H' _ ((Y.voyage i).domain k P.depth)) v0 (cash_nonneg ..) z.le)

include V
lemma pair_budget (d:ℕ){S T:Finset Cover}{f g:Family (tent Y H)} (p:InTest K true S false f)(t:InTest K true T false g)(a:CompactArc S d)(b:CompactArc T d)(v w:ℝ)(h:pay f v)(z:pay g w):‖E s (f*g)‖≤ C₀ d*(v*w):=by
 let D:=warm_limit Y H V s ((aux_test p).mul (aux_test t)); let q:= tandem Y H s d
 apply le_of_tendsto D.periods.norm
 filter_upwards [V.pick.grow_i.tendsto_atTop.eventually q] with i₀ h₀
 apply le_of_tendsto (D.inner _).norm
 exact (V.pick.pass Y H s _).mono fun _ hz=>h₀ _ hz p t a b v w h z
lemma early(d:ℕ): ∀ᶠ n:ℕ in atTop,
 ∀ (S T:Finset Cover)(f g:Family K), InTest K true S false f→InTest K true T false g→ CompactArc S d→ CompactArc T d→ ∀ a b:ℝ,pay f a→pay g b→ ‖I s (f*g) n‖≤ C₀ d*(a*b):=by
 filter_upwards [tandem Y H s d] with n p S T f g x u h v a b j k
 apply le_of_tendsto ((warm_limit Y H V s ((aux_test x).mul (aux_test u))).inner n).norm
 exact (V.pick.pass Y H s _).mono fun _ z=> p _ z x u h v a b j k
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.pair_budget
