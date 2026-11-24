import YM.SU5.FiniteGaugeData.Poin.Cobble
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Function Filter Metric Complex MeasureTheory Set OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {n:ℕ}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(x y:H)
open Boundary Probe Fin
variable (G: Fin n→ H.Op)(J:Bin n H.Op)(f:Fin n→Test4)
abbrev dress (p:Points n):=fun i:Fin n=>optx S (G i) (p i)
abbrev pitch(p:Points n):H.Op:= Rail (dress S G p) J
lemma pitch_step {n:ℕ} (G:Fin (n+1)→H.Op)(J:Bin (n+1) H.Op)(p:Points (n+1)):
 pitch S G J p= optx S (G 0) (p 0)* s1 n J * pitch S (Fin.tail G) (rump J) (Points.tail p):= Rail_step ..
local notation "P"=> Bench S
-- strong/sp continuity
lemma clothing {X:Type*}[TopologicalSpace X](f:X→E4)(p:Continuous f)(G:H.Op)(D:X→ H)(t:Continuous D): Continuous fun x=> optx S G (f x) (D x) :=by
 let K(x):=G (M S (-f x) (D x)); have he:Continuous K:= by have hv:=(step_c S).comp (t.prodMk p.neg); let Q(x):=M S (-f x) (D x); exact G.continuous.comp (show Continuous Q from hv)
 have hp:=(step_c S).comp (he.prodMk p); change Continuous (fun x=> M S (f x) (K x)); simp only [Function.comp_def] at hp; exact hp
lemma fee : ∃ r:ℝ,∀ p,‖pitch S G J p‖≤r:= by
 induction n with
 | zero=> exact ⟨‖(1:H.Op)‖,fun _=>show _ from (by unfold pitch Rail Each; simp only [List.finRange_zero,quiet]; exact le_rfl)⟩
 | succ n ih=>
   let A:=s1 n J; obtain ⟨r,t⟩:= ih (Fin.tail G) (rump J); refine ⟨‖G 0‖*‖A‖*r,fun p=>?_⟩; rw [pitch_step]; exact (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v=> vcost S v (p 0) (G 0))) (norm_nonneg _))) (t _) (norm_nonneg _) (by positivity)) -- vcost args
lemma shops {X:Type*}[TopologicalSpace X](g:X→Points n)(h:Continuous g)(d:X→H)(k:Continuous d): Continuous fun x=>pitch S G J (g x) (d x):=by
 induction n with
 | zero=> exact k
 | succ n ih=>
   simp_rw [pitch_step]; let c(x:X):Points n:= Points.tail (g x); have hc: Continuous (Points.tail (n:=n)):= continuous_snd.comp Joint.breakAt.continuous
   have ht:=ih (Fin.tail G) (rump J) c (hc.comp h); exact clothing S (fun i=> g i 0) (by fun_prop) (G 0) _ ((s1 n J).continuous.comp ht)
local notation "B"=>Joint.breakAt (n:=n)
theorem breakA(n:ℕ):MeasurePreserving (Joint.breakAt (n:=n)) volume volume:= (WithLp.volume_preserving_ofLp _ _).comp (LinearIsometryEquiv.measurePreserving (Points.peel (n:=n)))
lemma tail_cons(z:E4)(p:Points n):Points.tail (Points.cons z p)=p:= by
 let B':= B; exact congrArg Prod.snd (B'.apply_symm_apply (z,p))
lemma head_cons(z:E4)(p:Points n): Points.cons z p 0=z:= by rw [Points.cons]; simp
abbrev concert(p:Points n) := Joint.materialize n f p*inner ℂ x (pitch S G J p y)
lemma billI(f:Joint n) : Integrable (fun p=> f p * inner ℂ x (pitch S G J p y)):=by
 obtain ⟨r,t⟩:= fee S G J; refine (f.integrable.norm.mul_const (‖x‖*(r*‖y‖))).mono' (f.continuous.mul (continuous_const.inner (shops S G J id continuous_id _ (continuous_const (y:=y))))).aestronglyMeasurable ?_
 filter_upwards with p; rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((pitch S G J p).le_opNorm _).trans (mul_le_mul_of_nonneg_right (t p) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _)
lemma Pour {H:Type*}[NormedAddCommGroup H][NormedSpace ℝ H](L:Points (n+1)→H)(p: Integrable L): (∫ x,L x)= ∫ x:E4,∫ y: Points n, L (Points.cons x y):=by
 let V:= (B).symm; have he: MeasurePreserving V.toHomeomorph.toMeasurableEquiv volume volume:= ((show MeasurePreserving (B).toHomeomorph.toMeasurableEquiv volume volume from breakA n).symm); rw [← he.integral_comp' L]; exact integral_prod _ (he.integrable_comp_of_integrable p) -- tune
#print axioms billI
local notation "V"=>fun i:Fin n=> valise S (G i) (f i)
-- one price result any pair.Es.V
lemma orches : (∫ p, concert S x y G J f p)= inner ℂ x (Rail (fun i=> valise S (G i) (f i)) J y) := by
 induction n generalizing x y with
 | zero=> rw [Points.volume_nil,integral_dirac]; unfold concert pitch Rail Each; rw [Joint.materialize,Joint.trivial_at,List.finRange_zero, quiet, quiet,one_mul]
 | succ n ih=>
    let T:=Points.tail (n:=n); let X:= Points.cons (n:=n); let G':= Fin.tail G; let B₀:= s1 n J; let F' := fun (x:E4)=>optx S (G 0) x; let A(x):=(F' x)*B₀; let U:= Fin.tail f
    let Gui:=(fun i=>valise S (G' i) (U i)); let q:H:= Rail Gui (rump J) y
    let Camp(r:E4)(p:Points n):= concert S x y G J f (X r p); have hc(t:E4)(b:Points n): Camp t b= f 0 t* concert S ((A t).adjoint x) y G' (rump J) U b :=by
       unfold Camp X concert; rw [pitch_step, Joint.materialize,Joint.combine_at,head_cons,tail_cons]; rw [ContinuousLinearMap.adjoint_inner_left]; rw [mul_assoc]; rfl
    rw [Pour _ (billI ..)]; change (∫ z:E4, ∫ p:Points n,Camp z p)=_; simp_rw [hc,integral_const_mul, ih, Rail_step] -- last rewrites all (incl rump(n dep)? no automatic.S.)
    change (∫ z:E4, f 0 z* inner ℂ ((A z).adjoint x) q) = inner ℂ x (valise S (G 0) (f 0) (B₀ q)); simp_rw [ContinuousLinearMap.adjoint_inner_left]; exact sell_in S x (B₀ q) .. -- dirac problem factor 1
#print axioms orches
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
