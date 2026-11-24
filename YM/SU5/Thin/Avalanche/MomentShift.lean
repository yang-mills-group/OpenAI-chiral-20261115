import YM.SU5.Circuit.Oriole
/-!
# Under changing bodies

Use rotational trick (variant of Regis/Breeze) for a Wick recursion. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Regis.Resonance
open Function Filter Metric MeasureTheory ProbabilityTheory NormedSpace InnerProductSpace Finset
open scoped Topology BigOperators InnerProductSpace ENNReal NNReal Classical
section
variable {E E': Type*}[MeasurableSpace E][MeasurableSpace E']{A:Measure E}{U:Measure E'}
structure Valued (A:Measure E)(f:E→ℝ):Prop where
 charge : ∀ p:ℝ≥0, MemLp f p A
namespace Valued
local notation "AΣ"=> Valued A
variable {f g:E→ℝ}
lemma accepted [IsFiniteMeasure A] (h:Valued A f): Integrable f A:= (h.charge 1).integrable le_rfl
include g -- tune no f type mismatch
lemma times (h:AΣ f)(v:AΣ g): AΣ (f*g):=by
 constructor; intro k; let r:ℝ≥0∞:=k; haveI: ENNReal.HolderTriple (2*r) (2*r) r :=⟨by rw [← two_mul, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ENNReal.mul_inv_cancel_left (by norm_num:(2:ℝ≥0∞)≠0) (by norm_num)]⟩
 let b:ℝ≥0:=2*k; have he: (b:ℝ≥0∞)=2*r:=by unfold r b; push_cast; rfl -- tune
 have hk: MemLp g (2*r) A:=he ▸ v.charge b; have hp: MemLp f (2*r) A:=he ▸ h.charge b; exact hk.mul hp
lemma gain (h:AΣ f)(v:AΣ g): AΣ (f+g):=⟨fun k=> (h.charge k).add (v.charge k)⟩
lemma loss (h:AΣ f)(v:AΣ g): AΣ (f-g):=⟨fun k=> (h.charge k).sub (v.charge k)⟩
omit g
lemma cash[IsFiniteMeasure A] (u:ℝ): Valued A (fun _=> u):=⟨fun k=>memLp_const u⟩
lemma pulled (h:AΣ f){y:E'→ E}(p:MeasurePreserving y U A): Valued U (f ∘ y):=⟨fun k=> (h.charge k).comp_measurePreserving p⟩
lemma neg (h:AΣ f): AΣ (-f):=⟨fun k=> (h.charge k).neg⟩
lemma toll(x:ℝ)(h:AΣ f): AΣ (x•f):=⟨fun k=> (h.charge k).const_smul x⟩ -- type
lemma upward [IsFiniteMeasure A] (h:AΣ f)(n:ℕ): AΣ (f^n):=by induction n with| zero=>rw [pow_zero]; exact cash 1|succ n ih=>rw [pow_succ]; exact ih.times h
lemma more(T:List (E→ℝ))[IsFiniteMeasure A] (h:∀ i∈T,AΣ i): AΣ T.prod:=by induction T with |nil=>exact cash 1| cons f T ih=> exact (h f (List.mem_cons_self)).times (ih (fun i t=>h i (List.mem_cons_of_mem _ t)))
lemma finMore {ι:Type*}(X: Finset ι) (f:ι→E→ℝ)[IsFiniteMeasure A] (h:∀ i,AΣ (f i)):AΣ (∑ i∈X, f i):=by induction X using Finset.induction_on with| empty=>rw [sum_empty]; exact cash 0| @insert i X e ih=>rw [sum_insert e]; exact (h i).gain ih
lemma finBeam {ι:Type*}(X: Finset ι) (f:ι→E→ℝ)[IsFiniteMeasure A] (h:∀ i,AΣ (f i)):AΣ (∏ i∈X, f i):=by induction X using Finset.induction_on with| empty=>rw [prod_empty]; exact cash 1| @insert i X e ih=>rw [prod_insert e]; exact (h i).times ih
end Valued
inductive Beat (A:Measure E): (ℝ→E→ℝ)→(E→ℝ)→Prop where
| oneB (u:ℝ→ℝ)(d:ℝ)(b:HasDerivAt u d 0) (f:E→ℝ)(h:Valued A f) : Beat A (fun t=>u t • f) (d • f)
| two {f f':ℝ→E→ℝ}{v v':E→ℝ}: Beat A f v→Beat A f' v'→ Beat A (f+f') (v+v')
namespace Beat
local notation "P" => Beat A
variable {T T':ℝ→E→ℝ}{b b':E→ℝ}
lemma label(t:P T b) (y:ℝ): Valued A (T y) ∧ Valued A b:=by induction t with| oneB u d e f p=> exact ⟨p.toll _,p.toll _⟩| two _ _ t u=> exact ⟨t.1.gain u.1,t.2.gain u.2⟩
lemma mul_toll (y:ℝ→ℝ)(t:ℝ)(v:HasDerivAt y t 0)(p:P T b): P (fun s=> y s • T s) (y 0 • b + t • T 0):=by
 induction p with
 | oneB u d h f p=> convert! Beat.oneB (y*u) (t*u 0+y 0*d) (v.mul h) f p using 1; ext x; simp [smul_eq_mul,mul_assoc]; ext x; simp [smul_eq_mul]; ring -- autoImplicit parameter fixed?
 | @two f f' v v' p q e u=>
    convert! Beat.two e u using 1; ext i j; simp [smul_eq_mul,mul_add]; dsimp; rw [smul_add,smul_add]; abel -- tighten
lemma servile (x:E→ℝ)(h:Valued A x)(p:P T b): P (fun s=>x*T s) (x*b):=by
 induction p with
 | oneB u d h f p=>
    convert Beat.oneB u d h (x*f) (Valued.times (by assumption) p) using 1; ext i j; simp [smul_eq_mul,mul_left_comm]; ext i; simp [smul_eq_mul,mul_left_comm]
 | @two f g v v' p q e u=> convert Beat.two e u using 1; ext i j; simp [mul_add]; rw [mul_add]
lemma mix (u:P T b)(v:P T' b'):P (T*T') (T 0*b'+b*T' 0):=by
 induction u with
 | oneB f d h g p =>
    convert mul_toll f d h (servile g p v) using 1; ext i j; simp [smul_eq_mul,mul_assoc]; ext i; simp [smul_eq_mul,mul_assoc]
 | @two f f' b₁ b₂ h h' ih ih'=> rw [add_mul, Pi.add_apply,add_mul,add_mul,add_add_add_comm]; exact Beat.two ih ih'
lemma neg (u:P T b):P (-T) (-b):=by induction u with
 | oneB f d h g p => convert! oneB f d h (-g) p.neg using 1 <;> first| rfl | (ext; simp) -- syntax
 | @two f f' b₁ b₂ h h' ih ih' => simp_rw [neg_add]; exact Beat.two ih ih'
variable [IsFiniteMeasure A]
lemma stand (x:E→ℝ)(h:Valued A x): P (fun _=> x) 0:= by simpa using (oneB (fun _=> (1:ℝ)) 0 (hasDerivAt_const _ _) x h (A:=A)) -- arguments
lemma entry(p:P T b): HasDerivAt (fun t=> ∫ i,T t i∂A) (∫ i,b i∂A) 0:=by
 induction p with
 | oneB u d h f p=> simp_rw [Pi.smul_apply,smul_eq_mul,integral_const_mul]; exact h.mul_const _
 | @two f f' v v' p q e u=> simp_rw [Pi.add_apply,integral_add (f:= fun x=> v x) (g:=fun x=> v' x) (p.label 0).2.accepted (q.label 0).2.accepted, integral_add ((p.label _).1.accepted) ((q.label _).1.accepted)]; exact e.add u -- tune
end Beat
end
end YM.Regis.Resonance
