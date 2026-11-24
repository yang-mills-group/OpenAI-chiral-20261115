import YM.CF.DPress.Analytic.Compass
/- Dual pricing. collections of Scalar evaluations. Valid data have nonempty upper bounds, particular lemmas buy so. Need NOT claim globally linear response on unqualified data! Easiest signature uses sSup norma.X plus {0}. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open scoped Topology Classical BigOperators
variable {X Y I:Type*} {a b R:ℝ}
abbrev Dial (X:Type*) := Set (X→ℂ) -- not CF.Dial when in open.Beware. rename
structure Budget (V:Dial X)(x:X)(a:ℝ) :Prop where
 p : 0≤a
 t : ∀ f∈V, ‖f x‖≤a
def coins(V:Dial X)(x:X):Set ℝ:= insert 0 ((fun f:X→ℂ=> ‖f x‖) '' V)
variable (V:Dial X) -- patch
abbrev meter(V:Dial X)(x:X) := sSup (coins V x)
abbrev Live(V:Dial X)(x:X):= ∃ a:ℝ,Budget V x a
variable {V} {x:X}
lemma heart : Budget V x a↔ a∈upperBounds (coins V x):=by
 constructor; rintro ⟨p,h⟩ i g; rcases g with rfl|⟨i,t,rfl⟩; exact p; exact h _ t; intro g; exact ⟨g (Set.mem_insert _ _),fun i h=>g (Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ h))⟩
lemma lapLives (p:Live V x): IsLUB (coins V x) (meter V x):= isLUB_csSup (Set.insert_nonempty ..) (let ⟨a,t⟩:=p; ⟨a,heart.mp t⟩)
lemma Budget.less(v:Budget V x a): meter V x≤a:= (lapLives ⟨a,v⟩).2 (heart.mp v)
lemma Budget.up (p:Budget V x a)(h:a≤ b):Budget V x b:= ⟨p.p.trans h,fun f t=>(p.t f t).trans h⟩
lemma Live.pays (p: Live V x): Budget V x (meter V x):= heart.mpr (lapLives p).1
variable [DecidableEq I] {S:Finset I} (A:I→ Dial X)(c:I→ℝ)(p:∀ i∈S, 0 ≤ c i)
-- allow zero tests ALWAYS. linear combos arbitrary phases. deterministic. no geometry tolerance.
def tray(I:Dial X):=insert 0 I
def staff(S:Finset I):Dial X:= {g|∃ (t:I→ X→ℂ)(u:I→ℂ), (∀ i∈S,t i∈ tray (A i) ∧ ‖u i‖≤ 1) ∧ g = (fun x=> ∑ i∈S,(c i:ℂ)*u i*t i x)}
lemma tray_on : Budget V x a ↔ Budget (tray V) x a:= by
 constructor; rintro p; refine ⟨p.p,?_⟩; rintro i (rfl|g); change ‖(0:ℂ)‖≤_; rw [norm_zero]; exact p.p; exact p.t i g; rintro p; exact ⟨p.p,fun i h=>p.t _ (Set.mem_insert_of_mem _ h)⟩
include p
lemma staff_up (a:I→ℝ)(v:∀i∈S,Budget (A i) x (a i)): Budget (staff A c S) x (∑ i∈S,c i*a i):=by
 refine ⟨sum_nonneg (fun i t=>mul_nonneg (p i t) (v i t).p),?_⟩; rintro f ⟨t,u,k,rfl⟩; refine (norm_sum_le ..).trans (sum_le_sum (fun i h=>?_)); rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (p i h)]; exact mul_le_mul (mul_le_of_le_one_right (p i h) (k i h).2) ((tray_on.mp (v i h)).t _ (k i h).1) (norm_nonneg _) (p i h)
-- exact aggregation use induction summing maximal cash via support.Lim variant replace one-by-one
omit p in
private lemma realize (z:ℂ):∃ u:ℂ, ‖u‖≤1 ∧ u*z= (‖z‖ :ℝ):=by
 by_cases h:z=0; subst z; exact ⟨0,by simp,by simp⟩; refine ⟨(‖z‖:ℝ)/z, ?_, by field_simp⟩; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr h)]
lemma staffRank (a:I→ℝ)(v:∀i∈S,a i∈coins (A i) x): (∑ i∈S,c i*a i)∈ coins (staff A c S) x:=by -- parsing wrong notation ∑ extended
 have ht(i:I)(t:i∈S):∃ f∈tray (A i), ‖f x‖=a i:=by obtain h|⟨k,b,h⟩:= v i t; exact ⟨0, Set.mem_insert ..,(show ‖(0:ℂ)‖= _ from (norm_zero.trans (Set.mem_singleton_iff.mp h).symm))⟩; exact ⟨k,Set.mem_insert_of_mem _ b,h⟩ -- tune h eq
 choose! f u z using ht; choose F g l using realize
 let t(i:I):= F (f i x); apply Set.mem_insert_of_mem _; refine ⟨(fun y=> ∑ i∈S, (c i:ℂ)* t i * f i y),⟨ f,t,fun i h=> ⟨u _ h,g _⟩,rfl⟩,?_ ⟩; let b:= ∑ i∈S,c i*a i; change ‖∑ i∈S, (c i:ℂ)* t i * f i x‖=b; rw [show (∑ i∈S, (c i:ℂ)* t i * f i x) = (b:ℂ) from ?_,Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun i h=>mul_nonneg (p i h) (z _ h ▸ norm_nonneg _))]; unfold b; push_cast; apply sum_congr rfl; intro i h; rw [mul_assoc,l, z i h]
-- do LUB recursion. note summation cast.Fault.
lemma staff_due (tS:Budget (staff A c S) x b)(h:∀ i∈S,Live (A i) x): (∑ i∈S,c i * meter (A i) x) ≤ b:=by
 have ht(i:I)(w:i∈S): meter (A i) x∈ closure (coins (A i) x):= (lapLives (h i w)).mem_closure (Set.insert_nonempty ..)
 let u:=Set.pi (↑S) (fun i=> coins (A i) x); have hm : (fun i=> meter (A i) x)∈closure u:= mem_closure_pi.mpr ht
 let F(v:I→ℝ):=∑ i∈S, c i*v i; have hF: Continuous F:=by unfold F; fun_prop
 exact closure_minimal (s:=u) (fun i hi=> heart.mp tS (staffRank A c p _ hi)) (isClosed_le hF (continuous_const (y:=b))) hm
omit p
section profiles
variable {l:X}{f:ℂ→X}
abbrev Brings (R:ℝ)(f:ℂ→X)(u:X)(V:Dial X): Prop:= ∀ g∈V, Disc R (g ∘ f) (g u)
lemma Brings.stage (T:∀ i∈S,Brings R f l (A i)): Brings R f l (staff A c S):=by
 rintro g ⟨t,u,h,rfl⟩; apply Disc.sum S (fun i z=>_); intro i p; apply Disc.scale ((c i:ℂ)*u i); rcases (h i p).1 with q|q; ·  rw [q]; exact Disc.zero
 exact T i p (t i) q -- tune `partial implicit application`
lemma Brings.win (p:Brings R f l V)(v:∀ z∈ank R,Budget V (f z) a)(h:1<R): Budget V l (a/(R-1)):= ⟨div_nonneg (v _ (planeOne h)|>.p) (sub_nonneg.mpr h.le),fun i t=>(p i t).value (fun x u=>(v x u).t i t) h⟩
end profiles
end YM.CF.DPress.Fees
