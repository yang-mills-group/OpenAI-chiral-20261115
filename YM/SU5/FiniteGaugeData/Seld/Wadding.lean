import YM.SU5.FiniteGaugeData.Seld.Sault
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
-- prepaid exit. supply bounded both sides and HOL
variable (n m:ℕ)
def parabola : ℕ → ℂ → H.Op
 | 0=> S.F
 | n+1 => fun z=>let t:=z/2; looper S t * parabola n t
lemma midK (z:ℂ)(h:z∈inside): z/2∈inside:=by change 0<z.re at h; change 0<(z/2).re; simp [h]
abbrev Cache(n:ℕ) := R^n
local notation "K"=> Cache S
lemma gear(z:ℂ)(p:z∈inside)(n:ℕ): Commute R (parabola S n z):=by
 induction n generalizing z with | zero=> exact cupF S z p | succ n ih=> exact (show Commute R (looper S (z/2)) from (dorsal S _ (midK z p)).trans (jalousie S _ (midK z p)).symm).mul_right (ih _ (midK z p))
lemma recover (z:ℂ)(h:z∈inside): Cache S n * parabola S n z=S.F z:=by
 induction n generalizing z with
 | zero=> change R^0 * S.F z=_; rw [pow_zero,one_mul]
 | succ n ih=>
    let p:= z/2; have he:=midK z h; have hv:Commute (K n) R := (Commute.refl R).pow_left n; change R^(n+1)* (looper S p * parabola S n p)=_
    let A:=looper S p; let B:= parabola S n p
    calc
     _ = R*(K n*A)*B:=by change R^(n+1)*(A*B)=_; rw [pow_succ']; unfold Cache; simp only [mul_assoc]
     _ = R*A*(K n*B):=by rw [(show Commute R A from (dorsal S _ he).trans (jalousie S _ he).symm).pow_left n|> (show Commute (K n) A from ·) |>.eq]; simp only [mul_assoc]
     _ = S.F p*S.F p:=by rw [show R*A=_ from dorsal S _ he, show K n*B=_ from ih _ he]
     _ = _:= (S.pairs he he|>.symm).trans (congrArg S.F (add_halves z))
lemma change_m (z:ℂ)(h:z∈inside): parabola S n z * Cache S n = S.F z:= ((gear S z h n).pow_left n).eq.symm.trans (recover S n z h)
lemma Bokeh : AnalyticOnNhd ℂ (parabola S n) inside:=by
 induction n with | zero=>exact S.localHeat | succ n ih=>
    intro z p; let f(t:ℂ):ℂ:= t/2; change AnalyticAt ℂ (fun z=>looper S (f z)*parabola S n (f z)) z
    have hf : AnalyticAt ℂ f z:= (analyticAt_id (𝕜:=ℂ)).div analyticAt_const (by norm_num); have he: AnalyticAt ℂ S.F (f z):= S.localHeat _ (midK z p); exact AnalyticAt.mul ((he.sub he.deriv).comp hf) ((ih (f z) (midK z p)).comp hf) -- s.a timeout
lemma K_E(z:ℝ≥0)(h:0<z): Cache S n * parabola S n (duration z)=S.E z:= (recover S n _ (dur.mpr h)).trans (S.roots_heat h)
lemma cache_I : Injective (Cache S n):= by induction n with
 | zero=> unfold Cache; rw [pow_zero]; exact (injective_id (α:=H.space))
 | succ n ih=> exact show Injective _ from fun x y hx=> ih (paranoid S (by change (R^(n+1)) x=(R^(n+1)) y at hx; rw [pow_succ'] at hx; exact hx)) -- tune
abbrev Bench : Submodule ℂ H:= ⨅ n:ℕ,(Cache S n).range
local notation "W"=> Bench S
lemma bench : x∈Bench S ↔ ∀ n:ℕ, x∈Set.range (K n):= Submodule.mem_iInf _
def hall(n:ℕ): Bench S →ₗ[ℂ] H where
 toFun w:= ((bench S w.val|>.mp w.property) n).choose
 map_add' x y:= by apply cache_I S n; rw [map_add, ((bench S x.val |>.mp x.property) n).choose_spec, ((bench S y.val|>.mp y.property) n).choose_spec]; exact ((bench S (x+y).val|>.mp (x+y).property) n).choose_spec
 map_smul' c x:= by change _= c • _; apply cache_I S n; rw [map_smul,((bench S x.val |>.mp x.property) n).choose_spec]; exact ((bench S (c • x).val|>.mp (c • x).property) n).choose_spec
lemma releases (x:Bench S): Cache S n (hall S n x)=x.val:= ((bench S x.val |>.mp x.property) n).choose_spec
lemma downstairs (u:Bench S): Cache S n (hall S (m+n) u)=hall S m u:= by apply cache_I S m; rw [releases]; refine Eq.trans ?_ (releases S (m+n) u); unfold Cache; rw [pow_add]; rfl
lemma home : ∀ v:Bench S,hall S 0 v=v.val := fun v=>by simpa [Cache] using releases S 0 v
variable (z:ℂ)(p:z∈inside)(a':Bench S)
lemma rain (p:z∈inside) : S.F z x∈ Bench S:= (bench S _).mpr fun n=> ⟨parabola S n z x,DFunLike.congr_fun (recover S n z p) x⟩
lemma ray (h:0<u): S.E u x∈ Bench S:= S.roots_heat h ▸ rain S x _ (dur.mpr h) -- tune
lemma hail (h:∀ t,S.E t x=x): x∈Bench S:= h 1 ▸ ray S x 1 zero_lt_one
lemma bench_warm : Dense (W:Set H) := by apply Dense.mono ?_ (S.whole 1); rintro x ⟨y,rfl⟩; exact ray S y _ zero_lt_one
#print axioms bench_warm
#print axioms Bokeh
variable (A:H.Op)
abbrev pays (u:ℕ)(A:H.Op) := ∃ B:H.Op,A*K u=K u*B
lemma autumn (p:Commute A R):∀ u,pays S u A:=fun u=>⟨A,p.pow_right u⟩
lemma accepts (p:∀ u,pays S u A): A a'.val∈ Bench S:= by
 apply (bench S _).2; intro n; obtain ⟨B,z⟩:=p n; exact ⟨B (hall S n a'), (DFunLike.congr_fun z.symm (hall S n a')).trans (congrArg A (releases S n a'))⟩
-- lower receipts. q energy. every Bench element maps to Bench upon preimages
lemma altitude_H : hall S n a'∈ Bench S:= (bench S _).2 (fun m=> ⟨hall S (n+m) a',downstairs S m n _⟩)
def hill : W→ₗ[ℂ] W:= (hall S n).codRestrict _ (fun v=> altitude_H S n v)
lemma hill_comb (v:W): hall S n (hill S m v) = hall S (m+n) v:= by
 apply cache_I S n; rw [releases,downstairs]; rfl
variable (p':∀ u,pays S u A)
def park (p':∀ u,pays S u A) : W→ₗ[ℂ] W:= (A.toLinearMap.comp ((Bench S).subtype)).codRestrict _ (fun v=> accepts S v A p')
lemma park_κ (X:H.Op)(p':∀ u,pays S u A)(p:A*K n=K n*X): hall S n (park S A p' a') = X (hall S n a'):= by
 apply cache_I S n; rw [releases]; exact ((congrArg A (releases S n a')).symm).trans (DFunLike.congr_fun p (hall S n a'))
lemma comm_park (p:Commute A R): hill S n (park S A (autumn S A p) a')= park S A (autumn S A p) (hill S n a'):= Subtype.ext (park_κ S n a' A A _ (p.pow_right n))
variable {W':Type*}(ℱ:Filter W')(f:W'→Bench S)
def pays_to (f: W'→ Bench S)(x: Bench S) :Prop:= ∀ n,Tendsto (fun i=> hall S n (f i)) ℱ (𝓝 (hall S n x))
lemma tune_in (p:pays_to S ℱ f a') : Tendsto (fun i=>(f i).val) ℱ (𝓝 a'.val):= by simpa only [home] using p 0
lemma hill_limit (p:pays_to S ℱ f a'): pays_to S ℱ (hill S n ∘ f) (hill S n a'):= by intro m; simpa only [comp_apply,hill_comb] using (p (n+m)) -- rw needed
lemma cash_limit (p':∀ u,pays S u A)(p:pays_to S ℱ f a'): pays_to S ℱ (park S A p' ∘ f) (park S A p' a'):= by
 intro m; obtain ⟨g,h⟩:= p' m; simp_rw [comp_apply, park_κ S m _ A _ p' h]; exact (g.continuous.tendsto _).comp (p _)
lemma cache_cost : ∀ x:H,‖Cache S n x‖ ≤ ‖x‖:=by
 induction n with | zero=> simp [Cache] | succ n ih=> intro x; rw [Cache,pow_succ']; exact (ship_cost S (Cache S n x)).trans (ih x)
lemma cache_park (v:W)(n:ℕ): (hill S n (park S (Cache S n) (autumn S _ ((Commute.refl R).pow_left _)) v))=v:= by
 apply Subtype.ext; apply cache_I S n; exact releases S n _
lemma stronger (p:m≤n): ‖hall S m a'‖ ≤ ‖hall S n a'‖ := by obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le p; rw [←downstairs S k m]; exact cache_cost S k _
-- sequential density of E(t) vectors in every graph norm, simultaneously
lemma browse (u:ℝ≥0)(h:0<u): ∃ f:ℕ→H,pays_to S atTop (fun i=>⟨S.E u (f i),ray S _ _ h⟩) a':=by
 let r(n:ℕ):ℝ:=1/(n+1)
 choose g e using fun n:ℕ=> show ∃ x,‖S.E u x-hall S n a'‖ ≤ r n from (by obtain ⟨_,⟨x,rfl⟩,p⟩:= Metric.mem_closure_iff.mp (S.whole u (hall S n a')) (r n) (by unfold r; positivity); exact ⟨x,(by simpa [dist_eq_norm,norm_sub_rev (S.E u _)] using p.le)⟩)
 let f(n:ℕ): Bench S := ⟨S.E u (Cache S n (g n)),ray S _ _ h⟩
 have he(n:ℕ):hall S n (f n)=S.E u (g n):=by apply cache_I S n; rw [releases]; exact DFunLike.congr_fun ((cupE S u).symm.pow_right n).eq (g n)
 refine ⟨fun n=> K n (g n),show pays_to S atTop f a' from fun n=> tendsto_iff_norm_sub_tendsto_zero.mpr (?_)⟩; refine squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ tendsto_one_div_add_atTop_nhds_zero_nat; filter_upwards [eventually_ge_atTop n] with t ht; rw [←map_sub]; exact (stronger S _ n (f t-a') ht).trans (by rw [map_sub,he]; exact e t)
#print axioms cash_limit
#print axioms browse
#print axioms comm_park
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
