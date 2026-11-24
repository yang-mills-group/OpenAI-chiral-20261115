import YM.SU5.Voyager.Lunge
/-! # Accounting for packed spatial stencil (general finite axes price)
 No uniform across uncompressed room assumed. Expose QuiltC for direct use.
 Tilt equality in ℚmeasure only, various interested apertures may differ (operators kept straight).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Orbit.Prairie
open Function Filter Set Metric Finset Complex MeasureTheory Measure
open Boundary Boundary.Probe Caino
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators Classical
-- spatial dimensions
variable {K:Type*}[Fintype K][DecidableEq K]
local notation "X"=> Terrain K
variable {H: Hilbert} (T: Orbit H (Terrain K)) (P: PVM H (Terrain K))
local notation "U"=> T.translation
local notation "μ" y:max=> P.diagonal y
variable (g:ℝ)(i n:ℕ)(k d:K)(x y:H)
local notation "ρ[" k "]"=> sight g k
private lemma thick_comm (r z:X):Commute (U r) (U z):=by change (U _).comp _= (U _).comp _; rw [T.sends,T.sends,add_comm]
def dart := U ρ[k]-1
def lamps (S:Finset K): X→ℝ:= ∏ i∈S,Orbit.mallet ρ[i]
local notation "Θ" k:max=> dart T g k
lemma dartSpec : (Θ k) x=U ρ[k] x-x:=rfl
lemma dart_fee : ‖(Θ k) x‖≤ 2*‖x‖:=by -- syntax
 rw [dartSpec]; apply (norm_sub_le ..).trans; rw [T.unitary]; linarith
lemma darts_n (k:K)(n:ℕ) : ‖((Θ k)^n) x‖≤ 2^n*‖x‖:=by induction n with| zero=> simp| succ n ih=>rw [pow_succ']; exact (dart_fee T g k _).trans ((mul_le_mul_of_nonneg_left ih (by norm_num)).trans_eq (by rw [pow_succ' (2:ℝ)]; ring))
lemma lamps_cont (S:Finset K): Continuous (lamps g S):=by
 induction S using Finset.induction_on with
 | empty=>simp [lamps]; exact continuous_const -- tune
 | insert k S hs h=> rw [lamps, prod_insert hs]; exact (mallet_t ..).mul h
lemma lamps_p(S:Finset K)(p:X):0 ≤ lamps g S p:=by
 induction S using Finset.induction_on with
 | empty=> change 0 ≤ lamps g ∅ p; simp [lamps]
 | insert i s hi h=> rw [lamps,prod_insert hi]; exact mul_nonneg (mallet_p ..) h
variable (p:T.Spectrum P)
include p
lemma may_dart : μ ((Θ k) x)= serves (μ x) (mallet ρ[k]) 1:=by rw [dartSpec,windMarker T P _ x p]; unfold serves; rw [pow_one]
lemma n_dart : μ (((Θ k)^n) x)= serves (μ x) (mallet ρ[k]) n:=by
 induction n with
 | zero=> rw [pow_zero, serves,pow_zero]; change μ x = (μ x).withDensity (ENNReal.ofReal ∘ 1); rw [show ENNReal.ofReal ∘ (1 :X → ℝ)=(1:X→ℝ≥0∞) from funext fun i=>by simp, withDensity_one]
 | succ n ih=>rw [pow_succ']; let t:=((Θ k)^n) x; change (P.diagonal ((Θ k) t))=_; rw [may_dart ..]; unfold serves; unfold t; rw [ih,pow_one,serves,colors (μ x) ((mallet_t ..|>.pow n).measurable) ((mallet_t ..).measurable) (f:=mallet _^n) (fun k=> pow_nonneg (mallet_p _ k) _),pow_succ]; exact p -- tune
-- pair bounds
omit p
def Offer (a b:ℝ):Prop:= ∀ u:X,a≤ u k→ ‖inner ℂ x (U u y)‖≤ b
private lemma wander(u:X) : T.translation u * T.translation ρ[d] = T.translation (u+ρ[d]):= T.sends ..
lemma walk_off (u:X): inner ℂ ((Θ k) x) ((U u) y) = inner ℂ x ((U (u-ρ[k])) y)-inner ℂ x ((U u) y):=by
 rw [dartSpec,inner_sub_left]; let V:= U (u-ρ[k]); rw [← T.playAngle ρ[k] x (V y),← ContinuousLinearMap.comp_apply (U ρ[k]),T.sends]; rw [show ρ[k]+(u-ρ[k])=u from add_sub_cancel ..] -- orientation?
lemma talk_off (u:X): inner ℂ x (U u ((Θ k) y))=inner ℂ x ((U (u+ρ[k])) y)-inner ℂ x (U u y):=by rw [dartSpec,map_sub,inner_sub_right,← ContinuousLinearMap.comp_apply (U u),T.sends]
variable {a b:ℝ}
lemma offsetL (δ:ℝ)(z:Offer T k x y a b)(w:(ρ[d]) k=δ)(b₀:0 ≤ δ): Offer T k ((Θ d) x) y (a+δ) (2*b):=by
 -- need δ≥0 add; for u k≥a+δ yes to z u but if δ neg need separate
 intro u t; rw [walk_off]; apply (norm_sub_le ..).trans; refine (add_le_add (z _ ?_) (z _ ?_)).trans_eq (by ring); rw [PiLp.sub_apply,w]; linarith; linarith
lemma offsetR (z:Offer T k x y a b)(w: (ρ[d]) k=0): Offer T k x ((Θ d) y) a (2*b):=by
 intro u t; rw [talk_off]; apply (norm_sub_le ..).trans; refine (add_le_add (z _ ?_) (z u t)).trans_eq (by ring); rw [PiLp.add_apply,w]; linarith
lemma leapFirst (q:0<g)(u:Offer T k x y a b): Offer T k (((Θ k)^n) x) y (a+n*g) (2^n*b):=by
 induction n with
 | zero=> simpa using u
 | succ n ih=> rw [pow_succ',pow_succ']; simpa only [ContinuousLinearMap.mul_apply,Nat.cast_add,Nat.cast_one,mul_assoc,add_mul,one_mul, ← add_assoc] using offsetL T g k k _ _ g ih (by rw [shine_s]; simp) q.le
lemma fling (u:Offer T k x y a b)(t:d≠k): Offer T k (((Θ d)^n) x) (((Θ d)^n) y) a (2^(2*n)*b):=by
 have he:(ρ[d]) k=0:= by rw [shine_s]; simp [t];
 induction n with
 | zero=> simpa using u
 | succ n ih=>
    rw [pow_succ']; have hv:=offsetR T g k d _ _ (offsetL T g k d _ _ 0 ih he (le_refl _)) he; rw [add_zero] at hv
    rw [show (2:ℝ)^(2*(n+1))*b=2*(2*(2^(2*n)*b)) by rw [mul_add, pow_add]; ring]; exact hv
include p
lemma garment (S:Finset K) (k:K) (b:ℝ) (e:k∉ S) (z:Offer T k x x a b) : ∃ y:H, μ y= chisels (lamps g S^n) (μ x)∧ Offer T k y y a (((2:ℝ)^(2*n))^S.card*b):=by
 induction S using Finset.induction_on with
 | empty=> refine ⟨x,by simp [lamps,chisels],by simpa using z⟩ -- tune
 | insert i s hi ih =>
   obtain ⟨u,p₀,v⟩:=ih (notMem_mono (subset_insert ..) e); let y:= ((Θ i)^n) u; refine ⟨y, ?_,?_⟩
   · unfold y; rw [n_dart T P g n i u p,p₀, serves,colors (μ x) ((lamps_cont ..|>.pow n).measurable) ((mallet_t ..|>.pow n).measurable) (fun i=>pow_nonneg (lamps_p _ s i) _),show lamps g (insert i s)= lamps g s*mallet ρ[i] from (prod_insert hi).trans (mul_comm ..),mul_pow];
   rw [card_insert_of_notMem hi,pow_succ',mul_assoc]; exact fling T g n k i _ _ v (Ne.symm (not_or.mp (not_congr mem_insert |>.mp e)).1)
end YM.Spectral.Orbit.Prairie
#print axioms YM.Spectral.Orbit.Prairie.garment
