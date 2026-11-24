import YM.SU5.Reconstruction.UVPrice.Population
/-!
# Low energy chamber closure odd alias.Hearth with far moments.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
variable {Γ: AddSubgroup ℝ}
local notation "Q"=> Coupon a Γ
namespace Coupon
variable (q: Coupon a Γ)
local notation "P"=> S.ℚmeasure
local notation "μ₀" x:max => (P).diagonal x
noncomputable def billB (x:E4) (f: Coupon a Γ→ℂ)(q:Coupon a Γ) := (f q.twice).re-2* (inner ℂ (receipt x q) (f q)).re+‖receipt x q‖^2 * (f 0).re
lemma bill_p (x y:E4) : billB x (receipt y) q= ‖receipt x q-receipt y q‖^2:=by
 rw [norm_sub_sq (𝕜:=ℂ), squared q y]; unfold billB; change _ = _-2* (inner ℂ _ _).re + _; rw [no]; simp; ring
lemma bill_sum (s:Finset Q)(x:E4): Continuous (fun p:E4=> ∑ i∈s,billB x (receipt p) i):= by unfold billB; fun_prop
lemma allowed_bill (x:E4)(v:H): Integrable (fun p=>billB x (receipt p) q) (μ₀ v) := by
 let m:= μ₀ v; let t:= ((firm S q).price.rent P v); let r:=((firm S q.twice).price.rent P v)
 unfold billB; simp only [no,Complex.one_re,mul_one]; exact ((r.re).sub ((( (innerSL ℂ (receipt x q))).integrable_comp t).re.const_mul 2)).add (integrable_const _)
lemma wanBill (x:E4)(v:H): (∫ y,billB x (receipt y) q∂μ₀ v)= billB x (tagT S v) q:= by
 let m:= μ₀ v; let t:= ((firm S q).price.rent P v); let r:=((firm S q.twice).price.rent P v); let F:ℂ→L[ℂ] ℂ:= innerSL ℂ (receipt x q); let u(y):=receipt y q; let A(y):= (F (u y)).re
 have hb:= (F.integrable_comp t).re.const_mul (2:ℝ); -- tune API
 unfold billB; simp only [no,Complex.one_re,mul_one]; erw [integral_add (f:=fun y=> (receipt y _).re-2*(inner ℂ _ _).re) (r.re.sub hb) (integrable_const _),integral_sub r.re hb, integral_const_mul]; rw [integral_const, tag_zero,Registers.size,Complex.ofReal_re]; change (∫ p, Complex.re (receipt p q.twice)∂m)- 2*(∫ p, (F (u p)).re ∂m)+_=_
 rw [show (∫ p, (receipt p q.twice).re∂m)=(tagT S v q.twice).re from by rw [pays_t]; exact integral_re r];
 rw [show (∫ p, (F (u p)).re∂m)=(inner ℂ (receipt x q) (tagT S v q)).re from ?_,smul_eq_mul]; ring
 rw [pays_t]; exact (integral_re (F.integrable_comp t)).trans (congrArg Complex.re (F.integral_comp_comm t))
variable (d:Dense (Γ:Set ℝ))(k:Backs S)
include d
-- separate with one tiny t shelf and finitely many low checks
lemma above_shelf (x:E4)(p:0≤x a):∃ (q:Coupon a Γ)(u:ℝ),0<u∧∀ y∈Shelf S, x a+1 ≤ y a→u≤ billB x (receipt y) q:= by
 obtain ⟨w,g,h⟩:= d.exists_mem_open (U:=Ioi (0:ℝ)) isOpen_Ioi nonempty_Ioi
 let v:= (⟨w,g⟩:Γ); have ht:0<(v:ℝ):= h; let q:= Coupon.ray a v ht.le; let t:= q.dt; have hx : 0 < (t:ℝ):= by unfold t q; rw [ray_time,Real.coe_toNNReal _ ht.le]; exact ht
 let T:=‖receipt x q‖; let M:= Real.exp (-(t:ℝ)*(x a+1)); have l:0 < T-M:= by unfold T M; rw [amount, sub_pos, favor, max_eq_right p,Real.exp_lt_exp]; linarith
 refine ⟨q,(T-M)^2,pow_pos l 2,fun y h r=>?_⟩; rw [bill_p]; apply pow_le_pow_left₀ l.le
 refine le_trans (sub_le_sub_left ?_ T) (norm_sub_norm_le (receipt x q) _); rw [amount]; unfold M favor; rw [Real.exp_le_exp]; apply mul_le_mul_of_nonpos_left (le_trans r (le_max_right ..)) (by linarith)
include k
lemma on_shelf (x:E4) (p:0≤x a)(t:x∉Shelf S) : ∃ (s:Finset Q) (u:ℝ),0<u∧∀ y∈Shelf S,u ≤∑ q∈s, billB x (receipt y) q:=by
 let U:= Beneath S (x a+1); let W(q:Q):={y:E4| 0< billB x (receipt y) q}; have hx(q:Q): IsOpen (W q):= isOpen_lt continuous_const (show Continuous (fun p=> billB x (receipt p) q) from by unfold billB; fun_prop)
 obtain ⟨s,v,w,h⟩:= above_shelf S d x p
 have u : U⊆ ⋃ q,W q:= by
   intro y r
   have he: ∃ q:Q, receipt x q≠ receipt y q:= not_forall.mp (show ¬ (∀ q:Q, receipt x q=receipt y q) from fun w=> t ((no_alias d p (shelf_ePays S _ r.1) (funext w)).symm ▸ r.1))
   obtain ⟨q,e⟩:= he
   exact mem_iUnion.mpr ⟨q, (by change 0< billB x (receipt y) q; rw [bill_p]; exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr e)) 2)⟩
 obtain ⟨Z,z⟩:= (k (x a+1)).elim_finite_subcover W hx u
 let T:= insert s Z; let f(y):=∑ i∈T,billB x (receipt y) i
 have e(y)(i)(p:i∈T): billB x (receipt y) i≤ f y:= Finset.single_le_sum (f:=fun i=>billB x (receipt y) i) (fun i _=> by rw [bill_p]; positivity) p
 have hb:∀ y∈Shelf S,y∉U → v ≤ f y:=fun y r hz => (h y r (le_of_not_ge (show ¬ y a≤ _ from fun t=> hz ⟨r,t⟩))).trans (e _ _ (Finset.mem_insert_self ..)) -- le not ge? hz ¬ y ≤ x... ⇒ x< y
 by_cases u:U.Nonempty
 · obtain ⟨y,y',g⟩:= (k _).exists_isMinOn u (bill_sum (Γ:=Γ) T x).continuousOn
   obtain ⟨i,h,vi⟩:= mem_iUnion₂.mp (z y')
   refine ⟨T,min (f y) v,lt_min ((show 0< billB x (receipt y) i from vi).trans_le (e y i (Finset.mem_insert_of_mem h))) w,fun y h=>?_⟩
   by_cases t:y∈U; exact (min_le_left ..).trans (g t); exact (min_le_right ..).trans (hb y h t)
 refine ⟨T,v,w,fun y r=> hb y r (fun h=>u ⟨y,h⟩)⟩
lemma in_price (x:E4)(p:0≤x a)(h:receipt x ∈ Population S Γ): x∈Shelf S:= by
 by_contra t; obtain ⟨s,u,u₀,b⟩:= on_shelf S d k x p t
 let T:={f:Q→ℂ|u*(f 0).re≤∑ i∈s,billB x f i}; have ht:IsClosed T:= isClosed_le (show Continuous (fun f:Q→ℂ=> u*(f 0).re) from by fun_prop) (by unfold billB; fun_prop)
 have he: receipt x∈T:= closure_minimal ?_ ht h
 swap; · rintro v ⟨v,rfl⟩; change u*(tagT S v (0:Q)).re ≤ _; rw [tag_zero]; simp_rw [← wanBill]; rw [← integral_finsetSum s (fun i _=> allowed_bill ..)]; refine le_trans ?_ (integral_mono_ae (integrable_const (μ:=μ₀ v) u) (integrable_finsetSum _ fun i _=> allowed_bill ..) ((shelf_ae S v).mono fun y t=>b _ t)); rw [integral_const, Complex.ofReal_re,Registers.size,smul_eq_mul,mul_comm]
 change u*(receipt x (0:Q)).re ≤ _ at he; simp [bill_p] at he; linarith -- tune
end Coupon
end YM.Roy
