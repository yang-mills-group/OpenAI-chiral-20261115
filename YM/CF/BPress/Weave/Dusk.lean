import YM.CF.BPress.Weave.Jacob
import YM.CF.BPress.Wealth.Severe
/-! After jcost; split at PL cutoff. Unambiguous per severe support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(k:ℕ)(A:Seal X.Hcols→ Tender X)
def tookM (S T:Seal X.Hcols):= take1 (S∩T)
def arm (T:Seal X.Hcols)(i:X.Hcols):= univ.filter fun S:Seal X.Hcols=> S.card≤k ∧ tookM X S T=some i
def burden (i:X.Hcols)(T: Seal X.Hcols):=∑ j∈arm X k T i, A j T
def flareJ {Y:Type*}(b:Seal Y→ℝ)(i:Seal Y):= if k < i.card then b i else 0
def tailJ (S: Seal X.Hcols): Tender X:=if k < S.card then A S else (fun _=>0)
def stipendJ (k:ℕ)(a c:ℝ) := Real.exp (-(a/2)*k)*c
variable {X}{F:Fare X}{b:Tender X}{A}{a c:ℝ}(h:JacData X F A b a c)
namespace JacData
lemma took_spec (X:Bands s B)(v z:Seal X.Hcols)(i:X.Hcols)(p:tookM X v z=some i) : i∈v ∧ i∈z:=by
 unfold tookM take1 at p; split at p; next a=> exact mem_inter.mp (Option.some.inj p ▸ a.choose_spec)
 next t=> contradiction
include h
lemma rare (T S:Seal X.Hcols)(t:tookM X S T=none): A S T=0:=by
 rw [← h.ebb S]; apply h.localz; intro i v; simp only [notMem_empty,iff_false]; unfold tookM take1 at t; split at t; next=> contradiction
 next p=> exact fun u=> p ⟨i,mem_inter.mpr ⟨v,u⟩⟩
lemma calculate (T: Seal X.Hcols): jacdiff X F T=(∑ i∈T,burden X k A i T)+∑ S,tailJ X k A S T:=by
 unfold burden arm; simp_rw [sum_filter]; rw [sum_comm,←sum_add_distrib, h.audit]; refine sum_congr rfl fun S _=>?_ ; unfold tailJ; by_cases p:S.card≤k; swap; · simp [p,Nat.lt_of_not_ge p]
 simp only [p,true_and, if_neg (Nat.not_lt_of_ge p),add_zero]; cases q:tookM X S T with|none=> by_cases H:A S T=0; simp [q,H]; exact (H (h.rare T S q)).elim|some i=> simp [show i∈T from (took_spec X S T i q).2]
lemma bill_long (p:0 ≤ a) : Ledger.Cash id (flareJ k b) (a/2) (stipendJ k a c):=by
 let R:= Real.exp (-(a/2)*k); have hr:0≤R:=(Real.exp_pos _).le; have he(i):=h.budget.pos i; have hL(i):0≤flareJ k b i:=by unfold flareJ; split; exact he i; rfl
 refine ⟨hL, fun u=> budget_mono (budget_scale hr (h.budget.hits u)) (fun i=>?_ ) (fun i=>?_ )⟩
 · unfold Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le (hL _); rfl
 unfold Ledger.score; split; next e=>
   unfold flareJ; split; next v=> dsimp only [id]; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (he _); rw [← Real.exp_add]; apply Real.exp_monotone; nlinarith only [p,mul_le_mul_of_nonneg_left (Nat.cast_le.mpr v.le) p]
   next v=> rw [mul_zero]; exact mul_nonneg hr (mul_nonneg (Real.exp_pos _).le (he _))
 next e=> simp
lemma tail_pay (S T: Seal X.Hcols) : |tailJ X k A S T| ≤ flareJ k b S:= by unfold tailJ flareJ; split; exact h.value ..; simp
lemma long_turf (S:Seal X.Hcols)(v:flareJ k b S≠0) : Turf X S:= by unfold flareJ at v; split at v; exact h.turf _ v; contradiction
lemma tail_zone (S:Seal X.Hcols): Zoned S (tailJ X k A S):= by unfold tailJ; split; exact h.localz _; exact fun i j v=> rfl
lemma away (x:X.Hcols)(T:Seal X.Hcols)(p:x∉T): burden X k A x T=0:= by unfold burden; refine sum_eq_zero (fun i t=>?_ ); exact (p (took_spec X i T x ((mem_filter.mp t).2.2)).2).elim
lemma local_burden (x:X.Hcols): Zoned (columnBall X x k) (burden X k A x):=by
 intro i j u; simp only [burden,arm,sum_filter]; refine sum_congr rfl fun S _=>?_ ; by_cases b:x∈S; swap; · rw [if_neg _, if_neg _] <;> intro e <;> exact b (took_spec X S _ x e.2).1
 by_cases v:S.card≤k; swap; · simp [v]
 by_cases e:Turf X S; swap; · have hp (T) : A S T=0:= abs_nonpos_iff.mp (h.value S T|>.trans (Eq.le (not_not.mp (fun v=>e (h.turf _ v))))); simp [hp]
 have he:= column_mono X x v; let g : state S i j:=fun p y=> u p (he (turf_lim X S e x b y)); have hx:S∩i=S∩j:=by ext1 l; simp only [mem_inter]; exact and_congr_right (fun t=>g l t);
 unfold tookM; rw [hx,h.localz S i j g]
lemma short_bill (x:X.Hcols)(p:0 ≤ a) (T:Seal X.Hcols): |burden X k A x T|≤ c:=by
 let L:= arm X k T x; let Q:= h.budget.hits x; refine (abs_sum_le_sum_abs (s:=L) ..).trans ((sum_le_sum (fun i v=>?_)).trans (budget_sum Q L)); refine (h.value i T).trans ?_; unfold Ledger.score; rw [if_pos (show x∈id i from (took_spec X i T x ((mem_filter.mp v).2.2)).1)]; exact le_mul_of_one_le_left (h.budget.pos _) (Ledger.exp_one _ _ p) -- tune
end JacData
lemma k_bill (a C:ℝ→ℝ)(v:∀ᶠ i in atTop,0<a i)(p:PL fun i=>(a i)⁻¹)(q:PL C): ∃ r:ℝ→ℕ, PL (fun i=>(r i:ℝ)) ∧ NPL (fun i=> stipendJ (r i) (a i) (C i)):=by
 let H:=fun i:ℝ=>Real.log i * (2*(a i)⁻¹); let r:=fun i=>⌈H i⌉₊; refine ⟨r,(PL.log.mul ((PL.const 2).mul p)).ceil ?_, (npl_inv.mul q).mono ?_⟩
 · filter_upwards [v, Real.tendsto_log_atTop.eventually_gt_atTop 0] with i a p; exact mul_nonneg p.le (by positivity)
 filter_upwards [v,eventually_gt_atTop (0:ℝ)] with i p q; unfold stipendJ; rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (inv_pos.mpr q).le]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [show i⁻¹=Real.exp (-Real.log i) by rw [Real.exp_neg,Real.exp_log q]]; apply Real.exp_monotone; rw [neg_mul,neg_le_neg_iff]; apply le_trans _ (mul_le_mul_of_nonneg_left (Nat.le_ceil (H i)) (half_pos p).le); unfold H; exact Eq.le (by field_simp)
end YM.CF.BPress.Weave
