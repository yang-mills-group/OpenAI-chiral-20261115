import YM.SU5.Reconstruction.Anvil.Gap
/-! # Center payable as Mink spectroscopy. Note needs real spectators & s argument, also grant θ marker positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup Price Terrain ConePrice Analysis Sail
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {a:Axis} {H:Hilbert} (S:OS.Semigroup H a) (T:ℝ) (x:Meter) (b:ℝ) (v: ConePrice.Forward S)
local notation "𝔯"=> aim a x b
local notation "X" => rimPay a x
local notation "Λ"=> LedgerRide a
local notation "R"=> PaysOn S
local notation "j"=> onlyTime a
local notation "ℜ" c:max=> Real.toNNReal (c:ℝ)
local notation "U"=> S.U
local notation "O"=> S.edge
-- avoid names P
lemma rim_zero_aim : rimPay a (Deeper (aim a x b))=0:=by simp [aim,only_agree] -- tune implicit a lost?
lemma bare_aim (q:x a=0): (aim a x b a).re=0:=by simp [aim,q,sideways,onlyTime]
def polarize := S.U (rimPay a x)*S.edge b
noncomputable def sunny (A:H.Op) : H.Op:= (polarize S x b)*A*polarize S (-x) (-b)
lemma pure_loan (q:x a=0): Loan a (aim a x b):=by rw [Loan,rim_zero_aim,norm_zero,bare_aim x b q]
lemma negative_aim : aim a (-x) (-b)= - aim a x b:= by unfold aim; rw [facet_neg, show sideways (-b)=-sideways b from (by simp [sideways]), single_negate]; abel
include v
lemma noon (p:x a=0): PaysOn S (aim a x b) = polarize S x b:= by
 let h:Loan a (j (sideways b)):= by rw [Loan,only_agree]; simp [sideways,onlyTime]
 rw [aim,combine S _ _ ((loan_initial a x).2 p.ge) h (pure_loan x b p),realRent S v x p.ge, edgeJoin S v, p]; unfold polarize; simp [S.eZero]; rfl -- p.ge if x a=0: expected ≤
lemma tickS (t:ℝ) (p:0≤t): R (j (t:ℂ))= S.E (Real.toNNReal t):= by
 rw [← facet_t,realRent S v _ (by simpa [onlyTime] using p)]; simp [onlyTime,S.uZero]; rfl
omit v in
private lemma allowed {a:Axis} {x y:Wage}(p:Loan a x)(v: Loan a y): Loan a (x+y):= by rw [Loan,Pi.add_apply,Complex.add_re,deeper_add,rimPay_add]; exact (norm_add_le ..).trans (add_le_add p v) 
lemma convert_node (p:x a=0)(w:0<T) :
       PaysOn S (j ((T:ℝ):ℂ)+ 𝔯)= S.E (ℜ T) * polarize S x b ∧
       PaysOn S (j ((T:ℝ):ℂ)- 𝔯)= polarize S (-x) (-b) * S.E (ℜ T) := by
   let k:=j (T:ℂ); have pp:(-x) a=0:=by simp [p]
   have ht(t:ℝ): Deeper (j (t:ℂ))=0:=by rw [←facet_t,grace]
   have hx : Loan a k:= by unfold Loan k; rw [ht]; simp [onlyTime]; exact w.le -- syntax
   constructor
   · rw [combine S _ _ hx (pure_loan x b p) ?_, noon S x b v p,tickS S v T w.le]
     exact allowed hx (pure_loan x b p)
   rw [sub_eq_add_neg,add_comm,← negative_aim,combine S _ _ (pure_loan _ _ pp) hx ?_, noon S _ _ v pp,tickS S v T w.le]
   exact allowed (pure_loan _ _ pp) hx
variable (p:x a=0)
include p
variable (A B:H.Op)(L G:H)
local notation "F" y:max=> (vertical T 0 0).sale y S A B L G
lemma finishes (w:0<T):
       (vertical T 0 0).sale true S A B L G (aim a x b) = inner ℂ (S.E (ℜ T) L) (A (sunny S x b B (S.E (ℜ T) G))) ∧
       (vertical T 0 0).sale false S A B L G (aim a x b) = inner ℂ (S.E (ℜ T) L) (sunny S x b B (A (S.E (ℜ T) G))) := by
   have hx := convert_node S T x b v p w; have hz:(-x) a=0:=by simp [p]
   unfold sale; simp only [entry,Price.compare, leaves,takeAB,add_zero,zero_add,sub_zero,onlyTime, Complex.ofReal_zero,Pi.single_zero,zero_sub,reduceCtorEq,if_true,if_false]
   rw [hx.2,tickS S v T w.le,add_comm (𝔯),hx.1,noon S x b v p,← negative_aim x b,noon S (-x) (-b) v hz]; simp only [sunny, mul_apply_eq_comp, S.swing, and_self]
   -- tune assoc
omit v
local notation "e₁"=> vertical T 0 0
lemma honorable (e:ℝ) : AnalyticOnNhd ℂ (fun z=> (vertical T 0 0).sale true S A B L G (LedgerRide a (aim a x b) z)) (veil 0 T e) ∧
    AnalyticOnNhd ℂ (fun z=> (vertical T 0 0).sale false S A B L G (LedgerRide a (aim a x b) z)) (veil (-T) 0 e):= by
   constructor
   · refine (e₁).saleHol true S _ _ _ _ _ _ (ride_h a 𝔯 _) (veil_open 0 T e) fun z h=> (up_test T 0 0 (aim a x b) z (a:=a)).1.mpr ?_; have h1:= h.1; have h2:= h.2.1; rw [bare_aim x b p,rim_zero_aim,zero_add,norm_zero]; exact ⟨lt_trans h1 h2,by linarith,by linarith⟩
   refine (e₁).saleHol false S _ _ _ _ _ _ (ride_h a 𝔯 _) (veil_open (-T) 0 e) fun z h=> (up_test T 0 0 (aim a x b) z (a:=a)).2.mpr ?_; have h1:= h.1; have h2:= h.2.1; rw [bare_aim x b p,rim_zero_aim,zero_add,norm_zero]; refine ⟨by linarith,by linarith,by linarith⟩
lemma center_cont (y:Bool)(w:0<T):
   let ℓ := if y then 𝓝[>] (0:ℝ) else 𝓝[<] (0:ℝ)
   Tendsto (fun t:ℝ=> (vertical T 0 0).sale y S A B L G (LedgerRide a (aim a x b) t)) ℓ (𝓝 ((vertical T 0 0).sale y S A B L G (aim a x b))) := by
 intro ℓ; let C:=vertical T 0 0; let V(u:ℝ) := Λ (aim a x b) (u:ℂ)
 have m: ℓ ≤ 𝓝 (0:ℝ):=by unfold ℓ; split; exact nhdsWithin_le_nhds; exact nhdsWithin_le_nhds
 haveI: ℓ.IsCountablyGenerated:=by cases y<;> simp only [ℓ,reduceCtorEq,if_true,if_false] <;> infer_instance
 have he:Tendsto V ℓ (𝓝 (𝔯)):=by
   have E:Continuous V:= continuous_pi (fun j₁=> by by_cases e:j₁=a<;> simp [V,LedgerRide,onlyTime,e]<;> fun_prop); simpa [show V 0=(aim a x b) from by simp [V,LedgerRide,onlyTime]] using (E.continuousAt.tendsto (x:=(0:ℝ))).mono_left m -- tune x explicit
 have h:∀ᶠ t in ℓ, C.permeates a y (V t):=by
    cases y; swap
    · filter_upwards [show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin, m (show ∀ᶠ t in 𝓝 (0:ℝ), t < T from Iio_mem_nhds w)] with t h g; exact (up_test T 0 0 𝔯 t).1.mpr ⟨w,by rw [bare_aim x b p,rim_zero_aim]; simpa using h,by rw [bare_aim x b p,rim_zero_aim]; simpa using g⟩ -- orientation
    filter_upwards [show ∀ᶠ t in 𝓝[<] (0:ℝ), t<0 from self_mem_nhdsWithin, m (show ∀ᶠ t in 𝓝 (0:ℝ), t> -T from Ioi_mem_nhds (neg_lt_zero.mpr w))] with t h g
    apply (up_test T 0 0 (aim a x b) t).2.mpr; rw [bare_aim x b p,rim_zero_aim,Complex.ofReal_re]; simp; exact ⟨by linarith,h,w⟩
 -- better continuity via closure of tunnel Loan.isClosed.Use h loans implies by neBot and eventually.
 haveI:ℓ.NeBot:= by unfold ℓ; split <;> infer_instance
 have h₀(n: Wage→Wage)(v:Continuous n)(p:∀ᶠ i in ℓ,n (V i) ∈ Tunnel a)(g:ℝ→ H)(y1:H)(u:Tendsto g ℓ (𝓝 y1)): Tendsto (fun t=> PaysOn S (n (V t)) (g t)) ℓ (𝓝 (PaysOn S (n 𝔯) y1)):= by -- realage redundant tweak
    have ht: ∀ᶠ i in ℓ,Loan a (n (V i)):= p.mono (fun i v=>v.le)
    have H:= ((v.tendsto (aim a x b)).comp he)
    exact keepRight S ℓ (le_of_tendsto_of_tendsto (( (c_r a|>.comp c_y).norm).continuousAt.tendsto.comp H) ((show Continuous (fun z:Wage=> (z a).re) from by fun_prop).continuousAt.tendsto.comp H) ht) (n ∘ V) ht H g y1 u
 exact tendsto_const_nhds.inner (h₀ (C.entry a y) (C.entryCont a y) (h.mono (fun i hv=>hv.1)) _ _ ((takeAB y A B).continuous.continuousAt.tendsto.comp (h₀ (C.compare a y) (C.compareCont a y) (h.mono (fun i hv=>hv.2.1)) _ _ ((takeAB y B A).continuous.continuousAt.tendsto.comp (h₀ (C.leaves a y) (C.leavesCont a y) (h.mono (fun i hv=>hv.2.2)) (fun _=>G) _ tendsto_const_nhds)))))
end YM.Anvil
