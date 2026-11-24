

import GaugeFieldConstruction.Hubble

/-! # Pay gauge rent under localized aggregate mark perturbation. Adapt Inlets & Danube,
     determinant of unperturbed already licensed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 20000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)

namespace clocks
open Work.E09 AnalyticBridge.Annulus1AD
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort
variable (pL:LocalRatio J)
-- loose can include all Plume SCene plus ties. prove available by power/growth purchases
lemma vergeDuty (q:Clip)(L:Side){J:ChartRatio G}(H:LocalRatio J)(K:ℝ)(h:0≤ K) (x:ℝ)(p:0<x):
 ∀ᶠ y:ℝ in atTop,∀ β:ℝ,y/2≤β→β ≤ 2*y → ∀ {r n:Side}(Q:Ratio r n),Marked y Q.count L → Odd Q.count.val→
  sunkV J q β K * rimTax (∅:Support r) Q (hallBill (height y)) ≤ x * Rrp (-gratuity/2) y * Fintype.card (Site n) :=by
 obtain ⟨A,hA,hX⟩:= descends J H K h 0 le_rfl
 let X(y:ℝ):=(4*(A*(height y:ℝ)))*(8*(hallBill (height y):ℝ)); have hp : RunRate 0 0 X:=by
    simpa only [zero_add] using ((heightT.cmul A|>.cmul 4).mul (hallT.cmul 8))
 filter_upwards [wall_matures L,hX,logPrice _ _ hp (w:=0) (c:= -gratuity/2+gratuity) (d:=0) (by norm_num [gratuity]) p] with y ht h V β g i r n Q m k
 let w:=Q.count; let M:ℝ:=w.val; have hZ:0 ≤ M:=Nat.cast_nonneg _; let t:=hallBill (height y); have hu:(largerBill w.val t:ℝ) ≤8*(t:ℝ)*M^3:=wall_cheap k (ht w m)
 let N:ℝ:=Fintype.card (Site r);
 have he:(rimTax (∅:Support r) Q t:ℝ) ≤ N*(8*(t:ℝ)*M^3):= by change (↑(Fintype.card (Site r)*largerBill w.val t):ℝ) ≤ _; rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _)
 have hv:sunkV J q β K ≤ 4*(A*(height y:ℝ)):=mul_le_mul_of_nonneg_left (h β g i) (by norm_num) -- h shadow in context positivity unaffected
 have hx:(Fintype.card (Site n):ℝ)= N*M^4:=by unfold N M w; rw [site_card,site_card,Q.exact_size]; push_cast; ring
 rw [hx]; apply (mul_le_mul hv he (Nat.cast_nonneg _) (by positivity)).trans
 have hf: X y ≤ x*Rrp (-gratuity/2) y*M:= calc
    _ ≤ x*(Rrp (-gratuity/2) y*tileN y):= by unfold tileN Rrp; rw [coin_mul,zero_add]; exact V
    _ ≤ _:=by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left m.1 (mul_nonneg p.le (CF.BProof.coin_pos ..).le)
 change 4*(A* _)*(N*(8*(t:ℝ)* M^3)) ≤ _
 have hp : _ ≤ _ := mul_le_mul_of_nonneg_left hf (show 0≤ N*M^3 from mul_nonneg (Nat.cast_nonneg _) (by positivity))
 unfold X at hp; unfold t; linarith only [hp]
abbrev saveZ (y:ℝ) := Rrp (-gratuity/2) y
lemma tax_H (q:Clip)(L:Side){J:ChartRatio G}(H:LocalRatio J)(K:ℝ)(h:0≤ K)(R:Rules G) (e:0<η)(a:0≤ C)(S:ℝ):
 ∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2≤β → β ≤ 2*x → ∀ {n c:Side}(Q:Ratio c n), Odd Q.count.val → Marked x Q.count L → ∀ p:BudgetPoint,p.threshold=temp x → cutRate J R q p Q (height x) K β (suitCost L x) (hairFee x) η C S ≤ (1/2:ℝ)* saveZ x*(Fintype.card (Site n):ℝ):=by
 filter_upwards [tax_V L q R e a S, vergeDuty q L H K h (1/8) (by norm_num),grade_price ((RunRate.coins (-(1/4)) 0 0).cmul 4) (a':= -gratuity/2) (b':=0) (by norm_num [gratuity]) (1/4) (by norm_num) 0, grade_price (RunRate.coins (-1/5) 0 0) (a':= -gratuity/2) (b':=0) (by norm_num [gratuity]) (1/8) (by norm_num) 0] with x g V W D β u v n c Q w q' p d
 let s:=saveZ x; let N:ℝ:=Fintype.card (Site n); have hx:=V β u v Q q' w; let t:=suitCost L x; have hw:4*hairFee x ≤ (1/4:ℝ)*s:=(le_abs_self _).trans W
 have hv: taxΔ R q n p β t η C S (height x) ≤ (1/8:ℝ)*s*N:= (g β v p d n).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans D) (Nat.cast_nonneg _))
 unfold cutRate; change taxΔ R q n p β t η C S _+ _* _+ _ ≤ 1/2*s*N
 change _ ≤ 1/8*s*N at hx
 linarith only [mul_le_mul_of_nonneg_right hw (show 0≤ N from Nat.cast_nonneg _),hv,hx]

lemma tauTrade (q:Clip)(x:ℝ)(p:0<x){β:ℝ}(h:x/2≤β) : q.linear/2 * coin x 0 2 0 ≤ tauTicket q β x:= by
 unfold tauTicket; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h q.tail_pos.le) (sq_nonneg _))
 apply le_of_eq; nth_rw 2 [←CF.BProof.coinY p]; rw [← CF.BProof.thresh_eq p,coin_pow]; -- rewrote indices?
 let v:=q.linear
 calc
 _ = v/2 * (coin x 1 0 0 * coin x (-1 / 2 * (2:ℕ)) (1*(2:ℕ)) (0*(2:ℕ))) := by rw [coin_mul]; norm_num; exact Or.inl rfl
 _ = _ := by unfold v; ring
lemma boldTrade (q:Clip)(x:ℝ)(p:0<x){β:ℝ}(h:x/2≤β): q.linear/2 * coin x (6*gratuity) 2 0 ≤ boldTicket q β x:=by
 have he:Rrp (6*gratuity) x * (tauTicket q β x) = boldTicket q β x:=by unfold tauTicket boldTicket badgeDust; ring
 rw [←he]; apply le_trans _ (mul_le_mul_of_nonneg_left (tauTrade q x p h) (CF.BProof.coin_pos ..).le); rw [mul_left_comm,coin_mul,add_zero,zero_add,zero_add]
lemma Trade_Front (q:Clip)(R:Rules G)(J:ChartRatio G)(D:LocalRatio J)(K:ℝ)(k:0≤ K)(L:Side) : ∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2≤ β → β ≤ 2*x →∀ {c n:Side}(Q:Ratio c n), Marked x Q.count L →
 reachΔ J R q (height x) β K + Real.log x ≤ tauTicket q β x/8 ∧ castΔ J R q Q β K + Real.log x ≤ boldTicket q β x/8:=by
 obtain ⟨A,v,h⟩:= descends J D K k 0 le_rfl
 let T (x:ℝ):=4*(A*(height x:ℝ)); let E(x:ℝ):=(21:ℝ)^4*(2*L.val*tileN x)^4
 let D₁(x:ℝ):=((2:ℝ)*hallBill (height x)+1)^4; have h₁ : RunRate 0 0 T:= heightT.cmul A|>.cmul 4
 have h₂ : RunRate (4*gratuity) 0 E:=by unfold E; convert ((((RunRate.coins gratuity 0 0).cmul (2* (L.val:ℝ))).pow 4).cmul ((21:ℝ)^4)) using 1 <;> push_cast <;> ring
 have h₃ : RunRate 0 0 D₁:= by unfold D₁; convert (((hallT.cmul 2).add (RunRate.const 1)).pow 4) using 1 <;> ring
 have ht:RunRate 0 0 Real.log:=CF.BProof.PL.log_y
 let a:= q.linear/16; have ha:0<a:=div_pos q.tail_pos (by norm_num)
 have hv : RunRate 0 0 (fun x=>T x * D₁ x) := by convert h₁.mul h₃ using 1 <;> ring
 filter_upwards [h,logPrice _ _ (hv.add ht) (c:=0) (d:=2) (w:=0) (by norm_num) ha,logPrice _ _ ((h₁.mul h₂).add (ht.relax (by norm_num [gratuity]))) (c:=6*gratuity) (d:=2) (w:=0) (by norm_num [gratuity]) ha,eventually_gt_atTop 0] with x h A₁ A₂ e β b s c n Q t
 have he : sunkV J q β K ≤ T x:= mul_le_mul_of_nonneg_left (h β b s) (by norm_num)
 have hT:0 ≤ T x:= (no_trouble k).trans he
 have hp : reachΔ J R q (height x) β K ≤ T x*D₁ x:= by unfold reachΔ D₁; push_cast; apply mul_le_mul_of_nonneg_right he (by positivity)
 let z:=castΔ J R q Q β K; have hn:z ≤ T x*E x:=by unfold z castΔ E; apply (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans; push_cast; gcongr; norm_num; exact t.2
 constructor
 · apply (add_le_add_left hp (Real.log x)).trans (A₁.trans ?_); have hx:=tauTrade q _ e b; unfold a; linarith only [hx]
 exact (add_le_add_left hn (Real.log x)).trans (A₂.trans (by unfold a; linarith only [boldTrade q _ e b]))
lemma day_mist (q:Clip)(R:Rules G)(J:ChartRatio G)(D:LocalRatio J)(K:ℝ)(k:0≤ K)(L:Side) :
 ∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2≤ β → β ≤ 2*x →∀ {c n:Side}(Q:Ratio c n), Marked x Q.count L → ∀ w z:ℝ,w≤ tauTicket q β x/8 → z ≤ boldTicket q β x/8 →
   dewCost n (reachΔ J R q (height x) β K+w-tauTicket q β x/4) (castΔ J R q Q β K+z-boldTicket q β x/4) ≤ (1/2:ℝ) * saveZ x * Fintype.card (Site n):=by
 let a:= Fintype.card PlaqAxes
 filter_upwards [Trade_Front q R J D K k L,eventually_gt_atTop 0,logPrice _ _ ((RunRate.coins (-1) 0 0).cmul ((a:ℝ)*2)) (c:= -gratuity/2) (d:=0) (w:=0) (by norm_num [gratuity]) (show 0 < (1:ℝ)/2 by norm_num)] with x u h i β b t c n Q m w z v f
 obtain ⟨g,p⟩:= u β b t Q m; have hg:Fintype.card (Cell n)= Fintype.card (Site n)*a:=Fintype.card_prod ..
 let V:ℝ:=Fintype.card (Site n); unfold dewCost; rw [hg,Nat.cast_mul]
 have ht{c:ℝ}(p:c≤ -Real.log x):Real.exp c ≤ Rrp (-1) x:=by apply (Real.exp_monotone p).trans (le_of_eq ?_); rw [Real.exp_neg,Real.exp_log h,Rrp_out (-1) x h,Real.rpow_neg h.le,Real.rpow_one]
 apply (mul_le_mul_of_nonneg_left (add_le_add (ht (by linarith only [g,v])) (ht (by linarith only [p,f]))) (show 0 ≤ V* (a:ℝ) from mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans
 change (a:ℝ)*2*Rrp (-1) x ≤ (1/2:ℝ) * saveZ x at i
 change V* _ * _ ≤ _ * _ * V; linarith only [mul_le_mul_of_nonneg_right i (show 0≤ V from Nat.cast_nonneg _)]
lemma harvest_volume {R:Rules G}(D:LocalRatio J)(q:Clip) (e:0<η)(a:0≤ C)(S:ℝ)(K:ℝ)(k:0≤ K)(L:Side):
 ∀ᶠ x:ℝ in atTop,∀ β:ℝ,x/2≤ β → β ≤ 2*x →∀ {c n:Side}(Q:Ratio c n), Marked x Q.count L → Odd Q.count.val → 2*(Q.count.val+1)<n.val → ∀ (p:BudgetPoint),p.threshold=temp x→ ∀ {H:Bed}{Z:PathData G}(P:Attached H Z) (W:Z.Bounds q η C S){μ v:ℝ}, 0<μ→ Floor H q n μ v→ (∀ i, (Precision.K (H.metric.acts n)) i i ≤ K) → ∀ (T:Forest Q)(w z:ℝ),w≤ tauTicket q β x/8 → z ≤ boldTicket q β x/8 → ∀ (w' z' g:ℝ)(φ:Config G n→ℝ),Envelope φ → w' ≤ tauTicket q β x/8 → z' ≤ boldTicket q β x/8 → ModerateP W P p T (height x) (badgeDust x) β (suitCost L x) g w' z' φ → (∫ U:Config G n, aggregateA Z p q β w z (badgeDust x) T φ U ∂prior G n) ≤ Real.exp (Roof J β n H+saveZ x * Fintype.card (Site n) + g):=by -- include R
 filter_upwards [eventually_gt_atTop 0,boat L q R J D, tax_H q L D K k R e a S,day_mist q R J D K k L,wall_matures L] with x ht h v w u β g f c n V m p p' B X H Z P E μ b i wA hV T l l' s t j d qv φ e1 e2 e3 e4
 have he : 0<β:= lt_of_lt_of_le (half_pos ht) g
 let Y:= h _ m _ he.le _ X _ _ s t
 apply (at_height E P wA D e1 Y he k a p (u _ m) hV i p' e4).trans (Real.exp_monotone ?_) -- order
 linarith only [w β g f V m j d e2 e3, v β g f V p m B X] -- fix linarith. Need name with .cast
end clocks
end YM.Gleam
end
