import YM.CF.Buffered.Curriculum
/-!
# PC lower with offset price at the stopping level, through Volume.Window on
**sharp** brief anchors. Window price mode is purchased at sufficient pivot
before any of these evaluations. Here allowed histories just at paired
cutoffs. Uses Undivided budget comparisons from p-delt.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Burn
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker ComplexOrder
open Cube Tenant Lat Spire Scroll Scree Jet Phase Branch Fock Skye
open Py Vale Vale.Grace Haro Nova
open Wilson Precision Next.Free Next.SectorChange Tulip Gauge Paige Vault Brace
open Push.SectorMeasure
open Heat Advance Pressure Region
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Calibration} (J:Tiling K)(C:Conveyor K){n:ℕ}{m: Side}

def lodestar (C:Conveyor K)(m:Side)(n:ℕ):ℝ:= ‖vac0 K.P (C.warm m n 0) (C.loom m 0)‖
def barestar (C:Conveyor K)(m:Side)(n:ℕ):ℝ:= ‖partitionZ (C.warm m n 0) K.P (C.loom m 0)‖
def starfare (C:Conveyor K)(m:Side)(n:ℕ):ℝ:= (C.warm m n 0).v.re
lemma prices : lodestar C m n=Real.exp (-starfare C m n) * barestar C m n:=by unfold lodestar barestar vac0; rw [norm_mul,Complex.norm_exp,Complex.neg_re]; rfl
lemma same_sign : 0 < lodestar C m n ↔ 0 < barestar C m n := by rw [prices]; exact mul_pos_iff_of_pos_left (Real.exp_pos _)
lemma invoice (a:0 < barestar C m n): Real.log (lodestar C m n)=Real.log (barestar C m n)-starfare C m n:=by rw [prices,Real.log_mul (Real.exp_pos _).ne' a.ne',Real.log_exp]; ring

structure Flipbook (K:Calibration) (J:Tiling K) (C:Conveyor K) (n:ℕ) where
 frame (m:Side)(a:K.Allowed m n): Bedded C a
 bolt m (a:K.Allowed m n)(q:K.Allowed K.q n): Region.Ticket.Coherent ((frame _ q).permit J) ((frame _ a).permit J)
 offset (m k:Side)(q: K.Allowed K.q n)(a:K.Allowed m n)(b:m=K.q*k) : |starfare C K.q n-starfare C m n/(k.val:ℝ)^4| ≤ 2 -- weaken p-stepv at zero: compare both to listTop
 -- Issue receipts for the itinerary, involving only paired paths & charges. Proving existence from pc1 etc not asked. On selected histories, removes presrec/lux comparisons.

variable {C J}
local notation "rt" => (3:Side)
namespace Flipbook
variable (B:Flipbook K J C n)
local notation "o" => K.q
local notation "m₃" => K.q* (3:Side)
include B
lemma tilt_equal {m k:Side} (h:K.Allowed m n)(y:K.Allowed k n)(p:ℕ) (hx:p≤n) : (C.warm m n p).beta=(C.warm k n p).beta:=by
 have h₁ := (B.frame m h).pair; have h₂:=(B.frame k y).pair
 induction p with
 | zero=> exact (Shots.pivot h₁).trans (Shots.pivot h₂).symm
 | succ p ih=> specialize ih (by omega); linarith only [ih,Shots.shiftY h₁ p hx,Shots.shiftY h₂ p hx]
include B
variable (a: K.Allowed m n) (q: K.Allowed K.q n)(y: K.Allowed (K.q*(3:Side)) n)
include a q
lemma ruler (k:Side)(b:m=K.q*k) : J.qcount m=k*J.qcount o:=by
 have h₁:= J.ruler m a.1; have h₂:=J.ruler _ q.1; apply mul_left_cancel (a:=J.d'); rw [←h₁,mul_comm k,← mul_assoc,←h₂,b] -- tune
lemma price_scale : barestar C m n= ‖((B.frame m a).permit J).moment 1 K.K.top.clip (C.warm K.q n n).beta (launchK K n)‖:=by
 unfold barestar; rw [←B.tilt_equal a q n le_rfl,(B.frame m a).grantU J]
include y
lemma thick (k:Side)(b:m=K.q*k)(x:Odd k.val)(v:0 < lodestar C K.q n)(z:0 < lodestar C (K.q*(3:Side)) n): 0 < lodestar C m n ∧ Region.Ticket.lux k (barestar C K.q n) (barestar C m n) ≤ (3/2:ℝ)^4 * Region.Ticket.lux 3 (barestar C K.q n) (barestar C (K.q*(3:Side)) n):=by
 rw [same_sign] at v z ⊢; rw [price_scale B a q, price_scale B q q, price_scale B y q]; rw [price_scale B q q] at v; rw [price_scale B y q] at z
 exact Region.Ticket.escort_data _ _ _ _ _ (B.bolt m a q) (B.ruler a q k b) (by unfold launchK; positivity) _ (B.bolt _ y q) (B.ruler y q 3 rfl) x v z
end Flipbook

local notation "o" => K.q
local notation "m₃" => K.q*(3:Side)
variable (p:SpanCal K)
lemma big_one (K:Calibration): K.takes K.q:= ⟨1,odd_one,(mul_one _).symm⟩
lemma big_three (K:Calibration): K.takes (K.q*3):= ⟨3,⟨1,rfl⟩,rfl⟩

structure Printed (K:Calibration)(C: Conveyor K)(J:Tiling K)(p:SpanCal K): Prop where
 sizes : ∀ᶠ n in atTop, Nonempty (Flipbook K J C n)
 qualify : enrollment p≤ K.x
 window_q : under p K.q
 window_3q : under p (K.q*3)
namespace Bedded
variable {a:K.Allowed m n}(F:Bedded C a)
include F
lemma δ₀ : Delta K.P (C.sharp m n 0) (C.warm m n 0) (C.loom m 0) (bill m.val n K.b₀ (trial₀ K+loss K)) := rec_delta F.pair F.budget
lemma close (h:0<n): |lodestar C m n-‖vac0 K.P (C.sharp m n 0) (C.loom m 0)‖| ≤ bill m.val n K.b₀ (trial₀ K + loss K):=by
 unfold lodestar; rw [abs_sub_comm]; obtain ⟨t,hT⟩:= Granted.paid (Shots.cap_grant F.pair) 0 h; exact le_trans (abs_norm_sub_norm_le ..) (transfer_vac _ _ _ _ hT t (Granted.paid (Shots.warm_grant F.pair) 0 h |>.1) F.δ₀)
lemma price_hi : ‖vac0 K.P (C.sharp m n 0) (C.loom m 0)‖ ≤ Real.exp (trial₀ K * (m.val:ℝ)^4) := by
 rw [order_one]; unfold num0 markedRead; refine (norm_integral_le_of_norm_le_const (C:=Real.exp (trial₀ K*(m.val:ℝ)^4)) (Filter.Eventually.of_forall fun i=>?_)).trans (le_of_eq ?_); swap; · simp
 apply le_trans (mark_bound ..); change ‖(1:FC (Single (CSide (Vale.mesh m K.R.L 0) K.B)))‖*_≤ _; rw [norm_one,one_mul]; exact sharp_extensive F.pair i
end Bedded
namespace Printed
variable {p}
variable (W:Printed K C J p)
include W
lemma spring (h:K.takes m)(v:under p m):(0 < rake p m/2) ∧ (∀ᶠ n in atTop,rake p m/2 ≤ lodestar C m n ∧ lodestar C m n ≤ Real.exp (trial₀ K*(m.val:ℝ)^4)+rake p m):=by
 have he : ∀ᶠ n in atTop, ∃ a: K.Allowed m n, Nonempty (Bedded C a):=by filter_upwards [W.sizes, K.eventually_allowed h] with n w a using ⟨a,⟨w.some.frame m a⟩⟩ -- tune .some
 obtain ⟨k,a,y⟩:= he.exists; have hx:= (y.some.low p W.qualify v).1 -- tune
 refine ⟨by linarith,?_⟩; filter_upwards [he,(bill_shrinks K.b₀ m.val (trial₀ K+loss K)).eventually (gt_mem_nhds (half_pos hx)), eventually_gt_atTop 0] with n v' g ht
 change bill m.val n K.b₀ _ < rake p m/2 at g; obtain ⟨u,L⟩:=v'; obtain ⟨f⟩:=L; have W':= abs_le.mp (f.close ht); constructor <;> linarith [(f.low p W.qualify v).2, f.price_hi]
lemma above_K : ∃ s:ℝ,∀ᶠ n in atTop, Region.Ticket.lux 3 (barestar C K.q n) (barestar C (K.q*3) n) ≤ s:=by
 obtain ⟨e,u⟩:= W.spring (big_one K) W.window_q; obtain ⟨h,x⟩:= W.spring (big_three K) W.window_3q; let v:=Real.log (Real.exp (trial₀ K*(K.q.val:ℝ)^4)+rake p K.q); let t:= Real.log (rake p (K.q*3)/2); refine ⟨v-t/(3:ℝ)^4+2,?_⟩; filter_upwards [W.sizes,u,x,K.eventually_allowed (big_one K), K.eventually_allowed (big_three K)] with n ⟨B⟩ w y h₁ h₂
 have he:= invoice C ((same_sign C).1 (e.trans_le w.1)); have hf := invoice C ((same_sign C).1 (h.trans_le y.1)); have hp:= abs_le.mp (B.offset _ 3 h₁ h₂ rfl); have h':= Real.log_le_log h y.1; have g : Real.log (lodestar C K.q n) ≤ v:=Real.log_le_log (e.trans_le w.1) w.2
 unfold Region.Ticket.lux; norm_num at hp ⊢; change t ≤ _ at h'; linarith
lemma stores_P : ∃ x:ℝ,∀ᶠ n in atTop, ∀ m:Side,K.Allowed m n→ presrec m.val x ≤ lodestar C m n:=by
 obtain ⟨S,H⟩:=W.above_K; obtain ⟨e,u⟩:= W.spring (big_one K) W.window_q; obtain ⟨h,x⟩:= W.spring (big_three K) W.window_3q; let V:= Real.log (rake p K.q/2); let T:= (3/2:ℝ)^4; let Z:= V-T*S-2
 refine ⟨- Z / (K.q.val:ℝ)^4,?_⟩
 filter_upwards [W.sizes,u,x,K.eventually_allowed (big_one K), K.eventually_allowed (big_three K),H] with n ⟨B⟩ w y h₁ h₂ T'
 intro m v; obtain ⟨k,hk,b⟩:=v.1; obtain ⟨g,h'⟩:= B.thick v h₁ h₂ k b hk (e.trans_le w.1) (h.trans_le y.1); have hp:= (abs_le.mp (B.offset _ k h₁ v b)).1 -- need? log Ωv - SF = ; log bare q - log bare m/k ≤ ...; logL q - logL m/k ≤ ... - fare q + ... yes lower.
 have he : Region.Ticket.lux k (barestar C K.q n) (barestar C m n)≤ T*S:= h'.trans (mul_le_mul_of_nonneg_left T' (by positivity))
 rw [←Real.exp_log g]; refine Real.exp_le_exp.mpr ?_
 unfold Region.Ticket.lux at he; have hw:= invoice C ((same_sign C).1 g); have hx:=invoice C ((same_sign C).1 (e.trans_le w.1)); have hs:V≤Real.log (lodestar C K.q n):=Real.log_le_log e w.1
 change ((_ : ℝ)* _ ≤ _); have hg:Z ≤ Real.log (lodestar C m n)/(k.val:ℝ)^4:=by unfold Z; rw [hx] at hs; rw [hw,sub_div]; linarith
 have hd:= (le_div_iff₀ (by positivity : 0 < (k.val:ℝ)^4)).1 hg; apply hd.trans'; apply le_of_eq; nth_rw 1 [b]; push_cast; field_simp

noncomputable def narrative : Comparisons K:=
 { C with c':=W.stores_P.choose
          paired:=by filter_upwards [W.stores_P.choose_spec,W.sizes] with n k ⟨X⟩; intro m w; exact ⟨(X.frame m w).pair,(X.frame m w).budget,k m w⟩}

end Printed
end YM.CF.Buffered.Burn
#print axioms YM.CF.Buffered.Burn.Printed.above_K
