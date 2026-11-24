import YM.CF.BPress.LiftHaar
import YM.CF.BPress.Tally
import YM.CF.BPress.SupportN
import YM.CF.BPress.Envelope
/-!
Extension allowed in VolumeB-gate: Mark weights per term. Define `tail` as the Fock test with scalar weights including subsequent cancellations (only gauge-Mark base density `takeN` is separate). Day: one term. Night: one term at ALL pairs of admissible lifts. Support and cost before twist, true observable not averaged over gauges. Feeds finite products/interpolations including offset, sample law. Specific cancellations plugged later in eq:B-Ms/vac.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Tunnel Finset RG Wilson
open Law Push.SectorMeasure Env
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
open Tulip Fixed Fock Scree Skye Girt Net Bands
variable {N : Side}{B : BandWidth}{X:Bands (More N) B}{T : Sheet.Atlas}{C C' Lf y : ℝ}{b : ℕ}{F:Net (More N) T Lf y C C' b}
abbrev Theatre (N:Side) := Micro (More N)× Duo (More N) → FC (Single N)
structure Extends (F : Net (More N) T Lf y C C' b)(X:Bands (More N) B)(i:X.Index)(A:Theatre N) (K:ℝ) : Prop where
 mark (p): IsMark (X.band i) (fun U=> A (U,p)) K
 meas : Measurable A
 moves : i∈X.nc → ∀ U,∀ p∈T.pairs y ((X.mark i).reads U), F.takeN X U i p≠0 → ∀ a:Mach (More N), A (gauge a U,p*((X.mark i).framesE a)⁻¹)= twist (quantU (tradew _ a)) (A (U,p))

namespace Extends
variable {A A' : Theatre N}{K K':ℝ}{i : X.Index}
lemma env (p:Extends F X i A K): Envelope A:= ⟨p.meas,K,fun v=> (p.mark v.2).cost v.1⟩
lemma one : Extends F X i 1 1:= ⟨fun p=>IsMark.one _,measurable_const,fun _ x p _ _ a=> by change 1=twist _ (1:FC (Single N)); rw [twist_formula,mul_one]; exact (quantU _).property.2.symm⟩
lemma prod (p : Extends F X i A K)(h: Extends F X i A' K'): Extends F X i (A*A') (K*K'):= by
 refine ⟨fun i=>(p.mark i).mul (h.mark i),p.meas.mul h.meas,?_⟩ -- tune
 intro t U x v w a; simp only [Pi.mul_apply, p.moves t _ _ v w a,h.moves t _ _ v w a]; rw [map_mul]
end Extends
namespace Net
variable (F X) (i:X.Index)(A:Theatre N)
-- local term function
def price (U: Micro (More N))(p : Duo (More N)) := ((F.takeN X U i p):ℂ) • A (U,p)
def showM : Fixed.Test N:= fun U=> ∑ p∈ X.choices T y U i,F.price X i A U (X.putF T y U i p)
lemma price_bnd {K:ℝ} (h:Extends F X i A K) (U:Micro (More N))(p:Duo (More N)): ‖F.price X i A U p‖ ≤ quoteN (y:=y) X i*K:=by
 unfold price; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.takeN_pos X U ..)]; exact mul_le_mul (F.quoteN_bound ..) ((h.mark p).cost U) (norm_nonneg (A _)) ((F.takeN_pos X U i p).trans (F.quoteN_bound ..)) -- tune placeholders
lemma turn_read (k : Mach (More N))(h:i∈X.nc)(U:Micro (More N))(p:Duo (More N)): F.takeN X (gauge k U) i (p*((X.mark i).framesE k)⁻¹)=F.takeN X U i p:=by have v:= (mem_sdiff.mp h).2; unfold takeN; rw [if_neg v,if_neg v]; exact F.markN_a ..
set_option synthInstance.maxSize 128 in
lemma by_N (t:i∈X.nc) (U:Micro (More N)): F.showM X i A U= ∑ p∈ T.pairs y ((X.mark i).reads U), F.price X i A U p:= by
 rw [showM,← X.choices_B T y U (mem_sdiff.mp t).2,sum_image]; exact fun _ _ _ _ p=> X.putF_s T y U i (mem_sdiff.mp t).2 p
lemma by_D (t:i∈X.dc) (U:Micro (More N)): F.showM X i A U=F.price X i A U 1:= by rw [showM, X.choices_D T y U t,sum_singleton, X.putF_D T y U t]
set_option synthInstance.maxSize 128 in
lemma show_turnN (t:i∈X.nc)(U:Micro (More N)){K:ℝ}(r:T.Coasts y)(p: Extends F X i A K)(a:Mach (More N)): F.showM X i A (gauge a U)= twist (quantU (tradew _ a)) (F.showM X i A U):=by
 rw [F.by_N X i A t, F.by_N X i A t,T.pairs_a y (X.mark i) U r a,sum_image,map_sum]; -- requires Coasts y ; tune
 apply sum_congr rfl; intro j hj; rw [price,price,F.turn_read X i a t,twist_scalar]; by_cases e:F.takeN X U i j=0; rw [e]; simp; rw [p.moves t U j hj e]
 exact fun i _ j _ e=> mul_right_cancel e
lemma show_meas {K:ℝ}(p:Extends F X i A K) : Measurable (F.showM X i A):=by
 by_cases v:i∈ X.dc
 · simp_rw [show (F.showM X i A)= (fun U=> F.price X i A U 1) from funext (F.by_D X i A v)]; exact (Complex.continuous_ofReal.measurable.comp ((F.takeN_meas X i).comp (measurable_id.prodMk measurable_const))).smul (p.mark _).borel
 rw [show F.showM X i A=(fun U => ∑ p∈_, F.price X i A U p) from funext (F.by_N X i A (mem_sdiff.mpr ⟨mem_univ _,v⟩))]; apply T.pairs_sum y (X.mark i).reads (X.mark i).reads_cont.measurable (fun x=> F.price X i A x.1 x.2) ?_; exact (Complex.continuous_ofReal.measurable.comp (F.takeN_meas X i)).smul p.meas
-- Prices before weaken to polynomial; use eventual hypotheses only once
lemma show_mark {K:ℝ}(p:Extends F X i A K)(t:T.Coasts y) : IsMark (X.band i) (F.showM X i A) (25*quoteN (y:=y) X i*K):=by
 refine ⟨?_,fun U=> Sector.sumS _ _ (fun j _=> ((p.mark _).even U).scale _),F.show_meas X i A p,?_⟩
 · intro U V h; rw [showM,showM,show X.choices T y U i=X.choices T y V i from X.choices_local T y i U V h]; apply sum_congr rfl; intro j v; rw [show X.putF T y U i j=X.putF T y V i j from X.putF_local T y i j U V h]; let z:= X.putF T y V i j; apply congrArg₂ (fun w:ℝ=> ((w:ℂ) • ·)) (F.takeN_local X i z U V h) ((p.mark z).reads U V h)
 intro U; have ht:0≤ quoteN (y:=y) X i:=(F.takeN_pos X U i 1).trans (F.quoteN_bound X U i 1); have he:0≤K:=(p.mark 1).nonneg; apply (norm_sum_le ..).trans; refine (sum_le_sum (fun j (_:j∈X.choices T y U i)=>F.price_bnd X i A p U _)).trans ?_; rw [sum_const,nsmul_eq_mul, mul_assoc (25:ℝ)]; gcongr; exact_mod_cast X.choices_bound T y U t i
lemma ang_cash (T:Sheet.Atlas) : ∃ A : ℝ,0<A ∧ ∀ᶠ y:ℝ in atTop, ∀ (N:Side)(B: BandWidth)(X : Bands (More N) B)(i:X.Index), 25 * quoteN (y:=y) X i ≤ Real.exp (A * B.P * Real.log y * (More N).val^3):= by
 obtain ⟨C,v,Q⟩:= ball_charge_bound; refine ⟨8*C+1,by positivity,?_⟩; filter_upwards [Q,eventually_gt_atTop (25:ℝ)] with y p q N B X i; have hz : 1 < y:= by linarith
 let K:= (B.P:ℝ)*Real.log y*(More N).val^3; have he:Real.log y ≤ K:= by have hp: Real.log y ≤ B.P*Real.log y:= le_mul_of_one_le_left (Real.log_pos hz).le (by exact_mod_cast B.P_pos); exact hp.trans (le_mul_of_one_le_right ((Real.log_pos hz).le.trans hp) (one_le_pow₀ (by exact_mod_cast (More N).property)))
 rw [show _+(1:ℝ)=(1:ℝ)+8*C from (add_comm ..),add_mul,add_mul,add_mul,one_mul,Real.exp_add]; apply mul_le_mul _ _ (by unfold quoteN chord.charge; positivity) (Real.exp_pos _).le
 · refine q.le.trans ?_; nth_rw 1 [←Real.exp_log (zero_lt_one.trans hz)]; exact Real.exp_monotone he
 have hp : (X.pay i).card ≤ B.P * 2 * (More N).val^3*4:=by
    refine (card_le_card (X.pay_b i)).trans ((inside_bound _).trans ?_); rw [X.band_card]; gcongr; change B.marked.val+1≤ B.P*2; unfold BandWidth.P; have h:0<B.marked.val:=B.marked.property; omega
 apply le_trans (pow_le_pow_left₀ (zero_le_one.trans p.1) p.2 ((X.pay i).card)); rw [← Real.exp_nat_mul]; apply Real.exp_monotone; refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hp) (mul_nonneg v.le (Real.log_pos hz).le)) ?_; push_cast; exact Eq.le (by ring)
end Net
end YM.CF.BPress
