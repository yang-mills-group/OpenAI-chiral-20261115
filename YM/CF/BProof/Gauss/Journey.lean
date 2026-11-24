import YM.CF.BProof.Prox.Trace
import YM.CF.BProof.Gauss.Beam

/-! Resolvent and trace log for period Hessian inverse-sqrt approximations. Uses
no decay hypothesis on varying backgrounds other than the stated Numeric and Prox.Via;
make an explicit chunk with geometric budget. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Gauss.Journey
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open Prox (Base Show Scope Pup Solo)
open YM.SectorNext.Vacuum.Panel
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {X I A:Type*}[Fintype I][DecidableEq I][Fintype A]
variable [MeasurableSpace X][Countable X][MeasurableSingletonClass X]
variable {B:Base A}(F:B.Index I)(S: Scope X A)(T:X→ Pool I)(p a q:ℝ)

def pen (A:Pool I):= Bin.ray p A
def mag (T:X→Pool I) (p:ℝ)(n:ℕ): Pup X I ℝ := fun x=> pen p (T x)^n
abbrev feeO (T:X→Pool I) := Prox.Atmos.discrete A X S

variable {R k:ℕ}
structure Bloc (B:Prox.Base A)(p a q:ℝ)(b R k:ℕ): Prop where
 step : 0<k
 cost : 0<q
 precise : 0<a
 range : a ≤ p
 gain : Prox.Show.radiusBill B q (R*k) b*(3*(steep a p)^k)≤1/2
variable (p' : Prox.Via F S T R)(v:T=T) -- remove
variable (K: Bloc B p a q F.roof R k)(U:∀ x:X,(T x).IsHermitian)(h:∀ x:X, Numeric (T x) a p)
include p' K U h
private lemma pitch (x:X): 0≤ steep a p∧steep a p<1:= by
 have ht:=K.precise; have hp:=ht.trans_le K.range; exact ⟨sub_nonneg.mpr ((div_le_one hp).mpr K.range), sub_lt_self _ (div_pos ht hp)⟩ -- tune
lemma pen_pay (x:X)(n:ℕ): ‖mag T p n x‖≤ (steep a p)^n:=by
 obtain ⟨u,d,e,H⟩:= dial_receipt (T x) (U x) (h x); rw [mag,pen,e, Bin.ray_dial,←dial_pow]; refine RealM.norm_le u _ (pow_nonneg (pitch F S T p a q p' K U h x).1 n) (fun i=> ?_)
 have hk:=K.precise.trans_le K.range; have hv:0≤1-(d i)/p:=sub_nonneg.mpr ((div_le_one hk).mpr (H i).2); rw [show ((Bin.afford p ∘ d)^n) i=(1-(d i)/p)^n from by simp only [Pi.pow_apply,Function.comp_apply]; unfold Bin.afford; ring,abs_of_nonneg (pow_nonneg hv n)] -- tune ring not x/p syntax
 apply pow_le_pow_left₀ hv; unfold steep; gcongr; exact (H i).1
lemma atlas (n:ℕ)(d:ℝ)(b:n≤k)(u:∀ x:X,(steep a p)^n≤ d)(l:0≤d): Show (feeO S T) F F (mag T p n) q (Prox.Show.radiusBill B q (R*k) F.roof*(3*d)):=by
 apply Prox.Show.office _ S _ _ l (fun x i j=> (entry (mag T p n x) ..).trans ((pen_pay F S T p a q p' K U h x n).trans (u x))) K.cost.le
 exact (((Prox.Via.one (F:=F) (S:=S)).sub (p'.pi_smul p⁻¹)).pow n).le (Nat.mul_le_mul_left _ b)

def rent (B:Base A)(q:ℝ)(r R k:ℕ):=Prox.Show.radiusBill B q (R*k) r*3 +1
omit p' K U h in
lemma rent_pos (B: Base A) (k R t:ℕ)(q:ℝ): 0<rent B q t R k:=by unfold rent Prox.Show.radiusBill; positivity
lemma powder (n:ℕ): Show (feeO S T) F F (mag T p n) q (Prox.Show.cushion (rent B q F.roof R k) k n):=by
 -- X maybe empty. need steep nonnegative without x
 have hm:0≤steep a p:=sub_nonneg.mpr ((div_le_one (K.precise.trans_le K.range)).mpr K.range)
 let Y: Pup X I ℝ:= fun x=>pen p (T x)
 apply Prox.Show.chunk (X':=Y) K.step K.cost.le (rent_pos B _ _ _ _ |>.le) -- tune
 · exact (atlas F S T p a q p' K U h k _ le_rfl (fun _=>le_rfl) (pow_nonneg hm k)).presents_cost le_rfl K.gain
 intro i g; exact (atlas F S T p a q p' K U h i 1 g.le (fun x=> pow_le_one₀ hm (pitch F S T p a q p' K U h x |>.2.le)) zero_le_one).presents_cost le_rfl (by unfold rent; rw [mul_one]; linarith) -- tune

/-- any bounded-by-1 scalar coefficient. log powers and inverse as particular cases. -/
def wind (f:ℕ→ℝ) (x:X) : Pool I := ∑' n:ℕ, f n • mag T p n x
abbrev bill (B:Base A)(q:ℝ)(b R k:ℕ):ℝ:= k*(rent B q b R k)*2
lemma summit (f:ℕ→ℝ)(g:∀ i,|f i|≤1) (x:X):HasSum (fun n:ℕ=>f n • mag T p n x) (wind T p f x):=by
 let u:=steep a p; obtain ⟨hx,hg⟩:=pitch F S T p a q p' K U h x; have hp:=(summable_geometric_of_lt_one hx hg); apply Summable.hasSum; apply hp.of_norm_bounded; intro i; rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (g i)).trans (pen_pay F S T p a q p' K U h x i)
omit p' K U h in
private lemma navigate {a:ℕ→Pool I}{A:Pool I}(H:HasSum a A)(i j:I): HasSum (fun n=>a n i j) (A i j):=by
 let L:Pool I →ₗ[ℝ] ℝ:={toFun:=fun A=>A i j,map_add':=fun _ _=> rfl,map_smul':=fun _ _=>rfl}; exact H.map L L.continuous_of_finiteDimensional
lemma warrant (f:ℕ→ℝ)(g:∀ i,|f i|≤1): Show (feeO S T) F F (wind T p f) q (bill B q F.roof R k):=by
 have ht:= (rent_pos B k R F.roof q).le -- order tune
 have hv:= Prox.Show.cushion_pays K.step (C:=rent B q F.roof R k) (by unfold rent Prox.Show.radiusBill; positivity); let Y(n):= f n • mag T p n
 apply Prox.Show.presents_cost _ le_rfl hv.2.2; apply Prox.Show.finance hv.2.1 K.cost.le (Y:=Y) _ hv.1; swap
 · intro n; exact ((powder F S T p a q p' K U h n).smul (f n)).presents_cost le_rfl (mul_le_of_le_one_left (hv.1 n) (g n))
 intro x i j; exact (navigate (summit F S T p a q p' K U h f g x) i j).tsum_eq.symm -- tune entry cont map
-- choose log coefficient so zero term unused.
def coin (i:ℕ) :ℝ:= -(i:ℝ)⁻¹
omit p' K U h in
lemma coinage (i:ℕ): |coin i|≤ 1:=by unfold coin; rcases i with _|i; simp; rw [abs_neg,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i)))
lemma tourist (x:X) : Real.log (T x).det= (wind T p coin x).trace+(Fintype.card I:ℝ)*Real.log p:=by
 rw [log_form _ (U x) (h x) K.precise K.range,Matrix.trace, ←nsmul_eq_mul, ←Finset.card_univ, ← Finset.sum_const,←Finset.sum_add_distrib]; refine sum_congr rfl fun i hi=>?_
 have hx:= summit F S T p a q p' K U h coin coinage x; let u : ℕ → ℝ := fun n=> (coin n • mag T p n x) i i; have he : HasSum u (wind T p coin x i i):= navigate hx i i
 rw [priceLine,add_comm,Matrix.diag_apply,← he.tsum_eq, ← he.summable.sum_add_tsum_nat_add 1]; congr 1
 rw [Finset.sum_range_one]; simp only [u,coin,Nat.cast_zero,_root_.inv_zero,neg_zero,zero_smul,Matrix.zero_apply,zero_add]; refine tsum_congr fun i=>?_ ; unfold mag pen bead; rw [Matrix.smul_apply,Nat.cast_add_one]; simp only [stencil,Bin.ray, smul_eq_mul]; ring
lemma binder (x:X): (T x)⁻¹=p⁻¹ • wind T p (fun _=>1) x := by
 have hv:= pitch F S T p a q p' K U h x
 have he: ‖pen p (T x)‖ <1:= by simpa only [mag,pow_one] using (pen_pay F S T p a q p' K U h x 1).trans_lt (show (steep a p)^1<1 by rw [pow_one]; exact hv.2) -- tune
 apply Matrix.inv_eq_right_inv; unfold wind mag; simp_rw [one_smul]; convert mul_neg_geom_series (pen p (T x)) he using 1
 unfold pen Bin.ray; rw [sub_sub_cancel,Matrix.smul_mul,Matrix.mul_smul]
lemma bound_inv : Show (feeO S T) F F (fun x=>(T x)⁻¹) q (p⁻¹*(bill B q F.roof R k)) :=by
 rw [show (fun x:X=>(T x)⁻¹)=(p⁻¹ • wind T p fun _=>1) from funext fun x=> binder F S T p a q p' K U h x]; have he:= (warrant F S T p a q p' K U h (fun _=>1) (by intro; norm_num)).smul p⁻¹; rwa [Real.norm_of_nonneg (by have := K.precise.trans_le K.range; positivity : 0≤p⁻¹)] at he
end YM.CF.BProof.Gauss.Journey
