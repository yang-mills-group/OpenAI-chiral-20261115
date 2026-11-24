import YM.CF.BProof.Weights.Supply
import YM.CF.BProof.Gates.Dyad

/- uniform PL stretch permission & time_T(a) sharing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable (c:Clip)(M:ℝ→ℕ)(w R:ℝ)(d:ℕ)(y:ℝ)
-- k τ required gauge budgets; allow smaller with PL. choose intrinsic k. ≤1.
def pace := min (1:ℝ) (min (halfC d M c R y/3) (uPull w (M y)/3))
lemma pace_p (h:0<w) : 0<pace c M w R d y:=lt_min one_pos (lt_min (div_pos (half_pos (Pricing.rC_p ..)) (by norm_num)) (div_pos (Charge.uPull_p w h (M y)) (by norm_num)))
lemma pace_u : pace c M w R d y≤ 1:= min_le_left ..
lemma pace_j : 3*pace c M w R d y≤ halfC d M c R y:= by
 have h : pace c M w R d y ≤halfC d M c R y/3:= (min_le_right ..).trans (min_le_left ..); linarith
lemma pace_w : 3*pace c M w R d y≤ uPull w (M y):=by
 have h : pace c M w R d y ≤ uPull w (M y)/3:= (min_le_right ..).trans (min_le_right ..); linarith
lemma pl_pace (A:ℝ)(p:0<A)(h:0<w)(v:0<d) : PL (fun y=> (pace c (Charge.reach A) w R d y)⁻¹):= by
 let M:=Charge.reach A; let f(y):=halfC d M c R y; have he: PL (fun y=>(f y/3)⁻¹):=by
    have hx(y): (f y/3)⁻¹=3*(2*(rC c d M R y)⁻¹):=by unfold f halfC; rw [_root_.inv_div, div_eq_mul_inv,_root_.inv_div,div_eq_mul_inv]
    simp_rw [hx]; exact (PL.const 3).mul ((PL.const 2).mul (Pricing.rC_bill c d _ R v (Charge.reach_PL A p)))
 let q(y):=uPull w (M y)
 have hg: PL (fun y=>(q y/3)⁻¹):=by simp_rw [_root_.inv_div,div_eq_mul_inv]; exact (PL.const _).mul (Charge.uPull_PL w h A p)
 let K(y):=1+(f y/3)⁻¹+(q y/3)⁻¹; refine PL.by_le (((PL.const 1).add he).add hg : PL K) (Eventually.of_forall fun y=>?_)
 let p':=pace c M w R d y; have hx:= pace_p c M w R d y h; change |p'⁻¹|≤ |K y|; change 0<p' at hx; rw [abs_of_nonneg (inv_pos.mpr hx).le]; apply le_trans _ (le_abs_self _); have he:0<f y/3:= lt_of_lt_of_le hx (show p'≤_ from (min_le_right ..).trans (min_le_left ..)); have ht:0<q y/3:= lt_of_lt_of_le hx (show p'≤_ from (min_le_right ..).trans (min_le_right ..)); unfold K; have H : p'=1∨ p'=f y/3∨ p'=q y/3:=(by rcases min_choice (1:ℝ) (min (f y/3) (q y/3)) with h|h; exact Or.inl h; exact Or.inr ((min_choice (f y/3) (q y/3)).imp h.trans h.trans) )
 rcases H with r|r|r <;> rw [r] <;> linarith [inv_pos.mpr ht,inv_pos.mpr he]

-- minimum for Factor(lower on Lc chosen pre-pivot as a function of y). tag fx can choose eventual larger REAL provision via lemma.
variable (a:ℝ)(p q:ℝ→ℕ)
def stretch (α k:ℝ)(d:ℕ):= 1+d+⌈α*d*k⁻¹⌉₊
lemma stretch_p {y' b:ℕ}{α k:ℝ}(u:0≤α)(h:0<k)(p:stretch α k d ≤ y'): Factor y' b d k α:=by
 let r:=stretch α k d; have v:(stretch α k d:ℝ)≤ y':=Nat.cast_le.mpr p; have hz:0<r:=by unfold r stretch; omega
 refine ⟨lt_of_lt_of_le hz p,le_trans (b:=stretch α k d) (by unfold stretch; omega) p,h,u,?_⟩; rw [mul_comm k]; apply (div_le_iff₀ h).1; rw [div_eq_mul_inv]; exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr (show ⌈α*d*k⁻¹⌉₊≤ stretch α k d by unfold stretch; omega)).trans v)
lemma stretch_pl {d:ℝ→ℕ}(p: PL fun y=>(d y:ℝ)){k:ℝ→ℝ}(h:∀ y, 0<k y)(u:PL (fun y=>(k y)⁻¹))(α:ℝ)(k':0≤α): PL (fun y=>(stretch α (k y) (d y):ℝ)):= by
 unfold stretch; push_cast; exact ((PL.const _).add p).add ((((PL.const _).mul p).mul u).ceil (Eventually.of_forall fun y=>by have :=h y; positivity))
-- fixed `C=1` from purchases
variable (X:Face.Design)
def dist_need (b:ℕ)(v:ℝ)(y:ℝ)(W:ℝ)(α:ℝ):= stretch α W (expense 0)+stretch α W (upward b (r_F y v) 1 1)
def least (kP:ℕ) (v k y α:ℝ):= 1 + license M d c R y + steady c d M R y + dist_need kP v y k α
lemma least_p (v k α:ℝ):0<least c M R d X.size v k y α:=by unfold least; omega
lemma least_pl (p:PL fun y=> (M y:ℝ))(v₀:0<d)(v:ℝ)(k:ℝ→ℝ)(α:ℝ)(u:0<v)(h: PL (fun y=>(k y)⁻¹))(w:0≤α)(e:∀ y,0< k y) : PL (fun y=>(least c M R d X.size v (k y) y α:ℝ)):=by
 unfold least dist_need; push_cast; have ht:= license_p M p d c R v₀; unfold license at ht; push_cast at ht; refine (((PL.const 1).add ht).add (Pricing.steady_p c d M R v₀ p)).add ((stretch_pl (d:=fun _=> expense 0) (PL.const _) e h α w).add (stretch_pl ?_ e h α w)) -- push_cast tune
 unfold upward House.rate allowD memory; push_cast; exact (PL.const _).mul ((PL.const _).add ((PL.const _).mul ((PL.const _).mul (((PL.const _).mul ((PL.const _).add (((PL.const _).add (F_pl v u)).mul (PL.const _)))).add (PL.const _))))) -- tune

end YM.CF.BProof.Gates
