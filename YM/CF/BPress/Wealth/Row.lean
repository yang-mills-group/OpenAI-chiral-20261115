import YM.CF.BPress.Wealth.Path
/-!
Formulas eq:B-keepforms. Working in normal Hilbert spaces. Orbit attachment representation `shortRow` (infinite even if M small; absolutely convergent). v leg shift and pull included in `orbitP`. L terms will cancel in the SUM using physical reindex; never asserting drop from price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side} (M:ℕ) (v:Signed)(R:PathData group) {p:BudgetPoint}{d:Clip}{ζ C D σ Λ y κ β:ℝ}

-- short coefficients, true values
def prime (i : PlaqAxes)(n:ℕ) := if (R.row i n).2.length ≤ M then (R.row i n).1 else 0
def tally (i : PlaqAxes)(f:RG.Slot→ ink) := ∑' n, prime M R i n • f (R.row i n).2
lemma rank_r (i:Bonding s)(U:Micro s): tally M R i.2 (fun n=> n.atSite U i.1)=unitR R M U i:=by
 apply tsum_congr; intro n; unfold prime shortenTerm -- tune
 split_ifs with h h'; rfl; all_goals first| omega| simp
variable (H : R.Bounds d σ C Λ)
include H
lemma tally_price (i:PlaqAxes){f:RG.Slot→ink}{x : ℝ}(p:0 ≤ x)(t:∀ i:RG.Slot,i.length≤M → ‖f i‖ ≤ x) : let F(n):= prime M R i n • f (R.row i n).2; Summable F ∧ ‖tally M R i f‖ ≤ x*C:=by
 intro F; have hp : SumBudget (fun n=> ‖F n‖) (x*C):=by
    apply budget_mono (budget_scale p (H.rows i)); · exact fun _=> norm_nonneg _
    intro n; unfold F prime; split; next q=> rw [norm_smul,Real.norm_eq_abs,mul_comm x]; apply mul_le_mul _ (t _ q) (norm_nonneg _) (by positivity); exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity [H.width]))
    next q=> simp only [zero_smul,norm_zero]; positivity
 exact ⟨hp.2.1.of_norm,(norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2⟩
def safeR (M:ℕ) (f:RG.Slot→ink):=∃ C:ℝ, 0≤C∧∀ i:RG.Slot,i.length≤M→ ‖f i‖ ≤ C
namespace safeR
omit H
variable {M}
lemma cut (v:Config group s)(i:Site s): safeR M fun x=> RG.Slot.atSite x v i:= ⟨2,zero_le_two,fun i _=> RG.Slot.eval_norm ..⟩
lemma finiteC {F:PlaqAxes→ink}: safeR M fun i=> F i.plaq:= by
 let C:=∑ i: PlaqAxes, ‖F i‖; exact ⟨C,sum_nonneg fun i _=>norm_nonneg _, fun i _=> single_le_sum (f:=fun i=>‖F i‖) (fun i _=> norm_nonneg _) (mem_univ _)⟩
lemma graded (o:Site s)(w : Directions group s)(v:Signed) : safeR M fun i=> orbitP v (door i o) w:=by
 let C:= 4*‖w‖; have h:0 ≤‖w‖:=norm_nonneg _; exact ⟨C,by unfold C; positivity,fun i _=> psi_norm v ((pi_norm_le_iff_of_nonneg h).mp le_rfl) _⟩
lemma minus {f g : RG.Slot→ink} (h:safeR M f)(t:safeR M g): safeR M fun x=> f x-g x:=by obtain ⟨x,p,h⟩:=h; obtain ⟨y,q,t⟩:=t; exact ⟨_, add_nonneg p q,fun i m=> (norm_sub_le (f i) _).trans (add_le_add (h i m) (t i m))⟩
lemma scaled {f:RG.Slot→ink}(h:safeR M f)(c:ℝ): safeR M fun x=> c • f x:=by
 obtain ⟨x,p,h⟩:=h; refine ⟨_,mul_nonneg (norm_nonneg c) p, fun j m=>?_⟩; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h j m) (norm_nonneg c)
end safeR
lemma tally_sums (i:PlaqAxes) {f:RG.Slot→ink}(p:safeR M f): Summable fun n=> prime M R i n • f (R.row i n).2:=by obtain ⟨c,x,v⟩:=p; exact (tally_price M R H i x v).1
lemma tally_smul (c:ℝ)(i:PlaqAxes){f:RG.Slot→ink}(p:safeR M f) : c • tally M R i f=tally M R i (fun x=>c • f x):=by rw [tally,←(tally_sums M R H i p).tsum_const_smul c]; apply tsum_congr; intro x; apply smul_comm -- tune mathlib
lemma tally_sub (i:PlaqAxes){f g:RG.Slot→ink}(p:safeR M f)(h:safeR M g): tally M R i f - tally M R i g=tally M R i (fun x=> f x-g x):= by rw [tally,tally,← (tally_sums M R H i p).tsum_sub (tally_sums M R H i h)]; apply tsum_congr; intro n; rw [smul_sub] -- tune orientation
-- formulas under Breg

def C0 (z:PlaqAxes):= tally M R z (fun i=> psi v i.plaq)
def T0 (z:Bonding s)(f:Directions group s):= tally M R z.2 (fun i=> orbitP v (door i z.1) f)
def Lk (z:Bonding s)(f:Directions group s):= chPrice * β* inner ℝ (mA y • C0 M v R z.2) (T0 M v R z f)
def Qk (z:Bonding s)(f:Directions group s):= chPrice* β * ‖T0 M v R z f‖^2 /2
variable (q:Dividend D κ ζ y)
include q
lemma baseC (z:PlaqAxes): ‖C0 M v R z‖ ≤ ζ*C:= tally_price M R H z q.posC.le (fun i _=> q.fixed v i.plaq)|>.2
lemma rankBack (i:Bonding s): ‖unitR R M (pull v 0 (background y)) i‖ ≤ ζ*mA y*C:=by rw [←rank_r]; exact (tally_price M R H i.2 (mul_nonneg q.posC.le (mA_pos q.young).le) fun i _=> c_back i v _ q).2
omit q
lemma baseT (i:Bonding s)(w:Directions group s)(x : ℝ)(p:∀ i, ‖w i‖ ≤ x): ‖T0 M v R i w‖ ≤4*x*C:= by
 have hx:0≤x:=(norm_nonneg _).trans (p (i.1,0)); apply (tally_price M R H i.2 (by positivity : 0≤4*x) _).2; intro i t; apply psi_norm v p -- tune syntax
lemma base_lin (i: Bonding s)(f g:Directions group s): T0 M v R i (f-g)=T0 M v R i f-T0 M v R i g:= by
 rw [T0,T0,T0,tally_sub M R H i.2 (safeR.graded ..) (safeR.graded ..)]; congr; simp_rw [LinearMap.map_sub]
lemma base_smul (a:ℝ)(i:Bonding s)(f:Directions group s): T0 M v R i (a • f)=a • T0 M v R i f:= by
 rw [T0,T0,tally_smul M R H a i.2 (safeR.graded ..)]; congr; simp_rw [LinearMap.map_smul]
include q
omit H in
lemma stretch_pos : 0≤ stretch ζ M:=by unfold stretch; positivity [q.posC,show 0<scr from group.colorScale_pos]

lemma rank_z (i:Bonding s): ‖unitR R M (pull v 0 (background y)) i - mA y • C0 M v R i.2‖ ≤ ((stretch ζ M+ζ)*finer y)*C := by
 rw [←rank_r,C0,tally_smul M R H _ i.2 safeR.finiteC,tally_sub M R H i.2 (safeR.cut ..) (safeR.finiteC.scaled _)]; refine (tally_price M R H i.2 (by positivity [stretch_pos M q,finer_pos q.young,q.posC]) ?_).2 -- tune H include
 intro a h; exact a0_near M a v i.1 q h
lemma rank_t (i:Bonding s)(U:Micro s)(w:Directions group s)(t: Tested D κ y (tickets M (.inr (v,i))) U w):
 ‖unitR R M (pull v 0 U) i‖ ≤ temp y*C ∧ ‖unitR R M (pull v 0 U) i -unitR R M (pull v 0 (background y)) i - T0 M v R i w‖ ≤ ((2*stretch ζ M+ζ)*finer y)*C := by
 rw [←rank_r,←rank_r]; refine ⟨(tally_price M R H i.2 (temp_pos q.young).le fun a h=> c_actual M a v i.1 q t h).2,?_⟩
 rw [T0,tally_sub M R H i.2 (safeR.cut ..) (safeR.cut ..),tally_sub M R H i.2 ((safeR.cut ..).minus (safeR.cut ..)) (safeR.graded ..)]; refine (tally_price M R H i.2 (by positivity [stretch_pos M q,finer_pos q.young,q.posC]) ?_).2
 intro a h; exact near_cost M a v i.1 q t h
-- unified form all root, and Taylor statement. orientation indices.
omit H q
def form (R:PathData group)(M:ℕ)(i:Root s) : Directions group s→ ink:= Sum.elim (fun i w=> orbitP 1 i w) (fun i=> T0 M i.1 R i.2) i
def base (R:PathData group)(M:ℕ)(i:Root s):= Sum.elim (fun i:Bonding s=> psi 1 i.2) (fun ⟨a,p⟩=> C0 M a R p.2) i
def wgt (d:Clip)(i:Root s):= Sum.elim (fun _=>d.direct) (fun _=> chPrice) i
def first (R:PathData group)(d:Clip)(M:ℕ)(β y:ℝ)(i:Root s)(w:Directions group s):=wgt d i*β* inner ℝ (mA y • base R M i) (form R M i w)
def second (R:PathData group)(d:Clip)(M:ℕ)(β:ℝ)(i:Root s)(w:Directions group s):=wgt d i*β*‖form R M i w‖^2/2
include H q
variable {U: Micro s}{w:Directions group s}
lemma theorem_box (z:0<D)(x:p.threshold=temp y)(t:0 ≤ β)(P:Checks M p d)(i:Root s)(k: Tested D κ y (tickets M i) U w):
    |heavy R d p β M i U-(heavy R d p β M i (background y)+ first R d M β y i w + second R d M β i w)| ≤
    (β* (d.direct * (3*(1+4*D)*ζ) + chPrice*(3*( (1+ζ+4*D)*C) * ((2*stretch ζ M+ζ)*C))))* finer y*temp y:=by -- desired β parens tune
 have hζ:=q.posC; have hC:=budget_nonneg H.three; have ht:= temp_pos q.young; have hF:= finer_pos q.young
 rcases i with i|⟨v,i⟩
 · have hv(j): aperture i j∈tickets M (.inl i):= mem_image_of_mem _ (mem_univ j); refine le_trans ?_ (le_trans (income_direct q d p β t i x z.le (fun j=>k.small _ (hv j)) (fun j=>k.near _ (hv j)) k.angle) ?_); swap; · gcongr; exact le_add_of_nonneg_right (by positivity [stretch_pos M q, chPrice_pos])
   dsimp only [Lp,Qp, first, second, base,form,wgt, heavy,Sum.elim_inl]; rw [mul_comm β d.direct]
 have hm: unitR R M (pull v 0 (background y)) i= unitR R M (pull v 0 (background y)) i:= rfl
 let A:= pull v 0 (background y:Micro s); let B:= pull v 0 U; have hk: PathData.kept d p.threshold i.1 A:=by rw [x]; exact kept_bg v i.1 q d
 have he: PathData.kept d p.threshold i.1 B:=by rw [x]; exact kept_use M v i.1 q k d p P x
 let a:= unitR R M A i; let b:=unitR R M B i; let L:= T0 M v R i w; let X:=mA y•C0 M v R i.2; let Y:=(1+ζ+4*D)*C*temp y; let F:=(2*stretch ζ M+ζ)*finer y*C
 have ha: ‖a‖≤ Y:= calc
   _ ≤ ζ*mA y*C:= rankBack M v R H q i
   _ ≤ ζ*temp y*C:=by gcongr; exact q.mag
   _ ≤ Y:= by unfold Y; rw [mul_right_comm]; gcongr; linarith
 obtain ⟨p',h'⟩:= rank_t M v R H q i U w k; have hv:temp y * C ≤ Y:=by unfold Y; apply le_trans (by rw [mul_comm] : temp y*C≤ C*temp y); gcongr; exact le_mul_of_one_le_left hC (by linarith only [hζ,z])
 have hL:‖L‖ ≤ Y:=by refine (baseT M v R H i w (D*temp y) k.angle).trans ?_; unfold Y; nlinarith only [mul_nonneg (show 0≤(1+ζ) by linarith) (mul_nonneg hC ht.le)]
 have hx:= volumeQ ha (show ‖b‖≤ Y from p'.trans hv) hL (le_trans (a:= ‖a-X‖) (rank_z M v R H q i) (by unfold F; gcongr; nlinarith [stretch_pos M q])) (show ‖b-a-L‖≤F from h'); -- tune gcongr unfold F
 dsimp only [heavy, first, second, base, form, wgt, kept,keepR, Sum.elim_inr]; rw [if_pos hk,if_pos he]; let l:=chPrice*β; have hp:0≤l:=mul_nonneg chPrice_pos.le t; change |l*_-(l*_+l*inner ℝ X L+l*‖L‖^2/2)|≤ _
 rw [show l * _ - (l * _ + l * inner ℝ X L+l*‖L‖^2/2)= l* (‖b‖^2/2-(‖a‖^2/2+inner ℝ X L+‖L‖^2/2)) from ?_,abs_mul,abs_of_nonneg hp]; swap; · unfold l a b A B; ring
 apply le_trans (mul_le_mul_of_nonneg_left hx hp); let l':=3*((1+ζ+4*D)*C)*((2*stretch ζ M+ζ)*C); unfold Y F l; apply le_trans (b:=β*(chPrice*l')* finer y*temp y) (by unfold l'; exact Eq.le (by ring)); gcongr; exact le_add_of_nonneg_left (by positivity [d.quadratic_pos]) -- tune
end YM.CF.BPress.Wealth
