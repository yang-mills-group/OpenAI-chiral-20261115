import YM.CF.BProof.Scales

/-! Formal conventions in VOLUME_PROOF: PL=pays absolute value by C log^C with some
exponent; NPL by any inverse power. We absorb constants by enlarging purchased powers.
No restrictions on signs or small y. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Pressure Filter Set
open Real (exp log)
open scoped Topology
abbrev lp (y t:ℝ):=coin y 0 0 t
def PL (f:ℝ→ℝ):Prop:= ∃ d:ℝ,∀ᶠ y in atTop, |f y| ≤ lp y d
def NPL (f:ℝ→ℝ):Prop:= ∀ d:ℝ,∀ᶠ y in atTop, |f y| ≤ lp y d
lemma lmono {a b:ℝ}(h:a≤b) : ∀ᶠ y in atTop,lp y a≤lp y b :=by
 rcases h.eq_or_lt with h|h
 · subst a; simp
 filter_upwards [coin_budget (a:=0) (b:=0) (d:=0) (e:=0) (c:=a) (f:=b) (by simp [h]) 1 1 one_pos] with y hy; simpa using hy.le
lemma lmax (a b:ℝ): ∀ᶠ y in atTop,lp y a+lp y b≤lp y (max a b+1):=by
 have h:max a b<max a b+1:=lt_add_one _; filter_upwards [lmono (le_max_left a b),lmono (le_max_right a b),coin_budget (a:=0) (b:=0) (d:=0) (e:=0) (Or.inr (Or.inr ⟨rfl,rfl,h⟩)) 2 1 one_pos] with y h1 h2 h3
 change 2*lp y (max a b)<1*lp y _ at h3; linarith
lemma lscaled {a b t:ℝ}(h:a<b) : ∀ᶠ y in atTop,t*lp y a ≤ lp y b:=by
 simpa only [one_mul] using (coin_budget (a:=0) (b:=0) (d:=0) (e:=0) (Or.inr (Or.inr ⟨rfl,rfl,h⟩)) t 1 one_pos).mono (fun y hy=>hy.le)
lemma lscaled_lt {a b t:ℝ}(h:a<b) : ∀ᶠ y in atTop,t*lp y a < lp y b:=by simpa only [one_mul] using coin_budget (a:=0) (b:=0) (d:=0) (e:=0) (Or.inr (Or.inr ⟨rfl,rfl,h⟩)) t 1 one_pos
variable {f g : ℝ→ℝ}
lemma PL.by_le (u:PL g)(h:∀ᶠ y in atTop, |f y| ≤ |g y|): PL f:=by
 obtain ⟨d,hg⟩:=u; exact ⟨d,h.mp (hg.mono fun x hg (t:|f x| ≤ |g x|)=> t.trans hg)⟩
lemma NPL.by_le (u:NPL g)(h:∀ᶠ y in atTop, |f y| ≤ |g y|): NPL f:= fun d=> h.mp ((u d).mono (fun x hg (t:|f x| ≤ |g x|)=> t.trans hg))
lemma PL.powLog (t:ℝ): PL (fun y=>lp y t):= ⟨t,Eventually.of_forall fun y=> by rw [abs_of_nonneg (coin_pos ..).le]⟩
lemma PL.add (u:PL f)(v:PL g): PL (fun y=>f y+g y):=by
 obtain ⟨d,h⟩:=u; obtain ⟨k,g⟩:=v; refine ⟨max d k+1,?_⟩; filter_upwards [h,g,lmax d k] with y hx hk hv; exact (abs_add_le ..).trans ((add_le_add hx hk).trans hv)
lemma PL.neg (u: PL f): PL (fun y=> -f y):=by unfold PL at *; simpa using u
lemma PL.abs (u:PL f): PL (fun y=>|f y|):=by unfold PL at *; simpa using u
lemma PL.max (u:PL f)(v:PL g): PL (fun y=>max (f y) (g y)):=by
 refine PL.by_le (u.abs.add v.abs) (Eventually.of_forall fun y=>?_); rw [abs_of_nonneg (by positivity : 0≤ |f y| + |g y|)] -- tune
 rcases max_choice (f y) (g y) with h|h<;> rw [h] <;> simp
lemma PL.min (u:PL f)(v:PL g): PL (fun y=>min (f y) (g y)):=by convert u.neg.max v.neg |>.neg using 1; ext x; change Min.min (f x) (g x)=-(Max.max (-f x) (-g x)); grind -- tune
lemma PL.mul (u:PL f)(v:PL g): PL (fun y=>f y*g y):=by
 obtain ⟨d,h⟩:=u; obtain ⟨k,g⟩:=v; refine ⟨d+k,?_⟩; filter_upwards [h,g] with y hx hk; simp only [abs_mul]; exact (mul_le_mul hx hk (abs_nonneg _) (coin_pos ..).le).trans_eq (by rw [coin_mul]; simp)
lemma PL.const (x:ℝ): PL (fun _=>x):=by refine ⟨1,?_⟩; simpa using lscaled (t:=|x|) (show (0:ℝ)<1 from one_pos)
lemma PL.pow (u:PL f)(d:ℕ): PL (fun y=>f y^d):=by induction d with | zero=>simp only [pow_zero]; exact PL.const _|succ i ih=> simp_rw [pow_succ]; exact ih.mul u
lemma PL.ceil (u:PL f)(h:∀ᶠ y in atTop,0≤f y): PL (fun y=>(↑⌈f y⌉₊:ℝ)):=by
 refine PL.by_le (u.add (PL.const 1)) ?_; filter_upwards [h] with y hy; simp only [abs_of_nonneg (by positivity :0≤ (↑⌈f y⌉₊:ℝ)), abs_of_nonneg (by positivity :0≤ f y+1)]; exact (Nat.ceil_lt_add_one hy).le
lemma PL.log_y : PL Real.log:=by refine ⟨1,?_⟩; filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy; unfold lp; rw [coinLog hy, abs_of_nonneg (Real.log_pos hy).le]

lemma NPL.weak (u:NPL f) : PL f:= ⟨0,u 0⟩
lemma NPL.add (u:NPL f)(v:NPL g): NPL (fun y=>f y+g y):=by
 intro d; filter_upwards [u (d-1),v (d-1),lmax (d-1) (d-1)] with y hx hk hv; simpa only [max_self,sub_add_cancel] using (abs_add_le ..).trans ((add_le_add hx hk).trans hv)
lemma PL.muln (u:PL f)(v:NPL g): NPL (fun y=>f y*g y):=by
 intro d; obtain ⟨k,h⟩:=u; filter_upwards [h,v (d-k)] with y hx hk; exact (abs_mul ..).trans_le ((mul_le_mul hx hk (abs_nonneg _) (coin_pos ..).le).trans_eq (by rw [coin_mul]; simp))
lemma NPL.mulp (u:NPL f)(v:PL g): NPL (fun y=>f y*g y):=by simpa only [mul_comm] using v.muln u
lemma coin_n {a b:ℝ}(h:a<0∨a=0∧ b<0)(c:ℝ) : NPL (fun y=>coin y a b c):=by
 intro d; filter_upwards [coin_budget (a:=a) (b:=b) (c:=c) (d:=0) (e:=0) (f:=d) (h:=by grind) 1 1 one_pos] with y hy; -- missing a b
 simpa [abs_of_nonneg (coin_pos ..).le] using hy.le
lemma NPL.zero : NPL (fun _=>0):= fun d=>Eventually.of_forall fun y=>by rw [abs_zero]; exact (coin_pos ..).le
lemma NPL.limit (u:NPL f): Tendsto f atTop (𝓝 0):=by
 apply squeeze_zero_norm' _ (coin_purchases (a:=0) (b:=0) (c:= -1) (by norm_num)); exact u (-1)
lemma coin_strongLt {a b:ℝ}(h:0<a∨a=0∧0<b)(r:PL f) : ∀ᶠ y in atTop,|f y|<coin y a b 0:=by
 obtain ⟨d,v⟩:=r; filter_upwards [v, coin_budget (a:=0) (b:=0) (d:=a) (e:=b) (c:=d) (f:=0) (by grind) 1 1 one_pos] with y hx hk; exact lt_of_le_of_lt hx (by simpa using hk)
end YM.CF.BProof
