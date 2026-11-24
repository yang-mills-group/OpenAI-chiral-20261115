import GaugeFieldConstruction.Pinions
/-!
# Binomial/taylor even on crossed seams. x ∈ Z^d; seminorm form (for rows).
-/
set_option autoImplicit false
set_option maxHeartbeats 35000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FlightFlux
open Lattice Function Finset Metric
open scoped Topology BigOperators Classical
variable {I E:Type*}[Fintype I][DecidableEq I][AddCommGroup E][Module ℝ E]
variable {p: Shape I→ E} {K:E→ℝ}{n:ℕ}{m a:ℝ}
section
structure Dignity (f:E→ℝ):Prop where
 a x:0 ≤ f x
 b x y: f (x+y) ≤ f x+f y
 c (s:ℝ) x:f (s • x) =|s| *f x
lemma Dignity.norm {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]:Dignity (fun x:E=>‖x‖):=⟨norm_nonneg,norm_add_le,fun i a=>by rw [norm_smul, Real.norm_eq_abs]⟩
lemma Dignity.zero (h:Dignity K):K 0=0:=by simpa only [zero_smul,abs_zero,zero_mul] using h.c 0 0
lemma Dignity.neg (h:Dignity K)(x:E):K (-x)=K x:=by simpa only [neg_smul,one_smul,abs_neg,abs_one,one_mul] using h.c (-1) x
lemma Dignity.sub (h:Dignity K)(x y:E):K (x-y) ≤ K x+K y:=by rw [sub_eq_add_neg]; exact (h.b x _).trans_eq (by rw [h.neg])
lemma Dignity.swap_sub (h:Dignity K)(x y:E):K (x-y)= K (y-x):=by rw [← h.neg,neg_sub]
lemma Dignity.inTent (h:Dignity K)(x y:E):K x ≤ K (x-y)+K y:=by nth_rw 1 [←sub_add_cancel x y]; exact h.b _ _
local notation "t₀" i:max=> Pi.single i (1:ℤ)
lemma coin_op (h:Dignity K)(p:Shape I → E)(x:Shape I)(n:ℕ)(a:ℝ)(e:p 0=0)(f:lateral x≤ n)(g:∀ i:Shape I, lateral i ≤ n → ∀ j,K (advance j p i)≤a): K (p x) ≤ lateral x*a:=by
 apply climb (fun y=> K (p y)≤lateral y*a) x (by rw [e,h.zero,lateral_zero]; simp); intro i j w q y v z; have hp:K (p j) ≤ _:= q; have he : K (p y-p j) ≤ a:=by
    rcases z with Q|Q
    · rw [h.swap_sub, Q]; exact g y (by omega) i
    rw [Q]; exact g j (by omega) i
 change K (p y) ≤ _; rw [v,Nat.cast_add_one]; exact (h.inTent ..).trans ((add_le_add he hp).trans_eq (by ring))
structure Goose (hK:Dignity K)(a z:ℝ) (p:Shape I→ E)(r:ℕ):Prop where
 a' : 0 ≤ a
 z' : 0 ≤ z
 H(l:List I) (x:Shape I) (t:l.length≤r) : K (loom l p x)≤ a*z^l.length*(1+z*lateral x)^3
lemma Goose.mus {r:ℕ}(h:Dignity K) {a z:ℝ}(e:Goose h a z p r) (i:I): (k:ℕ) → k+1≤r → Goose h (a*z) z (advance i p) k:=by
 intros k hp; refine ⟨mul_nonneg e.a' e.z', e.z',fun l x v=>?_⟩; rw [←advance_sewn,←loom_cons]; exact (e.H _ x (by simp; omega)).trans_eq (by simp only [List.length_cons,pow_succ]; ring)
lemma Goose.leap {r:ℕ}(h:Dignity K) {a z:ℝ}(e:Goose h a z p r)(x:Shape I):K (p x) ≤ a*(1+z*lateral x)^3:= by simpa only [List.length_nil,loom,List.foldr, pow_zero,mul_one] using e.H [] x (by simp)
-- polynomials walking
lemma GoldC (h:Dignity K)(p: Shape I→ E) (x:Shape I)(a:ℝ) (v:K (p 0) ≤ a): K (curb p x) ≤ a:=v
abbrev slopeK(p:Shape I→E):= slope (fun i=>advance i p 0)
abbrev ticketK(p:Shape I → E):=ticket (fun i j=>loom [i,j] p 0)
lemma scaleStance (h:Dignity K)(p:Shape I→ E)(x:Shape I)(a:ℝ)(g:∀i,K (advance i p 0)≤a): K (slopeK p x)≤ lateral x*a:= by
 exact coin_op h (slopeK p) x (lateral x) a (slope₀ _) le_rfl (fun j _ i=> by rw [show advance i (slopeK p)= _ from φ_step ..]; exact g i)
lemma tear_t (p: Shape I → E) : ∀ k, advance k (ticketK p)=slopeK (advance k p):=by
 intro k; let x:=hitch_angle p k; unfold hitch at x; rw [advance_add,dock_angle] at x; exact add_left_cancel x
lemma GoldT (h:Dignity K)(p:Shape I→ E)(x:Shape I)(a:ℝ)(u:0 ≤ a)(g:∀i j,K (advance i (advance j p) 0) ≤ a): K (ticketK p x) ≤ (lateral x:ℝ)^2*a :=by
 let v:=lateral x; have hp(i):∀ j:Shape I,lateral j≤ v → K (advance i (ticketK p) j) ≤ v*a := by
    rw [tear_t]; exact fun j y=> (scaleStance h _ _ a (fun k=>g k i)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr y) u)
 apply (coin_op h _ x v (v*a) (ticket₀ _) le_rfl (fun i p j=> hp j i p)).trans_eq; unfold v; ring
-- first m-term Newton subtraction
abbrev wheelK (p: Shape I→ E)(m:ℕ) : Shape I→ E:= match m with|0=>0|1=>curb p|2=>dock p|_+3=>hitch p
lemma grade_wh (p:Shape I→E)(r:ℕ)(w:r≤ 3): Paper r (wheelK p r):=by
 interval_cases r; exact paper_start.mpr rfl; exact paper_const (I:=I) (p (0:Shape I)); exact paper_add (paper_low (curb_paper p) one_le_two) (slope_paper _);
 exact paper_add (paper_low (paper_add (paper_low (curb_paper p) one_le_two) (slope_paper _)) (by decide)) (ticket_paper _) -- tune le
lemma wheel_step (p:Shape I→ E)(r:ℕ)(w:r<3)(i:I): advance i (wheelK p (r+1))= wheelK (advance i p) r:=by interval_cases r; exact advance_const ..; exact dock_angle ..; exact hitch_angle ..
lemma shunt_zero (p:Shape I→E)(r:ℕ)(w:r≤2): (p-wheelK p (r+1)) 0=0:=by interval_cases r <;> simp [wheelK,sub_self,dock_port,hitch_port,curb] -- tune
lemma shunt_step (p:Shape I→ E)(i:I)(w:n<3): advance i (p-wheelK p (n+1))=advance i p-wheelK (advance i p) n:=by rw [advance_sub,wheel_step _ _ w]
lemma Goose.lower {a z:ℝ} {h:Dignity K} {m r:ℕ}(b:Goose h a z p m)(u:r ≤ m):Goose h a z p r:=⟨b.a',b.z',fun i j v=> b.H i j (v.trans u)⟩
lemma Goa_cost (h:Dignity K)(p:Shape I→ E) (a z:ℝ)(m:ℕ)(b:m≤3) (x:Shape I) (v:Goose h a z p m) (y:z*lateral x ≤ 1) : K ((p-wheelK p m) x) ≤ 8*a*z^m*(lateral x:ℝ)^m := by
 have ha:=v.a'; have hz:=v.z'
 induction m generalizing p a x with
 | zero=>
    change K (p x-0) ≤ _; simp only [sub_zero,pow_zero,mul_one]; apply (Goose.leap h v x).trans; refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show 1+ z*lateral x ≤2 from (by linarith)) _) ha).trans_eq ?_; ring
 | succ m ih=>
    have ht:m<3:=by omega
    apply (coin_op h _ x (lateral x) (8*(a*z)*z^m * (lateral x:ℝ)^m) (shunt_zero p m (by omega)) le_rfl (fun i hx j=> by
       let v':=Goose.mus h v j m le_rfl; rw [shunt_step _ _ ht]; exact (ih _ _ ht.le _ v' ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hx) hz).trans y) v'.a').trans (by gcongr))).trans_eq; rw [pow_succ,pow_succ]; ring -- tune
lemma Goa_far (h:Dignity K)(p:Shape I→E) (a z:ℝ)(m:ℕ)(b:m≤3) (x:Shape I)(v:Goose h a z p m)(y:1 ≤ z*lateral x) : K (wheelK p m x) ≤ 3*a*(z*lateral x)^3:=by
 let A:= (z*lateral x); have hp: 1≤ A:=y; have ha:=v.a'; have hz:=v.z'
 have ht(n:ℕ)(w:n ≤3): a*A^n ≤ a*A^3:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp w) ha
 have he: K (curb p x) ≤ a*A^3:=by have hh:K (p 0) ≤ a:=(by simpa only [lateral_zero, Nat.cast_zero,mul_zero,add_zero, List.length_nil,pow_zero,mul_one,one_pow, loom,List.foldr] using v.H [] 0 (by simp)); exact (GoldC h _ x _ hh).trans (by simpa only [pow_zero,mul_one] using ht 0 (by decide)) -- tune inner let p
 have hu(t:1 ≤ m): K (slopeK p x) ≤ a*A^3:= (scaleStance h _ x (a*z) (fun i=> by simpa only [lateral_zero,Nat.cast_zero, mul_zero,add_zero,List.length_cons,List.length_nil,Nat.zero_add, pow_one,mul_one,one_pow,loom_cons, show loom [] p=p from rfl] using v.H [i] 0 t)).trans ((le_of_eq (show (↑(lateral x):ℝ)*(a*z)=a*A^1 from by unfold A; ring)).trans (ht 1 (by decide)))
 let U:=a*A^3; have hU:0 ≤ U:=by unfold U; positivity
 have hh:2 ≤ m → K (dock p x)≤ U+U:=fun i=>(h.b _ _).trans (show _ from add_le_add he (hu (by omega)))
 change _ ≤ 3*a*A^3; rw [mul_assoc]; change _ ≤ 3*U
 interval_cases m
 · change K 0≤ _; rw [h.zero]; positivity
 · exact he.trans (by change U≤_; linarith)
 · exact (hh le_rfl).trans (by linarith)
 have hx: K (ticketK p x) ≤ U:= (GoldT h _ _ (a*z^2) (by positivity) (fun i j=> by simpa only [lateral_zero,Nat.cast_zero, mul_zero,add_zero,List.length_cons,List.length_nil,Nat.zero_add,mul_one,one_pow,loom_cons, show loom [] p=p from rfl] using v.H [i,j] 0 (by simp))).trans ((le_of_eq (show (lateral x:ℝ)^2*(a*z^2)=a*A^2 from by unfold A; ring)).trans (ht 2 (by decide)))
 exact (h.b _ _).trans ((add_le_add (hh (by omega)) hx).trans_eq (by ring))
lemma Goa_total (h:Dignity K)(p:Shape I→ E) (a z:ℝ)(m:ℕ)(b:m≤3) (x:Shape I)(v:Goose h a z p m) (u:z≤1): K ((p-wheelK p m) x) ≤ 12*a*z^m*(1+(lateral x:ℝ))^3:=by
 have ha:=v.a'; have hz:=v.z'; let R:ℝ:=lateral x; have hR:0≤R:= Nat.cast_nonneg _
 by_cases he:z*R≤1; · apply (Goa_cost h p a z m b x v he).trans; change 8*a*z^m*R^m ≤ 12*a*z^m*(1+R)^3; have hg:R^m ≤ (1+R)^3:=(pow_le_pow_left₀ hR (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right hR) b); gcongr; norm_num -- tune
 have hh:1≤z*R:=le_of_lt (not_le.mp he); let Q:=K (p x); have hx: Q ≤ 8*a*(z*R)^3:=by refine (Goose.leap h v x).trans ?_; refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show 1+z*R ≤2*(z*R) from (by linarith)) _) ha).trans_eq ?_; ring -- tune
 apply (h.sub (p x) (wheelK p m x)).trans; refine (add_le_add hx (Goa_far h p a z m b x v hh)).trans ?_; change 8*a* (z*R)^3+3*a*(z*R)^3 ≤ 12*a*z^m*(1+R)^3; -- tune
 have ht : 8*a*(z*R)^3+3*a*(z*R)^3=(11*a)*z^3*R^3:= by ring
 have hg: (11*a)*z^3*R^3 ≤ (12*a)*z^m*(1+R)^3:= by
    have hx:z^3 ≤ z^m:= pow_le_pow_of_le_one hz u b
    gcongr <;> linarith
 exact (le_of_eq ht).trans hg
end
end YM.FlightFlux
end
