import YM.CF.BPress.Census
import YM.CF.BPress.Locale.Cubus
/-! Generic enlargement estimate. Compare root & finger inclusion; connectedness to pay entry-count via PL harmonic. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix Push.AbsoluteSums Ledger
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}(X:Bands s b)(R:Hangar s)
section pricing
variable {Y:Type}[Fintype Y][DecidableEq Y]
-- ticket reaches at least one source index for counts, not buying cost for all path points. arbitrary
variable {I:Type*}
structure FareP (r:I→ Seal Y)(b:I→ℝ)(M:I→Seal (SiteX X R))(f:SiteX X R→Seal Y)(C A L:ℕ):Prop where
 lim i : b i≠0 → R.L.val * (M i).card ≤ A * R.L.val + L* (r i).card
 reach i : b i≠0 →∃ y∈ M i,∃ z∈r i,z∈f y
 fence w : (f w).card ≤ C
 trunk i : b i ≠ 0 → Grove (shape X R) (M i)
-- explicit power using θ & countsV. needs P≤Lc & τ. independent of terms.
def expense (a t:ℝ)(C A:ℕ):= Real.exp (a*A) * (C* (4*(A:ℝ)+1)^4)*harm 4 (t/2) 4
lemma ePos (a:ℝ){t:ℝ}(v:0<t)(C A:ℕ) : 0≤ expense a t C A:=by unfold expense; positivity [nonneg_harm 4 (t/2) 4 (half_pos v) (by norm_num)]
lemma ePL (a:ℝ)(t:ℝ→ℝ)(p:PL (fun i=>(t i)⁻¹))(C:ℝ→ℕ)(u:PL fun i=>(C i:ℝ))(A:ℕ) : PL fun i=> expense a (t i) (C i) A:=by unfold expense; apply ((PL.const _).mul (u.mul (PL.const _))).mul; apply pl_harm; simp_rw [inv_div,div_eq_mul_inv]; apply (PL.const _).mul p; exact PL.const 4
variable {X R}{r:I→Seal Y}{b:I→ℝ}{M:I→ Seal (SiteX X R)}{f:SiteX X R→Seal Y}{C A L:ℕ}
namespace FareP
lemma purse (w:FareP X R r b M f C A L) {a k t:ℝ}(p:Cash r b t k)(ha:0≤a)(hk:0 ≤ k)(ht:0<t)(he:L ≤ R.L.val)(v:a*L≤ t/2*R.L.val): Cash M b a (expense a t C A*k):= by
 let H:= shape X R; let K:= (4*(A:ℝ)+1)^4; let Z:=Real.exp (a*A); have h (x):=p.pos x; have hp:0≤Z:=(Real.exp_pos _).le; have hL:0<R.L.val:= R.L.property
 have F(i)(t:b i≠0): (M i).card ≤ A+(r i).card:=by apply Nat.le_of_mul_le_mul_left _ hL; refine le_trans (w.lim i t) ?_; rw [Nat.mul_add,mul_comm R.L.val A]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ he) (A*_) -- tune Nat.add_le...
 have z(i)(d:b i≠0): Real.exp (a*(M i).card) ≤ Z*Real.exp ((t/2)*(r i).card):=by
   unfold Z; rw [← Real.exp_add]; apply Real.exp_monotone; have h : (R.L.val:ℝ)*(M i).card≤ A*R.L.val+L*(r i).card:=by exact_mod_cast w.lim i d -- tune nat cast
   apply le_of_mul_le_mul_left (a:=(R.L.val:ℝ)) _ (by exact_mod_cast hL); nlinarith only [mul_le_mul_of_nonneg_right v (Nat.cast_nonneg (r i).card (α:=ℝ)),mul_le_mul_of_nonneg_left h ha]
 refine ⟨p.pos,fun i=>?_⟩
 let d(n:ℕ):= Real.exp (-(t/2)*n); let G:= Z * (C*K) * k; let q:= thin_count 4 (t/2) 4 (half_pos ht) (by norm_num); have hG:0≤G:=by unfold G K; positivity
 refine budget_fiberwise (fun x:I=> (r x).card) (fun x=>by unfold Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le (p.pos _); rfl) ?_ (budget_loosen (budget_scale hG q) ?_); swap; · exact Eq.le (by unfold G K Z expense; ring)
 intro n s o; let V:= bay H i (A+n); let W:=V.biUnion f; have hW: W.card ≤ estate (A+n)* C:= by refine card_biUnion_le.trans ((sum_le_sum (fun i _=>w.fence i)).trans ?_); rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (capacity X R i _)
 let g:=fun y:Y=> Ledger.score r b t y; have hv:0 ≤ Z*d n:=mul_nonneg hp (Real.exp_pos _).le; have hx(x)(s':x∈s):Ledger.score M b a i x ≤ Z*d n * ∑ y∈ W,g y x:=by
   have hP(y):0≤g y x:=(p.hits y).1 x; have hx:= sum_nonneg (s:=W) (fun y _=>hP y)
   unfold Ledger.score; split; next h=>
     by_cases e:b x=0; rw [e,mul_zero]; exact mul_nonneg hv hx
     apply le_trans (mul_le_mul_of_nonneg_right (z x e) (p.pos _)); obtain ⟨y,h',l,v',a'⟩:= w.reach x e
     have hy:l∈W:=mem_biUnion.mpr ⟨_,(bay_mem _).mpr (((w.trunk x e).lim i h y h').le.trans (by rw [←o x s']; exact F x e)),a'⟩; apply le_trans _ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun y=>g y x) (fun y _=>hP y) hy) hv); apply Eq.le; unfold g Ledger.score; rw [if_pos v',o x s']; unfold d; have hf:Real.exp (t/2*n)=Real.exp (-(t/2)*n)*Real.exp (t*n):=by rw [← Real.exp_add]; congr 1; ring
     rw [hf]; ring
   next h=> exact mul_nonneg hv hx
 refine (sum_le_sum hx).trans ?_; rw [← mul_sum,sum_comm]; apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>k) (fun i _=> budget_sum (p.hits i) _)) hv); rw [sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hW) hk) hv); unfold estate; push_cast; unfold G; calc
   _ ≤ Z*d n * ((K*((4:ℝ)*n+1)^4*C)*k):=by
      unfold K; rw [←mul_pow]; apply mul_le_mul_of_nonneg_left _ hv; gcongr; nlinarith [Nat.cast_nonneg n (α:=ℝ), Nat.cast_nonneg A (α:=ℝ)]
   _ = _:=by unfold d; ring
end FareP
end pricing
end YM.CF.BPress.Locale
