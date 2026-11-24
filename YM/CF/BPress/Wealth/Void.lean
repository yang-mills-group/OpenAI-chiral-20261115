import YM.CF.BPress.Wealth.Flip
/-! Linear magcancel over actual channel labels and retention geometry. No region restriction on canonical W here. Need it on all formal variables (including any substitution). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}(v:Signed)(t:Per s)(w:Directions group s)

lemma visits_pair (x y:PlaqAxes)(p:x≠y): ∃ a:Axis,(a=x.val.1∨ a=x.val.2) ∧ a≠ y.val.1 ∧ a≠y.val.2:=by
 by_contra q; have ht(a:Axis)(h:a=x.val.1 ∨ a=x.val.2): a=y.val.1 ∨ a=y.val.2:= Classical.byContradiction fun v=> q ⟨a,h,not_or.mp v⟩; -- tune
 have h:= x.property; have hx:= y.property; apply p; rcases ht _ (Or.inl rfl) with v|v <;> rcases ht _ (Or.inr rfl) with d|d; all_goals first| exact Subtype.ext (Prod.ext v d)| (rw [v,d] at h; order)
-- shift of physical root. sums over spatial sites at fixed shifted time t.
def visit_cost (x y:PlaqAxes) (o:Site s):= ∑ l:Tri s, inner ℝ (psi v x) (orbitP v (o+shiftLeg v t l,y) w)
lemma visit_cancel (x y:PlaqAxes)(o:Site s): ∑ i:Signed,visit_cost i t w x y o=0:=by
 have h (v :Signed) (x:PlaqAxes): visit_cost v t w x x o=0 := by
    unfold visit_cost; rw [←inner_sum]; by_cases e:v.perm x.val.1=0 ∨ v.perm x.val.2=0; simp [no_color v x e]; rw [cup_zero v t x o w (not_or.mp e).1 (not_or.mp e).2,inner_zero_right]
 by_cases g:x=y; subst y; simp_rw [h]; rw [sum_const_zero]
 obtain ⟨k,p,e,f⟩:= visits_pair x y g; let F(i:Signed):=visit_cost i t w x y o; let M:=Signed.mirror k; have hx (v:Signed): F (v*M)= - F v:=by
    unfold F visit_cost; rw [←inner_sum,←inner_sum, mirror_color v _ _ p]; by_cases h:v.perm k=0
    · have hv := no_color v x (by rcases p with p|p; exact Or.inl (by rw [←p,h]); exact Or.inr (by rw [←p,h])); rw [hv, neg_zero]; simp
    rw [mirror_orbit _ _ _ _ o w h e f,inner_neg_left];
 change ∑ i,F i=0; have he:= Equiv.sum_comp (Equiv.mulRight M) F; change ∑ i,F (i*M)=_ at he; simp_rw [hx,sum_neg_distrib] at he; linarith -- tune real

-- use `tally` via term sums. for fixed translated time and native kept plaquette type, cancel over channels. Cross product absolute convergent; alternatively map linear sums and actually swap in finite n dimension a.
variable (M:ℕ)(R:PathData group){d:Clip}{σ C Λ:ℝ}(p:R.Bounds d σ C Λ)
include p
private lemma familyShift (u : RG.Slot)(x:PlaqAxes) : ∑ v:Signed, ∑ l:Tri s, inner ℝ (psi v u.plaq) (T0 M v R (shiftLeg v t l,x) w)=0:=by
 -- for each leg of row expand T0, pull m and reindex.
 let F(v:Signed)(l:Tri s)(n:ℕ):= prime M R x n • orbitP v (door (R.row x n).2 (shiftLeg v t l)) w
 let g(v:Signed):= innerSL ℝ (psi v u.plaq); have h(v:Signed)(l:Tri s):Summable (F v l):= tally_sums M R p x (f:=fun i=> orbitP v (door i (shiftLeg v t l)) w) (safeR.graded (M:=M) (shiftLeg v t l) w v)
 have he (v:Signed)(l:Tri s) : inner ℝ (psi v u.plaq) (T0 M v R (shiftLeg v t l,x) w)=∑' n, g v (F v l n):= (g v).map_tsum (h v l)
 have hm(v:Signed)(l:Tri s): Summable fun n=>g v (F v l n):= (g v).summable (h v l) -- tune name
 have ht(v:Signed): Summable fun n=>∑ l,g v (F v l n):=summable_sum fun l _=>hm v l
 simp_rw [he]; simp_rw [← Summable.tsum_finsetSum (s:=univ) (fun l _=>hm _ l),←Summable.tsum_finsetSum (s:=univ) (fun l _=>ht l)] -- tune given v underscore
 have hx(n:ℕ): (∑ i:Signed,∑ j:Tri s, g i (F i j n))=0:=by
    let a:= (R.row x n).2; have hv:=visit_cancel t w u.plaq a.plaq (wrap s a.offset); unfold g F; simp only [map_smul, smul_eq_mul,←mul_sum]; apply mul_eq_zero.mpr; exact Or.inr hv -- tune using visit w
 simp_rw [hx]; rw [tsum_zero]
private lemma shiftPlus (x:PlaqAxes)(k:ℝ) : ∑ i: Signed,∑ l:Tri s, inner ℝ (k • C0 M i R x) (T0 M i R (shiftLeg i t l,x) w)=0:=by
 simp only [real_inner_smul_left, ←mul_sum]; let f(i:Signed)(n:ℕ):= prime M R x n • psi i (R.row x n).2.plaq; have hf(i): Summable (f i):= tally_sums M R p x (f:=fun a=> psi i a.plaq) (safeR.finiteC (F:=psi i))
 let g(i:Signed)(l:Tri s):=innerSL ℝ (T0 M i R (shiftLeg i t l,x) w); have h(i l): inner ℝ (C0 M i R x) (T0 M i R (shiftLeg i t l,x) w)=∑' n, g i l (f i n):= by rw [real_inner_comm]; exact (g i l).map_tsum (hf i)
 have ht(i:Signed)(l:Tri s):Summable fun n=>g i l (f i n):=(g i l).summable (hf i)
 have hz(i:Signed):Summable fun n=>∑ l:Tri s,g i l (f i n):=summable_sum fun l _=>ht i l
 have he(n:ℕ):(∑ i:Signed,∑ l:Tri s,g i l (f i n))=0:=by
    unfold f; simp only [map_smul, smul_eq_mul,←mul_sum]; simp only [g,innerSL_apply_apply]
    simp_rw [show ∀ (i:Signed) (s : Tri s), inner ℝ (T0 M i R (shiftLeg i t s,x) w) (psi i (R.row x n).2.plaq)=inner ℝ (psi i (R.row x n).2.plaq) _ from fun _ _=>real_inner_comm ..]; rw [familyShift t w M R p, mul_zero]
 simp_rw [h,← Summable.tsum_finsetSum (s:=univ) (fun l _=>ht _ l),←Summable.tsum_finsetSum (s:=univ) (fun l _=>hz l),he]; simp
omit p
private lemma direct_curl (x:PlaqAxes)(g:x.val.1 ≠ 0) : ∑ l:Tri s, orbitP 1 (event t l,x) w = 0:= by
 have hp : x.val.2 ≠ 0:= Fin.ne_zero_of_lt x.property; simpa [shiftLeg,g,hp] using cup_zero 1 t x (0:Site s) w g hp

-- support identity. retained for direct horizontal & channel times without ANY dependence on spatial coordinate
variable {b:BandWidth}(X:Bands s b)
lemma clock_root (x:PlaqAxes)(p:Tri s)(e:x.val.1≠0): (retained X M (.inl (event t p,x))) ↔ (retained X M (.inl (event t 0,x))) := by
    simp_rw [tang_ret _ _ (show ¬lower (event t p,x) from e),tang_ret _ _ (show ¬lower (event t 0,x) from e), ← time_Zone]; simp

include p
lemma magcancel (β y : ℝ) : (∑ i∈univ.filter (retained X M),first R d M β y i w)=0:=by
 rw [sum_filter,Fintype.sum_sum_type]; refine (congrArg₂ (·+·) (?_ : ∑ x:Bonding s,(if retained X M (.inl x) then first R d M β y (.inl x) w else 0)=0) (?_ : ∑ x:Signed × Bonding s,(if retained X M (.inr x) then first R d M β y (.inr x) w else 0)=0)).trans (add_zero _)
 · let F(i:Site s)(x:PlaqAxes):= if retained X M (.inl (i,x)) then first R d M β y (.inl (i,x)) w else 0; change ∑ i:Bonding s, F i.1 i.2=0; rw [Fintype.sum_prod_type_right]; apply sum_eq_zero; intro i _; rw [← Equiv.sum_comp (timeSpace s) (fun x=> F x i), Fintype.sum_prod_type]; apply sum_eq_zero; intro u _; change ∑ x:Tri s,F (event u x) i=0
   by_cases e:i.val.1=0; unfold F; apply sum_eq_zero; intro x _; split; next p=> simp only [Wealth.first,wgt,form,base, Sum.elim_inl,no_color 1 i (Or.inl e), smul_zero,inner_zero_left, mul_zero]
   rfl
   unfold F; simp_rw [clock_root u M X i _ e]; split; simp only [Wealth.first,wgt,base,form,Sum.elim_inl,←mul_sum,←inner_sum,direct_curl u w i e,inner_zero_right,mul_zero]; rw [sum_const_zero]
 let F(i:Signed)(j:PlaqAxes)(x:Site s) := if retained X M (.inr (i,x,j)) then first R d M β y (.inr (i,x,j)) w else 0
 change ∑ x:Signed×Bonding s, F x.1 x.2.2 x.2.1=0; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type_right (f:=fun x:Bonding s=> _)] -- tune
 have hr(i:Signed)(j:PlaqAxes): ∑ x:Site s,F i j x=∑ t:Per s,∑ a:Tri s, F i j (shiftLeg i t a):= by
    rw [←Equiv.sum_comp ((timeSpace s).trans i.actEquiv.toEquiv.symm) (F i j), Fintype.sum_prod_type (α₁:=Per s)]; rfl
 simp_rw [hr]; rw [sum_comm]; apply sum_eq_zero; intro j _; rw [sum_comm]; apply sum_eq_zero; intro t _
 unfold F; simp_rw [letKeep]; simp only [central, Sum.elim_inr,shiftLeg,Signed.act_inv,event_time]; split; next h=>
    unfold Wealth.first wgt form base; simp only [Sum.elim_inr,←mul_sum]; apply mul_eq_zero.mpr; exact Or.inr (shiftPlus t w M R p j (mA y))
 simp
end YM.CF.BPress.Wealth
