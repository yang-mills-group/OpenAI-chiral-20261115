import YM.CF.BProof.Charge.BasicPay

/- E retained factor exponent. Assemble equality on the true I charge, and uniform
c_S suppression. Include all near charges & all columns simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Form Angular Angular.Yard AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(M:ℕ)(Z:Finset Y.Col)
variable (y:ℝ)(c:Clip)(p:BudgetPoint)(T:PathData G)(β:ℝ)(U:Config G s)(W:Y.Branch)(l:Tile s)

def good := univ.filter (fun i=> Stove Y M i∧ Cave Y M i Z)
def bad := univ.filter (fun i=> Stove Y M i ∧ ¬ Cave Y M i Z)
def strong (b:Y.Col):= ∑ i∈ packs Y M Z b,(sound y c p T M β i + L T M c β y i (Y.roll W)-heavy c p T M β U i)
def work := ∑ i∈good Y M Z,Q T M c β i (Y.roll W)
def snow := ∑ i:Tile s with Stove Y M i,sound y c p T M β i
lemma split_cost : big Y c p T M β U = snow Y M y c p T β + work Y M Z c T β W +(∑ i∈good Y M Z,Taylor y (Y.roll W) c p T M U β i) -∑ b∈Z,strong Y M Z y c p T β U W b:=by
 have ht (f:Tile s→ℝ): (∑ i:Tile s with Stove Y M i,f i)=(∑ i∈ good Y M Z,f i)+(∑ i∈bad Y M Z,f i):= by
   unfold good bad; simp_rw [← filter_filter]; exact (sum_filter_add_sum_filter_not (p:=fun i=> Cave Y M i Z) ..).symm -- tune
 have h := Form.total (Y.roll W) Y T M c β y; change (∑ i:Tile s with Stove Y M i,L _ _ _ _ _ i _)=_ at h; rw [ht] at h
 have hh (f:Tile s→ℝ): (∑ i∈ bad Y M Z,f i)=∑ b∈Z,∑ i∈ packs Y M Z b,f i:=by
   rw [show bad Y M Z= Z.biUnion (packs Y M Z) from ?_]; apply Finset.sum_biUnion; exact packs_pair Y M Z; convert split_p Y M Z using 1 <;> (first | rfl | congr!)
 unfold snow big strong work; rw [show (∑ z:Tile s with ¬coldG Y M z,heavy c p T M β U z)=_ from ht _, ht,← hh]; simp_rw [Taylor,sum_sub_distrib,sum_add_distrib]; linear_combination h

variable {κ w C P D:ℝ}{S:Hall s}{F:Y.FaceS} (e:Y.Climate y S U F)(s₀:Y.Evap κ y U W)
variable (A:Chart G)(m:Room Y M)(h:Ink A C y) (v:p.threshold=thresh y)(k:ValidR c p M)(ht:T.Bounds c w P D)(hb:0≤β)

def summer (P y:ℝ):= bard P y ^2/2 + mA y*hull P*((P+1)*(4*thresh y))
include e s₀ A m h v k ht hb
lemma bill (b:Y.Col)(u: b∈Y.severe κ y U)(hp: 2*xi y ≤ κ*thresh y)(hg:thin C y≤mA y):
    let Z:=Y.severe κ y U; strong Y M Z y c p T β U (Y.roof Z W) b ≤
      β*((gearBound Y.short M:ℝ)*((c.direct+share)* summer P y) - plash c Y.short κ*(thresh y)^2):=by
 let Z := Y.severe κ y U; let f := Y.roll (Y.roof Z W); let S₁:=packs Y M Z b; let R:=c.direct+share; have hh:0≤P:=Push.AbsoluteSums.budget_nonneg ht.three
 have hu:0<thresh y:=coin_pos ..; have hv:0<mA y:=coin_pos ..; have hx:= hull_pos hh; have hp':0≤ R:= add_nonneg c.quadratic_pos.le share_pos.le
 have H(k:Tile s): sound y c p T M β k+L T M c β y k f ≤ β*R* summer P y:=by
   apply le_trans (add_le_add (cloud_p A M T c p k β y h ht v hb hg ‹ValidR c p M›) ((le_abs_self _).trans (L_pay M T c k β y ht hb f (Y.roll_short W (s₀.small) hu.le)))) -- tune
   unfold summer R; ring_nf; apply le_rfl
 intro Z; unfold strong; rw [sum_sub_distrib]; apply le_trans (sub_le_sub (sum_le_sum (fun i _=>H i)) (strength Y M U b p T c β hb m u v s₀.enough hp e))
 rw [sum_const,nsmul_eq_mul]; have hz: S₁.card ≤ gearBound Y.short M:= (card_le_card (pack_v ..)).trans (gear_count Y M b)
 apply le_trans (sub_le_sub_right (b:=(gearBound Y.short M:ℝ)*(β*R*summer P y)) (by unfold Z; gcongr; unfold summer; positivity) _) (le_of_eq (by unfold R; ring)) -- tune
omit e s₀ A m h v k ht hb
lemma bill_weather (u:0≤P)(d:ℕ)(κ:ℝ)(k:0<κ)(hv:0<d)(M:ℝ→ℕ)(p:PL fun y=> (M y:ℝ)):∀ᶠ y:ℝ in atTop,
    ((gearBound d (M y):ℝ)*((c.direct+share)*summer P y) ≤ plash c d κ/2*(thresh y)^2):=by
 let q(y:ℝ):=(gearBound d (M y):ℝ); have h : PL q:=by
   unfold q gearBound; push_cast; apply PL.mul (PL.const _); refine PL.pow ?_ 4; exact ((PL.mul (PL.const _) (PL.add (PL.const _) ((PL.const _).mul p))).add (PL.const _)) -- tune
 let r(y:ℝ) := coin y 0 (-1/4) 0
 have he : NPL r:= coin_n (a:=0) (b:=-1/4) (by norm_num) 0; let F:=(P+1)*(fixed₀+1); let D:=hull P*(P+1)*4
 have hx(y:ℝ): summer P y=(F^2/2*r y*r y+D*r y)*thresh y^2:=by
   let t:=thresh y; let m:=mA y; have hk:m=r y*t:=by unfold m r t; rw [coin_mul]; unfold mA; ring_nf
   unfold summer bard; change ((P+1)*((fixed₀+1)*m))^2/2+m*hull P*((P+1)*(4*t))=_; rw [hk]; unfold F D t; ring
 have ht:0<plash c d κ/2:=half_pos (plash_pos c d hv k)
 filter_upwards [((h.mul (PL.const (c.direct+share))).muln (f:=fun y=>q y*(c.direct+share)) ((((PL.const (F^2/2)).muln he).mulp he.weak).add ((PL.const D).muln he))).limit.eventually (ge_mem_nhds ht)] with y hy
 rw [hx]; apply le_trans (Eq.le (by ring : _= q y*(c.direct+share)*(F^2/2*r y*r y+D*r y)*thresh y^2)); exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)
end YM.CF.BProof.Charge
