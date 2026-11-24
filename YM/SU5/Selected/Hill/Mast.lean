import YM.SU5.Selected.Hill.Stripe
/-! Point estimate supporting sector integral. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
open Next.SectorChange Luge SectorTools.PhysicalGaussianSwitch
open CF.Graph
variable {G:Gauge}{n:Side}{r:Side}{S:Lots n}{B' B R m:ℕ}
variable {P:BudgetPoint}{W:PathData G}{C:Clip}{σ X D θ a τ e b:ℝ}
variable (Z:ChartRatio G)(L: Next.Rank.Spindle.Rules G)(p:LocalRatio Z) (h:W.Bounds C σ X D)
variable (κ:ℝ)(y:Borders r S B' G)(s:0<b)(F:B+2*R+4≤B')(v:m+2≤ B)(f:2*R+3 ≤ B)(w:7≤ B)
variable (g:4*r.val*P.threshold ≤ e)(j:e ≤ L.c)(U:2*e<Z.radius)(o:0<θ)(u:θ<1)
variable (k:2≤ P.threshold * Real.exp ((m:ℝ) / C.relaxation))(t:∀ x:G.Color, ‖x‖≤ 2*e→ Z.J x ≤ Real.exp τ)
abbrev fee₁ (n:Side)(C:Clip)(L:Next.Rank.Spindle.Rules G)(b X D θ e σ a:ℝ)(R:ℕ):= b * (Fintype.card (Plane n))* vault_fee C L X θ e σ R / 2+ taxY n b a X D
abbrev fare (W:PathData G)(C:Clip)(θ:ℝ)(E:Lots n)(R:ℕ)(x:ListT G n):=(1-θ)*pulse W C E R (tin x)
lemma remit (S:Lots n)(b:ℝ)(Z:Config G n): 0≤ pours W C P b κ S Z:=by unfold pours dish; split <;> positivity
-- roll ticket. use equality rather than tightening gaussian integral
include h s F v f w g j U o u k L t p -- B' casting price
set_option maxHeartbeats 300000 in
lemma buy (x: Scene G (seat_set r S B')): let x':=colorup x; let X':= release 1 x'; let P':= keyUp (tones r S B' 1 y)+icing (distil r S B') x; (mouth Z).indicator (fun x₀=> pay Z x₀ * pours W C P b κ S (tones r S B' (release 1 x₀) y)) x' ≤ (Z.scale*Real.exp τ)^ (Board r S B').card * Real.exp ( (κ-b*daily C P.threshold)*S.card+fee₁ n C L b X D θ e σ P.threshold R + -b*fare W C θ (lesson r S B) R P'/2):=by
 intro x' X' P'; let Y:=tones r S B' X' y; let Y₀:=frost r S B' X' y; have h0:=P.threshold_pos; have hB': 1≤ B':=by omega
 have hp:=p.scale
 by_cases hX:x'∈mouth Z; swap; · rw [Set.indicator_of_notMem hX]; positivity
 rw [Set.indicator_of_mem hX]
 by_cases hz:S=menu Y P.threshold; swap
 · change pay Z x' * (if menu Y P.threshold= S then _ else 0) ≤ _; rw [if_neg (Ne.symm hz),mul_zero]; positivity
 have hY(i):= arrival Z p L X' y x hX _ hB' rfl hz h0.le g j U i -- order
 have hQ: pay Z x' ≤ (Z.scale*Real.exp τ)^ (Board r S B').card:=by
    unfold pay; refine (prod_le_prod (fun i _=> mul_nonneg hp.le ((p.pos _ (hX i (Set.mem_univ i))).le)) (fun i _=> mul_le_mul_of_nonneg_left (t _ (hY i).2) hp.le)).trans_eq ?_; rw [prod_const,card_univ,Fintype.card_coe]
 have hx':0≤pours W C P b κ S Y:= remit κ ..
 apply mul_le_mul hQ _ hx' (by positivity)
 change pours W C P b κ S Y≤ _; unfold pours dish quota; rw [if_pos hz.symm,←hz]; apply Real.exp_monotone
 obtain hh:= abridge Y₀ (show Y=(columbia r n).drape Y₀ from rfl) L h g j v k w f o s.le; simp only [←hz] at hh; rw [tinsel_l x X' y (fun i=>(hY i).1)] at hh
 unfold fare fee₁; linarith only [hh]
end YM.Hill.Box
#print axioms YM.Hill.Box.buy
