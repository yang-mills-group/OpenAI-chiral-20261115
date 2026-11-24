import YM.CF.BProof.Release.Cut

/- PL accounted per y delays and schedule. These ones are entirely prechoice independent
of periods/depths. Proves B-gvolcost also. Use uniform β≤2y on histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Pricing
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)
variable {s:Side}(Y:Yard s)(T:PathData G){c:Clip}(M:ℕ)(θ y:ℝ){R q w:ℝ}(X:Beam c R Y.short M y) (H:Room Y M)(u:T.Bounds c w R q)(h:θ∈Set.Icc (1/2) 2)(r:BudgetPoint)(β:ℝ)

abbrev apt (d:ℕ):= Fin d × TAxis
abbrev turnP (d:ℕ):= apt d × Gauss.Color
-- sigma and det PL price. Z norm in pin. use log estimates for weights.
abbrev σd (d:ℕ)(y:ℝ):= P.base (apt d) (g y)*Day.Z (trunc y) (turnP d)
lemma σd₀ : σd P Y.short y=Sky.σ P Y y:=rfl
lemma scope_pl (d:ℕ) : PL (fun y=>Real.log (σd P d y)):=by
 let Q:=P.Q; let A:= Day.Z (1:ℝ) (turnP d); let R:= Day.total (1/2) (turnP d); let a(y:ℝ):= Day.Z (trunc y) (turnP d); have H:=Q.scale
 have he(y:ℝ): 1≤trunc y:=by unfold trunc hot.radius; rw [coin_scale]; exact one_le_pow₀ (one_le_pow₀ (Real.one_le_exp (sq_nonneg _)))
 have ha:0<A:= Day.filled 1 _ one_pos; have hw(y): A≤a y:= Day.ground _ _ _ (he y); have hV(y): a y ≤ R:= Day.ceiling ..
 have hk : PL (fun y=> Real.log (a y)):=PL.by_le (PL.const (|Real.log A|+|Real.log R|)) <| Eventually.of_forall fun y=> by rw [abs_of_nonneg (by positivity : 0≤|Real.log A|+|Real.log R|)]; have ht:= hw y; have hx:= hV y; rw [abs_le]; constructor<;> linarith [Real.log_le_log ha ht,Real.log_le_log (ha.trans_le ht) hx, abs_nonneg (Real.log A),abs_nonneg (Real.log R),le_abs_self (Real.log R),neg_le_abs (Real.log A)]
 let Z:=Fintype.card (apt d); let N:= Pub.angDim G (apt d); have hv(y): Real.log (σd P d y)= (Z*Real.log Q.scale+N*((-(1/2):ℝ)*Real.log y))+Real.log (a y):=by
    unfold σd; change Real.log _=_; rw [Real.log_mul (P.base_pos (g y) _ (coin_pos ..)).ne' (ha.trans_le (hw y)).ne',Pub.base,Real.log_mul,Real.log_pow,Real.log_pow, g,coin,Real.log_exp]; unfold Z N Q a; ring; all_goals apply pow_ne_zero; first | exact P.actual.scale.ne'| exact (coin_pos ..).ne'
 simp_rw [hv]; exact (((PL.const _).add ((PL.const _).mul ((PL.const _).mul PL.log_y))).add hk) -- parentheses tune

abbrev tech (c:Clip)(R:ℝ)(d M:ℕ):= YM.SectorNext.Vacuum.Panel.amount (Beam.low c R d M) (Beam.tide c d)
lemma tech_pl {M:ℝ→ℕ}(p:PL fun y=> (M y:ℝ))(d:ℕ)(c:Clip)(R:ℝ)(u:0<d) : PL (fun y=> tech c R d (M y)):=by
 unfold tech YM.SectorNext.Vacuum.Panel.amount; let f(y):= Beam.low c R d (M y); let g(y):=Gauss.peak c R d (M y)
 have hf(y):1 ≤ g y:=Gauss.peak_hi ..; have he(y):0<f y:=Bin.pay_pos (a:=Gauss.floor c d) (hf y) (Gauss.floor_p c d u) (Gauss.floor_le c d)
 refine PL.add ?_ (PL.const _); refine PL.by_le (Bin.pay_bill g (Gauss.peak_PL c R d M p) hf) ?_; filter_upwards with y; have hx:= Bin.pay_hi g hf y; have ha:= he y; change f y≤1 at hx; change abs (abs (Real.log (f y)))≤ |(f y)⁻¹|; rw [abs_abs,abs_of_nonpos (Real.log_nonpos ha.le hx),abs_of_nonneg (inv_pos.mpr ha).le,←Real.log_inv]; linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr ha)]
include H u h
lemma det_merit (Z:Finset Y.Col) : |Real.log (Beam.ζ T θ X Z).det| ≤ (Fintype.card Y.Col:ℝ)*(Beam.guard Y.short)*tech c R Y.short M:=by
 obtain ⟨a,b,l⟩:= Beam.measured T θ X H u h Z; have hp:= YM.SectorNext.Vacuum.Panel.determinant a b (Beam.round X).precise; have hx:=Roll.dimension Y; have hh: Fintype.card (Stamp Y)=Fintype.card Y.Col*Beam.guard Y.short:= hx; exact le_trans hp.2.2 (by rw [hh,Nat.cast_mul]; exact le_rfl)
-- K_h upper. direct clip and kept upper. Clip.large step. check. Tile count across times at most s⁴ * coeff
omit H h
abbrev rate (c:Clip)(R:ℝ):= (c.direct*2)+share*((R*2)^2/2)
def coinT : ℕ := Fintype.card PlaqAxes+Fintype.card Signed*Fintype.card PlaqAxes
omit u
lemma rate_0 (c:Clip)(R:ℝ) : 0≤ Pricing.rate c R:=by have := c.quadratic_pos; have := share_pos; unfold Pricing.rate; positivity -- omit u
include u
lemma snow_r (g:0≤β)(e:r.threshold ≤ 1): 0≤ snow Y M y c r T β ∧ snow Y M y c r T β≤β*(Pricing.rate c R*coinT)*(s.val:ℝ)^4:=by
 have hx(k:Tile s): sound y c r T M β k≤β*Pricing.rate c R:=by
    cases k; apply le_trans (direct_cost _ _ β (mag y) _ g e); unfold Pricing.rate; apply mul_le_mul_of_nonneg_left _ g; rw [le_add_iff_nonneg_right]; have := share_pos; positivity
    rename_i i; apply le_trans (higher_cost c r T M β (mag y) u i g); unfold Pricing.rate; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ g; rw [le_add_iff_nonneg_left]; have := c.quadratic_pos; positivity
 have hg:Fintype.card (Tile s)=s.val^4*coinT:=by
    unfold Tile Cell Lam; simp [coinT, Face,Site,Axis,Per,ZMod.card]; ring -- tune
 refine ⟨Finset.sum_nonneg (fun k _=> heavy_pos c r T M β _ _ g),?_⟩; unfold snow; rw [sum_filter]; apply le_trans (b:=∑ _:Tile s,β * Pricing.rate c R) (sum_le_sum (fun i _=>by split; exact hx i; exact mul_nonneg g (Pricing.rate_0 c R))); rw [sum_const,card_univ,hg,nsmul_eq_mul]; apply le_of_eq; push_cast; ring
omit u
lemma width : Fintype.card Y.Col ≤ s.val^4:=by
 unfold Col; rw [Fintype.card_prod,space_card]; have hv:Fintype.card Y.Index≤ s.val:=by
   have hp:Fintype.card Y.Index=Y.q.val:=ZMod.card ..; rw [hp,Y.grid.exact_size]; exact Nat.le_mul_of_pos_right _ Y.grid.count.property
 conv_rhs=> rw [pow_succ']
 exact Nat.mul_le_mul_right _ hv

abbrev skyLog (P:Pub G)(y:ℝ)(c:Clip)(R:ℝ)(d M:ℕ) := 2*y*(Pricing.rate c R*coinT)+|Real.log (σd P d y)|+ Beam.guard d*tech c R d M
include u H h
lemma ceiling (p:β≤2*y)(v:0≤β)(e:r.threshold ≤1) : |outcost P Y T θ y X r β|≤ skyLog P y c R Y.short M*(s.val:ℝ)^4:=by
 let d:=Pricing.rate c R; let D:= Beam.guard Y.short; let C:=(D:ℝ)*tech c R Y.short M; let L:=(s.val:ℝ)^4; let f:= |Real.log (σd P Y.short y)|; have hx:0≤d:= Pricing.rate_0 ..; have hL: (Fintype.card Y.Col:ℝ) ≤ L := by unfold L; exact_mod_cast width Y
 have ht := snow_r Y T M y u r β v e; unfold outcost; refine le_trans (abs_add_le ..) ((add_le_add (abs_add_le ..) (det_merit Y T M θ y X H u h ∅)).trans ?_); rw [abs_mul,abs_neg, abs_of_nonneg ht.1,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _), ← σd₀ P Y y]
 unfold skyLog; rw [add_mul,add_mul,add_assoc,add_assoc]; apply add_le_add
 · -- association mismatch tune
   exact le_trans ht.2 (by gcongr)
 have hC:0≤C:= mul_nonneg (Nat.cast_nonneg _) (YM.SectorNext.Vacuum.Panel.amount_nonneg ..); change _≤_; nlinarith [mul_le_mul_of_nonneg_right hL hC,mul_le_mul_of_nonneg_right hL (abs_nonneg (Real.log (σd P Y.short y)))] -- tune
omit u H h
lemma skyLog_purchase {M:ℝ→ℕ}(p:PL fun y=> (M y:ℝ))(R:ℝ)(c:Clip)(d:ℕ)(hd:0<d): ∀ᶠ y:ℝ in atTop, skyLog P y c R d (M y)≤ y^2:=by
 let L(y:ℝ):= |Real.log (σd P d y)|+Beam.guard d*tech c R d (M y); have hp:PL L:= (scope_pl P d).abs.add ((PL.const _).mul (tech_pl p d c R hd)); let S:=Pricing.rate c R*coinT
 filter_upwards [coin_strongLt (a:=1) (b:=0) (by norm_num) hp, eventually_ge_atTop (2*S+1),eventually_gt_atTop (0:ℝ)] with y hy H h; rw [coinY h] at hy; unfold skyLog; rw [add_assoc]; change 2*y*S+ L y≤_; nlinarith only [(le_abs_self _).trans hy.le,mul_le_mul_of_nonneg_right H h.le]
end YM.CF.BProof.Pricing
