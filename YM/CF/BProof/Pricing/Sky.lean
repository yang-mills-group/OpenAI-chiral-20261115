import YM.CF.BProof.Pricing.Wallet

/- PL edition of Warm settings (hot degree cost, ΔJ purchases). Long pieces NPL
with support Toll on B.base Col. output clearances receipt.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Pricing
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)(c:Clip)(d:ℕ)(M:ℝ→ℕ)(R:ℝ)(h:0<d)(u:PL fun y=> (M y:ℝ))
-- define lifetime horizon settings. no yard dependence.
abbrev focus := Gauss.frameBill d c R M
abbrev budget_inv (y:ℝ) := (Beam.tide c d)⁻¹*focus c d M R y
abbrev steady (y:ℝ) := frameR d c R M y
abbrev time_T := chargeT d c R M
abbrev now (y:ℝ) := lane d c R M y
structure Model (K:Chart G)(P: Pub G)(c:Clip)(d:ℕ)(M:ℝ→ℕ)(R y κ:ℝ) where
 X : Beam c R d (M y) y
 k : X.k=horizon d c R M y
 n : X.n=now c d M R y
 q : X.q=time_T c d M R y
 height : Warm K P c d (M y) (steady c d M R y) y κ (budget_inv c d M R y)
namespace Model
variable {s:Side}(Y:Yard s)(y κ:ℝ)(p:Model K P c Y.short M R y κ)
lemma p_now : p.X.time=focus c Y.short M R y:=by
 change (p.X.time (Y:=Y))=_ -- avoid typeclass
 unfold Beam.time; rw [p.q,p.n, Beam.horizon',p.k]; exact Month.tariff ..
lemma p_hor : p.X.horizon'=steady c Y.short M R y:=by unfold Beam.horizon' steady frameR; rw [p.k]
lemma bought : Book K P Y κ p.X:=by rw [Book,bid,p.p_now,p.p_hor]; exact p.height -- tune
end Model
include u
lemma beam_PL : PL (fun y=> Beam.cost c d (M y)):= by unfold Beam.cost; push_cast; exact ((((((PL.const _).mul u).add (PL.const _)).pow 3).mul (PL.const _)).mul (PL.const _))
include h
lemma steady_p : PL fun y=> (steady c d M R y:ℝ) := (calendar c R d M h u).1
lemma focus_p : PL (fun y=>focus c d M R y):= (calendar c R d M h u).2.2.2.1
lemma inv_p : PL fun y=> budget_inv c d M R y := (PL.const _).mul (focus_p c d M R h u)
lemma time_p : PL (fun y=> (time_T c d M R y)⁻¹):= (calendar c R d M h u).2.2.1
lemma book (κ:ℝ)(p:0<κ)(v: K.C*κ≤1)(q:κ<1/16): ∀ᶠ y:ℝ in atTop, Nonempty (Model K P c d M R y κ):=by
 let Z:= budget_inv c d M R; let F:=frameR d c R M; let Q(y):ℝ:= ((SU.group.lieDim+1:ℕ):ℝ)*Beam.cost c d (F y); let V:=Beam.guard d
 have hZ:= inv_p c d M R h u; have hF:= steady_p c d M R h u; have hQ:PL Q:= (PL.const _).mul (beam_PL c d F hF); let E(y):=coin y (-1/2) 2 0
 have he:NPL E:=coin_n (a:= -1/2) (b:=2) (by norm_num) _; have he':=(PL.muln hQ he).limit
 have ht:NPL thresh:=coin_n (a:= -1/2) (b:=1) (by norm_num) _; have hk:κ<1/16:=q; have hu:0<1/16-κ:=by linarith
 filter_upwards [(calendar c R d M h u).2.2.2.2,(PL.muln (PL.const κ) ht).limit.eventually (ge_mem_nhds K.positive),coin_budget (a:= -3/2) (b:=0) (c:=0) (d:= -1/2) (e:=1) (f:=0) (by norm_num) 1 (1/16-κ) hu,coin_budget (a:= -3/2) (b:=0) (c:=0) (d:= -1/2) (e:=1) (f:=0) (by norm_num) 2 κ p, ht.limit.eventually (ge_mem_nhds P.positive),he'.eventually (ge_mem_nhds P.positive),coin_strongLt (a:=0) (b:=2) (by norm_num) ((PL.const (V:ℝ)).mul (hZ.pow 2))] with y hz H1 H2 H3 H4 H5 H6
 obtain ⟨X,l,w,e⟩:= hz; have hv: 1≤scaleY y:=by rw [coin_scale]; exact Real.one_le_exp (sq_nonneg _)
 refine ⟨⟨X,l,w,e,p,v,H1,?_,H4,?_,?_,?_, one_le_pow₀ (one_le_pow₀ hv),H3.le⟩⟩
 · change 1*xi y< _ *thresh y at H2; unfold scaleD; linarith
 · have he: g y*radius y=E y:=by unfold g hot.radius scaleY E; rw [coin_pow,coin_mul]; ring_nf
   change _≤ P.radius; change Q y*E y ≤ _ at H5; rw [←he] at H5; apply le_trans (le_of_eq ?_) H5; unfold Q F steady; ring
 · change (V:ℝ)*(Z y*scaleY y)^2 ≤_; have he: (V:ℝ)* Z y ^2 < scaleY y^2:= by
     rw [scaleY,coin_pow]; ring_nf; convert lt_of_le_of_lt (le_abs_self ((V:ℝ)*Z y^2)) H6 using 1 <;> ring
   change (V:ℝ)*_≤(scaleY y^2)^2; nlinarith only [mul_le_mul_of_nonneg_right he.le (sq_nonneg (scaleY y))] -- tune
 have hl:0≤Beam.tide c d:=zero_le_one.trans (Bin.max_ge (p:=1) le_rfl (Gauss.floor_p c d h) (Gauss.floor_le c d)); unfold budget_inv focus frameBill Month.boundPL Month.cash Month.snap; positivity

abbrev rC (y):= time_T c d M R y/3
abbrev jPay (y) := Night.fareD 3 (Beam.guard d) (focus c d M R y) (time_T c d M R y)
omit h u
lemma rC_u (y:ℝ) : rC c d M R y≤1:=by
 apply div_le_one_of_le₀ _ (by norm_num); apply le_trans (b:=1); exact inv_le_one_of_one_le₀ (Month.snap_ge ..); norm_num
lemma rC_p (y:ℝ):0<rC c d M R y:=div_pos (Month.rate_pos ..) (by norm_num)
include h u
lemma rC_bill : PL (fun y=> (rC c d M R y)⁻¹):=by unfold rC; simp_rw [_root_.inv_div,div_eq_mul_inv]; exact (PL.const _).mul (time_p c d M R h u)
lemma jPay_bill : PL (jPay c d M R):=by
 unfold jPay Night.fareD; exact (PL.const _).mul ((focus_p c d M R h u).mul (Month.tr_receipt _ _ (rC c d M R) (rC_bill c d M R h u) (rC_p c d M R) (rC_u c d M R)))
abbrev splitD := Bin.stride (fun _=>1) (rC c d M R) 3
abbrev tPay (y:ℝ) := Real.exp (-rC c d M R y/2*splitD c d M R y)* jPay c d M R y
lemma j_tail : PL (fun y=>(splitD c d M R y:ℝ))∧ NPL (tPay c d M R):= Month.fast _ _ (jPay_bill c d M R h u) (rC_bill c d M R h u) (rC_p c d M R)
omit u h
namespace Model
variable {s: Side} (Y:Yard s) (y κ:ℝ) (p:Model K P c Y.short M R y κ)
variable (T:PathData G)(θ:ℝ){q w:ℝ}(H:Room Y (M y))(u:T.Bounds c w R q)(h: θ∈Set.Icc (1/2) 2)
def roster : Night.Design (Gauss.base Y) (Night.logDiff (Beam.ζ T θ p.X)) (rC c Y.short M R y) (jPay c Y.short M R y):= Classical.choice (by
 unfold rC jPay; rw [← p.q, ← p.p_now (Y:=Y)]; exact Beam.options T θ p.X H u h) -- include tune H
end Model
end YM.CF.BProof.Pricing
