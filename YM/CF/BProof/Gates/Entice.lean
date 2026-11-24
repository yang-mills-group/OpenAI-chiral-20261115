import YM.CF.BProof.Gates.Store

/- lifetime Before x. further choices can augment block size arbitrarily at any PL.
Given prescribed sizes through histories, choose required divisibility. Do account use at final. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}
namespace Stage
variable (S:Gates.Stage c w R v) (L:Side) (a:ℕ)(y:ℝ)(D:ℝ→ℕ)
abbrev focus (d:ℕ)(y:ℝ) := pace c (Charge.reach S.ms) w R d y
abbrev M := Charge.reach S.ms
abbrev bound (d:ℕ) := least c S.M R d S.F.size S.scene.size (Stage.focus S d y) y 4
lemma focus_h (d:ℕ) : 0<S.focus d y:= pace_p c S.M w R d y S.W
lemma focus_f (d:ℕ)(h:0<d) : PL fun y=>(S.focus d y)⁻¹:= pl_pace c w R d S.ms S.cost S.W h
lemma bound_p (d:ℕ)(h:0<d) : PL fun y=>(S.bound y d:ℝ):= least_pl c S.M R d S.F (Charge.reach_PL S.ms S.cost) h S.scene.size _ 4 (one_pos.trans_le S.scene.target) (S.focus_f d h) (by norm_num) (fun y=> S.focus_h y d) -- order
lemma wallet_p (d:ℕ)(h:0<d) (p:PL fun y=> (D y:ℝ)) : NPL (fun y=> wallet y (D y) S.P S.M c R w v S.height d (S.focus d y) 4):= fiscal _ _ (Charge.reach_PL _ S.cost) p c R w v _ _ d h _ _ (focus_f S d h) (fun y=>focus_h S y d) (fun y=> pace_u ..) S.uniform -- tune
variable {s':Side}
-- receipts independent of actual y geometry. `Weed` packages all pre-purchased field profile budgets/prices.
structure Dull (d:ℕ)(t:ℕ)(y:ℝ) where
 threshY : 2≤y
 smallT : thresh y≤1
 smallXi : xi y≤1
 permit (p:BudgetPoint) (u:p.threshold=thresh y) : ValidR c p (S.M y)
 ink : Ink S.K S.height y
 thin : thin S.height y≤ mA y
 frame (s:Side)(U:Hall s)(u:U.X=S.F)(v:U.K=S.K)(w:Face.Sized S.scene.size U.g y U.k)(hk:S.F.k₀≤U.k)(a:Per s)(X:Config G s)(i:Eyes s) : lifts a t y U X i→
      let r:= Face.blendR S.F S.K U.g; let m:= S.scene.costM*mA y;(∀ b, Face.Firm U.K (outlook a t U X i b) r m) ∧ r≤U.K.size∧ max (qoriz (r:=r) (m:=m) U) (qnorm (r:=r) t U)+4*xi y ≤ thresh y/2
 home (i:TAxis) : group.chord (Mag.comm y (Mag.f₁ i) (Mag.f₂ i)) + 4*xi y ≤ S.scene.charge*mA y ∧ S.scene.charge*mA y ≤ thresh y/2
 view (s:Side) (U:Face.Sheet s) (p:Space s) : (∀ i,cd G (Mag.comm y (Mag.f₁ i) (Mag.f₂ i)) (Face.read U p i)≤4*wc y) → ∀ i, Face.Mood S.K y U p (Face.orient S.K y U p i) ∧ cd G (Face.orient S.K y U p i) (Mag.center i) ≤ S.scene.C*Face.fine y
 lead (u v A : SU.group.El) (i j:Fin 5)(n:TAxis) : cd G u (Mag.center i) ≤ S.scene.C*Face.fine y→ cd G v (Mag.center j)≤ S.scene.C*Face.fine y→cd G (Mag.bg y n) A≤wc y→ (Face.Follow y u v A ↔ i=j)
 ease : Ease S.K c d S.M R S.κ y
 seen : Seen S.K y
 cost (s U) : (Face.labelSet S.K (s:=s) y U).card≤5
 p : Pricing.Model S.K S.P c d S.M R y S.κ
 stamp : Pricing.StampC S.P c d S.M R S.κ y
 cost_out : Pricing.skyLog S.P y c R d (S.M y)≤y^2

lemma seen_before : ∀ᶠ y in atTop, Seen S.K y:=by
 obtain ⟨C,hc,H⟩:= Mag.orbit_unique; filter_upwards [(coin_purchases (a:=0) (b:=-1/8) (c:=0) (by norm_num)).eventually (ge_mem_nhds hc)] with y hy; intro s U p u h; exact H u (Mag.lead _) _ (h.2.2.trans hy) h.2.1 (Mag.lead_spec.2 _)
lemma geometry (u:PL fun y=> (D y:ℝ)): ∀ᶠ y in atTop,
    1 < DP L a y/32 ∧ D y ≤ DP L a y/32 ∧ 5*S.M y+2 < 2*(DP L a y/32) ∧ 4*(5*S.M y+3)+4 ≤ DP L a y ∧ 2≤S.M y:=by
 have hp:PL fun y=>((32*D y:ℕ):ℝ) :=by push_cast; exact (PL.const 32).mul u -- tune
 filter_upwards [(lengths L a).eventually_ge_atTop 100, pl_D L a (fun y=>32*D y) hp,(Charge.reach_hi S.ms S.cost).eventually_ge_atTop 2, pl_D L a (fun y=>320*S.M y) (by push_cast; exact (PL.const _).mul (Charge.reach_PL S.ms S.cost))] with y hy hd hx hk
 change 2≤S.M y at hx; change 320*S.M y<_ at hk; change 32*D y<_ at hd; omega
lemma book : ∀ᶠ y:ℝ in atTop, Nonempty (Dull S (gap L a) (DP L a y) y):=by
 let d:=gap L a; let A:=S.P; have hc:0<d:= Gates.GP L a; let X:= S.M; have hz:PL fun y=>(X y:ℝ):= Charge.reach_PL S.ms S.cost
 let V:= Face.healthy_link S.K S.scene.C 1 S.scene.true_p one_pos
 filter_upwards [eventually_ge_atTop (2:ℝ),(coin_purchases (a:= -1/2) (b:=1) (c:=0) (by norm_num)).eventually (ge_mem_nhds one_pos),(coin_purchases (a:= -3/2) (b:=0) (c:=0) (by norm_num)).eventually (ge_mem_nhds one_pos),S.license,S.ink,coin_budget (a:=-3/4) (b:=11/8) (c:=0) (d:=-1/2) (e:=3/4) (f:=0) (by norm_num) S.height 1 one_pos,S.scene.firm,(scale_domain L a),S.scene.home,S.scene.view,V,Pricing.ease S.K c d X R S.κ hc hz S.κ_pos,seen_before S, Face.fare S.K,Pricing.book S.K A c d X R hc hz S.κ S.κ_pos S.tiny S.margin,Pricing.asks A c d X R S.κ hc hz S.T S.κ_pos, Pricing.skyLog_purchase A hz R c d hc] with y h1 h2 h3 h4 h5 h6 h7 h8 h9 H h10 h11 h12 h13 h14 h15 h16
 obtain ⟨p⟩:= h14; refine ⟨h1,h2,h3,h4,h5,?_,fun s U u v w k a X i=> h7 U a _ v u w k h8.2.2.2 X i,h9,H,?_,h11,h12,h13,p,h15,h16⟩
 · unfold thin; rw [mul_assoc,coin_mul]; ring_nf at h6 ⊢; exact h6.le -- tune
 intro u v A i j n ht h hh; exact h10 _ _ _ _ _ n ht h (by simpa using hh) -- tune h7
end Stage
end YM.CF.BProof.Gates
