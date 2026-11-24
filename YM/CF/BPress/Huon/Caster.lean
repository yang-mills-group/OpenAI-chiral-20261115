import YM.CF.BPress.Huon.Sundry
/- prep B-lastQ. bound NOT normalized except exp. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along
variable {m s N:Side}{B:BandWidth}
section Frag
variable {A:Bands (More N) B}{R:Hangar (More N)}(H:Sugar.Crew A)
-- assembler interface $χ$ using only inputs.Scale neutr.A$ g≥q>0,
structure Rates where
 pay : ℝ -- gained log per away-from-bad blk, positive
 bad : ℝ -- positive charge for truly bad blocks
 severe:ℝ -- gain per SEVERE column
 earn : 0≤pay
 paid : 0≤bad
 yellow:0≤ severe
namespace Rates
variable (u:Rates)(b:SlotT A R) (x:Choir A R)
/-- log cost. even outside $Q$ bucket. uses $ice$ in ρ accounting. When reading Pose.S.C cabin on excited core. -/
def budgetP : ℝ:= -(u.pay*(Upper H x b).card)+u.bad*(debris H x b).card-u.severe*(ice x b).card
def admits : Prop:= ∀ i∈ Upper H x b, ∃ j:Fin 5,j≠0∧ (x i).1= House.background R j -- only on $real.L`. force core impose
-- exact.Prom.Pay × measurable.
end Rates
end Frag
section prep
variable {A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k r r':ℕ} {c q d t v ε e d' C D ζ δ τ u b C':ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Pilot
variable {B0: Born A R X Y} {P: Edition Y}{F:Rented R H X Y.d e k c}{Q:Stamp A R X Y}{W: Recipe (A:=A) T}
local notation "Ξ" => Visit A R H
-- meas. Text.W.
variable (l: Passports Y T G h P p3 q d ε t v) (p: Budgeting H W τ u D ζ δ C) (tH:Seer H R X k) (p':ShortP X H R r)(a':Mangrove R H W.M)
-- Rates: derived. no height enters too early.
variable (v0:0<C')(a:0<ε)
def chargeP(R:Hangar (More (mid m s)))(ε:ℝ):=Pilot.costY 0 ε R.L.val B.D X.W.M
-- Pay.C.Frame.
include F p l p'
lemma brilliant (o:SlotT A R)(x: Visit A R H)(hQ:o∈ Camp x.val H) (K:Rates)(v:Banner B0 r' C')(ha:r'≤ mcap X H r)(t:(B.D+2*mcap X H r+1:ℕ)*blur r p3≤ C'/16) (g:Even R.L.val)(sB:K.pay ≤ (C'/16)*(R.L.val:ℝ)^3)(s₁: Pilot.costη R p3 B (mcap X H r)+chargeP (B:=B) (X:=X) R ε ≤ K.bad) (s₂:K.severe≤ Port.reward B.D H.κ H.y T.funds) (a:0<ε) : ‖duskWeight (ε:=ε) B0 P F Q W r o x‖≤ Real.exp (Rates.budgetP H K o x.val):=by
 let d:= (debris H x.val o).card; let V:= Upper H x.val o; let L:= chargeP (B:=B) (X:=X) R ε
 have he(W':Finset (Site (mid m s))):ε⁻¹^W'.card=Real.exp ((-Real.log ε)*W'.card):=by rw [mul_comm (-Real.log ε), ← Real.log_inv, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr a)]
 let w₂:=segYY (X:=X) x o; have hC:= cost_story (B0:=B0) (F:=F) (Q:=Q) l p' x o; let q₁:ℕ:=leis R B X.W.M; have hh:(w₂.card:ℝ)≤ (estate 29 * leis R B X.W.M:ℕ)* (d:ℝ):=by
    rw [←Nat.cast_mul]; refine Nat.cast_le.mpr ?_; apply (card_mask x o (F.dusk.summer.trans halfway)).trans; unfold d leis; exact Eq.le (by ring) -- parentheses
 unfold duskWeight logM; rw [norm_mul, cost_mask x o ε a.le,he, Complex.norm_exp, ←Real.exp_add]; -- tune
 refine Real.exp_monotone (le_trans (b:= L*d + ( (Huon.storm W x o)+ (d:ℝ)*costη R p3 B (mcap X H r)+ ( -(C'/16)*(R.L.val:ℝ)^3 * V.card))) (add_le_add ?_ ?_) ?_); · have p:=neg_le_abs (Real.log ε); apply le_trans (mul_le_mul p (show ((segYY x o (X:=X)).card:ℝ)≤_ from hh) (Nat.cast_nonneg _ (α:=ℝ)) (abs_nonneg _)); unfold L chargeP costY; push_cast; unfold leis; push_cast; exact Eq.le (by ring) -- tune arg order
 · rw [Complex.add_re,Complex.add_re,Complex.ofReal_re]; exact add_le_add (add_le_add le_rfl ((le_abs_self ..).trans ((Complex.abs_re_le_norm _).trans hC))) (Bias_est (F:=F) l p' x o g v ha t hQ) -- tune argument order
 unfold Rates.budgetP; let z:=-Port.reward B.D H.κ H.y T.funds; let k:= (V.card:ℝ); have hv : (-(C'/16)*(R.L.val:ℝ)^3)≤ -K.pay:=by linarith only [sB]
 let mm := (d:ℝ); change _≤ -(K.pay*k)+K.bad*mm- K.severe*_; have h0:= mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) V.card); have hm:= mul_le_mul_of_nonneg_right s₁ (Nat.cast_nonneg (α:=ℝ) d); let n₁:= ice x.val o; have hn:= mul_le_mul_of_nonneg_right s₂ (Nat.cast_nonneg n₁.card (α:=ℝ)); change _ + L ≤ K.bad at s₁; simp only [mm,d,V,k,n₁,L] at *; linarith only [stormC W p x o,h0,hm,hn,v.fit] -- tune
end Pilot
end prep
end YM.CF.BPress.Huon
