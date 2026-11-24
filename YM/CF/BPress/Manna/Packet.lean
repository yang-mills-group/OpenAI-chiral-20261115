import YM.CF.BPress.Manna.Paper
/- full exp of this signed integral, before Power Law final calibrations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Manna
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey Huon
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along Rates Huon.Pilot Mosaic.Pulse
variable {m s N:Side}{B:BandWidth}{A: Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k r r':ℕ} {c q d t v ε e d' α C D ζ δ τ u b C':ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
variable {B0: Born A R X Y}{P: Edition Y}{F: Rented R H X Y.d e k c}{Q: Stamp A R X Y}{W: Recipe (A:=A) T}
local notation "Ξ"=> Visit A R H
variable (l: Passports Y T G h P p3 q d ε t v) (p: Budgeting H W τ u D ζ δ C)
variable {K: Rates}
variable (u0: Budget K u v t τ C ζ D b α C' d c ε q p3 r r' B0 H W k)
namespace Budget
def Pole(P:Weave.Budget)(b:Clip)(J:ChartRatio SU.group)(p:Pledge)(d:ℕ)(C y:ℝ):= ((rootsCount*payC b 2 C)*y+ |Real.log (job_m d J y)|+(portDim d:ℝ)* traceTab (P.low y) P.upper)+ ((p.price+ 1)+Real.log 2)
-- area≤ etc.
include p u0 l
lemma output (C:Calyx P (ΓStage F Q))(A': List A.Index)(b:Orbit (mid m s)→ Phys (mid m s))(S:Pin C A' b (T:=T) (ε:=ε)):
 let f:=H.Z.lantern A A' (formula W H (design F Q C)) b; Real.exp (-(Pole H.P T.funds H.J p3 B.D W.C H.y)*((η).val:ℝ)^4) ≤ ‖f‖:=by
 intro f; let θ:= Credit H W; let w:= wool A R H.y; let a:=anchor B0 P r; have he : 0<paysP (B:=B) R H.y:= pay_f u0.fit.bright u0.fit.reputation; let v:= R.L; have A0:0<w:=pow_pos he _
 have ht: f=_ :=Pin.reflect_s p C l (u0.actual.c.le.trans u0.modes.1) u0.heat A' b S u0.fit.bright he; rw [ht,norm_smul,Real.norm_of_nonneg (mul_nonneg p.income_pos.le A0.le)]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (eventΩ (F:=F) (Q:=Q) l p u0) (mul_nonneg p.income_pos.le A0.le)); -- tune flush
 let u:=Fintype.card (SiteX A R); have hp: u ≤ Fintype.card A.Hcols:= Fintype.card_le_of_injective (fun i=>porch A R i (Classical.arbitrary _)) (fun i j e=>by dsimp only at e; rw [←porch_own A R i (Classical.arbitrary _), e,porch_own A R j (Classical.arbitrary _)])
 let z:ℝ:= (η).val^4; have hw:(u:ℝ)≤ z:=(by unfold z; rw [← Nat.cast_pow]; exact Nat.cast_le.mpr (hp.trans (at_most A))); let P':=Pole H.P T.funds H.J p3 B.D W.C H.y; let L:= Real.log θ+Real.log w; change Real.exp (-P'*z)≤ θ*w*(Real.exp (-(u:ℝ))*Real.exp a.re); conv_rhs=> rw [←Real.exp_log (show 0<θ from p.income_pos),←Real.exp_log A0,←Real.exp_add,←Real.exp_add (-(u:ℝ)),←Real.exp_add]; -- tune grouping
 apply Real.exp_monotone; let s1:ℝ:= Real.log 2; have h':0<s1:= Real.log_pos one_lt_two; have hw': -(z*s1)≤ Real.log w:=by
    let P0:=paysP (B:=B) R H.y; have he: Real.log (1/2)= -s1:=by unfold s1; rw [one_div,Real.log_inv]
    have hy: -(u:ℝ)*s1 ≤ Real.log w:=by unfold w wool; rw [Real.log_pow]; rw [neg_mul,mul_comm (u:ℝ)]; calc
     _ = (u:ℝ)*Real.log (1/2) := by rw [he]; ring
     _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num : (0:ℝ)<1/2) u0.fit.reputation) (by positivity)
    linarith only [hy, mul_le_mul_of_nonneg_right hw h'.le]
 have hu: -(z*p3.price) ≤ a.re :=by have h:= (abs_le.mp ((Complex.abs_re_le_norm _).trans (anchor_cost (B0:=B0) (r:=r) l))).1; rw [show Fintype.card (Site η)= (η).val^4 from (by simp only [Site,Four,Fintype.card_pi_const,Per,ZMod.card,Fintype.card_fin,Axis])] at h; rw [Nat.cast_pow] at h; exact h
 have hz:= (abs_le.mp (pref_content A H.J H.P H.y H.F W.M T.funds T.path T.p T.beta p.y_pos p.jRoot p.summer W.work p.chef p.cost).2).1; unfold θ P' z s1 at *; unfold Credit Pole at *; linarith -- tune `B0.a`
-- mark sup.
omit p u0 l
end Budget
end YM.CF.BPress.Manna
