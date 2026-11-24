import SatinThinCrest
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/
variable {z A c:ℝ}




open Regis Head.Garland Head.Etch Lamour.Bridge Celeste Clock Hookah Hookah.Blaze

open Papal -- needed addgap namespace
set_option linter.unusedVariables false
-- probes fare template incumbent
variable (z:PlaqAxes→ℝ) {I:Type}[Fintype I]
local notation "xθ" s:max=>hat P.R.L P.x s
local notation "ρ" s:max=>Real.sqrt (hat P.R.L P.x s)
local notation "N" s:max i:max=> (Journey.side Y i s)
local notation "ℰ" s:max=> meterC (xθ s)
variable {s:ℕ} {A B b:ℝ}
def dayDrift(v A:ℝ)(d:ℕ):ℝ:= -v-3-4*A*(d+1)
open BProof
abbrev Ψx(z:PlaqAxes→ℝ)(A x:ℝ)(d:ℕ):= (padC z SU.group A x).arc^d
abbrev rR(z:PlaqAxes→ℝ)(q:Clip)(A x:ℝ)(d:ℕ):= Regis.trend*sunstroke d q 2 (padC z SU.group A x) ^ 2+(Regis.Head.Garland.costZ z x ^ d)^2+3
lemma candee (d:ℕ)(P:Preparation)(v:ℝ)(u:0≤v)(p: 2*d+4+v <A):
  ∀ᶠ x:ℝ in atTop, let B:= trailℓ (-v) x; let t:= trailℓ (dayDrift v A d) x; let g:= (padC z SU.group A x).arc; ∀ a:ℂ, ‖a‖=t →∀ y:ℝ, |y| ≤ g^d → Real.exp (MoteFee P y d A a x z+ 3*t^2) ≤ 1+a.re*y+t*B/2:=by
 let t:= trailℓ (dayDrift v A d); let K(x:ℝ):= Ψx z A x d; let h(x:ℝ):= bankZ z d gaugeRules A x
 let Z:=2*(A*d+A); let F:=P.K.top.clip; let Y(x:ℝ):=rR z F A x d; let b':= trailℓ (-v)
 have hp':0 ≤ (d:ℝ):= Nat.cast_nonneg _; have hA:0<A:=by linarith
 have hj: A*d ≥0:= by positivity
 have hZ:0<Z:=by unfold Z; linarith only [hA,hj]
 have hz : dayDrift v A d + Z < -v:=by unfold dayDrift Z; linarith only [hZ, hA,hj] -- unfold hZ?
 have ht : Worth.Pays 0 (A*d) 0 K:= by
    have ha : Worth.Pays 0 A 0 (fun x=> (padC z SU.group A x).arc):=by simp_rw [winterK]; exact Pays.scale _ (whole ..)
    exact (by simpa only [zero_mul,K,Ψx] using Pays.pot ha d)
 have hY: Worth.Pays 0 Z 0 Y:=by
    let P'(x:ℝ):= padC z SU.group A x
    have hy: Worth.Pays 0 (A*d+A) 0 (fun x=> Regis.Head.Garland.costZ z x ^ d):= Worth.Pays.merit (Worth.Pays.pot (Regis.Head.Garland.cost_pay z) d) (by rw [zero_mul]; refine Or.inr (Or.inl ⟨rfl,?_⟩); nlinarith only [u,p,hA,hp']) -- need ho A>2
    have hk: Worth.Pays 0 Z 0 (fun x=> sunstroke d F 2 (P' x)^2):= by convert Worth.Pays.pot (sun2 z A d hA (q:=F) (G:=SU.group)) 2 using 1 <;> first|(unfold Z; push_cast; ring)|norm_num <;> ring -- syntax
    have ha: Worth.Pays 0 Z 0 (fun x=> (Regis.Head.Garland.costZ z x ^ d)^2):= by convert Worth.Pays.pot hy 2 using 1 <;> first|(unfold Z; push_cast; ring)|norm_num <;> ring
    unfold Y rR; exact Pays.plus (Pays.plus (Pays.scale _ hk) ha) (Worth.Pays.merit (Pays.constant _) (by right; left; constructor; rfl; exact hZ)) -- tune
 have hb:Worth.Pays 0 (A*d+A) 0 (fun x=> K x+b' x):= Pays.plus (Worth.Pays.merit ht (by right; left; constructor; rfl; linarith)) (Worth.Pays.merit (Pays.whole ..) (by right; left; constructor; rfl; linarith only [hA,u,hj]))
 have hv: Worth.Pays 0 Z 0 (fun x=>(K x+b' x)^2):= by convert Worth.Pays.pot hb 2 using 1 <;> first|(unfold Z; push_cast; ring)|norm_num <;> ring
 have hP(x:ℝ):0≤ K x:= by unfold K Ψx; exact pow_nonneg (padC z SU.group A x).arc_non _
 have h0:0≤ Regis.trend:= by unfold trend; positivity
 have hh(x:ℝ):0≤Y x:=by unfold Y rR; positivity -- local
 filter_upwards [Worth.Pays.compare (1/8) (by norm_num) (around z gaugeRules d hA) (w:=0) (p:=-v) (q:=0) (by right; left; constructor; rfl; linarith), Worth.Pays.compare (1/8) (by norm_num) (Pays.times (Pays.whole 0 (dayDrift v A d) 0) hY) (w:=0) (p:=-v) (q:=0) (by right; left; constructor; simp; exact hz),(Worth.Pays.limit (Pays.times (Pays.whole 0 (dayDrift v A d) 0) hb) (by right; left; constructor; simp; dsimp only [Z] at hz; linarith only [u,hA,hz,hj])).eventually (ge_mem_nhds zero_lt_one), Worth.Pays.compare (1/4) (by norm_num) (Pays.times (Pays.whole 0 (dayDrift v A d) 0) hv) (w:=0) (p:=-v) (q:=0) (by right; left; constructor; simp; exact hz)] with x e1 e2 e3 e4 B S' g a L y H
 have hir:0≤ t x:=(coin_pos ..).le; have hc:0≤ h x:=bank0 ..; have hB:0 ≤ b' x:=(coin_pos ..).le
 let U:= K x; let u:=t x; let P':=a.re*y; let V:=u*(h x+u*Y x); let p:= P'+V
 have hz:=L ▸ Complex.abs_re_le_norm a
 have hp:|a.re| ≤ u:=hz; have hi:h x ≤ b' x /8:=by apply (le_abs_self _).trans; exact e1.trans_eq (by unfold b' trailℓ; ring)
 have hv:u*Y x ≤ b' x/8:= (le_abs_self _).trans (e2.trans_eq (by unfold b' trailℓ; ring))
 have e4:u*(K x+b' x)^2≤ b' x/4:= (le_abs_self _).trans (e4.trans_eq (by unfold b' trailℓ; ring))
 have h1:V ≤ u*b' x/4:= le_trans (mul_le_mul_of_nonneg_left (add_le_add hi hv) hir) (le_of_eq (by ring)); have h2: |p|≤u*(U+b' x):=by
    have he:|V|=V:=abs_of_nonneg (mul_nonneg hir (add_nonneg hc (mul_nonneg hir (hh x)))); apply (abs_add_le ..).trans; change |a.re*y| + |V| ≤ _; rw [he,abs_mul]; refine (add_le_add (mul_le_mul hp H (abs_nonneg _) hir) h1).trans (?_); change u*U+_≤_; nlinarith only [mul_nonneg hir hB]
 have hl:= Real.abs_exp_sub_one_sub_id_le (h2.trans e3); unfold MoteFee CallLate plenitS; rw [L]
 have hz:a.re^2 ≤u^2:= sq_abs a.re ▸ pow_le_pow_left₀ (abs_nonneg _) hp _
 refine le_trans (b:=Real.exp p) (Real.exp_monotone ?_) ?_
 · let Q:= Regis.trend * sunstroke d F 2 (padC z SU.group A x) ^2; have hj:0≤ Q:=by unfold Q; positivity
   change a.re *y+ h x * |a.re| + Q*a.re^2 + u^2*(Regis.Head.Garland.costZ z x ^ d)^2 + 3*u^2 ≤ _
   unfold p V P' Y rR; unfold Q at hj; linarith only [mul_le_mul_of_nonneg_left hp hc,mul_le_mul_of_nonneg_left hz hj] -- tune
 have h3 := (pow_le_pow_left₀ (abs_nonneg _) h2 2); rw [sq_abs] at h3; change _ ≤ 1+P'+u*b' x/2
 have h4:p=P'+V:=rfl; nlinarith only [h3,mul_le_mul_of_nonneg_left e4 hir,(le_abs_self _).trans hl,h1,h4]

end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.candee
