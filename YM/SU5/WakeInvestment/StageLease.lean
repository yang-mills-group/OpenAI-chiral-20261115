import YM.SU5.WakeInvestment.Landhold
import YM.SU5.WakeInvestment.Satellite
import YM.SU5.WakeInvestment.Escalator
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
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

/-! Arithmetic of this replica intensive strip. Compare room vs doom only in leading fee. -/
open WakeInvestment
open Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
variable (s i k : ℕ) (h : Real.exp 1 ≤ P.x)

abbrev tabμ (x:ℝ) := chip x (-205) -- tolerance
abbrev tollR (x:ℝ) := chip x (-150) -- growth factor (Leaf and δ already multiplying)
abbrev skyline (x:ℝ) := chip x (-120000) -- small-link WA.7
variable {t:ℝ}
local notation "X" s:max => hat P.R.L P.x s
local notation "αp" x:max => Tempest.healthC x
structure castLeases (A:ℝ) : Prop where
 foyer: 0 < hat P.R.L P.x s
 costC : ∀ B:ℕ, (B:ℝ) ≤ sPow P s A →
     2*tollR (hat P.R.L P.x s) *(24/(terrace (hat P.R.L P.x s)).val:ℝ) * (4*((B:ℝ)+addgap (tent Y h)))^4 ≤ tabμ (hat P.R.L P.x s)
 carryFrame : ∀ i k:ℕ, s≤Y.uv k → Papal.coolR Y s i k (2*gateC (hat P.R.L P.x s)) ∧ Papal.freeR Y s i k 0
 frameCoin: 2*tollR (hat P.R.L P.x s)*shoreDust P.J.n (terrace (hat P.R.L P.x s)) ≤ gateC (hat P.R.L P.x s)
 shellL: shieldC (hat P.R.L P.x s)≤ P.J.k
 siren: 4*(terrace (hat P.R.L P.x s)).val*shieldC (hat P.R.L P.x s) ≤ skyline (hat P.R.L P.x s)
 toll_ge: chip (hat P.R.L P.x s) (-198) ≤ tollR (hat P.R.L P.x s)
 wall: 2*tollR (hat P.R.L P.x s) ≤ 4*Tempest.healthC (hat P.R.L P.x s)
 gauss: Regis.trend*tollR (hat P.R.L P.x s)^2 ≤ tabμ (hat P.R.L P.x s)
 outset: 5*tabμ (hat P.R.L P.x s) ≤ chip (hat P.R.L P.x s) (-204) -- 1* error,1*wall/omitted,2*φ-tariff & cloud,1*deriv
local notation "χ" x:max c:max => WakeInvestment.chip x c
private lemma width_rent (A:ℝ)(p:0<A) : ∀ᶠ s in atTop,∀ B:ℕ,(B:ℝ)≤ sPow P s A→
     2*tollR (X s) *(24/(terrace (X s)).val:ℝ) * (4*((B:ℝ)+addgap (tent Y h)))^4 ≤ tabμ (X s):=by
 let u:=addgap (tent Y h); let S(x:ℝ):= BProof.coin x 0 A 0; have hp:Worth.Pays 0 A 0 S:= Pays.whole ..
 let e(x:ℝ):= 48*tollR x* BProof.coin x (-Worth.r_width) 0 0
 have hv:Worth.Pays (-150/400000+-Worth.r_width) 0 0 e:=by simpa only [add_zero] using Pays.times (Pays.scale 48 (Pays.whole (-150/400000) 0 0)) (Pays.whole (-Worth.r_width) 0 0)
 have hs:Worth.Pays 0 A 0 (fun x=> 4*(S x+u)):=Pays.scale 4 (Pays.plus hp (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,p⟩))))
 filter_upwards [(turnover P).eventually (leap (p:=0) (q:=0) (w:= -205/400000) (times hv (pot hs 4)) (Or.inl (by norm_num [Worth.r_width])))] with s l B hB
 apply le_trans _ l; let x:=X s
 have hp:tollR x ≥0:= (chip_pos ..).le; have ht:0≤S x:=(BProof.coin_pos ..).le
 change 2*tollR x*(24/(terrace x).val:ℝ)*(4*(B+ (u:ℝ)))^4 ≤ e x*(4*(S x+u))^4
 have hv:0≤e x:=by unfold e; have hm:0≤ BProof.coin x (-Worth.r_width) 0 0 := (BProof.coin_pos ..).le; positivity
 refine mul_le_mul ?_ ?_ (by positivity) hv; swap; · gcongr
 apply mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (show 0≤(24:ℝ) by norm_num) (show 0<widthC x from BProof.coin_pos ..) (terrace_mm x)) (mul_nonneg (by norm_num) hp) |>.trans_eq; unfold e widthC; rw [div_eq_mul_inv, BProof.coin_inv]; simp only [neg_zero]; ring
private lemma bumper(Q:ℕ) : Worth.Pays (Worth.r_width*4) 0 0 (fun x=> shoreDust Q (terrace x)) := by
 let a:ℝ:= ↑(4*((Q+4)*2+1)^4 * Fintype.card PlaqAxes:ℕ); let b:ℝ:= ↑(4*(Q+Q+1)^4:ℕ); let f(x:ℝ):=((terrace x).val:ℝ)
 have hc(x):shoreDust Q (terrace x)= a*f x^4+b:=by unfold shoreDust a f b; push_cast; ring
 simp_rw [hc]; refine plus (Pays.scale _ ?_) (Worth.Pays.merit (constant b) (Or.inl (by norm_num [Worth.r_width])))
 simpa only [add_zero, zero_add, Nat.cast_ofNat,zero_mul] using pot terrace_size 4
lemma cast_funds (A:ℝ)(p:0<A) : ∀ᶠ s in atTop,castLeases Y s h A:=by
 let Hup:=turnover P
 have hc:= leap (times (Pays.scale 2 (whole (-150/400000) 0 0)) (bumper P.J.n)) (w:=Worth.r_gate) (p:=0) (q:=0) (Or.inl (by norm_num [Worth.r_gate,Worth.r_width])); have hv:Tendsto shieldC atTop (𝓝 0):=BProof.coin_purchases (Or.inl (by norm_num [Worth.r_shield]: Worth.r_shield<0)); let t(x:ℝ):= 4*(terrace x).val*shieldC x
 have hh:= leap (times (Pays.scale 4 terrace_size) (whole Worth.r_shield 0 0)) (w:= -120000/400000) (p:=0) (q:=0) (Or.inl (by norm_num [Worth.r_width,Worth.r_shield]))
 filter_upwards [Hup.eventually_gt_atTop 0,width_rent Y h A p,Hup.eventually hc,Hup.eventually hh,Hup.eventually (hv.eventually (ge_mem_nhds P.J.ht)),Hup.eventually (chip_spend (-198) (-150) 1 1 (by norm_num) zero_lt_one), Hup.eventually (chip_spend (-300) (-205) Regis.trend 1 (by norm_num) zero_lt_one), Hup.eventually (chip_spend (-205) (-204) 5 1 (by norm_num) zero_lt_one), Hup.eventually (BProof.coin_budget (b:=0) (a:= -150/400000) (c:=0) (e:=1) (d:=0) (f:=0) (Or.inl (by norm_num)) 2 4 (by norm_num)), Hup.eventually (Gleam.Tempest.rain_upper P.K.top.clip 2)] with s p L b c t1 v1 v2 v3 y1 y2
 refine ⟨p,L,?_,b,t1,c,?_,y1.le,?_,?_⟩
 · intro i k v; let Q:=RootBook Y i k s; let G:=Papal.prices_plot Y s i k v; have hB:hat P.R.L P.x s/2≤ Q.beta:= G.2.2.2.1.1
   refine ⟨y2 Q.beta hB,?_⟩; have hp:0<Q.beta:= ((half_pos p).trans_le hB); let T:=Q.p.threshold; change 0≤ Q.beta*(P.K.top.clip.linear * T^2/2)/2; have ht:=P.K.top.clip.tail_pos; positivity
 · simpa only [one_mul] using v1.le
 · unfold tollR; rw [chip_pow, show (-150:ℝ)*↑(2:ℕ)= -300 by norm_num]; simpa only [one_mul] using v2.le
 simpa only [one_mul] using v3.le

/-- More inherits its own width curtain eventually. Need i→∞ for each fixed s as here. -/
lemma n_standing (s:ℕ) : ∀ᶠ i in atTop, (terrace (X s)).val ≤ (More (N s i)).val:= by
 let x:=X s; filter_upwards [(Papal.count_grows Y s).eventually_ge_atTop (terrace x).val] with i h; exact h.trans (Nat.le_mul_of_pos_right (side Y i s).val two_pos)
lemma auth2 (f:ℝ)(t:0<f) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k→ authNear Y s i k f (2*tollR (X s)):=by
 let H:=near_flake (q:=P.K.top.clip) f t
 filter_upwards [(turnover P).eventually (BProof.coin_budget (a:= -150/400000) (b:=0) (c:=0) (d:=0) (e:=3/2) (f:=0) (Or.inl (by norm_num)) 2 1 zero_lt_one),(turnover P).eventually H] with s u p i k v
 obtain ⟨h,_,_,hv,_⟩:= Papal.prices_plot Y s i k v; let A:=RootBook Y i k s
 exact le_trans (b:= Tempest.droitC (X s)) (by simpa only [one_mul] using u.le) (p A.p A.beta hv.1 (h ▸ (Y.meter.boot s).1))
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
