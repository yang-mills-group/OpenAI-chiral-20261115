import SatinThinCaster
import YM.SU5.Regis.Screening
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
variable {A B b:ℝ} (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → ShelterCost b Y s i k)
open BProof
local notation "FF" m:max=> (Fintype.card m:ℕ)
abbrev BunchData (P:Preparation)(g:ℕ→ℕ):Prop:=∃ e:ℝ, 0<e ∧ ∀ᶠ s in atTop,(g s:ℝ)≤trailℓ e (hat P.R.L P.x s)
lemma affords_length (P: Preparation)(v u:ℝ)(h:0≤u) (g:ℕ→ℕ)(T:BunchData P g): ∀ᶠ s in atTop, 14* meterC (hat P.R.L P.x s)*(4*((g s:ℝ)+u))^4≤ trailℓ v (hat P.R.L P.x s) ^ 2:=by
 obtain ⟨e,he,f⟩:=T
 have h0: Worth.Pays 0 e 0 (fun x=> 4*(trailℓ e x+u)):=Pays.scale _ (Pays.plus (Pays.whole ..) (Worth.Pays.merit (Pays.constant _) (Or.inr (Or.inl ⟨rfl,he⟩))))
 have hK:= leap (w:=0) (p:=v*2) (q:=0) (Pays.times (Pays.scale 14 (Pays.whole Worth.r_meter 0 0)) (Pays.pot h0 4)) (Or.inl (by norm_num [Worth.r_meter]));
 filter_upwards [f, (turnover P).eventually hK] with s k p; let x:=hat P.R.L P.x s; refine le_trans ?_ (le_trans p ?_)
 · change _ ≤ 14 * meterC x * (4*(trailℓ e x+u))^4; have h:0 ≤ meterC x:= (coin_pos ..).le; gcongr
 apply le_of_eq; unfold trailℓ; rw [coin_pow]; push_cast; norm_num -- norm_num
abbrev pension (o:Tour I (More n))(x:ℝ):Mark n:= Hookah.chalkOp (fun u=> (silk z o (Real.sqrt x) (temp x) u:ℝ))
lemma tour_one (o:Tour I n): o.moves 1 0=o:=by cases o; unfold Tour.moves; simp [affine]
open Cliplet
lemma nestled {s i k:ℕ}(f:Ferry Y s i k)(o:Tour I (More (side Y i s))){S:Finset (Seat (side Y i s))} (p:AtSupport false S (pension z o (xθ s)))(h:∀ i, o.loc i ∈ S)(q:ℂ)(b:S): let x:=bootF z o (ρ s) (temp (xθ s)) q; Vote z o (ρ s) (temp (xθ s)) q (⟨x,S,b.val⟩:Hookah (side Y i s)) ∧ Journey.compass Y i k s x=1+q*Journey.compass Y i k s (pension z o (xθ s)):=by
 let T:= pension z o (xθ s); let U:Mark (side Y i s):=1
 intro f'; have hg:f'=U+q • T:=by funext F; change (1+q*(silk z _ _ _ F.1:ℝ)) • (1:FC _)= 1+q • ((silk z _ _ _ F.1:ℂ) • 1); rw [add_smul, one_smul,mul_smul]
 have hu:= AtSupport.oneM S; refine ⟨⟨hg.symm ▸ hu.addM (p.smulM q), b.property,1,0,q,Or.inl rfl,(by rw [tour_one]),(by rw [tour_one]; exact h)⟩,?_⟩ -- mismatch hg rewrite implicit? lean
 rw [hg]; unfold Journey.compass; rw [mark_add (roofage Y i s).bill hu.env (p.smulM q).env (Marks.can_read _ _ _ _ (Y.each_level i k s f.depth f.enters)),mark_smul,add_div]; rw [markvac,mul_div_assoc]; congr 1; exact div_self (part_here Y i s k f)
include Z
variable (H:Real.exp 1≤ P.x)
include H
private lemma ride (A:ℝ){v:ℝ}(p:2* (Fintype.card I:ℝ)+4+v< A)(u:0≤v){g:ℕ→ℕ}(Q:BunchData P g){η:ℕ→ℂ}(h:∀ s, ‖η s‖=trailℓ (dayDrift v A (Fintype.card I)) (xθ s)) :∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop, let t:= trailℓ (dayDrift v A (Fintype.card I)) (xθ s); ∀(o:Tour I (More (side Y i s))) (S:Finset (Seat (side Y i s))), S.Nonempty → (∀ i, o.loc i∈ S) → AtSupport false S (pension z o (xθ s)) → (∀ i,cows i (Lattice.halo 0 S) (g s)) → ‖1+η s* Journey.compass Y i k s (pension z o (xθ s))‖ ≤ 1+(η s).re* CallBook Y s i k z A o+t*trailℓ (-v) (xθ s)/2:=by -- g implicit
 let δ:= dayDrift v A (Fintype.card I); let t(s:ℕ):= trailℓ δ (xθ s); have hu(s):0<t s:=coin_pos ..
 have hm:0 ≤ (Fintype.card I:ℝ):=Nat.cast_nonneg _; have hs:4<A:=by linarith only [u,p,hm]
 filter_upwards [mote_paid (I:=I) Y z Z H η (fun i=> (h i).le) hs (show δ+A* (Fintype.card I:ℝ)< 1 from (by unfold δ dayDrift; nlinarith only [u,hs,hm])) (fun i=> t i^2) (fun i=> pow_pos (hu i) _) g (affords_length P δ _ (by positivity) _ Q), (turnover P).eventually (candee z (Fintype.card I) P v u p)] with s hv hC; filter_upwards [hv] with i hx; filter_upwards [ferry_later Y s i,hx] with k l hy t' o S uS e f g
 obtain ⟨q,hq⟩:=uS; obtain ⟨hp,b⟩:= nestled Y z l o f e (η s) (⟨q,hq⟩ : S); rw [← b]
 exact (hy _ _ hp rfl g).trans (hC _ (h s) _ (call_bound (k:=k) ..))
lemma earner {v:ℝ}(p:2* (Fintype.card I:ℝ)+4+v< A)(u:0≤v){g:ℕ→ℕ}(Q:BunchData P g):∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop, ∀(o:Tour I (More (side Y i s))) (S:Finset (Seat (side Y i s))), S.Nonempty → (∀ i, o.loc i∈ S) → AtSupport false S (pension z o (xθ s)) → (∀ i,cows i (Lattice.halo 0 S) (g s)) → ‖Journey.compass Y i k s (pension z o (xθ s))- (CallBook Y s i k z A o:ℂ)‖ ≤ trailℓ (-v) (xθ s):=by
 let t(s:ℕ):= trailℓ (dayDrift v A (Fintype.card I)) (xθ s); have hu(i):0<t i:=coin_pos ..
 let a(i):=(t i:ℂ); let c(i):= a i * Complex.I; have hp(i): ‖a i‖=t i:= by unfold a; rw [Complex.norm_real,Real.norm_of_nonneg (hu i).le]
 have hc(i): ‖c i‖=t i:= by unfold c; rw [norm_mul,hp,Complex.norm_I,mul_one]
 filter_upwards [ride Y z Z H A p u Q hp, ride Y z Z H A p u Q (η:= -a) (fun i=> by simp only [Pi.neg_apply,norm_neg,hp]; rfl), ride Y z Z H A p u Q hc, ride Y z Z H A p u Q (η:=-c) (fun i=>by simp only [Pi.neg_apply,norm_neg,hc]; rfl)] with s h1 h2 h3 h4; filter_upwards [h1,h2,h3,h4] with i h1 h2 h3 h4; filter_upwards [h1,h2,h3,h4] with k h1 h2 h3 h4 o S xS c0 pa oσ
 refine (cronus P.K.top.clip (CallBook Y s i k z A o) (t s) (trailℓ (-v) (xθ s)/2) (Journey.compass Y i k s (pension z o (xθ s))) (hu s) ?_ ?_ ?_ ?_).trans_eq (?_)
 · simpa only [t,a,Complex.ofReal_re,mul_div_assoc] using h1 _ _ xS c0 pa oσ
 · simpa only [a,t, sub_eq_add_neg,Pi.neg_apply,neg_mul, Complex.neg_re,Complex.ofReal_re,mul_div_assoc] using h2 _ _ xS c0 pa oσ
 · simpa only [show (c s).re=0 from (by simp [c,a]),zero_mul,add_zero,c,a,t,mul_div_assoc] using h3 o S xS c0 pa oσ
 · simpa only [show (c s).re=0 from (by simp [c,a]), sub_eq_add_neg,Pi.neg_apply,neg_mul, Complex.neg_re,neg_zero,zero_mul,add_zero,c,a,t,mul_div_assoc,←sub_eq_add_neg,sub_zero] using h4 o S xS c0 pa oσ -- tune
 ring
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.earner
