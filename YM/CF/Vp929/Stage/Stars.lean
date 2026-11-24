import YM.CF.Vp929.Stage.Factory
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false

variable {n m:Side}{p p':BudgetPoint}{x h g L₁ t Q D a b c b':ℝ}
open Pitching Focus
lemma Display.rightH {X:Type*}{c:X→ℝ→Prop}{H:Submodule ℝ (X→ℝ)}(s:Display H c)(u:X){f:ℝ→ℝ}(t:ℝ)(g:∀ a>t,c u (f a))(h:ContinuousAt f t): c u (f t):= by
 obtain ⟨Z,e,v,L⟩:=s.exists_T; have ha:= L u ⟨_,g _ (lt_add_one t)⟩; apply (ha _).2; intro i q; refine ge_of_tendsto (h.continuousWithinAt (s:=Set.Ioi t)) ?_; exact eventually_nhdsWithin_of_forall (fun a v=> (ha _).1 (g _ v) i q)
-- Fee property collects analytic and upper at same output call, no zero norm assumptions incl input offset.
variable (A:Operation n m)(hP:0< t)(hx:0<g)
variable {I:Interest m}{U:Interest n}{j L:ℕ}
local notation "T'"=> Charged p' I j L h
local notation "U'"=> Charged p U j L h
local notation "Xv"=> Pair (Corr m)
local notation "ε"=> (g/1000)
local notation "τ"=> (t/1000)
local notation "ƒ"=> (strip x)
variable (h₀: ∀ (b:ℂ)(F:Pair (Corr m)), enters x b → Both (Charged p' I j L h (3*g)) F → Both (fun F=>Cost p h (g/1000) F) (A.arrays b F)∧ ‖A.Δ b F‖≤D)
variable (h₁:∀ (S:Set ℂ), IsOpen S→ ∀ (b:ℂ→ℂ) (F:ℂ→Pair (Corr m)),(∀ z∈ S, enters x (b z) ∧ Both (Charged p' I j L h (3*g)) (F z)) → DifferentiableOn ℂ b S → HoloCorr S F → HoloCorr S (fun z=>A.arrays (b z) (F z))∧ DifferentiableOn ℂ (fun z=>A.Δ (b z) (F z)) S)
variable (hY:1 ≤ x)(hHz:1 ≤ h)(hT:t≤g) (g₀:strip x ≤ x/1000)
variable {F G:Corr m}(p₁:entersReal x b)(p₂:entersReal x b')(hF:Charged p' I j L h (t/1000) F)(hG:Charged p' I j L h (t/1000) G)(v:0≤a)(e:0≤ c)(r:Cost p' h (t*a) (F-G))(s:|b-b'|≤ Py.Rate.strip x*c)
include A h₀ h₁ hP hx p₁ p₂ hF hG v e r s hY hHz hT g₀
set_option maxHeartbeats 2400000 in
private lemma qualifies (u:ℝ)(hU:a+c < u): Cost p h (g*(u/4)) (A.realArr b F-A.realArr b' G) ∧ |A.posted b F-A.posted b' G|≤100*D*u := by
 let P:=ƒ; have hu:0<u:=lt_of_le_of_lt (add_nonneg v e) hU; have hp:0<P:= strip_pos hY; have hh:=zero_le_one.trans hHz
 have hg:τ≤3*g:= by linarith only [hP,hx,hT]
 let B:=T' (3*g); have ht(α:ℝ)(t:entersReal x α): enters x (α:ℂ):=by obtain ⟨k,l⟩:=t; have hh: |((α:ℂ).im)|=0:=abs_zero; exact ⟨by change _≤α; linarith,by change α≤_; linarith,by rw [hh]; exact mul_nonneg (by norm_num) hp.le⟩
 obtain ⟨pK,pD⟩:= h₀ (b:ℂ) (F,0) (ht _ p₁)  ⟨hF.mono hg,Charged.mono Charged.zero (by positivity)⟩
 obtain ⟨q,qD⟩:= h₀ (b':ℂ) (G,0) (ht _ p₂) ⟨hG.mono hg,Charged.mono Charged.zero (by positivity)⟩
 have hD:0 ≤D:=(norm_nonneg _).trans pD; have hz: |A.posted b F-A.posted b' G|≤ ‖A.Δ (b:ℂ) (F,0)- A.Δ (b':ℂ) (G,0)‖:=by unfold Operation.posted; rw [←Complex.sub_re]; exact Complex.abs_re_le_norm _
 by_cases tU: 1/16 ≤ u
 · refine ⟨ ((Cost.sub pK.1 q.1).mono ?_), hz.trans (((norm_sub_le ..).trans (add_le_add pD qD)).trans ?_)⟩
   · nlinarith
   nlinarith
 let U:= (1:ℝ)/(4*u); let V:= (1:ℝ)/(8*u); have hV:0< V:=by unfold V; positivity
 let Z:= ball (0:ℂ) U; let W:= F-G; let Δ:Charged p' I j L h (t*a) W:={ Charged.sub hF hG hh with toCost:= r }
 let B(z:ℂ):ℂ:= b'+ z*((b:ℂ)-b'); let Φ:= orbital (G,W); let L(z:ℂ):= A.arrays (B z) (Φ z); have hΓ(z:ℂ)(p:z∈Z): enters x (B z)∧Both (T' (3*g)) (Φ z) := by
    have he:= mem_ball_zero_iff.mp p; have hg:‖z‖*u≤1/4:= by apply (mul_le_mul_of_nonneg_right he.le hu.le).trans; unfold U; field_simp; norm_num
    have hu(k:ℝ)(y:ℝ)(q:0≤y)(t:0≤ k)(k':k≤u): ‖z‖*(y*k)≤y/4:=calc
       _ ≤ ‖z‖*(y*u):= by gcongr
       _ = (‖z‖*u)*y:=by ring
       _ ≤ _:= by refine (mul_le_mul_of_nonneg_right hg q).trans_eq ?_; ring
    have hc: ‖B z-b'‖ ≤ P/4:= by unfold B; rw [add_sub_cancel_left, norm_mul, ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left s (norm_nonneg _)).trans (hu _ _ hp.le e (by linarith))
    have hx: ‖z‖*(t*a) ≤ g/4:=by apply (hu _ _ hP.le v (by linarith)).trans; linarith
    constructor
    · have hl:= abs_le.mp ((Complex.abs_re_le_norm _).trans hc); have hd:= (Complex.abs_im_le_norm _).trans hc; simp only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero] at hl hd; obtain ⟨r',r''⟩:=p₂; unfold P at hc hp hl hd; refine ⟨?_,?_,?_⟩ <;> linarith [hl.1,hl.2]
    have ht0:= mul_nonneg hP.le v; have hx0:= (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) ht0).trans hx; have hr:= (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) ht0).trans hx
    exact ⟨(Charged.add hG (Δ.smul z.re hh) hh).mono (by linarith), (Δ.smul z.im hh).mono (by linarith)⟩
 let T₁(z:ℂ):= A.Δ (B z) (Φ z); let R(z:ℂ):=( (L z).1.1,(L z).2.1); let K(z:ℂ):=((L z).1.2,(L z).2.2); obtain ⟨hm,ht⟩:= h₁ Z isOpen_ball _ _ hΓ (by unfold B; fun_prop) (foot _ isOpen_ball); have u' (z:ℂ)(p:z∈Z):= h₀ (B z) (Φ z) (hΓ z p).1 (hΓ z p).2
 have B1:B 1=b:=by simp [B]
 have B0:B 0=b':=by simp [B]
 have F0:Φ 0=(G,0):=by simp [Φ,orbital]
 have F1:Φ 1=(F,0):=by unfold Φ orbital W; simp [show G+(F-G)=F from (by abel)]
 have tU':V+V≤U:=by unfold U V; field_simp; norm_num
 have hu1: (1:ℂ)∈ball 0 V:=mem_ball_zero_iff.mpr (by rw [norm_one]; unfold V; field_simp; push Not at tU; linarith)
 have hu0:(0:ℂ)∈ball 0 V:=mem_ball_self hV
 have he:Both (Cost p h (ε+ε)) (L 1-L 0):=by unfold L; rw [B1,B0,F1,F0]; exact ⟨Cost.sub pK.1 q.1,Cost.sub pK.2 q.2⟩
 have hR: Both (fun x=> IncX Utrue x p h (2*(ε)/V * ‖(1:ℂ)-0‖)) (R 1-R 0):= Portfolio.gradient (ask_Team hHz) (show Py.Rate.Census Z R from hm.1) (fun z e=> ⟨((u' _ e).1.1).inc,((u' _ e).1.2).inc⟩) ⟨⟨_,he.1.inc⟩,⟨_,he.2.inc⟩⟩ hu1 hu0 tU' hV
 have hk:Both (fun x=>Dark Utrue x p h (2*(ε)/V * ‖(1:ℂ)-0‖)) (K 1-K 0):= Portfolio.gradient (darkest_Team hHz) (show Py.Rate.Census Z K from hm.2) (fun z e=> ⟨((u' _ e).1.1).dark,((u' _ e).1.2).dark⟩) ⟨⟨_,he.1.dark⟩,⟨_,he.2.dark⟩⟩ hu1 hu0 tU' hV
 have hu : ‖T₁ 1-T₁ 0‖ ≤ D/V * ‖(1:ℂ)-0‖:= pay_diff ht (fun x p=> (u' _ p).2) hu0 hu1 hV tU'
 have hQ:Cost p h (2*(ε)/V) ((L 1-L 0).1) := by rw [show 2*(ε)/V=2*(ε)/V* ‖(1:ℂ)-0‖ from (by simp)]; exact ⟨hR.1,hk.1⟩
 unfold L at hQ; unfold T₁ at hu;
 rw [B1,F1,B0,F0] at hQ hu
 refine ⟨hQ.mono ?_, hz.trans (hu.trans ?_)⟩ <;> simp only [V,sub_zero,norm_one,mul_one] <;> field_simp <;> nlinarith only [hx,hU,add_nonneg v e,hD, lt_of_le_of_lt (add_nonneg v e) hU]
lemma fractions : Cost p h (g*((a+c)/4)) (A.realArr b F-A.realArr b' G) ∧ |A.posted b F-A.posted b' G|≤100*D*(a+c) := by
 let u:= a+c; let P(y:ℝ)(h:u<y):= qualifies A hP hx h₀ h₁ hY hHz hT g₀ p₁ p₂ hF hG v e r s y h
 refine ⟨⟨Display.rightH (ask_Team hHz) _ u (fun x p=> (P x p).1.inc) (by fun_prop), Display.rightH (darkest_Team hHz) _ u (fun x p=> (P x p).1.dark) (by fun_prop)⟩,ge_of_tendsto (x:=𝓝[>] u) ?_ (eventually_nhdsWithin_of_forall (fun t v=> (P t v).2))⟩
 exact (show ContinuousAt (fun y:ℝ=>100*D*y) u by fun_prop).continuousWithinAt
end YM.CF.Py.Rate
