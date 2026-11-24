import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Nord.Seat
import YM.SU5.Selected.Hill.Crete
import YM.Work.E09.Scales
set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
open Chene.Perks
namespace LocalLimit
open Preparation
variable {Λ:Preparation} {Q:(s:Side)→ Scree.Loom s→Prop}(Y:Course Λ Q)
local notation "G₅"=>SU.group
include Y
private lemma side_star (G:Side)(p:2≤G.val) (x b:ℝ)(h:Tendsto (fun i:ℕ=> x+i*b) atTop atTop)(g:ℕ→ℕ→ Side)(u:∀ i v:ℕ, (g i (v+1)).val=(g i v).val*G.val): ∀ᶠ i:ℕ in atTop,∀ v:ℕ, (Hill.Post.side (x+i*b)).val ≤ (g v i).val:=by
 have hh (i v:ℕ): 1+i ≤ (g v i).val:=by
    induction i with
    | zero=> exact (g v _).property
    | succ i ih=> rw [u]; apply (Nat.mul_le_mul ih p).trans'; omega
 let f(t:ℕ):=(x+t*b); let K:=|x|+|b|+1; have h₀:0<K:=by unfold K; positivity
 let V(j:ℝ):= radiusB j; have h':∀ᶠ j:ℝ in atTop, (V j:ℝ)^3 ≤ (1/(8*K))*j := by
    have ht:= (Work.E09.radiusB_small 1 zero_lt_one 3).bound (c:=1/(8*K)) (by positivity)
    filter_upwards [ht,eventually_gt_atTop (0:ℝ)] with j u v; simpa [Real.rpow_one, abs_of_nonneg v.le, V] using u -- norm simp
 filter_upwards [h.eventually h', (Work.E01.radiusB_tendsto.comp h).eventually_ge_atTop 1] with i H hb v
 let N:=(V (f i):ℝ); change N^3 ≤_ at H
 have hc:1≤N:= Nat.one_le_cast.mpr hb
 have ht:(Hill.Post.side (f i)).val ≤ 1+i:=by
    have h₁:N+1 ≤2*N:=by linarith only [hc]
    have hx:f i ≤ K*(1+i):=by unfold f K; nlinarith only [abs_nonneg x, abs_nonneg b,Nat.cast_nonneg (α:=ℝ) i,le_abs_self x,mul_le_mul_of_nonneg_left (le_abs_self b) (Nat.cast_nonneg (α:=ℝ) i),mul_nonneg (abs_nonneg x) (Nat.cast_nonneg (α:=ℝ) i)]
    apply (Nat.cast_le (α:=ℝ)).1; rw [Hill.Post.stance_, Nat.cast_add,Nat.cast_one]; unfold CF.BPress.lscale; rw [add_comm (1:ℝ) N] -- ambiguous motive
    refine (pow_le_pow_left₀ (by linarith) h₁ 3).trans ?_
    have hpK: N^3*(8*K) ≤ (x+i*b):=by rw [←le_div_iff₀ (by positivity : (0:ℝ)<8*K)]; exact H.trans_eq (by ring)
    refine le_of_mul_le_mul_right ?_ h₀; unfold f at hx; linarith only [hpK,hx] -- maybe ring NF
 exact ht.trans (hh i v)
theorem vista : ∀ᶠ s in atTop,∀ v:ℕ, (Hill.Post.side (hat Λ.R.L Λ.x s)).val ≤ (More (age Y v s)).val:= side_star Y Λ.R.L (by have h:=Λ.V.tallX; omega) _ _ (turnover Λ) _ (fun i v => kint ..) -- hint types infer via lambda? test
abbrev wingBill (i k s:ℕ) := schedule Λ.L (More (age Y i s)) (RefH (Λ:=Λ) (Y.uv k) s) (β_time Y i k s)
lemma terrainG {s i k:ℕ}(p:s≤Y.uv k) : let W:=RootBook Y i k s; let d:=Y.uv k-s;
 W.p.threshold=temp (hat Λ.R.L Λ.x s)∧ W.path= Λ.V.L.path d ∧ W.funds=Λ.K.top.clip ∧ matchedX (hat Λ.R.L Λ.x s) W.beta:=by
 intro W d; let H:= (Y.voyage i).X (Y.uv k); have hx:= H.pull.owns s p; exact ⟨(congrArg BudgetPoint.threshold hx.width).symm.trans (Y.meter.boot s).1,hx.path.symm,hx.fund.symm,H.pull.sift s p⟩
theorem enlist (ε:ℝ)(a:0<ε)(K:ℝ→ℝ)(h:BPress.PL K) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤ Y.uv k→
 let W:= RootBook Y i k s; let N:= More (age Y i s);∀ κ:ℝ,κ ≤ K (hat Λ.R.L Λ.x s) → (∫ U:Config G₅ N,Real.exp (- W.path.inChannels W.funds W.p W.beta U+ κ* Pannier.flakes W.p.threshold U)∂prior G₅ N) ≤ Real.exp (wingBill Y i k s+ε*sites (age Y i s)):=by
 filter_upwards [(turnover Λ).eventually (Hill.Post.gel (G:=G₅) (C:=Λ.K.top.clip) (σ:=Λ.K.top.width) (X:=Λ.K.top.paths) (D:=Λ.V.W.bar) Λ.L Λ.chart Λ.K.C _ ε Λ.V.W.reserve a (Λ.V.L.mood 0).width K h),vista Y] with s p ht i k t; intro W N c hc
 let d:= Y.uv k-s; let H:=RefH (Λ:=Λ) (Y.uv k) s; have hv:= terrainG Y (i:=i) t; have h':Floor H W.funds N Λ.V.W.parcel Λ.K.C:= hv.2.2.1.symm ▸ (Λ.V.L.roof d).2.1 N
 have he:1<N.val:=(by change 1<(age Y i s).val*2; have h:0<(age Y i s).val:=(age Y i s).property; omega)
 have hp:=p N he (ht i) W.beta hv.2.2.2 H (Λ.V.L.path d) W.p ((Λ.V.L.roof d).2.1 N) (Λ.V.L.tied d) (Λ.V.L.mood d) hv.1 c hc
 have hW:W.path=Λ.V.L.path d:=hv.2.1; have hw:W.funds=Λ.K.top.clip:=hv.2.2.1; rw [hW,hw,←volumesBB]; exact hp -- defeq budget Pannier.flake tr eq? 
-- absolute-price general complex integrals as requested in step
abbrev permit_upper (N:Side)(R: GramM N)(κ U:ℝ) := ∀ (F:Orbit N→ℂ)(m:ℝ), Integrable F (city N)→ (∀ x,‖F x‖≤ Real.exp ( -(R.path.inChannels R.funds R.p R.beta x.1) + κ*Pannier.flakes R.p.threshold x.1+m)) → (∫ x, ‖F x‖ ∂city N) ≤ Real.exp (U+m)
theorem ultraviolet_upper (ε:ℝ)(a:0<ε)(K:ℝ→ℝ) (h:BPress.PL K) :∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k→∀ κ:ℝ, κ ≤ K (hat Λ.R.L Λ.x s)→ permit_upper (age Y i s) (RootBook Y i k s) κ (wingBill Y i k s+ε*sites (age Y i s)):=by
 filter_upwards [enlist Y ε a K h] with s p i k t κ hF F m g u; let N:= age Y i s; let V:=More N; let W:=RootBook Y i k s; obtain ⟨hw,hZ,hx,hb⟩:=terrainG Y (i:=i) t; let f(U:Config G₅ V):=Real.exp ( - W.path.inChannels W.funds W.p W.beta U + κ* Pannier.flakes W.p.threshold U); let μ:= prior G₅ V; have ht: RG.Envelope f:=by
    apply Hill.Box.service_env W.path W.funds W.p W.beta κ (σ:=Λ.K.top.width) (E:=Λ.K.top.paths) (D:=Λ.V.W.bar); change W.funds=Λ.K.top.clip at hx; change W.path=Λ.V.L.path _ at hZ; rw [hZ,hx]; exact Λ.V.L.mood _
 have H: MeasurePreserving Prod.fst (city N) μ := measurePreserving_fst ..
 have he: Integrable (f ∘ Prod.fst) (city N):=H.integrable_comp_of_integrable (ht.integrable μ)
 apply (integral_mono g.norm (he.mul_const (Real.exp m)) _).trans; swap; · intro y; specialize u y; rw [Real.exp_add _ m] at u; exact u
 simp only [Function.comp_apply]; rw [integral_mul_const, CF.Window.usesPrior f (ht.integrable μ),Real.exp_add _ m]; exact mul_le_mul_of_nonneg_right (p i k t κ hF) (Real.exp_pos m).le
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.ultraviolet_upper
#print axioms YM.CF.Py.Rate.LocalLimit.enlist
