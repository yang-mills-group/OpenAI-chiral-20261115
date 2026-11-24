import YM.CF.BProof.Push.Exact
import YM.CF.Reed.Azim
import YM.CF.BProof.Stage.Watch
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau.PushA
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Iva Lilt Salt Palot Floral Sour Haro Tap Sour.BondL Mew
open scoped YM.CF.Mew
structure Crowd (P:BudgetPoint)(h γ Z H R κ:ℝ) : Prop where
 zK : 1 ≤ κ
 zH : 1 ≤ h
 zA : 0 < γ
 zC : degreePrice P.B γ wΨ<1
 zW : 0 < R
 zB : degreePrice P.B R 1 <1
 et : H + rateΓ P γ wΨ ≤ 1
 hpS : κ*Z + Real.exp 1*(rateΓ P γ wΨ+H) ≤ R
abbrev lightP (K:Cusp n): Pax n:=fun i=>K i ∅
abbrev kδ (P:BudgetPoint):=P.supportExponent+1+1
abbrev burn(P:BudgetPoint)(K V:Cusp n):=budgetR (roomV P (lightP K) K V)
abbrev spell (K:Cusp n)(i:Aura n)(D:Support (More n))(P:BudgetPoint): Prop:= Firm P i.val D (K i D)
abbrev bolt (P:BudgetPoint)(K:Cusp n):Prop:=∀ (i:Aura n) D, D.Nonempty→D⊆i.val→spell K i D P
abbrev billStar (P:BudgetPoint)(w:Aura n→ℝ)(γ:ℝ):= Trees.Ready Palot.stern P.B w (kδ P) γ wΨ (degreePrice P.B γ wΨ)
structure Wheel (P:BudgetPoint)(h γ Z H :ℝ)(K V:Cusp n): Prop where
 e:Binder P h (kδ P+wΨ) (lightP K) γ
 q:Flaws P h (kδ P+wΨ) K Z
 t:Heats P h (kδ P) V H
 ok:bolt P K
variable {γ Q Zc R κ Z:ℝ} -- Z shadows Support
namespace Wheel
variable {K V:Cusp n}(t:Wheel P h γ Z Q K V) (p:Crowd P h γ Z Q R κ)
include p t
lemma okay: ∃ w:Aura n→ℝ,billStar P w γ ∧∀ i:Aura n, Medal P i.val ∅ (lightP K i) h (w i):=by
 obtain ⟨w,b,v⟩:= beauty.mp t.e; refine ⟨w, ?_,b⟩; exact ready_T (P:=P) p.zA (by norm_num [wΨ]) p.zC (fun i=> (b i).wage (zero_le_one.trans p.zH)) v
lemma dark{Qm:Sweep n→ Prop}(u:∀ s,Qm s→∀ U:Orbit n,Injective (priorP U.2) → Zeal s U (suit_Y s) K∧ Zeal s U (suit_Y s) V ∧∀ i:Aura n,K (moldA s i) ∅ (yellA s U)=suit_Y s (K i ∅ U)): Dark Qm (burn P K V) P h (Cog_P P R κ):=by
 let v:= zero_le_one.trans p.zH; obtain ⟨w,g,T⟩:= okay t p; obtain ⟨A,u',t'⟩:= Heats.iff_anuk.mp t.t; obtain ⟨Y,v',h'⟩:=Flaws.give.mp (Flaws.wide (t:=kδ P) t.q (by unfold wΨ; linarith) v)
 have hC:ArmsK P K Y h:=⟨fun i D p t=>v' i D (Flaws.full_mem.mpr ⟨p,t⟩),t.ok⟩; have he:0 ≤ P.supportExponent+1:=(add_pos P.exponent_pos zero_lt_one).le
 refine dark_F hC u'.2 u'.1 g he zero_lt_one T zero_lt_one p.zH p.zK ?_ t' h' le_rfl p.zB p.zW p.hpS (fun s V T q i p=> ?_)
 · intro i; obtain ⟨j,k⟩:= i.property; apply le_trans (b:= Q+rateΓ P γ wΨ) _ p.et; apply add_le_add_left; apply le_trans _ (t' j); exact (le_mul_of_one_le_right (u'.1 i) (Real.one_le_exp (mul_nonneg (add_nonneg he zero_le_one) (by exact Nat.cast_nonneg _)))).trans (single_le_sum (s:=Finset.univ.filter (fun i:Aura n=>j∈i.val)) (f:=fun i=>A i * Trees.currency P.B (P.supportExponent+1+1) i.val) (fun i _=>mul_nonneg (u'.1 i) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,k⟩))
 rw [show FrameR s T=suit_Y s from AlgHom.ext fun x=> tama s _ p _]; exact u s q V i
lemma press : Pressed P (burn P K V) h (Cog_P P R κ):= t.dark p fun _ x=> x.elim
end Wheel
-- complex affine lines include arbitrary tags, do not reimpose Sweeps
variable {L:ℝ}
private lemma Fee_ana{K V:ℂ→ Cusp n}(p:Crowd P h γ Z Q R κ)(hv:1<L)(t:∀ z∈disk L, Wheel P h γ Z Q (K z) (V z))(he:∀ (i:Aura n) (u:Orbit n),Hol (disk L) (fun z=>K z i ∅ u))(i:Aura n)(u:Orbit n): Hol (disk L) fun z=> FeeD P (lightP (K z)) i u:=by
 let x:=lightP ∘ K; let A:=degreePrice P.B γ wΨ
 have hh(z:ℂ):∃ w:Aura n→ℝ,z∈disk L→billStar P w γ ∧∀ i,Medal P i.val ∅ (lightP (K z) i) h (w i):=by by_cases g:z∈disk L; obtain ⟨a,b⟩:=(t z g).okay p; exact ⟨a,fun _=>b⟩; exact ⟨0,fun v=>(g v).elim⟩
 choose w e using hh; have hx(z)(v:z∈disk L):billStar P (w z) γ:=(e z v).1; refine Rive.lore_pit x P p.zH he w (show 0 ≤ kδ P from add_nonneg (add_nonneg P.exponent_pos.le zero_le_one) zero_le_one) hx (fun z v=>(e z v).2) (ready_pos _ _ (hx 1 (d1 hv))|>.le) p.zC isOpen_ball i u
private lemma glow_ana{K V:ℂ→ Cusp n}(p:Crowd P h γ Z Q R κ)(hv:1<L)(t:∀ z∈disk L, Wheel P h γ Z Q (K z) (V z))(he:∀ i:Aura n,∀ u:Orbit n,∀ D,Hol (disk L) (fun z=>K z i D u))(hl:∀ i:Aura n,∀ u:Orbit n,∀ D,Hol (disk L) (fun z=>V z i D u))(i:Aura n)(D:Support (More n))(y:Orbit n): Hol (disk L) (fun z=>roomV P (lightP (K z)) (K z) (V z) i D y):=by
 let W(z:ℂ):=boastV (FeeD P (lightP (K z))) (V z)
 have hy {f:ℂ→ Cipher n}(T:Hol (disk L) f): Hol (disk L) fun z=> exp (f z):=by intro z hz; exact (hasFDerivAt_exp (𝕂:=ℂ) (x:=f z)).differentiableAt.comp_differentiableWithinAt z (T z hz)
 change Hol _ (fun z=>glowV (K z) (W z) i D y); unfold glowV; split; swap; exact differentiableOn_const _
 unfold mintF; simp only [Finset.sum_apply]; apply DifferentiableOn.fun_sum; intro j _; change Hol (disk L) (fun z=>gemB D (K z) (W z) j (beamH i.val) y); rw [funext (fun z:ℂ=>congrFun (gear_v (K z) (W z) D j i) y)]; split; swap; exact differentiableOn_const _
 simp_rw [Pi.mul_apply,Finset.prod_apply]; refine DifferentiableOn.mul (DifferentiableOn.fun_finsetProd (fun a _=> he a y _)) (DifferentiableOn.fun_finsetProd (fun a k=> ?_)); unfold W boastV; refine DifferentiableOn.sub ?_ (differentiableOn_const _); split; exact hy (hl a y _); exact hy (DifferentiableOn.neg (Fee_ana p hv t (fun i u=> he i u ∅) _ _))
private lemma haircut{K V:ℂ→ Cusp n}(p:Crowd P h γ Z Q R κ)(hv:1<L)(t:∀ z∈disk L, Wheel P h γ Z Q (K z) (V z))(he:∀ i:Aura n,∀ u:Orbit n,∀ D, Hol (disk L) (fun z=>K z i D u))(hl:∀ i:Aura n,∀ u:Orbit n,∀ D, Hol (disk L) (fun z=>V z i D u))(e:Force n)(y:Orbit n): Hol (disk L) (fun z=>burn P (K z) (V z) e y):=by exact DifferentiableOn.const_smul (glow_ana p hv t he hl (lordD e) (extraD e) y) _
lemma LipsK_line{K V:ℂ→ Cusp n}(p:Crowd P h γ Z Q R κ)(hv:1<L)(t:∀ z∈disk L, Wheel P h γ Z Q (K z) (V z))(he:∀ i:Aura n,∀ u:Orbit n,∀ D, Hol (disk L) (fun z=>K z i D u))(hl:∀ i:Aura n,∀ u:Orbit n,∀ D, Hol (disk L) (fun z=>V z i D u)): Pressed P (burn P (K 1) (V 1)-burn P (K 0) (V 0)) h ((Cog_P P R κ)/(L-1)):=Pressed.diff hv p.zH (fun z v=>(t z v).press p) (fun e y _=> haircut p hv t he hl e y) le_rfl
end YM.CF.Beau.PushA
