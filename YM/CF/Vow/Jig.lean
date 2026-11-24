import YM.CF.Vow.Goal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- horizon via saturated X only. rank sums from pointwise cut. Works for flagged if required later
open Rue
abbrev visible (P:BudgetPoint)(X D:Support (More n))(V:Pane n):Prop:= Rue.Gates {U|pingS P.threshold (X\D) U} X V
def zenS (P:BudgetPoint)(X D:Support (More n))(F:Copy n)(V:Orbit n):Cipher n:=if visible P X D V.1 then F V else 0
variable {U' W':Pane n}
lemma visibly (p: Agrees X U' W'):visible P X D U' ↔ visible P X D W':=⟨fun ⟨y,t,u⟩=>⟨y,t,fun i e s=> (p _ e s).symm.trans (u i e s)⟩,fun ⟨y,t,u⟩=>⟨y,t,fun i e s=> (p _ e s).trans (u i e s)⟩⟩
lemma visiL (V:Pane n)(g:Seat n→SU.group.El) : visible P X D (Lattice.gauge g V) ↔ visible P X D V:=by
 have ht(V:Pane n)(g:Seat n→SU.group.El)(p:visible P X D V): visible P X D (Lattice.gauge g V):=by
    obtain ⟨i,h,t⟩:=p; exact ⟨Lattice.gauge g i,(pingB i g).mpr h, Skye.tied _ V i g g t (fun _ _=> rfl)⟩
 refine ⟨fun p=>?_ ,ht V g⟩; have he:= ht _ g⁻¹ p; rw [show Lattice.gauge g⁻¹ (Lattice.gauge g V)= V from funext fun i=>by simp [Lattice.gauge,mul_assoc]] at he; exact he
lemma hates (u:pingS P.threshold (X\D) U): visible P X D U:=⟨U,u,fun _ _ _=>rfl⟩
variable {f:Pane n→ℂ}
local notation "Θ"=> pressQ P Y
local notation "Yc"=> P.threshold
local notation "ℙ"=>P.order
private lemma nearby(c:ℝ)(h:Pence ℙ (fun i:DN=> f (Θ U i)) 0 c):Allows ℙ (f ∘ gyrate (unrest Y P.B) U) 0 (composeCost ℙ (P.order.factorial*c) ‖((Yc⁻¹ :ℝ) • ContinuousLinearMap.id ℝ DN)‖):=by
 let L:DN→L[ℝ]DN:=Yc⁻¹ • ContinuousLinearMap.id ℝ _; rw [show f ∘ gyrate (unrest Y P.B) U=(fun i:DN=> f (Θ U i)) ∘ L from funext fun i=> by change _=f (gyrate _ _ (Yc • (Yc⁻¹ • i))); rw [smul_inv_smul₀ P.threshold_pos.ne']; rfl]; exact (show Allows ℙ _ (L 0) (P.order.factorial*c) from (L.map_zero).symm ▸ h.pay).comp (allows_linear le_rfl (by rw [map_zero L,norm_zero]; exact norm_nonneg _))
lemma tick (w:pingS P.threshold (X\D) U):∀ᶠ y:DN in 𝓝 0,pingS P.threshold (X\D) (Θ U y):=by
 let L:DN→L[ℝ]DN:=Yc • ContinuousLinearMap.id ℝ DN; let K:=gyrate (unrest Y P.B) U
 have ht:Tendsto (K ∘ L) (𝓝 0) (𝓝 U):=by
    rw [show (𝓝 U)= 𝓝 ((K ∘ L) 0) from congrArg _ (by rw [Function.comp_apply,map_zero]; exact (born ..).symm)]; exact ((stickU _ U).comp L.continuous).continuousAt.tendsto
 exact ht.eventually (ping_o.mem_nhds w)
lemma reach_p (w:pingS P.threshold (X\D) U):∃ V:ℝ,0 ≤ V ∧ ∀ᶠ x:DN in 𝓝 0,∀ (f:Pane n→ℂ)(c:ℝ), (∀ W:Pane n,pingS P.threshold (X\D) W→Pence ℙ (fun i:DN=> f (Θ W i)) 0 c)→ Allows ℙ (fun i:DN=> f (Θ U i)) x (V*c):=by
 let I:=(Yc⁻¹ • ContinuousLinearMap.id ℝ DN); let L:=Yc • ContinuousLinearMap.id ℝ DN
 let C:= composeCost ℙ (P.order.factorial*1) ‖I‖; have hp:0 ≤ C:=by unfold C composeCost; positivity
 let W:Set (Pane n):={U|pingS P.threshold (X\D) U}
 obtain ⟨T,hT,H⟩:= Arbor.lime (E:=ℂ) (α:=Unit) SU.group (unrest Y P.B) P.order 1 C hp; refine ⟨composeCost ℙ T (‖L‖+1),by unfold composeCost; positivity,?_⟩
 have hu: ∀ᶠ x:DN in 𝓝 0,‖L x‖ < 1:= (L.continuous.tendsto 0).eventually (isOpen_lt continuous_norm continuous_const|>.mem_nhds (show ‖L 0‖<1 by rw [map_zero,norm_zero]; norm_num))
 filter_upwards [(tick (Y:=Y) w),hu] with x p t f c m
 have hm:= (m U w).nonneg
 rcases hm.eq_or_lt with e|e
 · subst c; rw [mul_zero]; refine (allows_const x (show ‖(0:ℂ)‖≤0 by rw [norm_zero])).germ ?_; have hp':Tendsto (gyrate (unrest Y P.B) U ∘ L) (𝓝 x) (𝓝 (Θ U x)):= ((stickU ..).comp L.continuous).continuousAt.tendsto
   filter_upwards [hp'.eventually (ping_o.mem_nhds (show Θ U x∈W from p))] with i ht; have he:= (m (Θ U i) ht).pay.value; rw [mul_zero,norm_le_zero_iff] at he; dsimp only [pressQ] at he; rw [smul_zero,born] at he; exact he.symm
 let g(i):= c⁻¹ • f i
 have hk : Arbor W (fun _:Unit=> g) (unrest Y P.B) P.order C:=by
    intro u v t'; have he:= (nearby c (m u v)).smul c⁻¹; have hx: |c⁻¹| * composeCost ℙ (P.order.factorial*c) ‖I‖= C :=by rw [abs_of_pos (by positivity)]; unfold C composeCost; field_simp <;> ring -- tune
    change Allows _ _ _ (|c⁻¹| *composeCost ℙ _ ‖I‖) at he; rw [hx] at he; exact ⟨Warm.simple _ he.smooth,he⟩
 let M:= g ∘ gyrate (unrest Y P.B) U; have hy: Allows ℙ M (L x) T:=H _ hk () U _ p (mem_ball_zero_iff.mpr t)
 have ht: Allows ℙ (g ∘ Θ U) x (composeCost ℙ T (‖L‖+1)):=hy.comp (allows_linear (le_add_of_nonneg_right zero_le_one) (t.le.trans (le_add_of_nonneg_left (norm_nonneg _))))
 have hb:=ht.smul c; unfold g at hb; simp only [Function.comp_apply,smul_inv_smul₀ e.ne',abs_of_pos e, mul_comm c] at hb; exact hb
end YM.CF.Vow
