import YM.CF.Stax.Hold
import YM.CF.Stax.Sil
import YM.CF.Sour.Park
import YM.CF.Sour.Tile
import YM.CF.Ione.Tape
import YM.CF.Cadre.Point
import YM.CF.Cadre.Gear
import YM.CF.Vow.Grow
import YM.CF.Bake.Pep
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
end YM.CF.Stax
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
open Salt Ione Levier Sour
open Hake Jet Nor Bake Ione
local notation "Xr"=> Finset (Dwell n)
abbrev Dual (F:Copy n)(X Y:Support (More n))(p: BudgetPoint):Prop:=∀ i j:Orbit n, pingS p.threshold X i.1 → pingS p.threshold X j.1→ Agrees Y i.1 j.1→ F i=F j
variable (X:Scree.Hub n)(D:Support (More n)) (F': Copy n)(D': ℝ)(u:Medal P X.val.2 ∅ F' h D')(η:X.val.1∈D)(U: Orbit n)(f:Dual F' X.val.2 D P)(A:Raid (Dwell n))(g:WorthB P U ∅ F' A)(p:pingS P.threshold X.val.2 U.1)
local notation "Θ"=> (pressQ P (∅:Support (More n)))
local notation "Br"=> (Prism.trunk P X.val.1)
local notation "St"=> Signs P X.val.1
open Prism Forge Rill
include η f g p
lemma ard(i:Finset (Dwell n)):Signs P X.val.1 (fun y=>Pastry.crumb (F' (increment U.1 y,U.2)).val i) (liftR P D 1 (A i)):=by
 let W(x):=Nor.rodV P X.val.1 D (∅:Support (More n)) x; let Z:=Nor.rodV P X.val.1 D (∅:Support (More n)); let H(V:Orbit n):=Pastry.crumb (F' V).val i; let V:=fun x=> H (Θ U.1 x,U.2); let O:= X.val.2
 have hu:Allows P.order V (Z 0) (P.order.factorial * A i):=(Z.map_zero).symm ▸ (g.haveP i).pay; have hb(x:tangD n):openG P (∅:Support (More n)) x=x:=by funext i; simp [openG,Lattice.halo]
 have hl:∀ᶠ t:tangD n in 𝓝 0,pingS P.threshold O (Θ U.1 (W t)):=by
    simp_rw [show ∀ t,pingS P.threshold O (Θ U.1 (W t)) ↔ pingS P.threshold (O\∅) (Θ U.1 (W t)) from fun t=> by rw [sdiff_empty]]
    have he:Tendsto W (𝓝 0) (𝓝 0):= by nth_rw 2 [← Z.map_zero]; exact Z.continuous.continuousAt.tendsto
    exact he.eventually (Vow.tick (D:=∅) (by rw [sdiff_empty]; exact p))
 have hk:‖Z‖≤ surgeL P D 1:= lens_x P _ _ _ 1 η; apply Prism.skills; apply (hu.comp (Jet.allows_linear hk (by rw [map_zero,norm_zero]; exact (norm_nonneg _).trans hk))).germ
 let I(x:tangD n):=increment U.1 (Br x); have hf:Continuous I:=(show Continuous (increment U.1) from ?_).comp (Br).continuous; swap
 ·
   rw [show increment U.1= Forge.gyrate (Rill.unrest (∅:Support (More n)) P.B) U.1 from funext fun x=>by unfold Forge.gyrate; rw [Function.comp_apply,←Rill.padP,hb]]; exact Forge.stickU ..
 have ht:I 0=U.1:=by unfold I; rw [map_zero]; funext i; simp [RG.increment] -- tune
 filter_upwards [hl, hf.continuousAt.eventually (ping_o.mem_nhds (show pingS P.threshold O (I 0) from ht.symm ▸ p))] with x g v
 refine congrArg (fun i':Cipher n=> crumb i'.val i) (f _ (I x,U.2) g v ?_); have he:= loc_y (o:=X.val.1) (D:=(∅:Support (More n))) (P:=P) (X:=D) (U:=U.1) Z rfl x; rw [hb] at he; exact he
lemma fastE(i:Xr)(q:∀ V:Orbit n,Flour (camp D) (F' V).val) : Signs P X.val.1 (fun y=>Pastry.crumb (F' (increment U.1 y,U.2)).val i) (linkY P D A 1 i):=by unfold linkY; split; exact ard X D F' η U f A g p i; rename_i h; exact Prism.mint (Prism.hail (v:=(0:ℝ)) (norm_zero.le)) (Eventually.of_forall fun y=> ((q _).door h).symm)
omit g p
abbrev Burial (R:Copy n)(S:Ids n) : InkD n:=fun x=>R (x,S)
variable (Ht:Ids n)
include u
lemma lobe (pT:∀ i:Orbit n, F' i =F' (i.1,Ht))(q:∀ V:Orbit n, Flour (camp D) (F' V).val)(t:0 ≤ h) : PressB P X (Burial F' Ht) h (Vow.fareX 1 P D * D'):=by
 let V:= Burial F' Ht; let P':=u.toThemeR; have hu : F'= Vow.oV V:= funext pT; obtain ⟨A,C,K,v⟩:= u.pays
 refine ⟨fun i j k=> P'.same (i,Ht) (j,Ht) k (fun _ _=> rfl), fun V=> P'.lit _, P'.keeps.comp (measurable_id.prodMk (measurable_const (a:=Ht))),fun i g=>?_ ,linkY P D A 1,Vow.quietT A C, fun i k j=> ?_, (Nor.rate_i P D _ η A _ _ C t).trans (mul_le_mul_of_nonneg_left v (Vow.health_f ..))⟩
 · exact (pT (Lattice.gauge g i,threadG g Ht)).symm.trans (P'.gaugeX (i,Ht) g)
 have hk:WorthB P (i,Ht) ∅ F' A:= K (i,Ht) (by rw [sdiff_empty]; exact k) (Subset.refl _); exact fastE X D F' η _ f A hk k j q
end YM.CF.Stax
