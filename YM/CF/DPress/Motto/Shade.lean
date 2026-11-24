import YM.CF.DPress.Motto.Back
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Larch Ione Taxi Bake Salt
namespace WagesC.Blend
variable {n:Side}{k L:ℕ}(P:BudgetPoint){a h b:ℝ}
local notation "Sx"=> Point n
variable (B:Blend n k) (w: Wings k P a n)(t:1≤h)(z:ℝ)
abbrev μM {v:ℝ}(o:Sx): Pane n→ℝ := {i| pingS v (haloW o) i}.indicator (feeW o)
@[fun_prop] lemma measurable_μM {v:ℝ}(o:Sx):Measurable (μM (v:=v) o):=(contFee o).measurable.indicator ping_o.measurableSet
lemma gaugeμ (i:Sx):GaugeInvariant (μM (v:=h) i):=by intro z k; simp only [μM,Set.indicator,Set.mem_setOf_eq,pingB,gaugeW]; congr 1
lemma transitμ(s:Sweep n)(i:Sx)(u:Pane n): μM (v:=h) ((boxA s).symm i) (flashA s u)= μM (v:=h) i u:=by
 simp only [μM,Set.indicator,Set.mem_setOf_eq,moving_halo,Salt.glowA,stampW]; congr 1
lemma αeq0(n:Side): αLan (n:=n) 0=0:=by funext X; unfold αLan; split; exact zero_smul ..; rfl
lemma z0 : B.Zα 0=0:= by unfold Zα; simp only [zero_mul,zero_smul,sum_const_zero]
lemma s0 : B.Sα 0=0:= by funext i; simp only [Sα,sunY,fA,zero_mul,zero_smul,sum_const_zero]; rfl
lemma colorZ(s:Sweep n)(u:B.even s)(Y:Aura n)(V:Orbit n)(D:Support (More n)): Zα B z (moldA s Y) (actY s D) (yellA s V)= suit_Y s (Zα B z Y D V):=by
 simp only [Zα,Finset.sum_apply,map_sum]; symm; refine sum_equiv (τσ s) (fun i=>similar i s) ?_; intro k p; simp only [Pi.smul_apply, map_smul]; rw [show B.φΩ (τσ s k)=B.φΩ k from u k.1 k.2]; let F0:= stroke (τ₀ k.2) (τ₀ k.1) (coinP k) (oV (fund k.2)) (oV (fund k.1))
 apply congrArg; unfold stroke chasmR; by_cases t: Y=coinP k; swap; · rw [Pi.single_eq_of_ne t,Pi.single_eq_of_ne (mt (fun g=>?_) t),Pi.zero_apply,Pi.zero_apply, Pi.zero_apply, Pi.zero_apply,map_zero]; exact (moldA s).injective (g.trans (coinΩ s k)) -- tune meta
 rw [t, Pi.single_eq_same,←coinΩ,Pi.single_eq_same]; -- second equality rew `k`?
 have hp(o:Point n): suit_Y s (flick (τ₀ o) (oV (fund o)) D V)=flick (τ₀ ((boxA s).symm o)) (oV (fund ((boxA s).symm o))) (actY s D) (yellA s V):=by
    unfold Vow.flick; by_cases h:Disjoint D (τ₀ o).val; swap; · rw [if_neg h,if_neg]; exact map_zero _; rw [show (τ₀ _).val=actY s (τ₀ o).val from moving_halo ..]; exact fun g=> h (Finset.disjoint_map _|>.mp g)
    rw [if_pos h,if_pos (show Disjoint _ _ from (by rw [show (τ₀ ((boxA s).symm o)).val=actY s (τ₀ o).val from moving_halo ..]; exact Finset.disjoint_map _|>.2 h))]; change suit_Y s ((feeW _ V.1) • (1:Cipher n))=(feeW _ (flashA s V.1)) • (1:Cipher n); rw [stampW s V.1 o,map_smul,map_one]
 exact (map_sub ..).trans (congrArg₂ (·-·) (hp _) (hp _))
-- geom.All endpoints enough. Precise presence conditional for later FD budgets.
lemma ping_location(X:Support (More n)){U V:Pane n} (u:Agrees (Lattice.halo 2 X) U V) : pingS h X U ↔ pingS h X V:=by
 have hp(i:Face (Per (More n)))(g:¬ Disjoint X (touched i)): faceValue V i= faceValue U i:=by
    obtain ⟨x,p,t⟩:= Finset.not_disjoint_iff.mp g; exact Eq.symm (WilsonStartup.face_local i U V (agrees_mono u (fun i v=> halo_spec.mpr ⟨x,p,Plaque.bill _ t v⟩))) -- tune coerces X to Set
 exact ⟨fun h i t=> hp i t |>.symm ▸ h i t, fun h i t=> hp i t ▸ h i t⟩
lemma stool(o:Point n): LocalOn (Lattice.halo 2 (haloW o)) (μM (v:=h) o):=by intro U V t; unfold μM Set.indicator; simp_rw [Set.mem_setOf_eq]; rw [show feeW o U=feeW o V from Plaque.sits _ _ _ (agrees_mono t (Finset.coe_subset.mpr (halo_subset ..)))]; by_cases h':pingS h (haloW o) U; rw [if_pos h',if_pos ((ping_location _ t).1 h')]; rw [if_neg h',if_neg (mt (ping_location _ t|>.2) h')]
-- supplied matching scalar.
def Φ (x:Pane n): ℝ:= ∑ i∈κN n k,B.φΩ i * z* μM (v:=h) i.2 x -- convention includes threshold implicit angle
end WagesC.Blend
end YM.CF.Py.Kay
