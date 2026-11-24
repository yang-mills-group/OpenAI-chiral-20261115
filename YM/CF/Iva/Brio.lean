import YM.CF.Iva.Iva
import YM.CF.Rue.Pace
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
variable {N P B:Side}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{x β R e a b:ℝ} {n m l k:ℕ}
local notation "G₅"=> SU.group
variable{T:Tube G₅ S}(Z:Muster G S x e T)(M:Monk G₅ S){w t u C D:ℝ}
local notation "l_"=> Z.post
local notation "q_"=> Z.trot
local notation "Ba"=> radiusB x
local notation "Wa"=> (fun y=>M.atop y x)
local notation "W"=> M.sent x T q_ Z.room l_ Z.beta
open Next.SectorChange
variable {X Y:Support (Domain N B)}
abbrev glare: Support (Domain N B)→ Directions G₅ (Domain P B)→ Monk G₅ S:=fun X z=> {M with z:=fun i=> if Next.SectorChange.points S i⊆ X then z i else 0} -- M.key held, independence
variable {M₀:Monk G₅ S}
lemma dawn_l(X:Support (Domain N B))(U: Directions SU.group (Domain P B)):Forge.Duo SU.group S {M with z:=U} (glare M X U) X:=⟨⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun i _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=> rfl,fun _ _=>rfl,fun i g=>(if_pos g).symm⟩,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩
lemma down_l(Y:Support (Domain N B))(h:Forge.Duo SU.group S M M₀ X)(p:Y⊆X):Forge.Duo SU.group S M M₀ Y:=⟨h.toBeat.mono p,fun i g=>h.cost _ (fun t=> g (Disjoint.mono_right p t)),fun i g=> h.aisles _ (fun t=>g (Disjoint.mono_right p t)),fun i g=>h.flags _ (p g)⟩
local notation "r_"=> ((Z.loft+Z.post+200)*radiusB x)
-- event independent of fields,flags
abbrev Bravo(b:ℕ)(i:Sat S)(y: Directions G₅ (Domain P B))(d:ℝ):Prop:= ∃ j:Bond (Domain P B),Next.SectorChange.points S j⊆ (domeQ b i).val ∧ d< ‖y j‖
abbrev bravoK (y: Directions G₅ (Domain P B))(i:Sat S)(d C:ℝ): ℝ:= if Bravo r_ i y d then Jet.composeCost k (C+1) 1 else 0
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](I:E→L[ℝ] Directions SU.group (Domain N B))(i:Sat S)
variable(h:‖I‖ ≤ 1){L:ℝ}
local notation "M'"=>({M with key:=cusp M.key x M.V}:Monk SU.group S)
include h
lemma price_e(g:(domeQ r_ i).val⊆ X)(p:Ready T x)(hv:shovel S.patch+10≤ radiusB x)(ht:1000≤radiusB x)(hD:X∩ flags (temp x) M.V=M.key.flags)(hb: Cloak.Probe (fun y=>portF Z ((M').atop y x) w t i) 0 C k)(hk:0≤L)(hA:∀ z:Directions G₅ (Domain P B), ‖z‖ ≤ L→ portF Z {M' with z:=z} w t i=1) :Allows k (fun y=> portF Z (M.atop (I y) x) w t i-1) 0 (bravoK (k:=k) Z M.z i L C):=by -- Mem flags w ∩
 have he: Forge.Duo SU.group S M M' X:= cusp_d M.key rfl hD M.V
 let Y:= (domeQ r_ i).val
 let H:= highlight Y; let F:= H.comp I; have hx:‖F‖ ≤ 1:= (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_one₀ (high_nn _) (norm_nonneg _) h)
 have hf(v:ℝ)(U: Directions SU.group (Domain N B)→ℝ)(p:Allows k U 0 v) : Allows k (U∘ F) 0 (Jet.composeCost k v 1):=Allows.comp (f:=F) ((map_zero F).symm ▸ p) (allows_linear hx (by rw [map_zero,norm_zero]; norm_num))
 let V(y):= portF Z ((M').atop y x) w t i; let V'(y):= V y -1
 have hu(y:E):portF Z (M.atop (I y) x) w t i= V (F y):= payF Z _ _ _ (high_p (x:=x) (down_l M Y he g) (I y)) p ht hv _ (Subset.refl _) -- tunes
 unfold bravoK; simp only [hu]; split_ifs with y
 · exact hf _ V' (Newt.subtract_p hb.pays (Jet.allows_const _ norm_one.le))
 have hy: ¬Bravo r_ i (M').z L:= y; let N:= glare M' Y (M').z
 have hN:‖N.z‖ ≤ L:=by
    apply (pi_norm_le_iff_of_nonneg hk).mpr; intro j; change ‖if Next.SectorChange.points S j ⊆ Y then _ else _‖ ≤ L; split_ifs with z
    · apply le_of_not_gt; intro p; exact hy ⟨j,z,p⟩
    rw [norm_zero]; exact hk -- tune binder
 have hX:portF Z M' w t i=1:= Eq.trans (payF Z _ w t (dawn_l M' Y M.z) p ht hv _ (Subset.refl _)) (hA _ hN)
 have hv:V 0=1:=by
    change portF Z ((M').atop 0 x) w t i=1; rw [show (M').atop 0 x=M' by simp [ Monk.atop,Vmove]] -- notation M' not identifier parse
    exact hX
 have hp' :=(hb.flat hv).smul (-1:ℝ); rw [mul_zero] at hp'; have hu:=hf 0 _ hp'; simp only [Jet.composeCost,mul_zero,zero_mul] at hu; refine hu.germ ?_; filter_upwards with z; dsimp only [Function.comp_apply,neg_smul,one_smul]; simp [V] -- tune
end YM.CF.Iva
