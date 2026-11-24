import GaugeFieldConstruction.Gimmer
import GaugeFieldConstruction.Gin
import GaugeFieldConstruction.Vuoto
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
-- * uses Gimmer's gauge bill. composite z input not lattice increment vector. reuse Term consistency valid on actual changes support.
open TableF TableF.Axon
variable {c f:Side}{S: StepData (More c) (More f)}{κ:Ratio c f}{R:BudgetPoint}{P:BudgetPoint}
variable {Z:tangD c→ tangD f}{U: Pane c→ Pane f}
-- Ccenter
abbrev mastTar (s K:ℝ):ℝ:= Haro.horn * (prey s*(1+max 1 (sparkleC 6 K)))
lemma zenπ {V:Pane c}{Vp:ℕ}{W:InkD f}{E:InkD f} {θ K h d d' b s x ε:ℝ}(hw:1≤K)(u:TariffZ 6 K)(τ:R.order=6)(tx:R.threshold=temp x)(X:Scree.Hub f)(D:Support (More c))(h':S.ratio.parent X.val.1∈D) (g:Site (More c)→ SU.E) (Θ:tangD c→Seat f→ SU.group.Color)(z:Guide _ (R.dirBound (S.ratio.parent X.val.1)) 0 Θ 6 ε)(hg:∀ᶠ w in 𝓝 (0:tangD c),Agrees (inspected X.val.2) (increment 1 (Z w)) (Lattice.gauge (fun i=> SU.group.lieExp (Θ w i)) (Lattice.gauge (g ∘ S.ratio.parent) (U (increment V w))))) (hc:0≤ ε)(hu:ε ≤ 1)(A:LocalCurve P X Z {z| R.dirBound (S.ratio.parent X.val.1) z} s b)(hb:0 ≤ b)(yh:b≤1)(hs:1 ≤ s)
 (Bv:Raid (Dwell f))(xF:PressB P X E h d)(fF:∀ U,BedP P U E X Bv)(fP:∀ i,0≤ Bv i)(fG:∀ U,BedP P U W X Bv)(hp:PressB P X W h d')(hpF:PressB P X (W-E) h θ)(Γ:∀ U,BedP P U (W-E) X (ε • Bv))(i j:Rock f): let L:=temp x • lineP R (S.ratio.parent X.val.1) D Vp; let T:=fun y=>Haro.CharM E i j (increment 1 (Z (L y))); Allows 6 T 0 (mastTar s K*crack Bv i j) ∧ Allows 6 ( (fun y=>Haro.CharM W i j (gauge (g ∘ S.ratio.parent) (U (increment V (L y))))) - T) 0 (mastTar s K*crack Bv i j*ε) := by
 intro L T
 let N:= More f; let o:=X.val.1; let a:= S.ratio.parent o; let Tx(v):=Haro.CharM W i j (gauge (g ∘ S.ratio.parent) (U (increment V v))); let T'(v):= Haro.CharM E i j (increment 1 (Z v)); let U'(v) := Haro.CharM W i j (increment 1 (Z v))
 have he: 0≤crack Bv i j:=sum_nonneg fun i _=>sum_nonneg fun j _=>fP _
 let cη:=prey s*crack Bv i j; have hz:0 ≤ cη:=mul_nonneg (prey_r (zero_le_one.trans hs)) he
 have hf(l m:SU.Slot): Allows 6 (fun y=> T y l m) 0 cη:=by -- allows transport
    have hh:= peseta (slot_credit A (Eq.refl E) Bv xF fF fP hs hb yh τ i j l m) x D tx h' Vp; rw [τ] at hh; exact hh
 have hx(F:tangD c → Op SU.Slot)(u:ℝ)(p:0 ≤ u)(ff:∀ l m:SU.Slot,Allows 6 (fun y=>F y l m) 0 u): Allows 6 F 0 (Haro.horn*u):=by
    simpa only [sub_zero] using (Haro.softL F p 0 (fun i j=> (by simpa only [Matrix.zero_apply,sub_zero] using ff i j)))
 let κ:= max 1 (sparkleC 6 K)
 have hκ:0≤κ:=zero_le_one.trans (le_max_left ..); have hX: 0≤ Haro.horn:=zero_le_one.trans Haro.p0
 refine ⟨(hx T cη hz hf).mono ?_,?_⟩
 · calc
     _ ≤ Haro.horn*((1+κ)*cη):=mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hz (le_add_of_nonneg_right hκ)) hX
     _ = _:=by unfold cη κ mastTar; ring
 have hs₁(l m:SU.Slot): Signs R a (fun y=> Tx y l m-U' y l m) (κ*cη*ε):= high (Prism.goss (K:=K) (by omega : 2 ≤ 6) hw u Z Θ g hp z hg i j cη hc hu τ (fun l m=> slot_credit A (Eq.refl W) Bv hp fG fP hs hb yh τ i j l m) l m) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hz) hc)
 have hT(l m:SU.Slot): Signs R a (fun y=> Tx y l m-T' y l m) ((κ+1)*cη*ε):=by
    have hk:0 ≤ ε • Bv:=smul_nonneg hc fP; let hh:=slot_credit A (Eq.refl (W-E)) (ε • Bv) hpF Γ hk hs hb yh τ i j l m
    refine Prism.mint (high (tack (hs₁ l m) hh) ?_) ?_
    · rw [show Prism.crack (ε • Bv) i j= ε* Prism.crack Bv i j from (by unfold Prism.crack; simp_rw [mul_sum]; rfl)]; exact le_of_eq (by unfold cη; ring)
    apply Eventually.of_forall; intro y; change Tx y l m - U' y l m + _= Tx y l m - T' y l m; rw [show CharM _ _ _ _ l m= (U' y l m-T' y l m) from ?_]; abel
    let yy:= increment (1:Pane f) (Z y); let a:Dwell f:=(true, (i,l)); let b:Dwell f:=(false,(j,m)); change Prism.portB ((W yy-E yy)).val a b = Prism.portB (W yy).val a b - Prism.portB (E yy).val a b; have hp:a≠ b:=by simp [a,b]
    rw [Prism.port_eq,Prism.port_eq,Prism.port_eq,if_neg hp,if_neg hp,if_neg hp,←mul_sub]; rfl
 let P:=fun y=> Tx (L y)
 refine (hx (P-T) ((κ+1)*cη*ε) (by positivity) (fun l m=>?_)).mono (le_of_eq ?_)
 · have ht:= peseta (hT l m) x D tx h' Vp; rw [τ] at ht; exact ht
 unfold cη κ mastTar; ring
end YM.CF.Oath
end
