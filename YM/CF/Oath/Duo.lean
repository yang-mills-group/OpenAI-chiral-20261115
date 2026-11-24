import YM.CF.Oath.Pol
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
-- reindex independent True Tilt.Axis. Metric after PE.Z.W. EACH (p,q) coarse independent shape.ALL order consensus
variable (F':RegBudget (mid P B))(DΦ:Finset (Scree.Hub (mid P B)))
local notation "Xρ"=> (γl x (Domain P B))
local notation "KΩ"=> (Finset (Support (Domain P B)))
local notation "SX"=> (StackL F' DΦ)
-- stack includes all.Slip combined separately. ANY charges.
abbrev frame_w(S:Op (Single (mid N B)))(p q:Rock (mid N B)):Op SU.Slot:= Matrix.of fun i j=>S (p,i) (q,j)
local notation "ρk"=> (inbool (Domain P B) x)
variable (X: Finset (Support (Domain P B)))(U:Pane (mid N B))
local notation "Fv"=> (pulled G (bring t' Tg) W SX X)
local notation "tU"=> (bring t' Tg)
local notation "LI"=> (frame_w Fv)
variable (u:∀ i∈ DΦ,∀ (W':Pane (mid P B)), Flour (camp i.val.2) ((F' i W').val))
include t'
abbrev tide_s (i:Scree.Hub (mid P B))(U:Support (Domain P B))(V:Support (Domain P B))(p q:Rock (mid N B))(x y:Rock (mid P B)):Op SU.Slot:= lyric G t' W (F' i) U V x y p q 1 Tg
include u
lemma chores (p q: Rock (mid N B)): frame_w Fv p q= ∑ i∈DΦ, ∑ U∈ X,∑ Z∈X, ∑ a∈hue_I i.val.2, ∑ b∈ hue_I i.val.2,tide_s Tg W t' F' i U Z p q a b:=by
 let V'(i:Scree.Hub (mid P B)):= orbitPH (F' i 1)
 have hp: Fv=∑ i∈ DΦ,pulled G tU W (V' i) X:=by unfold pulled StackL; simp_rw [Matrix.mul_sum, Matrix.sum_mul,sum_comm (t:= DΦ) (s:=X)]; rfl
 have he(i)(h:i∈ DΦ)(a b: SU.Slot)(y z: Support (Domain P B)): ((openQ G tU W y true)ᴴ * orbitPH (F' i 1)*openQ G tU W z false) (p,a) (q,b)=(∑ i'∈hue_I i.val.2,∑ j'∈ hue_I i.val.2,tide_s Tg W t' F' i y z p q i' j') a b:=by
    let V:= V' i; let X₁:=openQ G tU W y true; let K:=openQ G tU W z false
    let Q(w x: Single (mid P B)):=star (X₁ w (p,a))* V w x*K x (q,b)
    have hx:(X₁ᴴ* V*K) (p,a) (q,b)=∑ w,∑ x,Q w x:=by rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply, sum_mul]; rw [sum_comm]; rfl
    let S'(i j: Prism.Rock (mid P B)):= ∑ v:SU.Slot, ∑ q:SU.Slot,Q (i,v) (j,q); have hy (d e): S' d e=tide_s Tg W t' F' i y z p q d e a b:=by unfold tide_s lyric; rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply, sum_mul]; unfold S'; rw [sum_comm]; rfl
    let B_:= hue_I i.val.2; have ht(w x:Single (mid P B))(p:¬(w.1∈ B_∧ x.1∈ B_)): Q w x=0:=by
       have hz: Haro.tray w x ∉ Wheat (camp i.val.2):=by
          intro v; refine p ((fellow _ w.2 x.2 w.1 x.1).mp (mem_filter.mpr ⟨v,?_⟩)); simp [Haro.tray] -- tune
       unfold Q V V' orbitPH; rw [Matrix.of_apply,Prism.port_eq]; split_ifs; simp; simp [(show Pastry.crumb (F' i 1).val _=0 from (u _ h _).door hz)] -- tune
    rw [hx];
    let hU:=h
    rw [Fintype.sum_prod_type]; simp only [Matrix.sum_apply]; rw [←sum_subset (subset_univ B_)]; swap
    · intro r _ v; exact sum_eq_zero (fun i _=>sum_eq_zero fun j _=> ht _ _ (fun h=>v h.1))
    apply sum_congr rfl; intro j hD; simp_rw [show ∀ v:SU.Slot, ∑ x:Single (mid P B),Q (j,v) x= ∑ x:Prism.Rock (mid P B),∑ w:SU.Slot,Q (j,v) (x,w) from fun _=> Fintype.sum_prod_type ..]; rw [sum_comm]; rw [← sum_subset (subset_univ B_)]
    · apply sum_congr rfl; intro d _; exact hy j d
    intro d _ h; exact sum_eq_zero fun v _=>sum_eq_zero fun w _=> ht (j,v) (d,w) (fun p=>h p.2)
 -- aggregate
 ext a b; unfold frame_w; rw [Matrix.of_apply,hp]; simp only [Matrix.sum_apply,pulled]; apply sum_congr rfl; intro i h; apply sum_congr rfl; intro x v; apply sum_congr rfl; intro z u; simpa only [Matrix.sum_apply] using he i h a b x z
end YM.CF.Oath
