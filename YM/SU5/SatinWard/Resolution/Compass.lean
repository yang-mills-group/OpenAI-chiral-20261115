import YM.SU5.SatinWard.Resolution.Inning

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
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
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

open ResolutionFrame
variable (F:ResolutionFrame ι) (C K A:ℝ) (L: Side)
local notation "cι"=> (Fintype.card ι:ℝ)
local notation "ε1" => Real.exp (1:ℝ)
namespace ResolutionFrame
variable {η:Type}[Fintype η][DecidableEq η]
local notation "ι₀" => Wage4
local notation "κ₀"=> Reflow ι₀ (ι₀⊕η)
local notation "F₀" => cloverFrame
abbrev plusE (s:Bool):= leg (.inl s:ι₀)
def gatherG : Coords ι₀→ₗ[ℝ]ℝ where
 toFun x:= x (.inl true)/3+2*x (.inl false)/3
 map_add' x y:= by simp only [Pi.add_apply]; ring
 map_smul' c v:=by change _=c*_ ; simp only [Pi.smul_apply,smul_eq_mul]; ring
lemma gather_formula (x:Coords ι₀): gatherG x=x (.inl true)/3+2*x (.inl false)/3:=rfl
lemma gather_t : gatherG (plusE true)=1/3:=by simp [gather_formula,plusE,leg]
lemma gather_f : gatherG (plusE false)=2/3:=by simp [gather_formula,plusE,leg]
lemma gather_norm (x:Coords ι₀): ‖gatherG x‖ ≤ ‖x‖:=by rw [gather_formula,Real.norm_eq_abs]; have a (i:Bool):= abs_le.mp (show |x (.inl i)| ≤ ‖x‖ from norm_le_pi_norm x (.inl i)); rw [abs_le]; constructor <;> linarith only [(a true).1,(a true).2,(a false).1,(a false).2]
variable (D: Reflow ι₀ (ι₀⊕η)) (W: Coords ι₀≃ₗ[ℝ]Coords ι₀)
noncomputable def rimWeight (D:Reflow ι₀ (ι₀⊕η)) (W: Coords ι₀≃ₗ[ℝ]Coords ι₀)(z: Bool → Coords ι₀):ℝ:= let L(b):=gatherG (W.symm (D.U.symm (plusE b +(2:ℝ) • z b))); L true + L false
local notation "w"=> cloverFrame.pulseHidden L C K A
local notation "m"=>rimWeight
local notation "Ξ"=>cloverFrame.chiLoss L
variable (P Q:BudgetPoint)(κ x y:ℝ) (t: Economics F₀ C K A L P Q κ x y D)(z:Bool → Coords ι₀)(V:∀ i:Bool, ‖z i‖ ≤ 2*cloverFrame.pulseHidden L C K A)(γ:ℝ)(ht:γ=cloverFrame.typical L P Q κ (.inl true)*(x/y))(u:PantryFin ι₀ F₀ L A C K)
variable (p: headFine * cloverFrame.chiLoss L ≤ |γ|)(q:|γ| ≤ 4*ε1*cloverFrame.chiLoss L)(w₀:∀ z,‖W.symm z‖ ≤ 2*‖z‖)(c₀:∀ i:Bool,W (plusE i)=plusE i)
include t V ht u p q w₀ c₀
lemma induction_of_gather : |γ*m D W z - 1| ≤ 1/2:=by
 have he:= receipt_pos; have hs:=cloverFrame.chi_pos L
 let p' := cloverFrame.pulseBase L; let a':=w
 have y':0≤ a':=by linarith only [show ‖z true‖≤ 2*a' from V true,norm_nonneg (z true)]
 have hd:p'*Ξ=receiptCost:=div_mul_cancel₀ _ hs.ne'; have hp:0<p':=div_pos receipt_pos hs
 let L'(i:Bool):= W.symm (D.U.symm (plusE i + (2:ℝ) • z i))
 have v(i:Bool): ‖γ • D.U.symm (plusE i) - plusE i‖ ≤ a':=by
    have hi: D.U.symm (γ • plusE i-D.U (plusE i))=γ • D.U.symm (plusE i)-plusE i:=by simp
    rw [←hi]; apply (t.sail _).trans; apply mul_le_mul_of_nonneg_left _ hp.le; rw [norm_sub_rev, ht]
    cases i <;> exact t.track _
 have hX:(1:ℝ)≤ ε1:=Real.one_le_exp (by norm_num); have hz:1≤ receiptCost:=by unfold receiptCost; apply (le_div_iff₀ headPos).mpr; unfold headFine; linarith only [Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num)]
 have H:1≤ε1*receiptCost:=by
    calc
     (1:ℝ) = 1*1:=by norm_num
     _ ≤ _:=by gcongr -- align
 have w'(i:Bool):‖γ • L' i-plusE i‖ ≤ 1/4:=by
    let a:=plusE i; let Z:=D.U.symm ((2:ℝ) • z i); have ha: W.symm (plusE i)=a:=by apply W.injective; rw [W.apply_symm_apply]; exact (c₀ _).symm
    rw [show γ • L' i-plusE i = W.symm ((γ • D.U.symm a-a)+γ • Z) from by unfold L' a Z; rw [map_add D.U.symm,map_add W.symm,map_add W.symm,map_sub,map_smul W.symm γ (D.U.symm (plusE i)),map_smul W.symm γ (D.U.symm ((2:ℝ) • z i)),ha, smul_add];  exact by unfold a; abel]
    apply (w₀ _).trans; let h:= t.sail ((2:ℝ) • z i)
    have Wq: ‖γ • Z‖≤ (4*ε1*Ξ)*(p'*(2*(2*a'))):=by rw [norm_smul]; have hx:‖Z‖≤ p'*(2*(2*a')):=by { apply h.trans; apply mul_le_mul_of_nonneg_left _ hp.le; rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]; exact mul_le_mul_of_nonneg_left (V i) zero_le_two }; exact mul_le_mul q hx (norm_nonneg _) (by positivity)
    refine (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add (v i) Wq)) zero_le_two).trans ?_
    have hy:128*ε1*receiptCost*a'≤1/16:=u.hidden
    let X:=ε1*receiptCost*a'; have hk:a'≤X:= by unfold X; simpa only [one_mul] using mul_le_mul_of_nonneg_right H y'
    have hy':128*X≤1/16:=by rw [show 128*X= (128*ε1*receiptCost)*a' from by unfold X; ring]; exact hy
    rw [show ((4*ε1)*Ξ)*(p'*(2*(2*a')))=16*X by unfold X; rw [←hd]; ring]; linarith only [hk, hy']
 have z'(i:Bool): |γ*gatherG (L' i)-gatherG (plusE i)| ≤ 1/4:=by
    change ‖γ • gatherG (L' i) - gatherG (plusE i)‖ ≤ _; rw [←map_smul,←map_sub]; exact (gather_norm _).trans (w' _)
 have v₁:=z' true; have v₂:=z' false; rw [gather_t] at v₁; rw [gather_f] at v₂; change |γ*(gatherG (L' true)+gatherG (L' false))-1| ≤ _; rw [abs_le] at v₁ v₂ ⊢; constructor<;> linarith only [v₁.1,v₂.1,v₁.2,v₂.2]

noncomputable abbrev mtorque (L:Side):ℝ:= (4*ε1)*cloverFrame.chiLoss L
noncomputable def mBooster (L:Side)(x:ℝ): Prop:= (1/2:ℝ)*(mtorque L)⁻¹ ≤ |x|∧ |x| ≤ cloverFrame.pulseBase L
lemma mBooster.of_rim: mBooster L (m D W z):=by
 have e:= abs_le.mp (induction_of_gather C K A L D W P Q κ x y t z V _ ht u p q w₀ c₀)
 let h:= m D W z; have v: 0 < |γ| := (mul_pos headPos (cloverFrame.chi_pos L)).trans_le p; let T:=mtorque L
 have i:0 ≤ γ*h:=by linarith only [show -(1/2:ℝ) ≤ γ*h-1 from e.1]
 have H: |γ| * |h| = γ*h:=by rw [←abs_mul,abs_of_nonneg i]
 refine ⟨?_,?_⟩
 · change (1/2:ℝ)*T⁻¹ ≤ |h|; rw [←div_eq_mul_inv]; have ht:0< T:=v.trans_le q; apply (div_le_iff₀ ht).mpr; linarith only [mul_le_mul_of_nonneg_right (show |γ| ≤ T from q) (abs_nonneg h),show -(1/2:ℝ) ≤ γ*h-1 from e.1,H]
 change |h| ≤ (2/headFine)/Ξ; rw [div_div]; apply (le_div_iff₀ (mul_pos headPos (cloverFrame.chi_pos L))).mpr; linarith only [mul_le_mul_of_nonneg_right p (abs_nonneg h),show γ*h-1≤ 1/2 from e.2,H]
#print axioms mBooster.of_rim
end ResolutionFrame
end ShapeLab
end YM.CF.QuadClock
