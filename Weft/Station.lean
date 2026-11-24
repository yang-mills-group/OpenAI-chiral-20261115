import Weft.Hut
import Weft.Carrier
import Weft.Quota
import Weft.ForgeCost
import Weft.Submit
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Ione Nacre Both Compass Moto Lattice.PlaqAxes AnalyticBridge.VerifiedReset
local notation "mH"=>mid N B
local notation "pH"=>mid P B
variable {uτ Δτ χτ g0 g1 g2 κτ Q1 Q2 Q3 Oτ:ℝ}{kκ:ℕ}(C0:Headquarters V U X Y S G G₀ G₁ Xi q kL Hh Vp Va χτ Δτ uτ g0 g1 g2 κτ Q1 Q2 Q3 Oτ kκ)
variable {I:Type}[LinearOrder I][Fintype I](o:I→Site (mid N B))(Lq:Log I (mid P B))(Bv:Bool→Pin (mid N B))
local notation "Iκ"=>PairKey I
local notation "dT"=> Ione.duty_Q X.p.order X.p.power
local notation "Jf"=> Ione.strive_E X.p.order
open Larch Moto
variable (br bw κw V' Z':ℝ)
local notation "Lζ"=> ThinGauge.boost (Xη R.L)
local notation "T_D"=> armL o Lq Y
local notation "Dζ"=> (fun _:Bool=> κw*br)
local notation "Q"=> ((annY V Xi C0 (armL o Lq Y) Bv (soot br) Dζ))
local notation "ιmk"=> cobble I V' Z' Lζ
abbrev minted(L:Side)(U V:ℝ){I:Type}[LinearOrder I][Fintype I](o:I→ Site (mid N B))(E:Key (PairKey I)→ RegBudget (mid N B))(F:Key (PairKey I)→ ForceBudget (mid N B)):Log I (mid N B):=⟨FlameX (sameY o) E (cobble I U V (ThinGauge.boost (Xη L))),FlameK (sameY o) F (cobble I U V (ThinGauge.boost (Xη L)))⟩
variable (T_:Key (PairKey I)→ RegBudget (mid N B))(L_: GrantedS V Xi C0 (armL o Lq Y) Bv (soot br) (fun _=>κw*br) T_)(q2:∀ i:PairKey I,νTip T_ i=annX (armL o Lq Y) Bv i)(hc:Very_Ψ o X.p.B)
variable (h0:0<br)(hq:br≤bw)(ht:1≤ κw)(vH:1≤Hh)(hB:10≤ X.p.B)
variable (Xq:Niche R.L V' Z')(z1:V'*(Bv false).blade=bw)(z2:Z'*(Bv false).blade+(Bv true).blade=0)
variable (Pq:∀ i:Site (mid N B),let c(b):=Ione.duty_Q X.p.order X.p.power*Δτ*κBill Y G R.L χτ Hh i (κw*br) (soot br b);
    |V'| * c false≤κw*bw/4 ∧ThinGauge.boost (Xη R.L)*(|Z'| * c false+c true) ≤κw*bw/4)
include L_ hc
include z1 z2 vH Pq
lemma deckCost(i:PairKey I): Axon R.L.val (o i.1) X.p (νTip (minted R.L V' Z' o T_ Q).earn i) Hh (κw*bw/4) (soot bw i.2):=by
 let z(i):=(Bv i).blade; let D:= κw*br; let W:= o i.1; let j(b:Bool):=pick i.1 b; let c(b:Bool):= Ione.duty_Q X.p.order X.p.power*Δτ* κBill Y G R.L χτ Hh W D (soot br b)
 let E(b):=νTip T_ (j b)
 let a:= ThinGauge.boost (Xη R.L)
 have hb: 0<a:= by unfold a ThinGauge.boost Xη; apply div_pos ThinGauge.gain_pos; positivity
 have he(b:Bool):Axon R.L.val W X.p (E b) Hh (c b) (coat (z b)):=(L_.pulse (j b)).1
 let t(b):=(stone V' Z' a b i.2)
 change Axon _ _ _ (νTip (FlameX (sameY o) T_ (cobble I V' Z' (ThinGauge.boost (Xη R.L)))) i) _ _ _
 have hm:=aromaX V Xi o hc.1 (armL o Lq Y).X (armL o Lq Y).Y (armL o Lq Y).Z (soot br ∘ altQ) (fun i:PairKey I=>coat (Bv i.2).blade) (fun _:PairKey I=>D) 0 T_ Q L_ V' Z' a i
 rw [hm]
 have fs (b):= charge_ν (t b) R.L.val W (E b) (coat (z b)) X.p (c b) (zero_le_one.trans vH) (he b)
 have hπ:= Axon_add _ _ _ (fs false) (fs true) (zero_le_one.trans vH)
 have hcD(i b:ℝ):((i:ℂ) • coat b : ArcΦ)=coat (i*b):=by
    apply Prod.ext
    · change (i:ℂ) • paintS (b:ℂ)=paintS ((i*b:ℝ):ℂ); rw [coat_scale,Complex.ofReal_mul]
    change (i:ℂ) • (0:Hove.Dome)=0; rw [smul_zero]
 have haD(i j:ℝ):coat i+coat j=coat (i+j):=by
    apply Prod.ext
    · funext c d; change paintS _ _ _+paintS _ _ _=paintS _ _ _; unfold paintS; rw [Complex.ofReal_add]; split_ifs <;> ring
    exact zero_add _
 have hu:=Pq W
 cases H:i.2
 · have e:t false=(V':ℂ):=by simp[t,H,stone]
   have p:t true=0:=by simp[t,H,stone]
   apply turf_A (v:=‖t false‖*c false+‖t true‖*c true) _ _ _ _ _
   · rw [e,p,norm_zero,zero_mul,add_zero,Complex.norm_real,Real.norm_eq_abs]; exact hu.1
   change Axon _ _ _ (_ • E false+_ • E true) _ _ (coat bw)
   -- replace goal RHS t via H? HM. Goal after cases H in term dependent -> t remains .2. inspect
   have hl:t false • coat (z false) + t true • coat (z true)=coat bw:=by rw [e,p,zero_smul,add_zero,hcD V' (z false),z1]
   rw [hl] at hπ
   conv at hπ=> enter [4]; dsimp [t]; simp only [H]
   exact hπ
 · have e:t false=((a*Z':ℝ):ℂ):=by simp[t,H,stone]
   have p:t true=(a:ℂ):=by simp[t,H,stone]
   have hl:t false • coat (z false)+t true • coat (z true)=coat 0:=by rw [e,p,hcD,hcD,haD,mul_assoc,←mul_add,show Z'*z false+z true=0 from z2,mul_zero]
   rw [hl] at hπ
   apply turf_A (v:=‖t false‖*c false+ ‖t true‖*c true) _ _ _ _ _
   · rw [e,p,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_pos hb,mul_assoc,←mul_add]; exact hu.2
   conv at hπ=> enter [4]; dsimp [t]; simp only [H]
   exact hπ
#print axioms deckCost
end Dyad
end YM.CF.Py
end
