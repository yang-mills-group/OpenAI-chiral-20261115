import WinterX.Pantry
import Thin.CapsLeaves
import YM.CF.Rive.Lyric
import YM.CF.Rive.Lob

/- Adapted from YM/CF/Rive/Lyric.lean for the NoSlip, capped ScaledV use below. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Oise Mew
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
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
local notation "sN"=>mid N B
local notation "θo"=> Hest.Budget R.L R.odd_side Y.P.den X.P.den G Y.M K.j
local notation "Δ"=> shipA G U Y.M Y.P.den Y.I X.I
local notation "TΦ"=> (Thera.yet_one)
-- expose program β for ALL basis. Output C history ζ trial independent. avoid choices depend on post path.ClockB. Stencil projection sizes. Integrated maturity of L.
open Corne
-- STEP TAKE. define substance tested with Apert budgets.B. K n with k in Sheep input. Not requiring CPS mu on β.L.path
variable {ρ α γ:ℝ}{F:Pilot}{Z:Pluck R}{P₁ P₂:BudgetPoint}
local notation "τ"=> (radiusB x)
open Girt Eire
variable{H₀: GramM (mid P B)}{H₁:GramM (mid N B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{pK L':ℝ}{q q':Chi}{H:Muster G S x d T}
variable {Q₁:Type}[Fintype Q₁][LinearOrder Q₁]
variable (Mk:Monk SU.group S)(A₀:Ids (mid N B))(T₁:Ids (mid P B))
variable (Xo Yo:Mew.Key Q₁→ RegBudget (mid P B))(Zo:Mew.Key Q₁→ForceBudget (mid P B)) -- no scalar change
local notation "P0" i:max=> color_b H₀ H₀.beta (Xo i) (Yo i) (Zo i) H₀.v
variable(hX:∀ i U,River (fun z:Key Q₁=>Xo z i U))(hY:∀ i U,River (fun z:Key Q₁=>Yo z i U))(hZ:∀ i U,River (fun z:Key Q₁=>Zo z i U))
variable {r₁:ℕ}
variable (M':Sheep V U W G H₀.J H₁.J (k+2) n A)
-- extend trivial outside ball to all Ward variant. no estimates there.
variable (Lx:∀ v: Key Q₁,Girt.BaseL U G (color_b H₀ H₀.beta (Xo v) (Yo v) (Zo v) H₀.v) G₀ G₁ q' pK)
variable (Y_:Fend V H M' Z F q H₀.p H₁.p γ α j l r₁)(U_:∀ X: Support (Domain P B), Lend P B d X)(w':Hive.Vista U H₀.J.M H₀.J.P U_ (k+2) M'.q ((Fintype.card Play:ℝ)*L') M'.lot M'.tone)
local notation "G'" v:max=> GroupD Mk A₀ T₁ (H₁:=H₁) (Lx v) Y_ U_ w'
open Stilo
open Jade Pail Nor Yaw Pig Wray
variable {u:Key Q₁}(F0:Mew.Key Q₁ → Troupe S r₁ (Words S)→ Palot.leaf (Site (Domain N B))→ Orbit (mid N B)→ Cipher (mid N B))(Uq: ∀ u∈hill Q₁,∀ i X, LullT V F Z (X:=H₁) (Y:=color_b H₀ H₀.beta (Xo u) (Yo u) (Zo u) H₀.v) M' U_ w' Y_ (Lx u) i (Stilo.beamH X.val) (F0 u i X))
open Bake Vow Lilt
variable (Ys:Mew.Key Q₁→ Troupe S r₁ (Words S)→ Palot.leaf (Site (Domain N B))→ Raid (LeanV (Single (mid N B)))) {HH LΞ Lx0 b Kk Hh:ℝ}{ι':ℕ}
variable (L0:∀ u∈hill Q₁,StageP V H (color_b H₀ H₀.beta (Xo u) (Yo u) (Zo u) H₀.v) H₁ U)(Pinc: ∀ i∈hill Q₁, GroV V F Z (X:=H₁) (Y:=color_b H₀ H₀.beta (Xo i) (Yo i) (Zo i) H₀.v) M' U_ w' Y_ (Lx i) (Ys i) (F0 i) HH Lx0 1)(wV:1≤Kk)(h2:Kk ≤Hh)(vΞ:∀ i∈hill Q₁,ScaledV (fun i => min Hh (stampY Hh Kk i)) (tolQ H₁.p) HH Lx0 x 1 (Ys i))(bQ:H₁.p.B=radiusB x)(hz:0 ≤ HH)
local notation "Θ"=> (tolQ H₁.p).supportExponent
local notation "TΞ" z:max i:max j:max=> taxV H₁.p (Ys z) HH i j
local notation "PW"=> grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 1
variable (k₀ k₁:ℕ)(s s0:ℝ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x) (hz':s ≤ s0)(hq:s0 <d)(hy:0 < s)(hT:Stake.PondP V F x s pK j l (k+2))
local notation "PX"=> H₁.p
local notation "Pδ"=> grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0
local notation "Bν"=> fun i:Mew.Key Q₁=> (fun U:Aura (mid N B)=> cone_f (F0 i) U ∅)
variable {J_:ℕ}{cq vl:ℝ}(Hp:∀ i∈hill Q₁,LookZ V (Xm:=H₁) (Xu:=color_b H₀ H₀.beta (Xo i) (Yo i) (Zo i) H₀.v) M' Y_ (Lx i) U_ w' J_ cq vl)
variable (σ:Q₁→Site (Domain P B))(ho:∀ i:Scree.Hub (mid P B),Hush σ i.val.2 (fun z=> Xo z i))(hp:∀ i:Scree.Hub (mid P B),Hush σ i.val.2 (fun z=> Yo z i))(hv:∀ i:Force (mid P B),Hush σ i.val.1.val.2 (fun z=> Zo z i))
local notation "Dν" z:max=> cone_f (F0 z)
variable(Y1: Monk SU.group S)
include hT A_ A₁ L0 heV hz' hq hy wV h2 vΞ bQ hz Pinc
open Larch Cadre Sour Haro
local notation "oδ"=> (cipherK k₀)
local notation "K1" v:max=> pence_v H₁.p (Ys v) HH
include hX hY hZ Hp ho hp hv
variable (u0:cipherK k₀ ≤ 10*H₁.p.B)
open Sour Haro Tap Ione Larch Nor Stax Salt
open Push.AbsoluteSums Trees
local notation "BN"=> (Scree.mid N B)
variable {R0:Tulip.Male} -- remove
variable (qK:QuotaH V.f V.g V.F1 V.F2) {RA a₀ b₀ c₀:ℝ}{qL:Mast SU.group (Domain N B)} [Nonempty (ΘS RA)] (AA: BondL (Py.tatE V qK (mid N B)) (Py.tagE V qK (mid N B)) (body_Q (N:=(mid N B)) RA) b₀ c₀ a₀ s0)(u':ΘS RA)(hR:TagT (Py.tatE V qK (mid N B)) (Py.tagE V qK (mid N B)) (body_Q (N:=mid N B) RA) s0)
variable{zB z0 z1:ℝ}(kZ:HopeT s0 z0 z1 H₁.p.order)(vt:H₁.p.threshold ≤ z1)(tH: H₁.p.threshold ≤ s)(hw:k₀+10 ≤ H₁.p.B)(hf:cipherK k₀ ≤ 5*H₁.p.B)(w0:1≤ HH)(vY:3≤ H₁.p.B)
local notation "Θv"=> AA.bead HH H₁.p
local notation "Dν_" z:max=> (fun Y:Aura (mid N B)=>Dν z Y ∅)
variable {d' v0 μa σ₀ κa γ0:ℝ}(hA:0 < a₀)(pp0:2*(wu H₁.p+2)*Fief.tileN 1≤ a₀/2/2*H₁.p.B)(r0:feeΨ H₁.p a₀ b₀ c₀ HH≤ d')(hw':0≤ d')(eP:1 ≤κa)(g0:grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0+κa*(Hh⁻¹*(grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0)) < μa)(qp:0 ≤ μa)(qa:spanV H₁.p.B*μa ≤1)(qd: spanV H₁.p.B * d' ≤ wΨ)(qc:d'+spanV H₁.p.B*d'*μa-(wΨ-spanV H₁.p.B*d')*μa<0) -- q' shadow rename
local notation "ψW"=> (spanV H₁.p.B*d'*μa+ spanV H₁.p.B*wΨ⁻¹*μa*d')
local notation "Ψz" i:max=> pivotS AA A_ (hy.trans_le hz') HH (cone_f (F0 i)) w0 vt tH hw hf vY kZ u'
local notation "WΦ" z:max=> (BondL.pivotS AA A_ (hy.trans_le hz') HH (cone_f (F0 z)) w0 vt tH hw hf vY kZ u')
local notation "Gv" z:max=> old_Q (F0 z)-old_Q (F0 0)
local notation "σr"=> Kk -- existing 
variable (hγ:0 < γ0)(htγ:degreePrice H₁.p.B γ0 wΨ < 1)
local notation "PE"=> (Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 1)+Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 1))
local notation "PK"=> (Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0)+Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0))
local notation "γx"=> degreePrice H₁.p.B γ0 wΨ
include w0 AA vt hA pp0 r0 hw' eP g0 qp qa qd qc hγ htγ tH hw hf vY hR kZ
open CF.Both
-- additional per-awakening credentials at this very pivot (economized by recomputing with the same inputs). NOTE \rhoL, timer resolution earned for every z, permits comparing even with another key dimension.
lemma amber_pantry_Th (po:μa+μa+σr*(PK+(PE+ψW+ψW))≤γ0): let fT(X:Cusp (mid N B)):=BondL.pivotS AA A_ (hy.trans_le hz') HH X w0 vt tH hw hf vY kZ u';
   ∀ z∈hill Q₁,PivotQual H₁.p HH γ0 (cone_f (F0 z)) (WΦ z) fT :=by
 let I(z):= K1 z; let Θi:=Θv; have hc:0 < Kk:=lt_of_lt_of_le zero_lt_one wV
 obtain ⟨pQ,hr,ha,hX'⟩:=talent_Th V Xo Yo Zo hX hY hZ M' Lx Y_ U_ w' F0 Ys L0 Pinc wV h2 vΞ bQ hz k₀ k₁ s s0 A_ A₁ heV hz' hq hy hT Hp σ ho hp hv (le_trans hf (by omega)) -- order
 let ℓ:=ρL H₁.p; let f0(z):=WΦ z
 let b:=widthK BN H₁.p.B; let a:= H₁.p.supportExponent+1+1
 have hu:0 ≤ spanV H₁.p.B:= Nat.cast_nonneg _
 have hu':0 <wΨ:=by norm_num [wΨ]
 have hℓ:0≤ℓ:=by unfold ℓ ρL wΨ; linarith [H₁.p.exponent_pos]; -- etc
 have hc':wΨ≤ wu H₁.p-wΨ*2:=by unfold wu wΨ; linarith [H₁.p.exponent_pos]
 have hd:ℓ+wΨ ≤ wu H₁.p-wΨ*1:=by unfold ℓ wu ρL wΨ; linarith only [hu'] -- numeric
 let f(z):= cone_f (F0 z); let T (i) (z):= Timer (Cadre.chip (cribR Θi) (I z)) Θi κa (wu H₁.p) wΨ b (spanV H₁.p.B) μa d' (spanV H₁.p.B*d') d' i Θi
 have hb:0 ≤ Θi:=((AA.litB A_ (hy.trans_le hz') HH w0 kZ vt tH hw hf vY u').buys vY hz).dice
 have hE(o:Seat (mid N B)):nook (Θi*loom_v (wu H₁.p+2) 0 b 0) o≤d':= (AA.duty HH H₁.p (wu H₁.p+2) hA (by unfold wu; linarith [H₁.p.exponent_pos]) pp0 o).trans r0
 have ht(z)(p:z∈hill Q₁):T 1 z:=by
    let N':=I z; have hX:= hX' z p; have he(o:Seat BN): nook (roofL N' κa * loom_v (wu H₁.p) wΨ b 0) o < μa:=by rw [←parse, mul_zero,sub_zero,age_t]; obtain ⟨u,g⟩:= hX.2 o; exact lt_of_le_of_lt (add_le_add g (mul_le_mul_of_nonneg_left u (zero_le_one.trans eP))) g0 -- notation
    exact Cadre.stallK _ eP _ _ b (vigor ..) μa d' hu'.le Θi N' (fun X D u=> (hX.1 X D u).merit.wage hz) hb hE hw' hu qp qa qd he (le_trans (le_trans hℓ (le_add_of_nonneg_right hu'.le)) hd) qc -- fix
 let U(z:Key Q₁):= Gv z
 let pH:= leaf_X_Th V Xo Yo Zo M' Lx Y_ U_ w' F0 Ys L0 Pinc wV h2 vΞ bQ hz k₀ k₁ s s0 A_ A₁ heV hz' hq hy hT
 let HXv(i x):= (hX' i x).1
 choose! C ha1 hC hQ Y Z1 p using fun z u=> black_Q AA A_ (hy.trans_le hz') w0 kZ vt tH hw hf vY I f HXv u' ht hℓ hu' hd eP U (fun x i p=>(pH i p).1 x) (fun i p=>(pH i p).2) le_rfl (by norm_num [wΨ]) hu' hγ htγ hc po z u -- result ∀ p
 obtain ⟨c0,c1,c2,c3⟩:=scale_G AA A_ (hy.trans_le hz') w0 kZ vt tH hw hf vY I f HXv pQ u' hR ht hℓ hu' hd eP (show a+wΨ≤ℓ from le_rfl) hu' hr (S.ratio.parent∘σ) ha (fun i p=> show T 2 i from {(ht i p) with ok:=by norm_num,boot:= hu'.le.trans hc'}) hc'
 intro fn i u
 refine ⟨?_,rfl,c0 _ u,_,ha1 _ u,hC _ u⟩
 intro sw Fb hv
 intro V' vT v D pr; refine Sour.BondL.teachAux AA A_ (hy.trans_le hz') HH w0 sw V' u' v (cone_f (F0 i)) kZ vt tH hw hf vY ?_ (pQ i u) (ht i u) hℓ hu' hd Fb (hv V' vT) D pr vT
 -- fray?
 exact HXv i u
#check Sour.BondL.teachAux
#print axioms amber_pantry_Th
end YM.CF.Rive
end