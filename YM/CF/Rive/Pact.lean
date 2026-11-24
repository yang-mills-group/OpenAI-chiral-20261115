import YM.CF.Rive.Bond
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
include hX hY hZ
lemma curl_o (i:Rust (mid P B)): Mew.River (fun z=> OpK S x (P0 z) Mk T₁ T H.trot H.room H.post i):=by
 let W:= Mk.sent x T H.trot H.room H.post H₀.beta; let t:= warmY S H₀ Mk; let s:= guardB S x H₀ Mk T H.trot H.room H.post
 cases i with
 | inl i=>
    let U:=i.1.val.2; change Mew.River (fun z:Key Q₁=> if t U then s U • (exp (if i.2 then Xo z i.1 W else Yo z i.1 W)-1) else 0); by_cases g:t U; swap; · simp_rw [if_neg g]; exact zeroR _
    simp_rw [if_pos g]; let G(z:Key Q₁):= if i.2 then Xo z i.1 W else Yo z i.1 W; have ht:River G:=by unfold G; split; exact hX ..; exact hY ..
    -- real smul constant via complex
    have hp:= dub_V ht.exp_V (zeroR (- (1: Cipher (mid P B)))); exact (River.scale hp (↑(s U))).cong (fun z _=>by change _ • (exp (G z)-_)=(s U:ℂ) • (exp (G z)+ -_); rw [sub_eq_add_neg]; rfl)
 | inr i=>
    let U:=i.val.1.val.2\i.val.2; change Mew.River (fun z:Key Q₁=> if t U then s U • Zo z i (W,T₁) else 0); by_cases g:t U; swap; · simp_rw [if_neg g]; exact zeroR _
    simp_rw [if_pos g]; exact ((hZ i (W,T₁)).scale (↑(s U))).cong (fun z _=>rfl)
lemma mint_T (t':Troupe S r₁ (Words S))(O:Ride S): River (fun z:Key Q₁=> (G' z).blazon x H.post t' O):=by
 let Zs:= penn S t'; let η:=capG S (flags (temp x) Mk.V) (chillB Mk) H₀.p.threshold t' O; let g(z):= (G' z).stageT x H.post t'; let c:= t'.toRight.toLeft; let M:= Eire.trot S Mk Zs
 have he(S':Finset (Rust (mid P B))):River (fun z:Key Q₁=> Eire.lure S x (P0 z) M T₁ T H.trot H.room H.post S'):=by
    unfold Eire.lure; induction S' using Finset.induction_on with
    | empty=>simp_rw [prod_empty]; exact zeroR _
    | insert i s v ih=>simp_rw [prod_insert v]; exact River.mul_T (curl_o (H:=H) M T₁ Xo Yo Zo hX hY hZ i) ih
 unfold Dress.blazon; by_cases l:η; swap; · simp_rw [if_neg (show ¬capG _ _ _ _ t' O from l)]; exact zeroR _
 simp_rw [if_pos (show capG _ _ _ _ t' O from l)]; exact vigR g O fun i=> canal g i (sc_V (he c) sheen) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)
end YM.CF.Rive
#print axioms YM.CF.Rive.curl_o
