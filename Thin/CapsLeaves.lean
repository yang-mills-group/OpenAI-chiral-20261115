import Thin.CapsRime
import Thin.CapsCoal
import YM.CF.Rive.Greet
import YM.CF.Rive.Cart

/- Adapted from YM/CF/Rive/Greet.lean for the NoSlip, capped ScaledV use below. -/
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
include Pinc L0 A_ A₁ heV hz hz' hq hy hT wV h2 vΞ bQ
open Larch
lemma leaf_X_Th(z: Mew.Key Q₁)(p:z∈hill Q₁):
 let E:= (Bν z)-(Bν 0) - (old_Q (F0 z)-old_Q (F0 0)); let F:= old_Q (F0 z)-old_Q (F0 0)
 (∀ x:Aura (mid N B),∀ V: Orbit (mid N B),¬ visible H₁.p x.val ∅ V.1 → F x V=0) ∧∃ A U: Aura (mid N B)→ℝ,(∀ i:Aura (mid N B),Medal H₁.p i.val ∅ (E i) HH (A i))∧ (∀ o:Seat (mid N B),tallB A H₁.p.B (tolQ H₁.p).supportExponent o ≤ Kk⁻¹ * Pδ 1+ Kk⁻¹ *Pδ 1) ∧ (∀ i:Aura (mid N B),Medal H₁.p i.val ∅ (F i) HH (U i))∧(∀ o:Seat (mid N B), tallB U H₁.p.B (tolQ H₁.p).supportExponent o ≤ Kk⁻¹ * Pδ 0+Kk⁻¹ *Pδ 0):=by
 intro E F'
 let K'(u) (i:Aura (mid N B)):=∑ j∈outerR S r₁,TΞ u i j; let H'(u):= dusk_A H₁.p (Ys u) HH
 let β(i)(p:i∈hill Q₁)(x y):= ((Pinc i p).quiet x y).toLullT
 have h(i)(p:i∈hill Q₁)(k:Troupe S r₁ (Words S))(U':Aura (mid N B))(q':(penn S k).flags=∅): Medal H₁.p U'.val ∅ (F0 i k U') HH (TΞ i U' k):= by
    refine cab_f V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) (L0 i p) k₀ k₁ s0 A_ A₁ heV hz' hq hz _ _ (Pinc i p) (half_lt_self hy) (half_pos (Lx i).legal.1) (half_lt_self (Lx i).legal.1) (fun j v p=>(hT Y_ j v p).1) (by rw [bQ]; exact Nat.le_trans (by norm_num) Y_.fireK.blade) U' k q'
 have hK(i p j): Medal H₁.p j.val ∅ (shot_Q (F0 i) j) HH (K' i j):=Medal.sumP _ _ _ fun x hx=> h i p x j (mem_filter.mp hx).2.1 -- tune
 have hU(i p j): Medal H₁.p j.val ∅ (old_Q (F0 i) j) HH (H' i j):= Medal.sumP _ _ _ fun x y=> h i p x j (elder_q x (mem_filter.mp y).2)
 have hx:= growth_S_Th V Xo Yo Zo M' Lx Y_ U_ w' F0 Ys L0 Pinc wV h2 vΞ bQ hz
 have hv(i pa y):= old_V_Th V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) hz bQ _ _ (Pinc i pa) h2 wV (vΞ i pa) y
 refine ⟨fun x v t=>?_ ,K' z+K' 0,H' z+H' 0,fun i=>?_ ,fun o=>?_ ,fun x=>?_ ,fun o=>?_ ⟩
 · have hp (i)(pi:i∈hill Q₁):old_Q (F0 i) x v=0:=by
      unfold old_Q; rw [Finset.sum_apply]; apply sum_eq_zero; intro j w; apply (β i pi j x).wherep; simp_rw [show Stilo.bay (Stilo.beamH x.val)=x.val from bay_beam _, show (cook S j.toLeft).flags=∅ from elder_q j (mem_filter.mp w).2]; rintro ⟨q,p,a⟩; apply t; exact ⟨q,p.1,a⟩ -- `p.1`
   unfold F'; rw [Pi.sub_apply,Pi.sub_apply,hp z p,hp _ roots,sub_self]
 · unfold E; rw [Pi.sub_apply,Pi.sub_apply,Pi.sub_apply,coin_r V Xo Yo Zo M' Lx Y_ U_ w' F0 β i z p,add_sub_cancel_left, sub_eq_add_neg]; exact (hK z p i).plus (hK 0 roots i).negT
 · rw [Larch.tall_add]; exact add_le_add (hx o z p) (hx o 0 roots)
 · unfold F'; rw [Pi.sub_apply, sub_eq_add_neg]; exact (hU z p x).plus (hU 0 roots x).negT
 rw [Larch.tall_add]; exact add_le_add (hv z p o) (hv 0 roots o)
end YM.CF.Rive
end

/- Adapted from YM/CF/Rive/Cart.lean for the NoSlip, capped ScaledV use below. -/
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
lemma talent_Th (u0:oδ ≤ 10*H₁.p.B):
 let I(z:Mew.Key Q₁):= pence_v H₁.p (Ys z) HH
 (∀ i∈hill Q₁,Bake.Turf (fun x:Aura (mid N B)=> cone_f (F0 i) x ∅)) ∧(∀ (X:Aura (mid N B)) D v,River (fun z:Key Q₁=> cone_f (F0 z) X D v))∧(∀ (X:Aura (mid N B)) D,Hush (S.ratio.parent∘σ) X.val (fun z=>cone_f (F0 z) X D)) ∧∀ i∈hill Q₁, (∀ X:Aura (mid N B),∀ D⊆X.val,Stax.Fray H₁.p HH (cipherK k₀) X D (cone_f (F0 i) X D) ((I i) X D))∧∀ v:Seat (mid N B), tallB (Vow.hymn (I i)) H₁.p.B (tolQ H₁.p).supportExponent v ≤ Hh⁻¹*(grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0) ∧ tallB (Sour.urnL (I i)) H₁.p.B (tolQ H₁.p).supportExponent v ≤ grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0:=by
 intro I
 let g(i t U W):= ((Pinc i t).quiet U W).toLullT
 let Hq(i p):=pep_f V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) (L0 i p) _ _ _ A_ A₁ heV hz' hq _ _ (Pinc i p) (half_lt_self hy) (half_pos (Lx i).legal.1) (half_lt_self (Lx i).legal.1) (fun i t q=> (hT Y_ i t q).1)
 refine ⟨Hq,fun X D v=>?_ ,fun X D z hz w hw p=> ?_ ,fun i p=> ⟨fun X D v=>?_, fun y=>⟨snow_b_Th V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) (by assumption) bQ _ _ (Pinc i p) h2 wV (vΞ i p) y,?_⟩⟩⟩
 · unfold cone_f; simp_rw [Finset.sum_apply]; refine tick_sum _ _ fun j _=> ?_; exact silk_B V Xo Yo Zo hX hY hZ M' Lx Y_ U_ w' j X _ (fun i p=>g i p j X) Hp v
 · unfold cone_f; refine sum_congr rfl fun j _=>?_ ; exact hush_O V Xo Yo Zo M' Lx Y_ U_ w' σ ho hp hv j X _ (fun i a=>g i a j X) z hz w hw p
 · refine ⟨?_,fun x t=> ?_⟩
   · by_cases w:D.Nonempty; · have hvQ:= spiceF V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) (L0 i p) _ _ _ A_ A₁ heV hz' hq hz _ _ (Pinc i p) (half_lt_self hy) (half_pos (Lx i).legal.1) (half_lt_self (Lx i).legal.1) (fun i t q=> (hT Y_ i t q).1) (by rw [bQ]; exact Nat.le_trans (by norm_num) Y_.fireK.blade); exact hvQ.price _ D w v
     rw [Finset.not_nonempty_iff_eq_empty.mp w]; exact spiceX V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) (L0 i p) _ _ _ A_ A₁ heV hz' hq hz _ _ (Pinc i p) (half_lt_self hy) (half_pos (Lx i).legal.1) (half_lt_self (Lx i).legal.1) (fun i t q=> (hT Y_ i t q).1) (by rw [bQ]; exact Nat.le_trans (by norm_num) Y_.fireK.blade) X
   unfold cone_f at t; rw [Finset.sum_apply] at t; obtain ⟨j,v,t'⟩:= exists_ne_zero_of_sum_ne_zero t; obtain ⟨u,l⟩:= Salt.permit (Lx i) Y_ U_ w' j (beamH X.val) (F0 i j X) (g i p j X) x t'; have ht:= Salt.hostB (Lx i) Y_ U_ w' j (beamH X.val) oδ (by rwa [←bQ]) u; have hw: D=(penn S j).flags:= (mem_filter.mp v).2.symm; rw [hw]; exact ⟨by simpa only [bay_beam] using ht,l⟩ -- tune
 exact lad_e V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y_ (Lx i) hz bQ _ _ (Pinc i p) y
end YM.CF.Rive
end
