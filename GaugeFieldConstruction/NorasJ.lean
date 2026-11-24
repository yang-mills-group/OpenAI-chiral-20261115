import GaugeFieldConstruction.AmusaJ
import GaugeFieldConstruction.SpursJ5
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
variable
  {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
  {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
  {w:Location (R:=R) B m n} {p p' : BudgetPoint}
  {o : Pitching w D x}
  {F:Corr (Scree.mid n B)}
  {N0:ℕ}
  {t bL σ κ Bv:ℝ}{nₐ:ℕ}{pW:WindV K.j 2}
  {κq γq:ℝ} {C:stationary D c x ag Cg κq Bv nₐ}{Z0:Cellar N0 o p p' c (allF R.L x) ag Cg}
  {r b0 b1 b2:ℝ} [Nonempty (Haro.ΘS r)]
  (s:Shop w J p p' q h x r)
  {nμ:ℕ}{Gχ v1 kf wC z b kc hℓ Dμ:ℝ}{Tφ:Hove.Grant K.j 2}
  (Pq:Pinewood R)
  {I:Type}[LinearOrder I][Fintype I]
  (u:ℂ)(tP:β∈Year R x)(K₀:Girt.BaseL U w.G (w.buildIn V p' β F u) w.coarse w.fine q J.d)(KΦ:Cusp (mid m B))(bQ:ℝ)(sq:HStmt (Z0:=Z0) (κq:=κq) (F:=F) (nₐ:=nₐ) s u tP K₀ KΦ b bQ kc hℓ Dμ)
  (Tp: Ids (mid m B))
  (D1 D2 D3 D4 NF Uω:ℝ)(NKey:ℕ)
open Mew Roots Connect Ing Ing.Iona CoeffArc Frugal
section
open Directory
variable {A':Type}[DecidableEq A'][Fintype A']
variable (P:Directory I A')(y:A'→ Seat (mid n B)) (R':P.TourF)(d':P.TourG)
local notation "Φ"=> P.F_v y
variable (E':Finset I→RegBudget (mid n B))(F':Finset I→ForceBudget (mid n B))
local notation "X1"=> Flank_P Φ E' F.1
local notation "K1"=> Flank_K Φ F' F.2
local notation "Xp"=> Pitching.start (V:=V) (w:=w) p β
variable (Jp:P.ToMG)(Kp:P.ToPC)(M_:I→Zone (mid m B))
variable (T_:Finset I→RegBudget (mid m B))(V_: Finset I→ForceBudget (mid m B))(ν:Finset I→Vow.Pax (mid m B))(η:Finset I→Vow.Cusp (mid m B))
local notation "ΤF"=> ((w.step V).ratio.parent∘ P.F_v y)
local notation "C0"=> (P.Ctags Jp Kp R.L d')
local notation "vT"=> (P.TransferX R.L (AxisPb y w V) d' Jp Kp)
-- carry enough credentials for Mark & fusion.Orb.β.
variable (Qu:Mende (Z0:=Z0) (κq:=κq) (F:=F) (v1:=v1) (kf:=kf) (b:=b) s Pq u tP KΦ Tp D1 D2 D3 D4 NF Uω NKey P y R' d' E' F' Jp Kp M_ T_ V_ ν η)
variable {I₁:Type}[LinearOrder I₁][Fintype I₁](T₀:Ids (mid m B))
variable {A₁:Type}[DecidableEq A₁][Fintype A₁]
variable (H₁:Directory I₁ A₁)(y₁:A₁→ Seat (mid n B)) (R₁:H₁.TourF)(d₁:H₁.TourG)
local notation "Φ₁"=> H₁.F_v y₁
variable (E₁:Finset I₁→RegBudget (mid n B))(F₁:Finset I₁→ForceBudget (mid n B))
local notation "X2"=> Flank_P Φ₁ E₁ F.1
local notation "K2"=> Flank_K Φ₁ F₁ F.2
local notation "Xp₁"=> Pitching.start (V:=V) (w:=w) p β
variable (J₁:H₁.ToMG)(K₁:H₁.ToPC)(M₁:I₁→Zone (mid m B))
variable (T₁:Finset I₁→RegBudget (mid m B))(V₁: Finset I₁→ForceBudget (mid m B))(ν₁:Finset I₁→Vow.Pax (mid m B))(η₁:Finset I₁→Vow.Cusp (mid m B))
local notation "ΤG"=> ((w.step V).ratio.parent∘ H₁.F_v y₁)
local notation "C1"=> (H₁.Ctags J₁ K₁ R.L d₁)
local notation "vB"=> (H₁.TransferX R.L (AxisPb y₁ w V) d₁ J₁ K₁)
-- carry enough credentials for Mark & fusion.Orb.β.
variable (St:Mende (Z0:=Z0) (κq:=κq) (F:=F) (v1:=v1) (kf:=kf) (b:=b) s Pq u tP KΦ T₀ D1 D2 D3 D4 NF Uω NKey H₁ y₁ R₁ d₁ E₁ F₁ J₁ K₁ M₁ T₁ V₁ ν₁ η₁)
variable {Y:Type}[Fintype Y][LinearOrder Y]
variable (S:Sweep (mid m B))
variable (d₀:Y→ℕ)(yν:Y→Seat (mid m B))(U₀:Y→Key I)(V₀:Y→Key I₁)
variable (oF:OnPlot (N:=m) (B:=B) d₀ ((w.step V).ratio.parent∘ P.F_v y) yν (P.depth∘ P.own) U₀)
variable (oG:OnPlot (N:=m) (B:=B) d₀ ((w.step V).ratio.parent∘ H₁.F_v y₁) (sh S∘ yν) (H₁.depth∘ H₁.own) V₀) 
variable (vFp:fortK≤ R.L.val)(eBC:CapeLen (mid m B) p R.L.val)(pC:300<(mid m B).val)(Q_:0< QLife R x)
variable (πg:∀ᶠ (i:Y→ℝ) in 𝓝 0,passingR (mid n B) (reSweep w.G S) ((Flank_P (P.F_v y) E' F.1) (LegQ U₀ i)) ((Flank_P (H₁.F_v y₁) E₁ F.1) (LegQ V₀ i))∧ passingF (mid n B) (reSweep w.G S) ((Flank_K (P.F_v y) F' F.2) (LegQ U₀ i)) ((Flank_K (H₁.F_v y₁) F₁ F.2) (LegQ V₀ i)))
include sq Qu St vFp eBC pC πg oF oG
variable (Z0':Y→Key I)(Z₁:Y→Key I₁)(hA:∀ i,(P.TransferX R.L (AxisPb y w V) d' Jp Kp) (Z0' i)=U₀ i)(hB:∀ i,(H₁.TransferX R.L (AxisPb y₁ w V) d₁ J₁ K₁) (Z₁ i)=V₀ i)
include hA hB
lemma mOrigin (z:Key Y): let zΩ:= SpotQ Z0' z; let z_x:= SpotQ Z₁ (Λpay S ∘z); passingR (mid m B) S (WritV ΤF T_ zΩ) (WritV ΤG T₁ z_x) ∧ passingF (mid m B) S (WritV ΤF V_ zΩ) (WritV ΤG V₁ z_x) ∧ passingFee (mid m B) S (WritV ΤF ν zΩ) (WritV ΤG ν₁ z_x) ∧ passingU_n (mid m B) S (WritV ΤF η zΩ) (WritV ΤG η₁ z_x) ∧ α_ξ (G_s M₁) (vB z_x)=Spire.payZ S (α_ξ (G_s M_) (vT zΩ)) :=by
 intro X H
 obtain ⟨_,Fz,Yb,Ku,Ωp,sqK,rfl,Vp,hF',rfl,rfl,rfl,rfl⟩:= Qu.picked; obtain ⟨_,Fq,Yq,Kq,Ωq,sqE,rfl,t₁,H₁',rfl,rfl,rfl,rfl⟩:=St.picked; -- rfl warnings
 have ho:100<(mid m B).val:=lt_trans (by norm_num) pC
 exact PolarCost s Pq u tP K₀ KΦ bQ sq X1 K1 (P.F_v y) Fz Yb Ku Ωp NF sqK X2 K2 (H₁.F_v y₁) Fq Yq Kq Ωq sqE S (P.depth∘ P.own) (H₁.depth∘ H₁.own) d₀ yν U₀ V₀ vFp eBC ho oF oG πg Tp T₀ C0 C1 Z0' Z₁ hA hB (fun i u=>(hF'.audit.ax i).2 _) (fun i u=>(hF'.audit.force i).2 _) (fun i u=>(H₁'.audit.ax i).2 _) (fun i u=>(H₁'.audit.force i).2 _) z
#print axioms mOrigin
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
