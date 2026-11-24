import YM.CF.Vp929.Stage.Stores
import YM.SU5.Intrinsic.Rate.Conveyor

/-! # R124 boost the tapped component of the assembled Shop using its exact Lz formula. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'

open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
open Engine Engine.Basin Engine.Docket Dialect
local notation "T_"=> Troupe S' z' (Words S')
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "De"=> T_→ Lo→ Raid D'
local notation "PZ"=> T_→Lo→ Orbit ι→ Cipher ι
local notation "oWell"=> o.muster
local notation "Loχ"=> Palot.leaf (Site (Domain m B))
local notation "Px"=> V_→Loχ→ Orbit ι→ Cipher ι
local notation "Kx"=> V_→ Loχ→ Raid (Scree.Dwell ι)
open Vow Bake Salt Stax Sour Larch
local notation "Θ'" t:max=> (cook S' (Finset.toLeft t)).flags
local notation "δ_"=> (cipherK J.n)
local notation "U_"=> (fullD (n:=ι))
variable {t bL σ κ Bv:ℝ}{nₐ:ℕ}{pW:WindV K.j 2}
variable {Z:Cellar N0 o p p' c f ag Cg} {M:Climate D.pilot R c x t bL σ κ ag Cg Bv nₐ}
namespace Focus
variable (Uq:Focus Z M pW ff)(Ty:Ids (Scree.mid m B))
local notation "Upp"=> ((tolQ p).supportExponent)
variable (Q:β∈ Year R x)(hF:Charged p' w.input K.j R.L.val h f F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> Xs β
local notation "F_"=> (Z.toLid.crew β Q).1
local notation "A0"=> (Z.toLid.choice Q (gross_shape hF (le_refl f)))
variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}
open Appel.Rate Stockpile
variable {κq γq:ℝ}

local notation "ΦTap" κ:max x:max γ:max=> coinW R x κ 1 (ticket_f (radiusB x) γ 1+burnQ R x κ 1)
variable (tF:Charged p' w.input K.j R.L.val h ff F){γ:ℝ}
include Q Uq tF
lemma tapped_support (pβ:(β:ℂ) ∈ Ledge nₐ t (Scales.y SU.group R.L x))(hk:Fair p R x κ γ σ) (hv:Rill.Arch w.G d) (hm:hv.val=1) : let L:= Banker.Phi Z (β:ℂ) F; IncX Utrue (tapped p o Ty L) (plusOneRate p) h (ΦTap κ x γ):= by
 intro L
 let pP:= gross_shape (D:=D) tF Uq.cost
 obtain ⟨X,hX⟩:= Banker.Hoisted Z pP M pβ
 let hp := (Uq.live_state Ty Q hv hm hk tF pβ).spirit
 obtain ⟨uP,tP⟩:= hp.livelihood Uq Ty hk hX zero_le_one (by norm_num); let Q:=Cash.priceSurcharge D.high Ty tP uP
 let H:=pertainsS Uq Ty hp.seed hX hp; unfold coinW; conv in wren_K _ _ => rw [← Z.request.boot.order,←Z.request.boot.power]
 rw [show reserveT 2 6 (radiusB x) 1=reserveT p.power p.order p.B 1 from by rw [Z.request.boot.order,Z.request.boot.power,Z.request.boot.B]]; exact Ione.addT (plusOneRate p) H Q
omit Q Uq tF

/- In fact, we can pay the charge for `tapped` with shrinking cost even
at this extra rate (sizeK L 1). The scalar `Planner:credit` may want less
(`dleaf`). Do not bound this component alone by `dleaf`. -/

lemma scheduled_port {Lk G:ℝ→ℝ}(u:sizeK R.L 1 Lk)(t:Jade.warmK Lk)(v:sizeK R.L 1 G)(g:Jade.warmK G) : sizeK R.L 1 (fun x=> ΦTap (Lk x) x (G x)):=
 coinY u t (sizeK.mild R.L 1) ((feeK v g).accrue (sustain u (sizeK.mild _ 1) t)) -- test order names

section
local notation "FΩ"=> (allF R.L x)
local notation "Ef"=> εLeaf R.L x
local notation "Λ"=> thinR R x
variable {C:stationary D c x ag Cg κq Bv nₐ}{Z0:Cellar N0 o p p' c (allF R.L x) ag Cg}(T:Weather C Z0 pW γq)(Vq:Rill.Arch w.G d)(hv:Vq.val=1)
local notation "βΛ"=> Ledge nₐ (dwidth R x) (Scales.y SU.group R.L x)
local notation "Tρ"=> εp R Pay pW.C x
local notation "ψ"=> pre_Phi Z0
local notation "E_s"=> sprayM D.pilot R ag x
local notation "Aρ"=> τa R c x κq (sprayM D.pilot R ag x) h Pay γq
local notation "mK"=> τk R c x κq (sprayM D.pilot R ag x)
local notation "mF"=> τp R c x κq (sprayM D.pilot R ag x)
local notation "PE"=> Pre_T (Z:=Z0) Ty Vq
local notation "PA"=> Pre_A (Z:=Z0) Ty Vq
open Tap Lilt Sour.MatchW Technique
local notation "Tu"=> (T.toFocus)
local notation "Cl"=> Client K R x w.input p' h
local notation "Uφ"=> Banker.Phi Z0
include T Ty Vq hv
lemma addressed_pressure (pK:Cl (β:ℂ) (F,0)): IncX Utrue (tapped p o Ty (Uφ β F)) (plusOneRate p) h (ΦTap κq x γq):= by
 let v:=(matured Ty T Vq hv _ pK).1; exact tapped_support T.toFocus Ty (T.member v pK.1) (v.mono (by have ht:=T.buy; linarith)) (T.ledge _ pK.1) T.fair _ hv
end
end Focus
end Pitching
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pitching.Focus.addressed_pressure
#print axioms YM.CF.Py.Rate.Pitching.Focus.scheduled_port
