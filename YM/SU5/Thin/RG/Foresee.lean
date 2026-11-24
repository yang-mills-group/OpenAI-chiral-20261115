import YM.CF.Vp929.Pre.Mosaic
import YM.SU5.Thin.RG.Marked

/-! # Purchase of enriched weather. Adapted from Mosaic. -/
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
local notation "Yf"=> εLeaf R.L
local notation "FΩ"=> allF R.L
local notation "CL" x:max=> dwidth R x
local notation "E" x:max=> sprayM D.pilot R ag x
variable {X G:ℝ→ℝ} {κq γq:ℝ}
local notation "πY"=> tablePad R c pW.C Pay x κq ρ h (sprayM D.pilot R ag x) γq
structure MarkForesee (D:Treaty J q A C' Pay h ρ)(c:Estimate)(X G:ℝ→ℝ)(P:WindV K.j 2)(ag Cg Bv:ℝ)(n:ℕ)(kC:ℝ)(sB:BudgetPoint)(hℓ:ℝ)(oμ Dκ:ℝ→ℝ) : Prop where
 cost : Estimate.Economic c R
 warm : Jade.warmK c.F
 bookK : sizeK R.L 1 X
 warmK : Jade.warmK X
 chart : sizeK R.L 1 G
 warmG : Jade.warmK G
 heat : ∀ n, sizeK R.L n (sprayM D.pilot R ag)
 forwards : ∀ᶠ x in atTop,Neon.TimΞ R.L 6 2 5 x hℓ (oμ x) sB ∧ ∃ M:stationary D c x ag Cg (X x) Bv n,∀ N0:ℕ,D.size+200≤ N0→ ∀ (m n:Side)(w:Location (R:=R) B m n) p p', w.Request V U W J q N0 x p p'→∃ o:Pitching w D x,∃ u:Cellar N0 o p p' c (allF R.L x) ag Cg, Weather M u P (G x) ∧ Monetary o c p p' (εLeaf R.L x) kC hℓ (oμ x) (Dκ x)

include D
lemma Weather.costlier{kC:ℝ}{sB:BudgetPoint}(DH:Treaty.Marked D kC sB) (g:Patron ag Cg)(pV:Framing nₐ Bv)(P:WindV K.j 2)(N0:ℕ): ∃ c:Estimate,∃ X G:ℝ→ℝ,∃ hℓ oμ Dκ, MarkForesee D c X G P ag Cg Bv nₐ kC sB hℓ oμ Dκ ∧ 0<hℓ ∧ sizeK R.L 4 oμ ∧ Litt R 2 Dκ ∧ N0≤ c.blips:= by
 have hv:∀ᶠ x in atTop,0≤ FΩ x ∧ 0≤ εLeaf R.L x:= (stockpile_ν (R:=R)).mono fun x t=> ⟨mul_nonneg (by norm_num) (mul_nonneg (zero_le_one.trans t.2.2.2) t.2.2.1.le), t.2.2.1.le⟩
 obtain ⟨c,c0,hC,hℓ,uℓ,oμ,Dκ,ζV,Dv,H⟩:= Treaty.cautions D DH (Stockpile.high (R:=R)) (Stockpile.low (R:=R)) hv g.pos (zero_lt_one.trans_le g.earns) N0
 have tF: Jade.warmK c.F:= H.mono fun x h=>⟨(h.2 D.size le_rfl).revenue,(h.2 D.size le_rfl).crew⟩
 obtain ⟨X,u,h⟩:= eventually_climate c0 g pV D.pilot; let G: Jade.warmK X:= h.mono fun x t=>⟨t.purse,t.step⟩; let S(n):sizeK R.L n (sprayM D.pilot R ag):=sinks g.pos n
 obtain ⟨Gv,v,Kμ,Eμ⟩:= grantFair u G S (h.mono fun x t=> t.pulse); refine ⟨c,X,Gv,hℓ,oμ,Dκ,⟨c0,tF,u,G,v,Kμ,S,?_⟩,uℓ,ζV,Dv,hC⟩
 filter_upwards [stockpile_ν (R:=R),tableDeemed (pW:=P) (A:=A) (Pay:=Pay) u G v Kμ S c0 tF D.high D.pos, H, h, hv, Eμ, delivery (A:=A) (pW:=P) (Pay:=Pay) u G v Kμ S c0 D.pos D.high nₐ, progP 2 6 100,Work.E01.radiusB_tendsto.eventually_ge_atTop (J.n+J.n+cipherK J.n+3)] with x t a' H' h hx Eμ Vx g W0
 refine ⟨H'.1,h,fun n0 e m n w p p' v'=>?_⟩; let PV:= H'.2 n0 (by omega); obtain ⟨o,po,pm⟩:=PV.provides m n w p p' v'; let pG:= Cellar.to_cellar po (by omega) (PV.norm D) v' hx.1 t.1
 refine ⟨o,pG,⟨⟨po,?_,?_,g,(by omega),?_ , t.2.2.1,?_⟩,Eμ p,a',Vx⟩,pm⟩
 · have f:= h.speed; rw [v'.boot'.B]; omega
 · have q:=(Nat.mul_le_mul_right (radiusB x) (by omega:200≤n0)).trans v'.size; omega
 · unfold allF; have he:= t.2.2.2; nlinarith [t.2.2.1]
 rw [v'.boot.B]; omega
theorem MarkForesee.foresee {kC:ℝ}{sB:BudgetPoint}{hℓ:ℝ}{oμ Dκ:ℝ→ℝ} (p: MarkForesee D c X G pW ag Cg Bv nₐ kC sB hℓ oμ Dκ) : Outlook D c X G pW ag Cg Bv nₐ:=by
 refine ⟨p.cost,p.warm,p.bookK,p.warmK,p.chart,p.warmG,p.heat,?_⟩
 filter_upwards [p.forwards] with x u
 obtain ⟨_,v,t⟩:=u; refine ⟨v,fun n e m m' w p p' h=> ?_⟩; obtain ⟨o,H,x,-⟩:=t n e m m' w p p' h; exact ⟨o,H,x⟩
end Focus
end Pitching
end YM.CF.Py.Rate
