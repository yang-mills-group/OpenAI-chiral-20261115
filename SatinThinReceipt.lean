import YM.CF.Vp929.Stage.Bundle
import YM.SU5.Fineness.Cordon
import YM.CF.Vp929.Budget.Offset
/-! # re-budgeting at fixed step. Reuse the arguments of Stage.Menu & Stage.Bundle.
 Compare log to kernel warrants, not bounding coarse offsets itself. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 150000
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

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau

open Sour Cycle929 Vow Sour.BondL
local notation "ι"=> Scree.mid m B
variable {r:ℝ}[Nonempty (Haro.ΘS r)]{Wk Aχ Γχ ψ₁ ψ₂ θ₁ θ₂ ξ₁ ξ₂ u0 Ep Ek Ea Λf γ z b0 b1 b2 b3 ν:ℝ}
local notation "Cl"=> Client K R x w.input p' h
local notation "μB"=> rainX R 2 x
local notation "XR"=> (V.L.path (w.lag+1))
local notation "fp"=> K.top.clip

variable {Lp:Depot (Scree.mid m B) (Scree.mid n B)}(qL:Lobby x h K w p p' J.n Lp u0 Ep Ek Ea)
variable {A0:Stakehouse (h:=h) p J w b0 b1 b2 r}{n₀:ℕ}(s: Major V Wk b0 b1 b2 b3 Aχ Γχ n₀)
local notation "dr"=> A0.dream
variable (Th: Mood p (512*Wk) h b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) r (Scales.g SU.group R.L x) Ep Ek u0 (rainX R 1 x) (rainX R 2 x) Λf ψ₁ θ₁ ξ₁ ψ₂ θ₂ ξ₂)
variable (S0: Cease p (V.L.path (w.lag+1)) K.top.clip Aχ Γχ K.below.width K.below.paths V.W.bar (Scree.mid m B))(Ty: Ids (Scree.mid m B))(t: 0≤ u0)

variable (X:Pair (Corr (Scree.mid n B)))
local notation "Ex"=> verseX (Lp:=Lp) (A0:=A0) Ty
local notation "Qx"=> stock_ξ (Lp:=Lp) (A0:=A0)
local notation "βν"=> β+w.movement V
variable {y:ℂ}{G H:Corr (Scree.mid n B)}{S:Set ℂ}

local notation "Kt"=> K.below
local notation "VE"=> shownP (A0:=A0) (Lp:=Lp) Ty
local notation "ZA"=> shownA (A0:=A0) (Lp:=Lp) Ty
local notation "Zβ"=> shownΦ (A0:=A0) (Lp:=Lp) Ty
local notation "Hc"=> houseP p K Aχ Γχ Λf
local notation "Ht"=> ηF p R K Γχ Λf
variable {Sh v m' C:ℝ}{ψ:Pair (Cusp (Scree.mid m B))}{Aτ:RegBudget (Scree.mid m B)}(Q:Cycle929.Coin p θ₂ ((rainX R 2 x)⁻¹ * ψ₂) Sh (rainX R 2 x) v)
local notation "Ωs"=> Larch.Cog_P p v (rainX R 2 x)


local notation "φC"=> makeK (A0:=A0) (Lp:=Lp) Ty
include qL Th s A0 S0 Ty Q
variable (pH:2*((Ea+ηF p R K Γχ Λf)+m') ≤ Sh)

include pH


/-- Keep also the price of the canonical cusp on *this actual operation*. -/
structure CuspTicket (p p':BudgetPoint) (x β:ℝ) (G:Corr (mid n B))(Lp:Depot (mid m B) (mid n B))(A0:Stakehouse (h:=h) p J w b0 b1 b2 r)
  (i:Haro.ΘS r)(Pν:Corr (mid m B))(ΔT fit:ℝ):Prop where
 body : let Ktt:= stock_ξ (Lp:=Lp) (A0:=A0) (rePoint i) (β:ℂ) (G,0); ∃ (μ:ℝ)(As:Cusp (mid m B)), Course p Ktt.1 (V.L.path (w.lag+1)) K.top.clip (β+w.movement V) (β+w.movement V-ΔT) Pν.1 As μ ∧ ZealQ As ∧ Packed p h (Cash.prominence p) As fit ∧ Pν.2=roomB p Ktt.1 As ∧ EdgeC p A0.dream.H A0.dream.pay (tatE V A0.letter (mid m B)) (tagE V A0.letter (mid m B)) (Lp.Vφ β (G,0)).1 Ktt.1 (Haro.riseV i) ∧ ∀ y:Orbit (mid m B), Rue.FleetS p.threshold y.1 → Palot.hGas (flags p.threshold y.1) (keyL p Ktt.1 (rebP Ktt.1) y)=Real.exp (μ+((V.L.path (w.lag+1)).inChannels K.top.clip p (β+w.movement V) y.1-(V.L.path (w.lag+1)).inChannels K.top.clip p (β+w.movement V-ΔT) y.1)) • (exp (exponentL p Pν.1 y.1)*fueled p Pν.2 y)
lemma movie_cusp (i:Haro.ΘS r)(hs:sunny (rePoint i))(pX:Cl (β:ℂ) (G,0))(E:RegBudget ι)(Q0:Cusp ι)(Δ:ℝ)(f0:PackSale p XR fp E Q0 Δ)(hP:Packed p h (Cash.prominence p) Q0 m')(hZ:ZealQ Q0) : let E1:=VE (rePoint i) (β:ℂ) (G,0); let βp:=Zβ (rePoint i) (β:ℂ) (G,0); let F:= E1.1+E; let F1:= φC (β:ℂ) (rePoint i) (G,0) (Q0,0); CuspTicket p p' x β G Lp A0 i (F,F1.1) (βp.re-Δ) Sh:=by
 intro E1 βp F F1; let X:=Qx (rePoint i) (β:ℂ) (G,0); let Vζ:= ZA (rePoint i) (β:ℂ) (G,0)
 obtain ⟨μ,p0,zp,zF,zX,e,x1,x2,x3,b2,hμs⟩:= house_real qL s Th S0 Ty Q.full pX i hs
 let A:= Vζ.1+Q0
 have hp: Course p X.1 XR fp (βν) ((βν)-(βp.re-Δ)) F A μ:= (show (βν)-βp.re+Δ=(βν)-(βp.re-Δ) from (by ring)) ▸ p0.packs f0
 let Ktt:=roomB p X.1 A
 have hx' : Pair.plus X=X.1:= by rw [Pair.plus,show X.2=0 from x3,smul_zero,add_zero]
 obtain ⟨g,k⟩:= (show MonoQ p h (ρL p) (rebP (Pair.plus X)) θ₂∧ Armed p h (Pair.plus X) ((μB)⁻¹*ψ₂) from (inkwell qL s Th Ty _ _ hs pX).2.1)
 rw [hx'] at g k; have Kp:F1=(Ktt,0):=by unfold F1 makeK; change theater p X (Vζ+(Q0,0))=(Ktt,0); have he: Vζ+(Q0,0)=(A,0):= Prod.ext rfl ((show Vζ.2+0=Vζ.2 from add_zero Vζ.2).trans x2); rw [he]; exact (congrArg (fun v:Pair (Cusp ι)=> theater p v (A,0)) (show X=(X.1,0) from Prod.ext rfl x3)).trans movie_real
 have hx: Packed p h (Cash.prominence p) A (Ea+Ht+m'):= ((house_r qL s Th S0 Ty _ pX _ hs).2.2.2.1).add hP
 have hu:0≤Ea+Ht+m':= Display.coin (Packed.team (dr).floor (by unfold Cash.prominence; linarith [p.exponent_pos])) A (Ea+Ht+m') hx
 have hm : Ea+Ht+m' ≤ Sh:=by linarith only [hu,pH]
 rw [Kp]; exact ⟨μ,A,hp,Cash.zealAdd zp hZ,hx.purse hm,rfl,e,hp.gas (dr).floor Q g⟩
end Focus
end Pitching
end YM.CF.Py.Rate

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

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Sour Stockpile Test TestW QuiltB
namespace Shop
open BudgetPoint
variable {r:ℝ}[Nonempty (Haro.ΘS r)]
variable (s:Shop w J p p' q h x r)
local notation "ι"=> Scree.mid m B
variable {y:ℂ}{G H:Corr (Scree.mid n B)}{S:Set ℂ}
local notation "φE"=> (houseP p K s.Aχ s.Γχ s.Λf)
local notation "VE"=> shownP (A0:=s.A0) (Lp:=s.Lp) s.Ty
local notation "Sch"=> Client K R x w.input p' h
include s
local notation "Zβ"=> shownΦ (A0:=s.A0) (Lp:=s.Lp) s.Ty
local notation "Θχ"=> (s.RepΔ)
local notation "zZ"=> (s.RepK)
local notation "τE"=> (s.RepE)
variable {F:Pair (Corr (mid n B))}
-- solved real wearable.
private lemma ΩBlink : s.pA 0=0∧s.hood 0=0∧s.hoodZ 0=0:= ⟨s.LogicA.dormant,funext fun i=>funext (fun x=>(s.logic_X i x).dormant), funext fun i=>funext fun D=>funext fun V=> (s.logic_Z i D V).dormant⟩
local notation "Bβ"=> (β:ℂ)
local notation "XG"=> (G,0)
local notation "Λχ"=> (s.pickW Bβ XG)
variable {price:ℝ}
lemma rep_point (p0:Sch Bβ XG): let b:=s.standby Bβ XG; let Δ:=Θχ Bβ XG; let F:= τE Bβ XG; let R:=zZ Bβ XG; CuspTicket p p' x β G s.Lp s.A0 b.1 (F.1,R.1) Δ.re s.Sh ∧ b.1.val=(s.pickW (β:ℂ) (G,0)).1:=by
 intro i Δ F R; let r₀:= i.1; obtain z: i=rePoint r₀:= s.real_I (s.sleepsW p0).1.1 (s.real_pick p0); have hi':sunny (rePoint r₀):= z ▸ s.homely p0
 let E:=s.pF Bβ XG; let U:=s.gear Bβ XG; let Q:= s.pA E.1
 obtain ⟨r,_,_,_,_,_,x0,x1,x2,hb,-⟩:= house_real (A0:=s.A0) s.qL s.s s.Th s.S0 s.Ty s.coin.full p0 r₀ hi'
 rw [←z] at x0 hb; change E.2=0 at x0
 have pZ: (s.pF Bβ XG).2=0:= x0; have hz':s.τz Bβ XG=Zβ (rePoint r₀) Bβ XG:= congrArg (fun i=>Zβ i Bβ XG) z; have h0: U=(U.1,0):=Prod.ext rfl (show U.2=0 from (congrArg s.hoodZ x0).trans s.ΩBlink.2.2); have ht:makeK (A0:=s.A0) (Lp:=s.Lp) s.Ty Bβ (rePoint r₀) XG (U.1,0)= R:= (by rw [←z,←h0]; rfl)
 have H:Δ.re=(Zβ (rePoint r₀) Bβ XG).re-Q:= by unfold Δ RepΔ; rw [hz',Complex.sub_re,prob_re,prob_re]
 have pL:= movie_cusp (A0:=s.A0) s.qL s.s s.Th s.S0 s.Ty s.coin s.pH r₀ hi' p0 (s.hood E.1) U.1 Q (s.careτ p0).1.1.piece.delivers (s.feeQ p0).1 (s.careτ p0).1.1.piece.zealed
 have he: r₀.val=Λχ.1:=congrArg Prod.fst (intent0 Λχ (mem_ball_zero_iff.mp (s.half_room (s.sleepsW p0).1.1)).le)
 change CuspTicket p p' x β G s.Lp s.A0 r₀ (F.1,R.1) Δ.re s.Sh ∧ r₀.val=(s.pickW (β:ℂ) (G,0)).1
 have hpz:F.1=(VE (rePoint r₀) Bβ XG).1+s.hood E.1:= by change (VE i _ _).1+s.hood E.1=_; rw [z]
 refine ⟨?_,he⟩; rw [H,hpz,←ht]; exact pL
end Shop
end Focus
end Pitching
end YM.CF.Py.Rate
