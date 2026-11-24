import YM.CF.Vp929.Kinematic.Lantern
import YM.CF.Vp929.Kinematic.Vise
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
local notation "y"=> Scales.y SU.group R.L x
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
namespace Lid
variable (H: Lid o p p' f)
variable {F F': Corr (Scree.mid n B)}
local notation "τ"=> radiusB x
variable (Mk: Monk SU.group (w.step V))(A₀:Ids (Scree.mid m B))(T₁:Ids (Scree.mid n B))
local notation "Rc" v:max=> poleY Mk v (Scales.y SU.group R.L x)
local notation "Δ" => (o.muster.post+90)*radiusB x
local notation "Δ₀"=> (D.pilot.hat R x)
local notation "χ"=> (shotM o.muster.vita)
variable (hF:Location.gross p' D f F)
variable {X X':Pilot}
local notation "θ"=> (vast (k:=D.Z.N1*τ) A')
local notation "Μ"=> Cipher ι
local notation "Λ" z:max l:max=> (H.lantern Mk A₀ T₁ z l hF)
local notation "Tt"=> o.muster.trot
local notation "Tr"=> o.muster.room
local notation "Tx"=> o.muster.post
local notation "δ"=> Jq Tt Tr Tx
private abbrev opQ (β:ℝ) (F:Corr η) (i:Rust η):= OpK S' x (Ys β F) (Rc β) T₁ (w.Φ (V:=V)) Tt Tr Tx i
include H
private lemma guard_t (i:Support (More η))(hb:β∈Year R x)(hb':β'∈Year R x): guardB S' x (Ys β F) (Rc β) Jq Tt Tr Tx i=guardB S' x (Ys β' F') (Rc β') Jq Tt Tr Tx i:= by
 unfold guardB; rw [show (poleY Mk β y).sent x Jq Tt Tr Tx (Ys β F).beta= (poleY Mk β' y).sent x Jq Tt Tr Tx (Ys β' F').beta from ((spirit_X o.muster Mk H.night (H.pos hb)).2.trans (spirit_X o.muster Mk H.night (H.pos hb')).2.symm)]; rfl
private lemma op_eq (hb:β∈Year R x)(i:Rust η)(F:Corr η): opQ (o:=o) (p':=p') Mk T₁ y F i= opQ (o:=o) (p':=p') Mk T₁ β F i:= by
 have Q(L:Lattice.Support (Domain n B)): guardB S' x (Ys y F) (Rc y) Jq Tt Tr Tx L=guardB S' x (Ys β F) (Rc β) Jq Tt Tr Tx L:= guard_t (p':=p') H Mk L H.living hb
 have U: (poleY Mk y y).sent x Jq Tt Tr Tx y= (poleY Mk β y).sent x Jq Tt Tr Tx β:= (spirit_X o.muster Mk H.night H.night).2.trans (spirit_X o.muster Mk H.night (H.pos hb)).2.symm
 unfold opQ OpK; cases i with
 | inl i=>  dsimp only [Sum.elim_inl, sheer]; rw [Q i.1.val.2,U]; rfl
 | inr i=> dsimp only [Sum.elim_inr,shineK]; rw [Q _,U]; rfl
variable (t:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V)))
local notation "B0"=> (penn S' t)
local notation "Hk" z:max l:max=> (Λ z l).stageT x Tx t
section
variable (z l:ℂ) (p0:Ride (w.step V))
lemma torso (hb:β∈Year R x)(hv:fends p p' o β X)(Lx: Bs β F):
    let U:=groupTide Mk A₀ T₁ X hv Lx
    (Hk z l).knots p0=(U.stageT x Tx t).knots p0 ∧ (Hk z l).voice=(U.stageT x Tx t).voice ∧ (Hk z l).rhythm p0=(U.stageT x Tx t).rhythm p0 := by
 intro U; have Q(Rt): (Λ z l).blocks Rt= U.blocks Rt:= (H.qori Mk A₀ T₁ H.living hb (H.crew y H.living).1 hv (H.choice H.living hF) Lx Rt).2
 refine ⟨?_,?_,?_⟩
 · change (Λ z l).heatT t p0= U.heatT t p0; unfold Eire.Dress.heatT Eire.Dress.coats; rw [Q]; rfl
 · let t0:=penn S' t; let f (β):= opQ (o:=o) (p':=p') (Eire.trot S' Mk t0) T₁ β F; have e: (Λ z l).bodyL x Tx t= U.bodyL x Tx t:= prod_congr (s₁:=t.toRight.toLeft) (f:=f y) (g:=f β) rfl (fun i _=> H.op_eq (Eire.trot S' Mk t0) T₁ hb i F)
   exact congrArg Subtype.val e
 · let f(Pq:Rill.Arch w.G d):= Eire.paint S' (20*τ) o.bags o.SheepR.dyes Pq.val.1.1 Pq.val.2 T₁ t.toLeft (Plume.walksK T₁); exact congrArg f (Q (penn S' t))
end
lemma tenor (hb:β∈Year R x)(hv:fends p p' o β X)(Lx: Bs β F)(g:X.cost=D.pilot.cost)(v:X.s=D.pilot.s) : Hk (β:ℂ) (χ (X.hat R x) β:ℂ)=(groupTide Mk A₀ T₁ X hv Lx).stageT x Tx t:=by
 let l:ℂ:= χ (X.hat R x) β; let Lz:= Λ (β:ℂ) l; let Ω:=groupTide Mk A₀ T₁ X hv Lx
 have Dp : Lz.brew t= Ω.brew t:= by unfold Eire.Dress.brew; dsimp only; refine congrArg₂ (·*·) (prod_congr rfl fun i hi=>(H.jewelReal Mk A₀ T₁ B0 i g v hb hv Lx).symm) (prod_congr rfl fun i hi=>(H.crownReal Mk A₀ T₁ B0 i g v hb hv Lx).symm)
 have h:= fun p=>H.torso Mk A₀ T₁ hF t (β:ℂ) l p hb hv Lx
 have code : ∀ (U V:ModeW (Eire.mint S') Eire.rayB (BranchX S' θ Δ) t), U.knots=V.knots→U.voice=V.voice→U.rhythm=V.rhythm→U.diet=V.diet→ U=V:=by intro U V P Q R F; cases U; cases V; congr
 exact code _ _ (funext fun i=>(h i).1) (h ⊥).2.1 (funext fun i=>(h i).2.2) (funext fun i=>congrArg Subtype.val Dp)
lemma cap_t (z l:ℂ)(P0: Ride (w.step V)): (Λ z l).blazon x Tx t P0= if capG S' (flags (temp x) Mk.V) (chillB Mk) p'.threshold t P0 then Scion.vigor ((Λ z l).stageT x Tx t) P0 else 0:= rfl
-- evaluated blazon at any hat; no support restrictions
lemma blazon_on (P0:Ride (w.step V))(hb:β∈Year R x)(hv:fends p p' o β X)(Lx: Bs β F)(g:X.cost=D.pilot.cost)(v:X.s=D.pilot.s): (Λ (β:ℂ) (χ (X.hat R x) β:ℂ)).blazon x Tx t P0=(groupTide Mk A₀ T₁ X hv Lx).blazon x Tx t P0:=by rw [cap_t,Eire.Dress.blazon,H.tenor _ _ _ hF t hb hv Lx g v]; rfl
end Lid
end Pitching
end YM.CF.Py.Rate
