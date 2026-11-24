import Bay.C.Blush
import Bay.Estate
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
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

set_option autoImplicit false
open Mew Waxy Roots Rive Oise



open Rate LocalLimit Preparation Pitching Focus 
set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
local notation "VΔ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


section
variable (P:VΔ)
local notation "Λ_" => P.par
local notation "Yc" => P.run
lemma leafArc (s k i:ℕ)(p:s<P.run.uv k):
 let Y:= RootBook Yc i k (s+1); let a:=3*dleaf P.par.R.L (hat P.par.R.L P.par.x s)
 Arc_r Y P.par.h a a a:=by
 let T:=P.run.voyage i
 let R:= T.paths (P.run.uv k)
 obtain ⟨β,H,j,_⟩:=R.issued
 dsimp only [RootBook]
 rw [congrFun j _]
 let V:= R.paid.flow (R.paid.charged P.par.H H.toRealQ (s+1) p)
 have hx:0 ≤ 3*dleaf P.par.R.L (hat P.par.R.L P.par.x s):=
    mul_nonneg (by norm_num) ((R.paid.clocks s).leaf.le)
 exact ⟨⟨V.inc.weight,fun _ h=>False.elim h⟩, Provides.liftE P.par.h _ _ _ ((Vale.lye _ _ _).1) hx,
       ⟨V.dark.weight,fun _ h=>False.elim h⟩⟩
end

variable {P:VΔ}{M t:ℕ}{g:Outfit}
abbrev YFine(P:VΔ)(M t:ℕ)(g:Outfit):= Year P g M P.par.R.L.val t
open Till
open BPress (lscale lscale_one)

lemma streetDr {n:ℕ}(p:WaitZ P.par.R (powZ n) (YFine P M t g)):
 ∀ᶠ x in atTop,0≤YFine P M t g x ∧ YFine P M t g x ≤ pinpr P.par.R.L x:=by

 filter_upwards[Till.warm_gt P.par.R,p.eventually (ge_mem_nhds zero_lt_one)] with x a e
 let v:=YFine P M t g x
 have j:0≤v:= by
   unfold v YFine Year icedCost xPool
   positivity
 exact ⟨j,(le_mul_of_one_le_left j (one_le_pow₀ (lscale_one x):1≤powZ n x)).trans ((div_le_one a).mp e)⟩



abbrev JumpF (P:VΔ)(s:ℕ):=hat P.par.R.L P.par.x s
abbrev PriceF (P:VΔ)(M:ℕ)(g:Outfit)(t s:ℕ):=YFine P M t g (JumpF P (s+1))
abbrev DyeF (P:VΔ)(Gφ:ℝ)(s:ℕ):=colorsPhi P.par.R.L Gφ (JumpF P s)
abbrev WorkF (P:VΔ)(Gφ:ℝ)(s:ℕ):=3*dleaf P.par.R.L (JumpF P s) + DyeF P Gφ s
lemma plankF {n:ℕ}(Gφ:ℝ)(p:WaitZ P.par.R (powZ n) (YFine P M t g)):
 ∀ᶠ s in atTop, 0≤PriceF P M g t s ∧ PriceF P M g t s ≤ DyeF P Gφ s:=by
 let L:=P.par.R.L
 filter_upwards [((turnover P.par).comp (tendsto_add_atTop_nat 1)).eventually (streetDr p),
    (turnover P.par).eventually (pal_U L _ (Vale.pitch L)),(turnover P.par).eventually (colors_more P.par.R Gφ 1)] with s h j k

 refine ⟨h.1,h.2.trans ?_⟩
 rw [Function.comp_apply, hat_step]
 exact j.2.1.trans ((one_mul _).symm.le.trans k)

abbrev Edge (P:VΔ)(f:ℕ→ℕ→ℕ→Prop):Prop:=
 ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k,s+1<P.run.uv k→f s i k
lemma Dry.next {f:Berth→Prop}(d:Dry P f):Edge P (fun s i k=>f (takeUp P (s+1) i k)):= (tendsto_add_atTop_nat 1).eventually d
lemma Edge.and {f h:ℕ→ℕ→ℕ→Prop} (e:Edge P f)(d:Edge P h):
 Edge P (fun s i k=> f s i k ∧ h s i k):=by
 filter_upwards [e,d] with s u v
 filter_upwards [u,v] with i y t k l
 exact ⟨y k l,t k l⟩

structure Rib(P:VΔ) where
 n:ℕ
 Pay:ℝ
 kc:ℝ
 Γ:ℝ
 Tξ:Hove.Grant P.par.K.j 2
 Z:ℝ→ℝ
 W:ℝ→ℝ
 V1:ℝ→ℝ
 Kf:ℝ→ℝ
abbrev ArmX(P:VΔ)(b:Rib P):=works_X (K:=P.par.K) b.Tξ b.n 6 5 HI b.Pay b.kc b.Γ

abbrev SceneF (P:VΔ)(b:Rib P)(M s i k:ℕ) : Prop:=
 let x:=JumpF P s; let y:=P.run.voyage i; let r:=ArmX P b
 AstroFunding P.par.V P.par.U (apt (P.run.ir i) P.par.block P.par.R.L s) (Stem P.run i k s) (y.CapeT s) (y.CapeT (s+1))
   (RootBook P.run i k s) (RootBook P.run i k (s+1)) ((y.X (P.run.uv k)).wave s).val Chi.canonical P.par.J.d P.par.h
   (b.V1 x) (b.Kf x) (b.W x)
   r.delta r.f0 r.g0 r.g1 r.g2 (WorkF P b.Γ s) (DyeF P b.Γ s) (b.Z x) (cipherK P.par.J.n) M

structure TicketF(P:VΔ)(b:Rib P)(M:ℕ)(X:TintDemand):Prop where
 rates:BladeQ P.par.R b.Z b.W b.V1 b.Kf
 -- 
 minimum:((2+(M:ℝ))*strive_E 6)<(b.n:ℝ)
 wealth:0≤b.Pay ∧ 0≤b.kc ∧ 0≤b.Γ ∧ Taxi.DayT 6 b.Γ
 demand: crayon X P.par.K P.par.L b.Pay b.kc b.Γ b.Tξ ≤ P.par.R.L.val
 tariff: RateCover P.par.J Chi.canonical P.par.h P.par.N0 b.Pay b.kc b.Γ b.Tξ b.n P.par.P

lemma fRib {X:TintDemand}(p:Hammer P M X):∃b,TicketF P b M X ∧ Edge P (SceneF P b M):=by
 obtain ⟨n,Pay,kc,Γ,Tξ,h,x,y,z,i,v,_,_,_,u,g⟩:=p.cover
 obtain ⟨Z,W,U,Kf,L,e⟩:=g.scene
 exact ⟨⟨n,Pay,kc,Γ,Tξ,Z,W,U,Kf⟩,⟨L,h,⟨x,y,z,i⟩,v,u⟩, e.mono fun _ h => h.mono fun _ r k l =>r k (by omega)⟩
