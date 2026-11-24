import SatinThinAbility
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
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
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
variable (s i k:ℕ)
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "XP" s:max=> RootBook Y i k s
local notation:max "S" s:max=> (VO).CapeT s

open Graph -- for recX

#check Shaft
variable {I:Type*}[Fintype I][LinearOrder I]
def Bright (ρ:ℝ)(A:FC I)(q:ℝ):Prop:=
 ∀ (G:Shaft I), ColumnDeal G.sell ρ → ColumnDeal (star G.buy) ρ → ‖G.glow A‖ ≤ q

/-- Literal on all uses, including marks without support conventions. -/
def Shines (ρ:ℝ)(W:Mark n)(q:ℝ):Prop:=
    ∀ x, Bright ρ (W x) q
variable {v z:ℝ}
structure GlowCost (C ρ:ℝ)(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ):Prop where
 buys : ∀ (A0:FC (Single (side Y i s)))(t:ℝ), Bright ρ A0 (Real.exp t) →
    ∀ (z:ℝ)(X:RegBudget (side Y i s))(J:RegBudget (side Y i s))(Y':ForceBudget (side Y i s)), MarketR (pertain (RootBook Y i k s) X J Y') P.h z→ let G:=RootBook Y i k s; let R':=(Y.voyage i).CapeT s; ∀ (w:Orbit (side Y i s))(g:Seat (side Y i s)→SU.E), ‖letterRead A0 (recX P.U (pertain G X J Y') R' w)‖ ≤ Graph.past G w.1 * Real.exp (z+ Cascade.angleFin G.J.M (side Y i s) P.K.j+t+C*metroStress P.K.j G R' w g)


lemma glowing (t':Drawbill P v):
 ∃ρ,1≤ρ ∧ ∀ s:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ, GlowCost v ρ Y s i k:=by
 obtain ⟨x,R,N,hx,u,rfl,hα,hP,hK⟩:= t'.bought
 refine ⟨45*(1+R),by linarith,?_⟩; intro s
 filter_upwards [(Papal.count_grows Y s).eventually_ge_atTop N] with i t k
 constructor; intro A0 t0 zB z X J F e G R' w g
 let b:= Cascade.angleFin G.J.M (side Y i s) P.K.j
 let ρ:=45*(1+R); let C:=2+ρ^2+(1+R)^2
 let hT:0< (↑(side Y i s).val:ℝ)^4:=pow_pos (by positivity) _
 let D':=C*metroStress P.K.j G R' w g
 let N':ℝ:=(↑(side Y i s).val:ℝ)^4
 let T:=fun x:ℝ=>Graph.past G w.1 * Real.exp (z+b+x*N'+t0+D'); have hT':Continuous T:=by unfold T; fun_prop
 have hV:Filter.Tendsto T (nhdsWithin 0 (Set.Ioi (0:ℝ))) (𝓝 (Graph.past G w.1 * Real.exp (z+b+t0+D'))):= by simpa only [ContinuousWithinAt,T,zero_mul,add_zero] using hT'.continuousWithinAt (x:=0) (s:=Set.Ioi (0:ℝ))
 letI:NeBot (nhdsWithin 0 (Set.Ioi (0:ℝ))) := inferInstance -- tune nebot
 let q':= side Y i s; let E':= RootBook Y i k s; let Q:=spar P.K.j E'.J.M (1:Pane q'); have hQ:IsStarProjection Q:= (P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) E'.J.M).projection _ (guard0 P.dpos.le)
 change _ ≤ Graph.past G w.1*Real.exp (z+b+t0+D')
 apply ge_of_tendsto hV
 filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ)) (a:=0)] with ε hε
 obtain ⟨m,hm⟩:= (CF.Papyrus.Franc.purge P.K.j (by rw [P.kJ]; decide) ε hε).exists
 have hp:= seeMarket Y s i k w X J F A0 e g u hQ hx m t0 hP (hK _ t (R' w) ((Papal.roofage Y i s).paid w) E'.J.M) hα (zB _ (metroBuy g hQ hα m).1 (metroBuy g hQ hα m).2)
 refine hp.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (Real.exp_pos _).le)
 let u:= stunt m (tickA q') Q; have ht:u≤ b+ ε*N':=hm q' E'.J.M hQ; change z+u+t0+D' ≤ z+b+ε*N'+t0+D'; linarith only [ht]

