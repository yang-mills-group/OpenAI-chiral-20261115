import YM.SU5.WakeInvestment.BookBill
import SatinThinBases
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
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)

/-- Extra occupancy tilt & Board pension. Increases the earlier DrawBill floor for `Λ.h`.
State upstream of h: a choice of C and sizes can still be made before the subsequent queries. -/
structure Investment (P:Preparation) (E v:ℝ) : Prop where
  chr : 0 ≤ E
  spectrum : CF.Papyrus.Franc.postage P.K.j E
  chr' : 0 ≤ v
  toll : (v+1)*(tiltBound*(45*(1+E))) ≤ P.h
  pillar : ∀ᶠ k:ℕ in atTop, ∀ n:Side, k ≤ n.val → ∀ (U:Pane n), Guard U P.d→∀ M:Tulip.Male,∀ i:Single n, Gall.dialZ (acts (spar P.K.j M U) (basisKet i)) ≤ v

/-- relative-accuracy commissioning, maintain *given* RΘ (e.g. the preparation-criterion
with the election's Reg stamp), add the payments for positivity range to purchase the
higher Mark energies. Thus usable too with a later augmented EA.1 replay needing additional
pre-L & pre-h criteria, provided that it implements its promised `CommissionVector`. Does not
implement that whole additional replay here. Similar to `Yoke.draw_grants`. -/
lemma invest_grants {RΘ:Preparation→Prop} (T_ : CommissionVector RΘ) :
    CommissionVector (fun P=> RΘ P ∧ ∃ E v, Investment P E v) := by
  constructor; intro e' ε he Q
  obtain ⟨R,u,y⟩:= CF.Papyrus.Franc.grantH 4 (by omega)
  obtain ⟨v,δ,hv,hδ,N0,p⟩:= Graph.burley 4 (by omega)
  let T:=(v+1)*(tiltBound*(45*(1+R)))
  let X:Supplier:=fun K p Lm V Bm d W U M J ℓ Z=> max (Q K p Lm V Bm d W U M J ℓ Z) T
  obtain ⟨P,ℓ,Z,Y,p',u',t',r,c,A,w,X',L',G',B',J⟩:= T_.purchased (min e' δ) ε (lt_min he hδ) X
  refine ⟨P,ℓ,Z,Y,(show decorate Q P ℓ Z ≤ P.h from (le_max_left (decorate Q P ℓ Z) T).trans p'),u',t'.trans (min_le_left ..),r,c,A,⟨w,R,v, ?_⟩,X',L',G',B',J⟩
  refine ⟨u.le,?_,hv.le,(show T≤ P.h from (le_max_right ..).trans p'),?_⟩
  · rw [P.kJ]; exact y
  rw [P.kJ]; filter_upwards [eventually_ge_atTop N0] with k z n i U f M j
  exact p n (z.trans i) U (f.shrink (t'.trans (min_le_right ..))) M j

lemma nontrivial_spin (P : Preparation) : 1 ≤ P.K.j := P.kJ.ge.trans' (by decide)
variable (s i k : ℕ)

lemma flat_post : IsStarProjection (spar D (Gξ s i k).J.M (1:Pane (side Y i s))) :=
  (P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _).projection _ (guard0 P.dpos.le)

def inclined (g: Seat (side Y i s) → SU.E) :=
  windShaft (nontrivial_spin P) (flat_post Y s i k) g

def flatShear := shear (nontrivial_spin P) (flat_post Y s i k)

local notation "η" s:max => Worth.gateC (shx s)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))

structure TiltInvoice (E : ℝ) : Prop where
  column (g : Seat (side Y i s) → SU.E) (t:ℝ) (p:|t|≤1): let W:= weighted flatP t (inclined Y s i k g); ColumnDeal W.sell (tiltBound*(45*(1+E))) ∧ ColumnDeal (star W.buy) (tiltBound*(45*(1+E)))
  norm (F J : RegBudget (side Y i s)) (R : ForceBudget (side Y i s))
    (u : Orbit (side Y i s)) (a t : ℝ) :
    let G:= pertain (RootBook Y i k s) F J R; let W:= inclined Y s i k (atFrame Y s i u); tier P.h (G.board u).val ≤ Real.exp a → |t| ≤ 1 →
    ‖acts (wholeTilt flatP t) (acts (quant W.sell) (recX P.U G ((Y.voyage i).CapeT s) u))‖ ≤
      Real.exp (a + meterC (hat P.R.L P.x s)*sites (side Y i s))*shadeY Y s i k 0 (gateC (hat P.R.L P.x s)) u

variable {s i k}
theorem tilt_paid {E v : ℝ} (D' : Dispatchers P) (c : Investment P E v) :
    ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s ≤ Y.uv k→ TiltInvoice Y s i k E := by
  obtain ⟨n,hC⟩:= c.pillar.exists
  filter_upwards [map_meters Y D' _ (boardRent_pos E).le] with s r
  filter_upwards [r, (Papal.count_grows Y s).eventually_ge_atTop n] with i u h k p
  constructor
  · intro g t ht; exact wind_sells (nontrivial_spin P) (flat_post Y s i k) c.spectrum g ht
  intro F J R x a t G W hA ht; let f:= (ℂk s i); let L':= RootBook Y i k s
  let g:= atFrame Y s i x; let n':= side Y i s
  let R_:=(hat L P.x s); let M:=meterC R_; let b:=gateC R_; let T:=metroStress P.K.j L' f x g
  obtain ⟨hx,hz⟩:= Papal.safety Y s i k x
  have hh (y : Single n') := hC n' h (f x) ((Papal.roofage Y i s).paid x) L'.J.M y
  apply (posture P.U G f x g (nontrivial_spin P) (flat_post Y s i k) hx hz c.chr' hh c.chr c.spectrum c.toll hA t ht).trans
  change past L' x.1*Real.exp (a+boardRent E*T) ≤ _
  unfold Graph.past shadeY Papal.frost_bill; simp only; rw [zero_mul,add_zero,←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
  have h0:boardRent E*T≤ M*sites n'+ b*Py.Rate.Pannier.flakes (shieldC R_) x.1:= u k p x
  change -L'.path.inChannels L'.funds L'.p L'.beta x.1 + _ ≤ a+M*sites n' + (-L'.path.inChannels L'.funds L'.p L'.beta x.1 + b*flakes (shieldC R_) x.1)
  linarith only [h0]

#print axioms tilt_paid
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
