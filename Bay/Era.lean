import Bay.RollAx
import Bay.Cold
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


abbrev xHead (P:VΩ)(D:ℝ→ℝ)(x:ℝ):ℝ:=
  (1+(weeB x:ℝ))^100 * (Nor.reserveT 2 6 (weeB x) (BScale.runway x) * (D x * Till.qL P.par.R x))

/-- One cumulative fee. Independent of volume, locations, degrees. -/
def xPool (P:VΩ)(M:ℕ)(F D:ℝ→ℝ)(x:ℝ):ℝ:=
 (1+2*M:ℝ) * |xHead P D x|
 + |Till.markEG (TopBill P M F D) x|
 + Real.exp (4*M) * |Till.markFG (TopBill P M F D) x|

lemma headOf {P:VΩ}{D:ℝ→ℝ}(h:NPL D): Quench P.par.R (xHead P D):=
   ((Till.alloy _ h).bondF (reserve_bond ..)).bondF
   (((Lor.BoreP.still 1).join Lor.BoreP.radius_c).self _)

lemma poolOf {P:VΩ}{F C D:ℝ→ℝ}{M:ℕ}
 (d:NPL D)(p:Icicle P M F C D):PinNPL P (xPool P M F D) :=by
 let W:=p.charge
 have h:=@headOf P D d
 have e: Quench P.par.R (Till.markEG (TopBill P M F D)):=chill_iff.mpr p.reserveE
 have f: Quench P.par.R (Till.markFG (TopBill P M F D)):=chill_iff.mpr p.reserveF
 exact chill_iff.mp (((h.normF.manyF _).addL e.normF).addL (f.normF.manyF _))

lemma pool_hit{P:VΩ}(M:ℕ)(F D:ℝ→ℝ)(x:ℝ):
 let γ:= TopBill P M F D
 let w:= xPool P M F D x
 let y:=BScale.runway x + BScale.runway x
 0≤y →
 |xHead P D x| ≤ w∧ 
    ((2*|xHead P D x| *M)+TreasuryFog.sigma y (weeB x)*Till.markEG γ x) ≤ w∧
    Real.exp (4*M)*Till.markFG γ x ≤ w:=by
 intro γ w y h
 have hσ:=Real.exp_pos (-(y)*(weeB x:ℝ)^2/6)
 have hu: TreasuryFog.sigma y (weeB x) ≤ 1:=by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
       (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (sq_nonneg _)) (by norm_num)
 let e:=Till.markEG γ x; let f:=Till.markFG γ x
 let u:=|xHead P D x|
 let p:=Real.exp (4*M)
 have hw:0≤u:=abs_nonneg _
 have hz:0≤M*u:=mul_nonneg (Nat.cast_nonneg _) hw
 have hp:0≤p*|f|:=mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
 have hf:p*f ≤ p*|f|:=mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
 have hE:TreasuryFog.sigma y (weeB x)*e ≤ |e|:=
  (mul_le_mul_of_nonneg_left (le_abs_self _) hσ.le).trans
     (mul_le_of_le_one_left (abs_nonneg _) hu)

 rw [show w=(1+2*M:ℝ)*u+|e| +p*|f| from rfl] -- fail rw let? 
 refine ⟨?_,?_,?_⟩
 · change u ≤ _
   nlinarith only [abs_nonneg e,hp,hz]
 · change 2*u*↑M+TreasuryFog.sigma y (weeB x)*e ≤ _
   nlinarith only [hE,hp,hw]
 change p*f ≤ _
 nlinarith only [hf,hz,hw,abs_nonneg e]
namespace Berth
variable {w:Berth} {M:ℕ} {F C D:ℝ→ℝ} {r:blazeK w.side}
abbrev SlipCount(w:Berth)(M:ℕ):=36*M ≤ w.p.B

lemma limits(e:w.Firm M F C D r)(l:w.SlipCount M):
 let g:= w.coincert e
 let a:= |xHead w.P D w.x|
 let b:=xPool w.P M F D w.x
 
 (9*4*M:ℝ) ≤ g.η*(w.p.B:ℝ)^2 ∧
 bracer w.p * (Nor.reserveT w.p.power w.p.order w.p.B g.η * (D w.x * w.Q))≤ a ∧ 
 a≤ b ∧
 ((2*a*M)+TreasuryFog.sigma (g.η+g.η) w.p.B*yσE w.p g)≤ b ∧ 
 Real.exp (4*M)*yσF w.p g ≤ b ∧
 w.p.supportExponent+g.η ≤ rScale w.p:=by
 intro g a b
 obtain ⟨z,_,_,t,v⟩:=w.caratOf e
 have hR0:=g.hη
 have hηR: g.η=↑(w.p.B:ℝ)⁻¹:=by rw [z,e.rail.size];rfl

 have hk:0 < (w.p.B:ℝ):=inv_pos.mp (hηR ▸ hR0)
 obtain ⟨o,y,x⟩:= pool_hit (P:=w.P) M F D w.x (by
    change 0 ≤ w.snowEta+w.snowEta
    rw [←z]
    exact add_nonneg hR0.le hR0.le)
 refine ⟨?_,?_, o,?_,?_,?_⟩
 · rw [hηR,sq,mul_left_comm,inv_mul_cancel₀ hk.ne',mul_one]
   exact_mod_cast l
 · unfold bracer
   rw [z,e.rail.H6,e.rail.H2,e.rail.size]
   exact le_abs_self _
 · rw [t,e.rail.size,z]; exact y
 · rw [v];exact x
 rw [hηR,e.rail.coin]
 unfold rScale
 have h:=inv_pos.mpr hk
 rw [div_eq_mul_inv]
 linarith
end Berth

/-- (20), doubled torus (Seat side). -/
abbrev LatticeWide {n:Side}{I:Type}[LinearOrder I][Fintype I]
  (σ:I→Seat n)(b:ℕ):=∀ i j,σ i≠σ j→ 2*b^3+2*b < separation (σ i) (σ j)

lemma rents {n:Side}{I:Type}[LinearOrder I][Fintype I]
 {σ:I→Seat n}{M b:ℕ} (g:LatticeWide σ b)(h:Multiplicity σ M): Force_M b σ M:=by
 refine ⟨?_,?_⟩
 · intro i j k
   dsimp only [cape_B]
   have l:=g i j k
   omega
 intro y
 let S:=reach_B (cape_B b) b σ y
 change S.card ≤ M
 by_cases k:S.Nonempty
 · obtain ⟨i,t⟩:=k
   apply le_trans _ (h (σ i))
   apply card_le_card
   intro j u
   refine mem_filter.mpr ⟨mem_univ j,Classical.byContradiction fun z=>?_⟩
   have l:=g j i z
   have hz:=separation_triangle (σ j) y (σ i)
   have hh:= (mem_filter.mp t).2
   have hu:separation (σ j) y ≤ b+b^3:=(separation_comm (σ j) y).trans_le (mem_filter.mp u).2
   dsimp only [cape_B] at hh
   omega
 rw [not_nonempty_iff_eq_empty.mp k,card_empty]
 exact Nat.zero_le _



def Receives{I:Type}[LinearOrder I][Fintype I] {n:Side}
 (p:BudgetPoint)(L:ℕ)(σ:I→Seat n)
 (EE:Mew.Key I→RegBudget n)(FF:Mew.Key I→ForceBudget n)(h W:ℝ):Prop:=
  Quince _ σ EE ∧ Quince _ σ FF ∧ BillRoll σ EE FF ∧
  (∀ i,Dagger p L (σ i) (νTip EE i) h W) ∧
  ∀ y:Mew.Key I, (∀ i, ‖y i‖≤ 2)→ 
     IncX primeU (EE y) p h W ∧ Dark primeU (FF y) p h W
lemma Receives.raise {I:Type}[LinearOrder I][Fintype I]{n:Side}{P:BudgetPoint}{L:ℕ}
 {σ:I→Seat n}{EE:Mew.Key I→RegBudget n}{FF:Mew.Key I→ForceBudget n}{h W V:ℝ}
 (p:Receives P L σ EE FF h W)(q:W ≤ V):Receives P L σ EE FF h V :=by
 obtain ⟨a,b,c,d,w⟩:=p
 refine ⟨a,b,c,fun i=>(d i).raise q,fun i k=>?_⟩
 obtain ⟨⟨⟨_,z,h⟩,e⟩,⟨⟨_,y,l⟩,v⟩⟩:=w i k
 exact ⟨⟨⟨_,z,fun j=>(h j).trans q⟩,e⟩,
   ⟨⟨_,y,fun j=>(l j).trans q⟩,v⟩⟩

-- Preparation.Ctor=>Scree.mid mass


section
variable {N B:Side}{I:Type}[LinearOrder I][Fintype I]
abbrev rootE {n:Side}(R:GramM n)(K: Mew.Key I→Cadre.Rinse (Seat n) (Copy n))
 (s:ℕ)(τ:Ids n):Mew.Key I→RegBudget n:=lensD (P:=R.p) R.K K s τ 
abbrev rootF {n:Side}(R:GramM n)(K: Mew.Key I→Cadre.Rinse (Seat n) (Copy n))
 (s:ℕ):Mew.Key I→ForceBudget n:=lensPort (P:=R.p) R.K K s

variable {R:GramM (mid N B)} {C:Occlus R.p} {σ:I→Seat (mid N B)}
 {K: Mew.Key I → Cadre.Rinse (Seat (mid N B)) (Copy (mid N B))}
 {q:ℕ}{h:ℝ}{z b: Aura (mid N B)→ℝ} {r:Aura (mid N B)→Support (More (mid N B))→ℝ}
 {M:Mew.Key I→ Orbit (mid N B)→ Aura (mid N B)→ FC (Dwell (mid N B))}
variable (T:OrbitRack C σ q R.K h K z b r M)(s:ℕ)(p:1 ≤ h)(τ:Ids (mid N B))
 {L:ℕ}{E:I→RegBudget (mid N B)}{y0 y:ℝ}
 (pD:∀ i,Dagger R.p L (σ i) (E i) h y0)
include pD T p

lemma teary {t:ℕ}(hv: (9*4*t:ℝ) ≤ C.η*↑R.p.B^2)(W:Force_M R.p.B σ t)(hC:0≤ y0)
  (d:y0 ≤ y)(f:(2*y0*t)+TreasuryFog.sigma (C.η+C.η) R.p.B*yσE R.p C ≤ y)
  (g:Real.exp (4*t)*yσF R.p C ≤ y):
  let QE :=awake σ (rootE R K s τ) E
  let QF :=bustle σ (rootF R K s)
  Receives R.p L σ QE QF h y ∧
    ∀ i,νTip QE i=E i ∧ emberTip QF i=νΦK (rootF R K s) {i}:=by
 intro QE QF
 obtain ⟨u,v⟩:=displayD C K σ q M T s p τ L E y0 pD
 refine ⟨⟨quinceE σ _ E, ⟨_,fun i=>rfl⟩,u,fun i=>?_,fun i k=>?_⟩,v⟩
 · rw [(v _).1]
   exact (pD i).raise d
 have hx:4 ≤ Real.exp (4:ℝ):=(show 4 ≤ (4:ℝ)+1 by norm_num).trans (Real.add_one_le_exp _)
 obtain ⟨⟨⟨_,a,c⟩,l⟩,⟨⟨_,b,w⟩,r⟩⟩:=
     loans C K σ q M T s p τ L E y0 pD 4 hx (by norm_num) hv W hC i k
 exact ⟨⟨⟨_,a,fun j=>(c j).trans f⟩,l⟩,
  ⟨⟨_,b,fun j=>(w j).trans g⟩,r⟩⟩
end

namespace Berth
variable {I:Type}[LinearOrder I][Fintype I]
variable (w:Berth) {M L:ℕ}{F C D:ℝ→ℝ}
 {r:blazeK w.side}
 {A:I→Support (More w.side)} {v:I→Sour.Bag w.side}
 {E B:I→Aura w.side→ℝ}
abbrev flareE (d:w.Estate A v E B C D)(σ:I→Seat w.side)
 (s:ℕ)(τ:Ids w.side):Mew.Key I→RegBudget w.side:=
 awake σ (rootE w.R (flare d.bill) s τ) (kilnTip d.bill σ τ)
abbrev flareF (d:w.Estate A v E B C D)(σ:I→Seat w.side)
 (s:ℕ): Mew.Key I→ForceBudget w.side:=
 bustle σ (rootF w.R (flare d.bill) s)

-- for any Estate compile both (52), key arms (zeros, purchases)
variable {w} (e:w.Firm M F C D r)(d:w.Estate A v E B C D)
variable (σ:I→Seat w.side)(mulσ:Multiplicity σ M)
 (lw:LatticeWide σ w.p.B)(p:∀ i,σ i∈A i)
 (c:w.SlipCount M)
include e mulσ lw p c

set_option maxHeartbeats 2000000 in
lemma flared
 (outer:∀ i X,v i X≠0→ outmint w.p L (σ i) X.val)
 (s:ℕ) (τ:Ids w.side):
 let U:=w.flareE d σ s τ
 let V:=w.flareF d σ s
 Receives w.p L σ U V w.H (xPool w.P M F D w.x)∧
 ∀ i, νTip U i= kilnTip d.bill σ τ i ∧
    emberTip V i=νΦK (rootF w.R (flare d.bill) s) {i}:=by
 obtain ⟨h,z,u,t,l,m⟩:=limits e c
 have w0:=w.P.par.height
 have dag(i:I):Dagger w.p L (σ i)
     (kilnTip d.bill σ τ i) w.H |xHead w.P D w.x|:= by
   have a:=Orchard.repaid (d.bill i) (σ i)
    ((by norm_num:3 ≤ (5:ℕ)).trans e.wide)
    (zero_le_one.trans w0) τ (w.coincert e).hη m L (outer i) (d.birth i)
   exact a.raise z
 intro U V
 exact teary (N:=Vale.mesh (w.P.run.ir w.i) w.P.par.R.L w.s) (B:=w.P.par.block) (R:=w.R)
   (farm e σ mulσ p d)
   s w0 τ dag h (rents lw mulσ) (abs_nonneg _) u t l
end Berth
end YM.CF.Bay
#print axioms YM.CF.Bay.Berth.flared
