import YM.SU5.SatinWard.Resolution.TruffleX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
variable {S:Type}{F: Ultrafilter S}{s:ℕ}(X': Cross s (F:Filter S)) {p:Stack}
local notation "X★"=> X'
local notation "Nβ"=> X'.N
local notation "Mβ"=> X'.M
open Ember Hove
variable (D:Division)
local notation "X"=> bins SU.Slot
local notation "H"=> Coats I
local notation "Z" => SectorLayer
local notation "ℐ"=> Complex.I
-- lift iff BOTH endpoints chosen. finite.F.L.Wptr. root always 0.
abbrev shoreZ(N:Side)(z:SectorLayer):Prop:= Lattice.lift (wrap N z.1)=z.1 ∧ Lattice.lift (wrap N z.2)=z.2
def shrinkCoast(N:Side)(V:SectorLayer→Op I)(z:SectorLayer) :Op I:= if shoreZ N z then V z else 0
variable (T: (i:S)→ SOp (X'.N i))(E:∀ i:S, Pattern (X'.oil i) (T i) r d a v)
variable (Cs:∀ i:S, Solo a b (X'.oil i) d)(u:∀ i:S,Solo a b (T i) d)(e:∀ i:S, T i 1=0) (ha:0<a)(hd:0<d)(h0:0<r)
local notation "ϱ"=> LitCurrent.expiry (4*a) v
local notation "qX"=> faithMoney (ϱ)
noncomputable def headP (j:Axis)(i:S)(z:SectorLayer):Op I:= fullnx D (E i) hd z.1 z.2 j
noncomputable abbrev headS (j:Axis)(i:S)(z:SectorLayer): Op I:= shrinkCoast (Nβ i) (headP X' D T E hd j i) z
local notation "Zβ"=> headP X' D T E hd
local notation "ZX"=> headS X' D T E hd
include X' -- omit notation parse
include D Cs u e ha hd E
set_option autoImplicit false in
lemma turnPromise : ∃ J:Axis→ SectorLayer→ Op I,
 (∀ (i:Axis)(x:Z),Tendsto (fun t=>ZX i t x) F (𝓝 (J i x))) ∧ (∀ i x,Tendsto (fun t=>Zβ i t x) F (𝓝 (J i x))) ∧
 (∀ i x, ‖J i x‖≤ (qX)*expNote a x.1 x.2)∧ ((0<r) → (∀ i:Axis, ℐ • lacquer (∑' z:SectorLayer,J i z)= sweepValue D i r)):=by
 obtain ⟨p0,g⟩:=Cross.builds X'; obtain ⟨h,V⟩:=looming X'.yes; obtain ⟨m,Yk,a2⟩:= V.passes X'.yes F X'.M; have hc:= g.shade V Yk
 let p(x:Z):= qX*expNote a x.1 x.2 -- rename p locally.K∗
 have he(x:SectorLayer):∀ᶠ g in (F:Filter S), shoreZ (Nβ g) x:=(X'.apply_lift x.1).and (X'.apply_lift x.2)
 have hK(j:Axis)(x:SectorLayer): ∀ᶠ i in (F:Filter S), ‖Zβ j i x‖ ≤ (qX)*expNote a x.1 x.2:= (he x).mono fun g v=> peakBarrier D (E g) hd _ _ ha j v.1 v.2 -- η0 tune
 have ht(j:Axis)(x:SectorLayer): ∃ y,Tendsto (fun i=> (Zβ j i x)) F (𝓝 y):=by
    let M:=F.map (fun i=> (Zβ j i x)); obtain ⟨y,hy,Y⟩:=(isCompact_closedBall (0:Op I) (p x)).ultrafilter_le_nhds' M (by change ∀ᶠ i in (F:Filter S), _; simpa only [Metric.mem_closedBall,dist_zero_right, Set.mem_preimage] using! hK j x); exact ⟨_,Y⟩
 choose J pJ using ht
 have hD(i:Axis)(x:Z): ‖J i x‖ ≤ qX * expNote a x.1 x.2:=le_of_tendsto ((pJ i x).norm) (hK i x)
 have h2:∀ i x,Tendsto (fun t=>ZX i t x) F (𝓝 (J i x)):= fun i x=>(pJ i x).congr' ((he _).mono fun _ u=> Eq.symm (if_pos u))
 refine ⟨J,h2,pJ,hD,fun h0 i=>turnPay (p:=p0) D i J hD ha (fun x y o=>?_) h0 ?_ ?_⟩
 · refine tendsto_nhds_unique_of_eventuallyEq (f:=fun i:S=> pledgeScale r (fun j=> headP X' D T E hd j i) o x y) (tendsto_finsetSum Finset.univ (fun j _=> (pJ j _).sub (pJ j _))) (fundsD _ g D x y o r) (Eventually.of_forall fun i=> tarGlow D (E i) hd (Cs i) (u i) (e i) x y o) -- args
 · rw [hc]; exact atBreaker V Yk
 rw [hc]; exact peakNote V Yk X'.yes i
#print axioms turnPromise
end AuroraX
end YM.CF.LitCurrent
