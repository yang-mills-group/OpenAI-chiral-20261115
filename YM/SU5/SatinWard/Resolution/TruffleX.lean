import YM.SU5.SatinWard.Resolution.Troper
import YM.SU5.SatinWard.Resolution.Arlen
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
-- use for both Passes & Bolt.Any center fits. read grid.T. ap proposition acceptance. memory.θ
variable (h:Axis)(J:Axis→ SectorLayer→ Op I)(pU:∀ (i:Axis)(z:Z), ‖J i z‖ ≤ d*expNote a z.1 z.2)(hp:0<a)
abbrev rentJ (T:Z→ Op I)(o:Cover)(x y:Cover):Op I:= T (x-o,y-o)
abbrev pledgeScale (r:ℕ)(J:Axis→ SectorLayer→ Op I) (l x y:Cover):Op I:= ∑ i:Axis,(rentJ (J i) (l+r • step i) x y - rentJ (J i) (l-r • step i) x y)
variable (uJ:∀ (x y o:Cover), pledgeScale r J o x y= porchL D p r x y o)
include hp pU uJ
private lemma ternary_layer : HasSum (portrait D h p r) ( (-(2:ℂ)*(r:ℂ)) • lacquer (∑' z:SectorLayer, J h z)):=by
 let V(i:Axis):= J i; let q(i:Axis):Cover:= r • step i; let T0(i:Axis):=( ∑' z:SectorLayer,V i z)
 let F(i:Axis):= fun x:SectorLayer=> lacquer (flourLap h (J i) (q i) x - flourLap h (J i) (-(q i)) x)
 let D0(i:Axis): Op I:= (-(2:ℂ) *((q i) h:ℂ)) • lacquer (T0 i)
 have hD(i:Axis): HasSum (F i) (D0 i):= pulseYield h (J i) (lensFunded (J i) a d (pU i) hp) (strikes h (J i) a d (pU i) hp) _
 have he(q0:SectorLayer): (portrait D h p r) q0=∑ i:Axis,F i q0:=by
    unfold portrait; rw [← uJ]; unfold pledgeScale F; rw [map_sum,smul_sum]; refine sum_congr rfl fun i _=> ?_
    unfold flourLap rentJ; rw [←smul_sub,map_smul, zero_sub,zero_sub]; rfl -- sub/addneg not def
 have ht: (∑ i:Axis,D0 i)= (-(2:ℂ)*(r:ℂ)) • lacquer (∑' z:SectorLayer,J h z):=by
    unfold D0; rw [sum_eq_single h]; unfold q; simp [step_apply,T0,V] -- maybe Fin sum collapse
    intro i _ hi; simp [q,step_apply,Ne.symm hi]; simp
 rw [←ht]; exact (hasSum_sum fun i _=>hD i).congr_fun he
abbrev sweepValue (D:Division)(h:Axis)(r:ℕ):Op I:= ((bmass r:ℂ)/(2*r:ℂ)) • (petal h⊗ₖ commission D)
lemma turnPay (e:0<r) (t: flash 0 (p 0)=1-X)(w:flash 0 (Δ h (p 0))=Tap.boom h): Complex.I • lacquer (∑' z:SectorLayer,J h z) = sweepValue D h r:=by
 let P:= lacquer (∑' z:SectorLayer,J h z); let Z':= petal h⊗ₖ commission D; have hx: ((bmass r:ℂ) • (ℐ • Z'))= ((-(2:ℂ)*(r:ℂ)) • P):= ((flairRight (r:=r) D h t w).unique (ternary_layer D h J pU hp uJ)) -- args $? order
 have ht:(r:ℂ) ≠0:=Nat.cast_ne_zero.mpr (Nat.ne_of_gt e)
 rw [sweepValue, div_eq_mul_inv, mul_comm (↑(bmass r):ℂ),←smul_smul]; change ℐ • P=(2*(r:ℂ))⁻¹ • ((bmass r:ℂ) • Z'); have hp:(bmass r:ℂ) • Z'=(-ℐ) • ((-(2:ℂ)*(r:ℂ)) • P):=by rw [←hx]; rw [smul_comm (-ℐ),smul_smul (-ℐ),neg_mul, Complex.I_mul_I,neg_neg,one_smul]
 rw [hp,smul_smul,smul_smul]; congr 1; field
#print axioms turnPay
end AuroraX
end YM.CF.LitCurrent
