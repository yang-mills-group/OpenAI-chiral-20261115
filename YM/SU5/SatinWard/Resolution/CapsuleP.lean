import YM.SU5.SatinWard.Resolution.Dapple
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
variable {P T:SOp N}(E:Pattern P T r d a v)(q:BudgetPoint)(t:Scree.Loom N){B:ℕ}
variable {g:ℝ}{m:ℕ}
noncomputable def onPay (i:Axis) (z:Cover)(k:ℕ) (U:Pane N) (Z':SectorLayer) : Op I:= shore N (z+Z'.1) (z+Z'.2) (centHat D (wrap N z) E t q k (i,false) U)
noncomputable def vowBand (k:ℕ)(i:Axis):SectorLayer → Op I:= shrinkCoast N (onPay D E q t i 0 k 1)
noncomputable def momenti (k:ℕ)(i:Axis) := ℐ • lacquer (∑' z:SectorLayer, vowBand D E q t k i z)
local notation "Ξ"=>vowBand D E q t
noncomputable def billE (a:ℝ):ℝ:=∑' z:SectorLayer, expNote a z.1 z.2
lemma bill_nn(a:ℝ) : 0≤ billE a:= tsum_nonneg (fun i=> (Real.exp_pos _).le)
noncomputable abbrev tickFull (h:0<d)(i:Axis):SectorLayer→ Op I:= shrinkCoast N (fun z=> fullnx D E h z.1 z.2 i)
variable (C:Checked q t g d a B m)
local notation "Ω"=> LitCurrent.expiry (4*a) v
local notation "Mκ"=> faithMoney (Ω)
local notation "νκ"=> Real.exp (-a*B)
include C E
lemma fuelX :0≤ faithMoney (Ω):=let H':=E; holds_money _ (pearl_pos C.hint (H'.A 0) (H'.moorA 0)) -- E not referenced syntactically.add include.
include E
variable (i:Axis)
lemma townDebit (hd:0<d) (x:SectorLayer): ‖tickFull D E hd i x- Ξ B i x‖ ≤ (νκ*Mκ)*expNote a x.1 x.2:=by
 have he:= peakBridge D E hd x.1 x.2 q C.hint t C i; by_cases z:shoreZ N x; · unfold tickFull vowBand shrinkCoast; rw [if_pos z,if_pos z]; unfold onPay; simp_rw [zero_add]; exact he z.1 z.2
 unfold tickFull vowBand shrinkCoast; simp only [if_neg z,sub_zero,norm_zero]; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (fuelX E q t C)) (Real.exp_pos _).le
include E
omit C in
lemma tickBudget (e:0<a)(hd:0<d) (x:SectorLayer): ‖tickFull D E hd i x‖≤ faithMoney (Ω)*expNote a x.1 x.2:=by
 by_cases z:shoreZ N x; · unfold tickFull shrinkCoast; rw [if_pos z]; exact peakBarrier D E hd _ _ e i z.1 z.2
 unfold tickFull shrinkCoast; simp only [if_neg z,norm_zero]; exact mul_nonneg (holds_money _ (pearl_pos e (E.A _) (E.moorA (0:Site N)))) (Real.exp_pos _).le -- want omit C.P
lemma candleIn : Summable (Ξ B i):=by
 let F:= tickFull D E C.angle i; let U:=(νκ*(Mκ)+(Mκ)); have h(x:Z):‖Ξ B i x‖ ≤ U*expNote a x.1 x.2:=by
    let e:= townDebit D E q t C i C.angle x; rw [norm_sub_rev] at e; unfold U; rw [add_mul]; exact (norm_le_norm_sub_add _ (F x)).trans (add_le_add e (tickBudget D E i C.hint C.angle x)) -- order
 exact lensFunded (Ξ B i) _ _ h C.hint
lemma glow_payment (hd:0<d): ‖ℐ • lacquer (∑' z:SectorLayer,tickFull D E hd i z)- momenti D E q t B i‖ ≤ νκ * (‖lacquer‖ * faithMoney (Ω) * billE a):=by
 let F:= tickFull D E hd i; let G:=Ξ B i; let q':= Summable.tsum_sub (lensFunded (tickFull D E hd i) _ _ (tickBudget D E i C.hint hd) C.hint) (candleIn D E q t C i); unfold momenti; rw [←smul_sub,←map_sub,← q', norm_smul,Complex.norm_I,one_mul]
 refine (lacquer.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (?_ : ‖∑' z:SectorLayer,(F z-G z)‖≤(νκ*Mκ)*billE a) (norm_nonneg lacquer)).trans_eq (by ring))
 have u:=expPair a C.hint; let U:=u.mul_left (νκ*Mκ); have d:=townDebit D E q t C i hd; let e:= U.of_nonneg_of_le (fun _=> norm_nonneg _) d; refine (norm_tsum_le_tsum_norm e).trans ((e.tsum_le_tsum d U).trans_eq ?_); exact u.tsum_mul_left _
#print axioms glow_payment
end AuroraX
end YM.CF.LitCurrent
