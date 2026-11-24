import YM.SU5.SatinWard.Resolution.CapsuleP
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
variable (q:S→ BudgetPoint) (T: (i:S)→ SOp (X'.N i))(E:∀ i:S, Pattern (X'.oil i) (T i) r d a v)
variable (Cs:∀ i:S, Solo a b (X'.oil i) d)(u:∀ i:S,Solo a b (T i) d)(e:∀ i:S, T i 1=0) (ha:0<a)(hd:0<d)(h0:0<r)
variable {k m:ℕ}{g:ℝ}(U:(i:S)→ Scree.Loom (X'.N i))(V:∀ i:S,Checked (q i) (U i) g d a k m)
local notation "Θ"=> LitCurrent.expiry (4*a) v
local notation "τ"=> faithMoney (Θ)
noncomputable abbrev curbE(a v:ℝ)(k:ℕ):ℝ:= Real.exp (-a*k)*(‖lacquer‖*faithMoney (LitCurrent.expiry (4*a) v)*billE a)
local notation "κ"=> Real.exp (-a*k)
local notation "Κ"=> curbE a v k
include V u Cs e -- fix
include hd ha h0
variable (h:Axis)
lemma paid_balance :∀ᶠ i in (F:Filter S), ‖momenti D (E i) (q i) (U i) k h - sweepValue D h r‖ ≤ curbE a v k+Real.exp (-a*k):=by
 let Y:=F; obtain ⟨J,t,_,u0,hm⟩:= turnPromise X' D T E Cs u e ha hd; let f(i):=ℐ • lacquer (∑' z:SectorLayer,tickFull D (E i) hd h z); have ht:Tendsto f F (𝓝 (sweepValue D h r)):=by
    rw [←hm h0 h]; have Hh:= tendsto_tsum_of_dominated_convergence ((expPair a ha).mul_left (τ)) (t h) (Eventually.of_forall fun i=> tickBudget D (E i) h ha hd); exact (((lacquer.continuous.tendsto _).comp Hh).const_smul ℐ)
 let v:=Real.exp (-a*k); have hz:0<v:= Real.exp_pos _; filter_upwards [ht.eventually (ball_mem_nhds _ hz)] with i u; exact (norm_sub_le_norm_sub_add_norm_sub _ (f i) _).trans (add_le_add ((norm_sub_rev ..).trans_le (glow_payment D (E i) (q i) (U i) (V i) h hd)) (show ‖f i-sweepValue D h r‖ ≤ κ from (by apply le_of_lt; exact (dist_eq_norm (f i) (sweepValue D h r)) ▸ Metric.mem_ball.mp u))) -- `<`
omit V u e Cs
variable (b g:ℝ)(k m:ℕ)
set_option maxRecDepth 2800 in
lemma shineWork (hP: 1 ≤ s) :∃ l:ℕ,∀ (N:Side),l≤N.val→∀ (T:SOp N)(M:Male)(E:Pattern (funde s M N) T r d a v)(t:Scree.Loom N) (q:BudgetPoint),Solo a b (funde s M N) d→Solo a b T d→ T 1=0→ Checked q t g d a k m→
 ‖momenti D E q t k h-sweepValue D h r‖ ≤ curbE a v k + Real.exp (-a*k):=by
 by_contra! u
 choose α hx B m' E l q t g e w r' using u -- order after ∃. y₀ x ≤. choose depends previous.
 let F:= Ultrafilter.of (atTop :Filter ℕ)
 let V: Cross s (F:Filter ℕ):= ⟨α,m',?_,hP⟩; swap; · exact (tendsto_atTop_mono hx tendsto_id).mono_left (Ultrafilter.of_le _)
 obtain ⟨i,hi⟩:=(paid_balance V D q B E t g e ha hd h0 l w h).exists; exact (r' i).not_ge hi
#print axioms shineWork
end AuroraX
end YM.CF.LitCurrent
