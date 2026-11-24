import Merino.Brooch.Strand
import Merino.Audience

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier RG Salt Mew Stax
open Dial Vow TreasuryFog Paige Vault Roots
open Py Rate LocalLimit Preparation Filter Buffered.Afterglow.Tower.VacuumSelection
set_option maxHeartbeats 800000

open Levier Hom
lemma equips (P:Preparation) (N:Side)(Q:GramM (mid N P.block))(u:InterestX P.W.C _ Q.J)(p:P.U.roundZ ≤ (mid N P.block).val)
  (s:Sweep _):
    Steers s (funde P.K.j Q.J.M (mid N P.block)) (Moire.bloom Q.J.P) P.d:=by
 refine ⟨rosterly _ _ _ u p,?_⟩
 intro V h
 let U:=back s V
 let t:=s⁻¹
 have G:Guard U P.d:=keepC (xtra s.charge) (castX s) _ _ h
 have T:flashA t U= V:=by unfold U back t; exact revB _ _
 have hs:=spinZ t.charge t.s
 have hv: 1 ≤ P.K.j:=by rw [P.kJ];norm_num
 have f:=P.V.note.fields_one (mid N P.block) (P.U.needed.trans p)

 let p2:=profile U
 change sings t.charge (actSpin s) (funde P.K.j Q.J.M _ p2)=swapX (actR s) (funde P.K.j Q.J.M _ (profile V))∧
   Moire.bloom Q.J.P (profile V)=jazz (actR s) (sings _ _ (Moire.bloom _ p2))
 rw [←T]
 exact ⟨funde_f _ _ _ hs _ _ hv _ _ f (G.shrink P.U.gem),
       prism_x _ _ _ u.leanJ.1 u.ready _ _ hs⟩

lemma drop {n:Side}{o:Seat n}{X:SOp n}{a b c d:ℝ}(h:Soak o X b c d)(t:a≤b):
 Soak o X a c d:=by
 obtain ⟨F,V,u,e,z,r⟩:=h
 refine ⟨F,V,u,e,le_trans (sum_le_sum fun i _=>?_) z,r⟩
 exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right t (Nat.cast_nonneg _)))
    (sum_nonneg fun j _=>sum_nonneg fun k _=> (u i).nonn j k)
open Vale Rive
variable (P:Spine)(s i k:ℕ)
local notation "L"=> P.par.R.L
local notation "N"=> RegNum P s i
local notation "R"=> LedgerM P s i k
local notation "x"=> scaleM P s
local notation "Q"=>Qprice P s
local notation "h"=>P.par.h
local notation "K"=>LoomM P s i
local notation "M"=> priceTick P
local notation "A"=>P.par.U
local notation "J"=>P.par.J
variable (p:Bolts)


theorem certs (a c:ℝ)
  (g:License R L x K A a c h (J).k M (J).n) (ha:a ≤ p.a)
  (T:BudgetPoint)(v:T.order=(R).p.order) {o₀:Site N}
  (d:Dress P s i k p M o₀)(t:Sweep N):
  ∃ F:Bag N,Nest A R K (J).n 24 (boxA t d.y.post) h (rScale (R).p)
           (ghost t d.y (R).p K (hueM P s))
         F (Fcoat L T M h a c p.c p.a x)
        (Dcoat L T M h a c p.c p.a x*Q):=by
 unfold ghost spindle

 rw [d.leap]
 refine nestB L T M h a c p.c p.a A R x K g d.y.origin d.y.spin d.clips d.y.color d.selv
   ⟨fun j=>drop (d.ticket.hem.spurt j).pay ha,
    drop d.ticket.hem.sip.pay ha,?_,?_,?_,?_⟩ v t
 all_goals rw [d.here]
 · exact fun i' => drop (d.echoes _) ha
 · exact drop d.wane ha
 · exact d.spur_funds
 · exact d.glaze_funds
end YM.CF.Merino.Brooch

