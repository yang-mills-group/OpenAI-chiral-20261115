import YM.SU5.SatinWard.Resolution.Jungfrau
import YM.SU5.SatinWard.Resolution.Glare
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Salt
-- Circ on Pane too: note one mesh q, areal. shared mask for tax (inc bar subtraction)
-- and for each chir ingredient.
variable {P T:SOp N} {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
open Urn

namespace Chamber
section proof
variable (bI:Division)(K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)
local notation "S"=>offsetMask p.B x
local notation "Â"=> skyHat bI x E K p k
local notation "J"=> centHat bI x E K p k
local notation "Λ"=> (tickA N)
variable (z:Checked p K t d a k q)
variable (e:FaceDir)
local notation "J0"=> beforePing (grantJ bI E (x,e)) k
noncomputable abbrev jewelCostLeg: Mark N:= fun V=>liftHalf w (centHat bI x E K p k e V.1)
local notation "sectorM"=> jewelCostLeg bI K p k w x E e
variable {s H l₀:ℝ}{l:ℕ}
include z
lemma costC (i:Orbit N): sectorM (i.1,K i)= houseK p (offsetMask p.B x) (heavy w K J0) i:=by
 unfold jewelCostLeg centHat; dsimp only; rw [noTag x (grantJ bI E (x,e)) z (E.moorJ (x,e)),houseK]; split; next h=> rw [Set.indicator_of_mem (show i∈_ from h)]; rfl
 next h=> rw [Set.indicator_of_notMem (show i∉pingMask p (offsetMask p.B x) from h)]; simp [liftHalf,dg,dyad]
local notation "F"=> jewelJ bI x E K p k w e
lemma cameo : let j:=p.B+12;∃ v:ℝ, WindowTag F x j v ∧ Contact K (offsetMask j x) F (fun i=>sectorM (i.1,K i)):=by
 intro j; have hx:(inspectFoot p x) ⊆ offsetMask j x:=Swell.inspect_fits ..; let Z:= (current_support bI K p k w x E z e).mono hx; obtain ⟨u,v⟩:= Z.env.cost; refine ⟨u,⟨Z,current_moves bI K p k w x E z e,v,fun x y t=>?_⟩,Z,fun i=>?_ ,fun i=>?_⟩
 · unfold jewelJ; rw [t]
 · unfold jewelCostLeg liftHalf; rw [sub_eq_add_neg, ←neg_one_smul ℂ]; apply Sector.add _ (((Sector.one.scale _).scale _).scale _); exact lift_v (pair_charge (modes_pass x (grantJ bI E (x,e)) z (E.moorJ (x,e)) i)) (modes_monotone ((halo_foot p x).trans hx))
 unfold jewelJ jewelCostLeg preHalf liftHalf; rw [star_sub,star_sub,act_sub,act_sub,bra_eq _ (touchP N ▸ cutM_idp _) _ (tickB N)]
open Leaf Swell
variable (CV: DockPulse p K t d a H s l q)(Yp:Solo a b P d)(Yv:Solo a b T d)
include CV Yp Yv
local notation "Ξ"=> legOut l p s H w a b r
lemma pilot_cost (hl: 1≤l):
    Fence P T K p q l (node x) H s (fun i=>sectorM (i.1,K i)) (Ξ* LitCurrent.expiry (4*a) v) (Ξ*LitCurrent.expiry (4*a) v):=by
 have hv:= (limbFee w x CV Yp Yv x (totals (grantJ bI E (x,e)) CV.hint (E.moorJ (x,e)) k).1.pay (show separation x x ≤r by rw [separation_self]; omega)).aft (show offsetMask p.B x ⊆ grooveB l p (node x) from Corona.halo_mono ((Nat.le_mul_of_pos_left _ hl):p.B≤ l*p.B) le_rfl)
 rw [show (fun i:Orbit N=> sectorM (i.1,K i))= houseK p (offsetMask p.B x) (heavy w K J0) from funext (costC bI K p k w x E z e)]; exact hv
end proof
end Chamber
end YM.CF.LitCurrent
