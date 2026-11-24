import YM.SU5.SatinWard.Resolution.ShoreE
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
variable (D:Division)
private lemma stair_glue (G:Cover→List Cover)(h:∀ x y,G (x+y)=(G x).map (fun z=> z+y)) (i:Axis)(x y:Cover)(r:ℕ) : stair G i (x+y) r = (stair G i x r).map (fun z=> z+y) :=by
 induction r with
 | zero=> rfl
 | succ r p=> simp only [stair,List.map_append,p]; rw [show x+y+r • step i=x+r • step i+y by abel, show x+y-r • step i=x-r • step i+y by abel,show x+y+(r+1) • step i=x+(r+1) • step i+y by abel,show x+y-(r+1) • step i=x-(r+1) • step i+y by abel]; rw [h (x+r • step i) y, h (x-r • step i) y,h (x+(r+1) • step i) y,h (x-(r+1) • step i) y]
lemma layout_glue (x y:Cover)(L:List Axis) : layout r (x+y) L=(layout r x L).map (fun x=>x+y):=by induction L generalizing x y with |nil=> rfl|cons i L p=> exact stair_glue _ p i x y r
abbrev floorLine (r:ℕ): List Cover:= layout r 0 arcOrder
noncomputable def roomSand (S T:Cover→ Cover→Op I) (x y l:Cover): Op I:= S x l*coinPal D* T l y
lemma layFund (S T:Op (Single N))(r:ℕ)(x y l:Cover): (shore N x y (S * hall D (roomW (wrap N l) r)*T))= ((floorLine r).map (fun u=>roomSand D (fun i j=> shore N i j S) (fun i j=> shore N i j T) x y (u+l))).sum:=by
 rw [←layout_eq]; have hx:layout r l arcOrder= (floorLine r).map (fun i=>i+l):=by simpa only [floorLine,zero_add] using layout_glue (r:=r) 0 l arcOrder
 rw [hx, List.map_map]; generalize floorLine r=L; induction L with|nil=> simp only [List.map_nil,List.sum_nil]; unfold hall; rw [mul_zero,zero_mul,mul_zero,zero_mul,map_zero]| cons a L p=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,hallPlus, mul_add,add_mul,map_add,p,Function.comp_apply,crestWind]; rfl -- maybe rfl goal
-- fixed finite torus equality. include positive lags? n.Context. `rollCurrent` exact. supply P/T a/v.
local notation "Ζ"=> markG D N
local notation "Φ" x:max y:max W:max=> shore N x y W
lemma willF (T P: Op (Single N)) : inward T P 0= T* P*(1-T)+(1-T)*P*T:=by unfold inward capT blockD; rw [mul_zero,zero_mul,sub_zero,add_zero,one_mul,mul_one]; noncomm_ring
lemma layGroup (P: Op (Single N))(T: Cover)(r:ℕ)(x y:Cover): let Ψ:Cover→ Cover→Op I:= fun i j=> shore N i j P; let Θ:Cover→ Cover→Op I:=fun i j=> shore N i j (1-P); shore N x y (Sault.inward P (hall D (roomW (wrap N T) r)) 0)= ((floorLine r).map (fun u=>roomSand D Ψ Θ x y (u+T))).sum+((floorLine r).map (fun u=>roomSand D Θ Ψ x y (u+T))).sum:=by
 intro Ψ Θ; rw [willF,map_add, layFund,layFund]
#print axioms layGroup
end AuroraX
end YM.CF.LitCurrent
