import YM.SU5.SatinWard.Resolution.Floribunda
import YM.SU5.SatinWard.Resolution.GrainMap
import YM.SU5.SatinWard.Resolution.Beryle
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
noncomputable abbrev HeartP {S:Type}{L:Filter S}{k:ℕ} (X:Cross k L) (i:S): Op (Single (X.N i)):= X.oil i (profile 1)
noncomputable def armP (p:Stack)(x y:Cover): Op I:= seam (y-x) (p 0)
noncomputable def brightEnd(p:Stack)(x y:Cover):Op I:=seam (y-x) (1-p 0) -- Crest ∎ complement.
private lemma β_ticket(Y:Oil N)(x y:Cover) (i j:I) : tuft Y (stream N) x y i j 0= (shore N x y (Y (profile 1))) i j:=by change lint (Y (profile (_root_.Zephyr.Chern.petals _ _))) _ _ _ _= _; rw [petal_idle]; rfl
include X'
variable (κx:X'.Relax p)
include κx
lemma brinkOne (x y:Cover): Tendsto (fun i=>shore (X'.N i) x y (HeartP X' i)) F (𝓝 (armP p x y)):=by
 rw [Branch.kernel_test]; intro i j; let h:= κx.pulse (y-x) (-y) i j 0; rw [show (-(y-x) :Cover)- -y=x from (by abel), neg_neg,show splice _ _ 0=seam (y-x) (p 0) i j from ?_] at h; simp_rw [β_ticket] at h; exact h
 change 1 * (seam (y-x) (p 0) i j)= _; exact one_mul _
lemma brinkTwo (x y:Cover): Tendsto (fun i=>shore (X'.N i) x y (1-HeartP X' i)) F (𝓝 (brightEnd p x y)):=by
 have he:Tendsto (fun i:S=> shore (X'.N i) x y 1) F (𝓝 (if x=y then (1:Op I) else 0)):= by
    apply EventuallyEq.tendsto; filter_upwards [X'.apply_lift x, X'.apply_lift y] with i a b using shore_one (fun h=> a.symm.trans ((congrArg Lattice.lift h).trans b))
 simp_rw [map_sub]; unfold brightEnd; rw [map_sub, show seam (y-x) (1:Coats I)=(if x=y then (1:Op I) else 0) from ?_]; · exact he.sub (brinkOne _ κx x y)
 ext i j; by_cases h:x=y
 · subst y; rw [sub_self,if_pos rfl, seam_apply]; by_cases g:i=j; · subst j; rw [Matrix.one_apply_eq,Matrix.one_apply_eq]; change echo 1 0=1; simp [Zephyr.Chern.echo] -- root
   rw [Matrix.one_apply_ne g,Matrix.one_apply_ne g]; change echo 0 0=0; simp [Zephyr.Chern.echo]
 rw [if_neg h,seam_apply]; by_cases g:i=j; · subst j; rw [Matrix.one_apply_eq]; change echo 1 (y-x)=0; rw [_root_.Zephyr.Chern.echo,if_neg (sub_ne_zero.mpr (Ne.symm h))]
 rw [Matrix.one_apply_ne g]; change echo 0 (y-x)=0; simp [_root_.Zephyr.Chern.echo]
variable (D:Division)
noncomputable def porchL (p:Stack)(r:ℕ)(x y o:Cover):= ((floorLine r).map (fun u=>roomSand D (armP p) (brightEnd p) x y (u+o))).sum+((floorLine r).map (fun u=>roomSand D (brightEnd p) (armP p) x y (u+o))).sum
lemma fundsD (x y o:Cover)(r:ℕ) : Tendsto (fun i=> shore (Nβ i) x y (Sault.inward (HeartP X' i) (hall D (roomW (wrap (Nβ i) o) r)) 0)) F (𝓝 (porchL D p r x y o)):=by
 let A₀:= armP p; let V:= brightEnd p; let Q:=fun i:S=> HeartP X' i; let f(i:S):=fun x y=>shore (X'.N i) x y (Q i); let g(i:S):=fun x y=>shore (X'.N i) x y (1-Q i)
 let H (L: List Cover)(S U:Cover→ Cover→ Op I):Op I:= (L.map (fun u=>roomSand D S U x y (u+o))).sum
 change Tendsto _ _ (𝓝 (H _ A₀ V+H _ V A₀)); have hp{F₁ F₂:S→ Cover→ Cover→ Op I}{P₁ P₂:Cover→ Cover→ Op I}(u:∀ x y:Cover,Tendsto (fun i=> F₁ i x y) F (𝓝 (P₁ x y)))(v:∀ x y:Cover,Tendsto (fun i=>F₂ i x y) F (𝓝 (P₂ x y)))(L:List Cover): Tendsto (fun i=>H L (F₁ i) (F₂ i)) F (𝓝 (H L P₁ P₂)):=by
    induction L with
    | nil=> exact tendsto_const_nhds
    | cons h L p => exact (((u x (h+o)).mul_const _).mul (v (h+o) y)|>.add p )
 exact ((hp (F₁:=f) (F₂:=g) (brinkOne _ κx) (brinkTwo _ κx) _).add (hp (F₁:=g) (F₂:=f) (brinkTwo _ κx) (brinkOne _ κx) _)).congr (fun i=> (layGroup D _ _ _ x y).symm)
#print axioms fundsD
end AuroraX
end YM.CF.LitCurrent
