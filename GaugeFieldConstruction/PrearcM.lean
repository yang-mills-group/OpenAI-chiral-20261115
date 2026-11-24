import GaugeFieldConstruction.Durango4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I θ E:Type}[Fintype I][LinearOrder I]{n:Side}
open Rio Grotto Isle Lattice.Corona
section
variable (σ:I→Seat n)(F:XE I (InkD n) n)(K:KK I (Copy n) n)
variable {t a b v η:ℝ}(P:BudgetPoint) (h:ℝ)(u:0<h)
open Py Py.Riant Nor
local notation "θX" i:max=> (fun j=>F (i,j))
local notation "θY" i:max=> (fun j=>K (i,j))
-- book converters both directions.C.Lattice n AutoImp
structure Horn4 (r w z₀:ℝ)(v:ℕ): Prop where
   core : Ledges (SecX (KeyUp P) u.le n) σ (fun i j=>F (i,j))
   holdK :Ledges (SecK P u.le n) σ (fun i j=>K (i,j))
   paw: BookT (SecX (KeyUp P) u.le n) (fun i j=> F (i,j)) P.B (realm_C σ) w r z₀
   crowd: BookT (SecK P u.le n) (fun i j=> K (i,j)) P.B (realm_C σ) w r z₀
   haloT(i:KI I n): K i≠0→ Lattice.halo (Rill.cipherK v) i.2.val.2⊆ cloudK i.2
private lemma showsF{M E θ : Type}[Fintype M][Zero E]{Γ:dues I M→ θ→ E}(x:dues I M)(u:Γ x≠0):∃ y:θ, Γ x y≠0:=by by_contra! h; exact u (funext h)
-- Beam extraction exact cost placement
variable {ι M Z:Type}[Fintype ι][NormedAddCommGroup M][NormedSpace ℂ M][CompleteSpace M]
include u
variable (r:ℝ)(p:0 < r)(a w:ℝ)
local notation "T"=> (realm_C σ)
private def tariffs (t:ℝ) (B:Finset I→ι→ℝ) (i:dues I ι):= if i.1∈T then r^i.1.card*(t*B i.1 i.2) else 0
include p
omit u
private lemma term4 (H:Cornea ι Z M (More n))(V:dues I ι → Z→ M)(B:Finset I→ι→ℝ)(f:∀ i∈realm_C σ,∀ j,H.Lux j (V (i,j)) (B i j))(y:∀ x:Seat n,(∑ i∈realm_C σ,r^i.card*(∑ j∈ univ.filter (fun j=>x∈H.Φ j),dra_k P.B a (H.Φ j)* B i j)) ≤ w) (v₀:ℝ)(t:0≤ v₀) : 0 ≤ tariffs σ r v₀ B ∧ ∀ x:Seat n,pointX H.Φ (tariffs σ r v₀ B) (March P.B a) x ≤ v₀*w :=by
 constructor
 · rintro ⟨i,j⟩; unfold tariffs; split; next g=> exact mul_nonneg (pow_pos p _|>.le) (mul_nonneg t (H.posG _ _ _ (f i g _)))
   exact le_rfl
 intro i; rw [← pointX_π]
 let L(x:dues I ι):= v₀*B x.1 x.2
 rw [show tariffs σ r v₀ B =fun i:dues I ι=> if i.1∈realm_C σ then r^i.1.card*L i else 0 from rfl, ←preissue]; apply (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left (y i) t)
 rw[mul_sum]; apply sum_congr rfl; intro x y; rw [mul_left_comm]; apply congrArg (r^x.card*·); rw[mul_sum]; apply Finset.sum_congr rfl; intro i v; dsimp only [L]; ring
variable {r p} (z₀:ℝ)(v:ℕ)(B: Horn4 σ F K P h u r a z₀ v)
-- syntax.prepare.M.PW
omit p
include B u
lemma horn_hold : keepArc σ cloudP F ∧ keepArc σ cloudK K:=by
 constructor
 · rintro ⟨i,j⟩ t; obtain ⟨v,h⟩:= showsF (Γ:=F) _ t; exact B.core j v trivial i h
 rintro ⟨i,j⟩ t; obtain ⟨v,h⟩:= showsF (Γ:=K) _ t; exact B.holdK j _ trivial i h
variable (pr:0<r)
include pr
-- Reverse charge P.implicit in arc.
lemma hornprice : ∃ (X:PI I n→ℝ)(Y:KI I n→ℝ), BillX P σ h r X F ∧ BillF P σ h r (Rill.cipherK v) Y K ∧∀ i:Seat n,pointX cloudP X (March P.B a) i ≤ chi_f P.order*z₀ ∧ pointX cloudK Y (March P.B a) i ≤ chi_f P.order*z₀:=by
 obtain ⟨Q,H,t⟩:=B.paw; obtain ⟨A',d,T'⟩:=B.crowd
 let X:= SecX (KeyUp P) u.le n; let Y:=SecK P u.le n; let g:=chi_f P.order; have hg:=spicy_f P.order
 have hp:=term4 σ P r pr a z₀ X F Q H t g hg; let hu:=term4 σ P r pr a z₀ Y K A' d T' g hg; have Q':=horn_hold σ F K P h u a z₀ v B
 refine ⟨tariffs σ r g Q,tariffs σ r g A',⟨fun x=> ?_,fun i=>hp.1 _,Q'.1⟩,⟨fun x=>?_,fun i=>hu.1 _,Q'.2⟩,fun i=> ⟨hp.2 i,hu.2 i⟩⟩
 · rcases x with ⟨i,j⟩; unfold PitR tariffs; split
   next w=>
    rw[Bplain,mul_comm (_^_),mul_div_cancel_right₀ _ (pow_pos pr _|>.ne')]
    have h : Medal (KeyUp P) j.val.2 ∅ (oV (F (i,j))) _ (g * Q i j):= rimR (H _ w j) u.le
    obtain ⟨T0,A,L,G1⟩:= h.pays; refine ⟨h.toThemeR,T0,A,?_,G1⟩; intro v₀ i h hU; exact L v₀ i hU
   next q=> rw [show F (i,j)=0 from Classical.byContradiction (fun t=> q (Q'.1 _ t).1), Bplain,zero_div]; exact Medal.zeroT
 rcases x with ⟨i,j⟩; unfold tariffs; split
 next q=>
    constructor
    · unfold Bplain; rw [mul_comm (_^_),mul_div_cancel_right₀ _ (pow_pos pr _|>.ne')]; exact (rimP (d _ q _) u.le).2
    intro x y; have D:ForceB P j (K (i,j)) h _:=d _ q j; exact ⟨D.protect _ y, B.haloT _ (fun z=>y (congrFun z x))⟩
 next q=> rw [show K (i,j)=0 from Classical.byContradiction (fun t=> q (Q'.2 _ t).1)]; exact (ReefxF _).tele (i,j)
#print axioms hornprice
end
end Iona
end YM.CF.Scree.Ing
end
