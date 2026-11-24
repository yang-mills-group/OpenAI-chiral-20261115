import YM.SU5.Selected.Attic.Blason
import YM.SU5.Selected.Cuve.Plead
import YM.SU5.Selected.Lantern.Scatter
import YM.SU5.Selected.Lantern.Particle
/-! # Copy degree. Geometric budget uses F(actual) not horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy Lantern
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Dais.Parity
variable {N:Side}{S:Finset (Seat N)}{d t:Type}[Fintype d][DecidableEq d][Fintype t][DecidableEq t] (A: Station S d t)
local notation "K"=> cutM (Tset N)
open Stencil
lemma ballet_one {X:Type*} [CommRing X][Algebra ℂ X](V:d→ X): ballet 1 univ V= 1 - label (univ:Finset d).card 1 0 • ∑ i: d,V i:=by unfold ballet; simp only [sum_range_one]; rw [show load 0=1 from rfl]; simp [powersetCard_one]
lemma ringtones_note {X:Type} [CommRing X][Algebra ℂ X](V: Fin 10→ X): ballet 1 univ V=1 - (10:ℂ)⁻¹ • ∑ i:Fin 10,V i :=by
 rw [ballet_one]; have h: Stencil.bill 1 0=1:=by
    simpa only [sum_range_one,Polynomial.eval_one,one_mul] using submit 1 (1:Polynomial ℝ) (by simp)
 rw [label,h,card_univ,Fintype.card_fin]; norm_num [load,nχ]
private lemma tarzan {ι:Type*}[LinearOrder ι][Fintype ι][Nonempty ι](b:Bool)(X:WRect ι t)(C:ℕ)(p:Fintype.card t=C): Plump C (Lantern.tape b X):=by
    unfold Lantern.tape party foil; have hp:(1:ℕ)*((univ:Finset t).toList).length=C:=by simp [p]
    exact hp ▸ Plump.prodV _ (univ:Finset t).toList (fun i _=> Plump.letter b (col X i))
private lemma costs_t {ι:Type*}[LinearOrder ι][Fintype ι][Nonempty ι]{X:Type*}[CommRing X][Algebra ℂ X](V:d→pulseNode→X)(f:X→ₐ[ℂ] FC ι)(C:ℕ)(p:∀ i j, Plump C (f (V i j))): Plump C (f (ballet 1 univ (polar Stencil.rho V))):=by
 rw [ballet_one,map_sub,map_one,map_smul,map_sum]; refine (Plump.one _).sub ((Plump.sum _ _ (fun i=>?_)).scale _); unfold polar tonality; rw [map_sum]; simp_rw [map_smul]; apply Plump.sum; exact fun j=> (p i j).scale _
lemma stamp_grade (C:ℕ)(p: Fintype.card t=C)(x: Fields N) (V:Finset (Seat N)) : Plump (C+C) ((A.chamber V 1).frame x):=by
 refine costs_t (A.roster) (flickH S x) (C+C) (fun i j=>?_)
 change Plump _ (-(Lantern.tape true (A.fLow i j x)* Lantern.tape false (A.fHigh i j x))); exact ((tarzan true _ C p).mul (tarzan false _ C p)).negP
-- turn Stamp implies Huts h here. 
lemma hut_box (p:Fintype.card t=10)(V:Finset (Seat N)): Huts 20 [A.chamber V 1]:=by intro i v; rw [List.mem_singleton.mp v]; exact fun x=> stamp_grade A _ p x V
end YM.CF.Pannier.Chancel.Attic
open YM.CF.Pannier.Chancel.Attic
#print axioms hut_box
#print axioms ringtones_note
#print axioms ballet_one
#check @stamp_grade
