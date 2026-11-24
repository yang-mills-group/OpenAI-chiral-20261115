import YM.CF.Scion.Rye
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel

open Cour Acorn Atala Reef MeasureTheory Jet
variable {N B:Side} (D e:ℝ) (J:Pride (mid N B)) (X Y:Seal (Site (Domain N B)))
variable (V:Tints N B e)
def strokeC(A: Ids (mid N B))(x:Castle N B e X):ℂ:= let S:=Hive.chip X A; cSignX (Hive.χ S) (V (actS S X) (actS S Y) (strideH X A x))
lemma peak_h(b:Bool)(t:ℂ):Complex.exp (cSignX b t)=cSignX b (Complex.exp t):=by cases b; rfl; exact Complex.exp_conj _ -- order
lemma tile (j:ℕ)(v a:ℝ)(h:Dyes D e J j V v a)(g:Grove (terr _) X)(x:Castle N B e X)(A:Ids (mid N B))(hp:WordK J)(hq: ClearP J): ∑ Y,strokeC e X Y V A x= hoopI X e J x:=by
 obtain ⟨C,l,t,b⟩:=h.arch _ (grove_t _ (Hive.chip X A) g); let i:=Hive.chip X A; let W:=strideH X A x; let f:= V (actS i X); let K:Seal (Seat (mid N B)) ≃ Seal (Seat (mid N B)) := Equiv.ofBijective (actS i) ((Finite.injective_iff_bijective).mp (actG_in _)) -- tune
 let T:=cSignX (Hive.χ i); rw [show ∑ Y,strokeC e X Y V A x=T (∑ z,f z W) from ?_,← b]
 · change cSignX _ (Complex.exp _) =Complex.exp _; rw [←peak_h]; congr 1; unfold W strideH; -- tune
   have he (j:Bool):pigment J ((strideH X A x).val j)=T (pigment J (x.val j)):=by change pigment J (stir _ _ (gauge _ (x.val j)))= _; rw [portPartH J hp hq,pinG]; rfl -- tune
   rw [show pigment J _ = _ from he false, show pigment J _=_ from he true]
   unfold T; cases hx:Hive.χ i<;>simp [cSignX]
 unfold T; rw [show cSignX _ _= (∑ z,cSignX (Hive.χ i) (f z W)) from ?_]; exact Fintype.sum_equiv K _ _ (fun _=>rfl)
 cases h:Hive.χ i <;> simp [cSignX]
end YM.CF.Scion
