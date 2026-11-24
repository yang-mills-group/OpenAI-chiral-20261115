import YM.CF.Continuum.Current
import YM.CF.Emu.Town
/-!
# Match point currents to FiniteGaugeData's asymptotic reader vocabulary
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter Metric Finset Fock Lattice Lat Rush Cube SU Scroll Spire Tulip Mir Mir.Trip Phase RP
open Flare Emu Dial Ember Kea
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {N:Side}
/-- convention `u` in later current components starts on the gauge/matter anchor
specified by o; no tag argument, even before taking term-specific Haar integral. -/
def matchPair (o: Site N)(U:Bkg (More N))(t:E)(R:ℝ)(z:Cover)(a b:Wing): FC (Single N):=
  ton (nac o U t R (z,a))*ton (nac o U t R (z,b))

structure Component where
  fam : Family
  up : SpinIdx
  down : SpinIdx
  hu : up ∈ plusHalf
  hd : down ∉ plusHalf
open Component
variable (o : Site N)(U : Bkg (More N))(t : E)(R : ℝ)(z : Cover)(a : Component)

lemma match_trace (l : Lattice.Order)(w : 0≤R) :
    ∑ j∈colors a.fam, matchPair o U t R z ⟨a.down,j,l⟩ ⟨a.up,j,l⟩ =
      ((R:ℂ)^3) • current N a.fam (o+wrap _ z) a.up a.down U := by
  classical
  let f : Site (More N)→ E:=fun _=> (travel U (node o) (leap z l))⁻¹*t
  let L:= twist (quantU (tradew N f)); let K(i:SpinIdx)(j:Slot):Single N:=((o+wrap _ z,i),j)
  have hK(i j): hint o z ⟨i,j,l⟩ U t= wind o z • acts (tradew N f).val (basisKet (K i j)) :=by
    unfold hint; rfl
  let s:=a.up; let d:=a.down
  have hs(i:Slot) : signW ⟨s,i,l⟩=false:=by simp only [signW,decide_eq_false_iff_not]; exact not_not_intro a.hu
  have ht(i:Slot) : signW ⟨d,i,l⟩=true:= by simp only [signW,decide_eq_true_eq]; exact a.hd
  let w' := wind o z; let A:=gain R*w'
  have hu : star A=A:=by unfold A; rw [star_mul', gain, show star w'=w' from fee_real _]; simp
  have he : A*A=(R:ℂ)^3:=by
    unfold A; rw [mul_mul_mul_comm, show w'*w'=1 from fee_one _,mul_one,gain, ← sq, ←Complex.ofReal_pow, Real.sq_sqrt (by positivity),Complex.ofReal_pow]
  let F := fun j=>matchPair o U t R z ⟨d,j,l⟩ ⟨s,j,l⟩; let T := current N a.fam (o+wrap _ z) s d U
  have h(j:Slot): F j = ((R:ℂ)^3) • L (put (K s j)*takeF (K d j)) := by
    unfold F matchPair; unfold ton nac; dsimp only; rw [hK,hK,hs,ht, if_neg Bool.false_ne_true, if_pos (rfl: Bool.true = Bool.true), ←mul_smul, ←mul_smul]
    change remove (-(A • (acts (tradew N f).val (basisKet (K d j))))) * create (A • acts (tradew N f).val (basisKet (K s j))) = _
    have h0:remove (-(A • (acts (tradew N f).val (basisKet (K d j))))) = - (A • L (takeF (K d j))) := by
      unfold remove; rw [map_neg,map_smul,star_neg,star_smul,hu,←twist_create,create_put]; unfold takeF L; rw [map_star]
    rw [h0, map_smul,←twist_create,create_put,neg_mul]; change - ((A • L _) * (A • L _))= _; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul,he,←map_mul,←smul_neg,←map_neg]; congr 2
    have p:=mixed (K d j) (K s j); rw [if_neg (fun h=>a.hd ( (show a.down=a.up from Prod.mk.inj (Prod.mk.inj h).1|>.2) ▸ a.hu))] at p; exact neg_eq_iff_add_eq_zero.mpr p
  have hc:L T=T :=by unfold T L current; rw [dg_cov,jOp_gauge]
  change ∑ j∈_,F j=_; simp_rw [h,←smul_sum,←map_sum]; rw [←current_words]; exact congrArg ((R:ℂ)^3 • ·) hc
end YM.CF.Window
