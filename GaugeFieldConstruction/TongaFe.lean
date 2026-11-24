import YM.SU5.FiniteGaugeData.Tower.Cloaks
import YM.SU5.FiniteGaugeData.Tower.Ink
import GaugeFieldConstruction.PavilionFe
import GaugeFieldConstruction.GladeFe
import GaugeFieldConstruction.TimorFe
import GaugeFieldConstruction.GaolFe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Native gauge holds also on the step lift (no Protected equality hypotheses).
-/
open Fock Laurent Bloch Next.Free Fir Branch Tap Tenant Precision Drapes Vault Tree
open Reed (Fine think)
open BrentFe
open YM.GaugeFieldConstruction (Flavor)
open YM.GaugeFieldConstruction.Flavor
open XGarden.MastTin.ArtCart
set_option maxHeartbeats 70000
variable {K: Calibration}
open XGarden.MastTin.ArtCart
namespace MatrixFe
variable (g:Flavor)
def RayPFe (F: Family K):Family K:= fun i=>latticeFφFe g _ (F i)
lemma rayAe(x y:Family K): RayPFe g (x+y)=RayPFe g x+RayPFe g y:=funext fun _=> funext fun _=> map_add _ _ _
lemma rayBe(z:ℂ)(x:Family K): RayPFe g (z • x)=z • RayPFe g x:=funext fun _=> funext fun _=> twist_scalar ..
lemma rayMe(x y:Family K):RayPFe g (x*y)=RayPFe g x*RayPFe g y:= funext fun _=>funext fun _=>map_mul _ _ _
lemma rayZe : RayPFe g (0:Family K)=0:=funext fun _=> funext fun _=>map_zero _
lemma rayUe : RayPFe g (1:Family K)=1:=funext fun _=> funext fun _=>map_one _
lemma rayVe(f:PairsC →ℂ):RayPFe g (scalar K f)=scalar K f:=by
 funext m i; let h:=quantU (TVfe (K.c m) g); unfold scalar RayPFe; change twist h ( (f _ ) • (1:FC (Single (K.c m))))= _; rw[twist_scalar,map_one]
lemma raySFe {I:Type}(S:Finset I)(F:I→Family K):RayPFe g (∑ i∈ S,F i)=∑ i∈S,RayPFe g (F i):=by induction S using Finset.induction_on with| empty => rw[sum_empty,sum_empty,rayZe]|@insert i S p ih=> rw[sum_insert p,sum_insert p,rayAe,ih]
local notation "♥" g:max b:max => YM.GaugeFieldConstruction.pay (sensation g b) (1:ℂ)
lemma rayHP (i:SpinIdx)(b:SU.Slot)(x: Cover)(N:Side): acts (TVfe N g).val (basisC N x i b)= ♥ g b • basisC N x i (sensor g b):=by
 unfold basisC; rw[map_smul, ←smul_comm]; congr 1; apply PiLp.ext; intro j; rw[basis_act]; rw [ilkFe]; let K':= Lifted.index N x i (sensor g b); change (if K'=j then ♥ g b else (0:ℂ))=(♥ g b • basisKet K').ofLp j; by_cases p:j=K'
 · subst j; rw [if_pos rfl]; simp
 rw [if_neg (show K'≠ _ from Ne.symm p)]; simp [Ne.symm p,p]
lemma rayCf(x:Cover)(b:SU.Slot)(i:SpinIdx): RayPFe g (creation K x i b)= ♥ g b • creation K x i (sensor g b):=by funext m y; change twist (quantU (TVfe (K.c m) g)) (create (basisC (K.c m) x i b))= ♥ g b • create (basisC _ _ _ _); rw [twist_create,rayHP, map_smul] -- notation
private lemma payStar (b:SU.Slot):star (♥ g b)= ♥ g b :=by cases sensation g b<;>simp
lemma rayRf(x:Cover)(b:SU.Slot)(i:SpinIdx): RayPFe g (removal K x i b)=♥ g b • removal K x i (sensor g b):=by funext m y; change twist (quantU (TVfe (K.c m) g)) (Fock.remove (basisC (K.c m) x i b))= ♥ g b • Fock.remove (basisC _ _ _ _); rw [twist_remove, rayHP]; unfold Fock.remove; rw[map_smul, star_smul,payStar] -- tune
variable {S:Finset Cover} {p q:Bool}{F:Family K}
lemma axP (h:InTest K p S q F): InTest K p S q (RayPFe g F):=by
 induction h with
 | seed p=>rw[rayVe]; exact .seed p
 | creator b p v=>rw[rayCf]; exact .smul _ (.creator _ p v)
 | remover b p v=>rw [rayRf]; exact .smul _ (.remover _ p v)
 | zero=>rw [rayZe]; exact .zero
 | one=>rw[rayUe]; exact .one
 | add _ _ a b=>rw[rayAe]; exact .add a b
 | mul _ _ a b=>rw[rayMe]; exact .mul a b
 | smul c _ ih=>rw[rayBe]; exact .smul c ih
-- commutes with mirrors & transport
variable (a:Axis)(z:ℤ)(b:SU.Slot)(X:Cover)(i:SpinIdx)
private lemma RCFe: Tower.mirror K a z (creation K X i b) = -Complex.I • ∑ j, star (Mir.pin a j i) • removal K ((plane a z).flee X) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold mirror reflMark creation removal
 rw [(flips_basisC a z (K.c m) X i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma RRFe: Tower.mirror K a z (removal K X i b)=Complex.I • ∑ j, Mir.pin a j i • creation K ((plane a z).flee X) j b:=by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold mirror reflMark creation removal
 rw [(flips_basisC a z (K.c m) X i b).2]; simp only [map_sum,map_smul]
private lemma leftComFe {V:SpinIdx→Family K}(U D:ℂ) : U • (D • ∑ i:SpinIdx, V i)= D • ∑ i:SpinIdx, U • V i:=by rw [smul_comm U]; apply congrArg (D • ·); rw[Finset.smul_sum] -- tune
lemma flipFe (h:InTest K p S q F): Tower.mirror K a z (RayPFe g F)=RayPFe g (Tower.mirror K a z F):=by
 induction h with
 | seed p=>
    rw [rayVe]; funext m x; change _=twist _ ((mirror _ _ _ (scalar _ _)) _ _); simp only [mirror, scalar,reflMark,Fock.theta_smul,Fock.theta_one,twist_scalar,map_one]
 | @creator x i b h v=>
    rw [rayCf,mirror_scale,RCFe,RCFe,rayBe,raySFe, payStar]; simp only[rayBe,rayRf, leftComFe]; apply congrArg; apply sum_congr rfl; intro i _; rw [smul_comm]
 | @remover x i b h v=>
    rw [rayRf,mirror_scale,RRFe,RRFe,rayBe,raySFe,payStar]; simp only [rayBe,rayCf,leftComFe]; apply congrArg; apply sum_congr rfl; intro i _; rw [smul_comm]
 | zero=> rw [rayZe,show Tower.mirror K a z 0=0 from funext fun _=>funext fun _=>Fock.theta_zero _,rayZe]
 | one=> rw [rayUe,mirror_unit, rayUe]
 | add _ _ i j=> rw [rayAe,mirror_plus,mirror_plus,rayAe,i,j]
 | mul _ _ i j=> rw [rayMe,mirror_times,mirror_times,rayMe,i,j]
 | smul c _ ih=>rw [rayBe,mirror_scale,mirror_scale,rayBe,ih]
#print axioms axP
#print axioms flipFe
end MatrixFe
end YM.CF.Buffered.Afterglow.Tower
