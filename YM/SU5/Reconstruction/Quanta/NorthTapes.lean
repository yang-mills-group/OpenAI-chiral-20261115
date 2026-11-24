import YM.SU5.Reconstruction.Quanta.Lamplight
import YM.SU5.FiniteGaugeData.Tower.Diagram

/-! # Pole proof, true root vacuum with graded tests. -/
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
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)


-- integer-aligned federal planner (buffer plane across positive time)
def poleForm (J:Calibration)(j:Axis)(z:ℤ)(b:Bool)(F F':Family J):Family J:= Reflect.chord b • (mirror J j z F*F')
variable {J:Calibration}{g₀ : Bool}{S S' : Finset Cover}{F F' : Family J}
variable (a:Axis)(z:ℤ)
namespace NorthTapes
lemma statement (x:InTest J true S g₀ F) (y:InTest J true S' g₀ F') : InTest J true (reflectedBox a z S∪S') false (poleForm J a z g₀ F F'):=by
 let t:= InTest.mul ((axial J a z x).mono (subset_union_left (s₂:=S'))) (y.mono (subset_union_right (s₁:=reflectedBox a z S)))
 rw [Bool.xor_self] at t; exact InTest.smul _ t
variable (n k₁:ℕ)
local notation "B"=>Λ.block
local notation "A₁"=> Heat.gaugeShift Λ.block z
local notation "M"=> side Y n s
local notation "P₁"=> poleForm K a A₁
local notation "m"=> momentm Y n s
local notation "ν"=> (Y.voyage n).CapeT s
lemma hot_positive (p:Ferry Y s n k₁){f:Family (tent Y H)}(x:AtSupport g₀ (band ((K).c m) a A₁ (reserve Λ l)) (f m)):0 ≤ hot Y H s n k₁ (P₁ g₀ f f):=by
 let w:=lamp_poles Y n k₁ p.depth s p.enters a z (distribute Y H s n f) (plane_cast a _ _ (terrain Y H (Y.ir n) s) x)
 let f':Mark M:=distribute Y H s n f
 let Z:= ((Y.voyage n).Q k₁ p.depth).gram s
 have he: 0≤ partitionZ Z Λ.U ν := by
    have hp:= throbbing Y n k₁ p.depth s p.enters a z 1 (AtSupport.oneM (band M a A₁ (reserve Λ l)))
    rwa [mul_one,show reflMark a A₁ (1:Mark M)=1 from funext fun _=> Fock.theta_one _,markvac] at hp
 unfold hot; rw [dif_pos p.depth]; change 0 ≤ markedRead (distribute Y H s n (P₁ g₀ f f)) _ _/ _
 have e:distribute Y H s n (P₁ g₀ f f)=Reflect.chord g₀ • (reflMark a A₁ f'*f'):=by
    unfold poleForm; rw [(distribute_arith Y H s n (mirror (tent Y H) a A₁ f*f) f (Reflect.chord g₀)).2.2.1,
       (distribute_arith Y H s n (mirror (tent Y H) a A₁ f) f (0:ℂ)).2.1,
       (distribute_arith Y H s n f f (0:ℂ)).2.2.2.2 a A₁]
 rw [e]; exact div_nonneg w he
where plane_cast(a:Axis)(z:ℤ)(v:ℕ){c d:Side}(q:c=d){f:Mark c}(w:AtSupport g₀ (band c a z v) f): AtSupport g₀ (band d a z v) (Tower.ship q f):=by subst d; exact w
include V
lemma I_positive {f:Family (tent Y H)}(w:InTest K true S g₀ f)
    (x:AtSupport g₀ (band ((K).c (momentm Y n s)) a A₁ ((K).ℓ)) (f (momentm Y n s))):0≤ I s (P₁ g₀ f f) n:=
 ge_of_tendsto ((warm_limit Y H V s (aux_test (statement a A₁ w w))).inner n) (((V.pick.pass Y H s n)).mono fun _ p=> hot_positive Y H s a z n _ p x)
lemma election0 {f:Family (tent Y H)}(p:InTest K true S g₀ f)(h: region a A₁ ((K).ℓ) S):0≤ E s (P₁ g₀ f f):=by
 apply ge_of_tendsto ((warm_limit Y H V s (aux_test (statement a A₁ p p))).periods)
 filter_upwards [((momentum Y s).comp V.pick.grow_i.tendsto_atTop).eventually (recedes (tent Y H) h)] with r b₀
 exact I_positive Y H V s a z (i r) p ((p.support _).mono b₀)
end NorthTapes
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.NorthTapes.election0
