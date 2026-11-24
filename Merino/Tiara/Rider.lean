import Merino.Tiara.Parade
import Merino.Plume.Tusk
import YM.SU5.FiniteGaugeData.Tower.Chimes
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

-- Family clashes? use abbreviation
abbrev Horse:=Buffered.Family
variable (K:Calibration) (f:LinksC→ℂ)
abbrev Reins(K: Calibration) :=Signed→Axis→Horse K
variable (J:Reins K)
def staff {K: Calibration}(J:Reins K) (σ:Signed)(i:Axis):=
 let a:=σ.perm.symm i
 if σ.flip a then - J σ a else J σ a
def air (σ:Signed):=present K (f∘Plume.snow σ 0 (detX σ))
variable (m:ℤ)
def rolling (L:Axis→Horse K):=
   ∑i:Axis,(chime K i m (L i) - chime K i (-m) (L i))
def trail (σ:Signed):=
 air K f σ + rolling K m (staff J σ)
lemma negativeCh(i:Axis)(v:Horse K):chime K i m (-v)= -chime K i m v:=by
 rw [← neg_one_smul ℂ v,chime_scale,neg_one_smul]

lemma unstagger (σ:Signed):
 rolling K m (staff J σ)=∑i:Axis,(chime K (σ.perm i) (bend σ i m) (J σ i) -
   chime K (σ.perm i) (bend σ i (-m)) (J σ i)):=by
 unfold rolling
 rw [←Equiv.sum_comp σ.perm]
 apply sum_congr rfl;intro i _
 simp only [staff,Equiv.symm_apply_apply,bend]
 split
 · rw [negativeCh,negativeCh,neg_neg];abel
 rfl

variable {K} (σ:Signed) {r:Side}
local notation "N"=>K.c r
lemma airs:
 air K f σ r = toMark (trinc ((f∘onC (K.c r))∘flashA (rim (K.c r) σ))):=by
 funext V
 unfold air present
 change f (Plume.snow _ _ _ (onC N V.1)) • _ = f (onC N (flashA _ _)) • _
 rw [slush, revoke]
 simp [rim, ←Ratio.root_embed]

lemma ascending {F:Evaluation (K.c r)} {R:Horse K}(u:R r=toMark F)
 (h:Bide.plainP F)(i:Axis)(x:ℤ):
 chime K i x R r =toMark (prance (taxiPlus (slide N i x)) F):=by
 unfold Tower.chime Tower.mirror prance slide
 rw [u,←hinges _ _ h, ←hinges _ _ (Bide.keys _ h),Bide.dance _ _ h, ← fl_prod,
   _root_.mul_inv_rev,flipL_i,flipL_i]

def mark_at (n: Side): Evaluation n→ₗ[ℂ] Mark n where
 toFun:=toMark
 map_add' _ _:=rfl
 map_smul' _ _:=rfl

section stencil
variable {p:RG.BudgetPoint}{W:Scree.Loom (K.c r)}{a b d:ℝ}{y:Spool (K.c r)}
 (h:y.Hem W p a b d)(parts:∀i,J σ i r=toMark (prance (rim (K.c r) σ) (y.jPole W p i)))
include parts h
lemma paradeRoll :
 rolling K (y.stepY:ℤ) (staff J σ) r = toMark (prance (rim N σ) (y.jumps W p)):=by
 change _=(mark_at N) (prance (rim N σ) _)
 rw [unstagger,Finset.sum_apply]
 unfold Spool.jumps
 rw [map_sum,map_sum]
 apply sum_congr rfl;intro i _
 rw [Pi.sub_apply,map_sub,map_sub]
 have u:=ascending (parts i) (plainJ σ h i)
 rw [u, u,shiftJ σ h _ (right_offset i),shiftJ σ h _ (left_offset i)]
 rfl

lemma paradeTrail (pF:f∘onC N=traceCost W p y.post y.color):
 trail K f J (y.stepY:ℤ) σ r=toMark (prance (rim N σ) (y.patchwork W p)):=by
 unfold trail Spool.patchwork
 rw [Pi.add_apply,map_add,paradeRoll J σ h parts]
 rw [airs, pF]
 change _= toMark (prance (rim N σ) (trinc _)+_)
 rw [pr_scalar]
 rfl

lemma parade (A:ℝ)(pF:f∘onC N=traceCost W p y.post y.color) :
 (((A:ℂ) • trail K f J (y.stepY:ℤ) σ):Horse K) r=toMark (prance (rim N σ) (y.opening W p A)):=by
 rw [Pi.smul_apply,paradeTrail f J σ h parts pF,Spool.opening, prB]
 rfl
end stencil

variable (K)
def scene (A:ℝ)(j:Axis)(x:ℤ):Horse K:=
 chime K j x ((A:ℂ) • trail K f J m σ)
variable {K}
def crest {n:Side} (i:Axis)(x:ℤ)(σ:Signed):Sweep n:=
 taxiPlus (slide n i x) * rim n σ

lemma nativeScene {n:Side}(e:K.c r=n) {p:RG.BudgetPoint}{W:Scree.Loom n}{a b d:ℝ}
 (j:Axis)(x:ℤ)(y:Spool n)
 (h:y.Hem W p a b d)(parts:∀i,ship e (J σ i r)=toMark (prance (rim n σ) (y.jPole W p i)))
 (pF:f∘onC n=traceCost W p y.post y.color)(A:ℝ):
 ship e ((scene K f J (y.stepY:ℤ) σ A j x) r)=
   toMark (prance (crest j x σ) (y.opening W p A)):=by
 subst n
 have t:=parade f J σ h (show ∀i,J σ i r=_ from parts) A pF
 have u:=Bide.plain (Brooch.allowedX (h.licensed A))
 trans toMark (prance (taxiPlus (slide N j x)) (prance (rim N σ) (y.opening W p A)))
 · exact ascending t (Bide.keys _ u) j x
 rw [prA _ _ u];rfl
#print scene
end YM.CF.Merino.Tiara
