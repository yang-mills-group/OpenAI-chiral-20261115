import Merino.Tiara.Coach
import Merino.Tiara.Rise
import Merino.Plume.Runners
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


open SlabMark
variable {K:Calibration}
 {f:LinksC→ℂ}{F:ℕ→LinksC→ℂ}{j:Reins K}{J:ℕ→Reins K}
 {d:ℕ}{b:ℝ}
lemma steel {S:Finset Cover}
 (p:∀σ i,Elite S (fun n=>J n σ i) (j σ i))(σ:Signed)(i:Axis):
    Elite S (fun n=>staff (J n) σ i) (staff j σ i):=by
 simp only [staff]
 split;exact (p σ _).neg
 exact p σ _
lemma brim {S:Finset Cover}
 (p:∀σ i,Elite S (fun n=>J n σ i) (j σ i))(Q:ℝ)(i:Axis):
    Elite S (fun n=>tassels K Q (J n) i) (tassels K Q j i):=by
 simp only [tassels,Pi.smul_apply,Finset.sum_apply]
 apply Elite.smul
 exact Elite.sum _ fun σ=>(steel p σ i).smul _

def roomBox(d m:ℕ):=Lattice.box (d+2*m)
lemma movedRoom (m:ℕ)(i:Axis)(x:ℤ)(h : -(m:ℤ) ≤ x ∧ x ≤ m):
    Tower.address i x (Lattice.box d)⊆roomBox d m:=by
 intro v g;obtain ⟨w,a,rfl⟩:=mem_image.mp g
 apply box_test.mpr;constructor<;> intro j <;>
   obtain ⟨u,k⟩:=box_test.mp a<;>
   specialize u j <;> specialize k j <;>
   simp only [Pi.add_apply, Pi.smul_apply,step_apply] <;>split <;>
   simp <;> omega

lemma keep {j:Axis→Horse K}{J:ℕ→Axis→Horse K}
 (p:∀i,Elite (Lattice.box d) (fun n=>J n i) (j i))(m:ℕ):
    Elite (roomBox d m) (fun n=>rolling K m (J n)) (rolling K m j):=by
 apply Elite.sum
 intro i
 exact (((p i).goes i m).mono (movedRoom m i m (by omega))).sub
   (((p i).goes i (-m)).mono (movedRoom m i (-m) (by omega)))
lemma stabilize (K:Calibration)(h:Plump (Lattice.box d) b F f) (σ:Signed):
 Elite (Lattice.box d) (fun n=>air K (F n) σ) (air K f σ):=by
 have z:vale d 0=Lattice.box d:=by unfold Plume.vale;simp
 have m:Plump (Lattice.box d) b (fun n=>F n ∘ Plume.snow σ 0 (detX σ)) (f ∘ Plume.snow σ 0 (detX σ)):=
   ⟨fun n=>z ▸ (h.1 n).hill _ _ _, fun ε u=>(h.2 ε u).mono fun n p x=>p _⟩
 have s:=m.rides K
 exact ⟨s,fun i=> aligned K (s.whereTo i) ((m.1 i).greet K),
   aligned K s.landing ((fat m).greet K)⟩

variable (p:∀σ i,Elite (Lattice.box d) (fun n=>J n σ i) (j σ i))
 (h:Plump (Lattice.box d) b F f)(m:ℕ)(i:Axis)(x:ℤ)(c:ℝ)
def balcony(d m:ℕ)(i:Axis)(x:ℤ):=Tower.address i x (roomBox d m)
include p h
lemma excursus (σ:Signed):
 Elite (balcony d m i x) (fun n=>scene K (F n) (J n) m σ c i x) (scene K f j m σ c i x):=by
 have u: Lattice.box d ⊆ roomBox d m:=fun r u=>box_test.mpr ⟨fun i=>by
       have z:=(box_test.mp u).1 i; omega,fun i=>by have z:=(box_test.mp u).2 i; omega⟩
 exact ((( (stabilize K h σ).mono u).add (keep (steel p σ) m)).smul _).goes i x

lemma cluster :
 Elite (balcony d m i x) (fun n=>roses K m i x c (F n) (J n)) (roses K m i x c f j):=
 Elite.sum _ (F:=fun n s=>(ramp s:ℂ) • scene K (F n) (J n) m s c i x)
     fun s=> (excursus p h m i x c s).smul _
end YM.CF.Merino.Tiara
