import Anomaly.Framing.Folk
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Sour.Turning
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r:Bool)(U V:UNI n) {z:ℂ} (p:U.val=z • V.val) (h:z^2=1) (s:star z=z)
open Ione Nacre
local notation "π" => lotY b r U
local notation "σ" => lotY b r V
include p h s
lemma polar_equal {T:Finset (LeanV n)}{c:Bool}{X:FC (LeanV n)} (q:Sector T c X) : π X=(if c then z else 1) • σ X:=by
  have hx(i):π (put i)=z • σ (put i):=by
    rw [Urn.mold,Urn.mold]; unfold roseB; rw [smul_sum]; apply sum_congr rfl; intro j _; rw [smul_smul]; obtain ⟨b,i⟩:=i; obtain ⟨t,j⟩:=j; unfold sewV; rw [Urn.cream, Urn.cream]; split_ifs; swap; · rw [mul_zero]
    rw [show (Urn.crib U r b).val=z • (Urn.crib V r b).val from ?_]; rfl; cases b <;> cases r <;> simp only [Urn.crib, Pastry.thread]<;> simp [filmG,ccU,p,cc_smul,s,smul_comm z]
  induction q with
  | one=> rw [map_one,map_one]; exact (one_smul ..).symm
  | zero=> rw [map_zero,map_zero,smul_zero]
  | up i w=> exact hx i
  | down i _=> unfold takeF; rw [show π (star (put i))=star (π (put i)) from Sault.handL ..,hx,star_smul,s,show σ (star (put i))=star (σ (put i)) from Sault.handL ..]; exact rfl
  | mul _ _ i j=> rw [map_mul,map_mul,i,j, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul]; congr 1; split_ifs with v w u<;> first | assumption | rfl | (simp_all [pow_two])
  | scale _ a i=> rw [G_lot,G_lot,i,smul_comm]
  | add _ _ i j=> rw [map_add,map_add,i,j,smul_add]
omit p h s

-- using same calculation through all cover representatives: phase dies even.
variable {N:Side}
variable {T: Finset (Dwell N)}{X:FC (Dwell N)} (x:Sector T false X)
include x
lemma pin_paid (a:Shape)(U V:UNI SpinIdx)(p:JetS a.s b (detX a.s) U)(h:JetS a.s b (detX a.s) V) : lotY b (detX a.s) (siteU a b U N) X=lotY b (detX a.s) (siteU a b V N) X:=by
  obtain ⟨z,w,a_,s⟩:= king b _ U V p h; exact (polar_equal _ _ _ _ (Ygs _ _ _ w) a_ s x).trans (one_smul ..)
lemma wrapSpin (A:Shape)(U:UNI SpinIdx) :lotY b (detX A.s) (siteU (castX (Levier.ray (N:=N) b A)) b U N) X=lotY b (detX A.s) (siteU A b U N) X:=by
  let B:=wrap N A.t; let z:= fee (Rush.periods N (Lattice.lift B)-Rush.periods N A.t); have he: (siteU (castX (ray b A)) b U N).val= z • (siteU A b U N).val:=utu N b _ _ _ _ (wrap_lift _)
  exact (polar_equal _ _ _ _ he ((pow_two _).trans (fee_one ..)) (fee_real _) x).trans (one_smul ..)

lemma spin_spin (s t:Sweep N): sauce t.charge (detX t.s) (γS t) (sauce s.charge (detX s.s) (γS s) X)=sauce (s*t).charge (detX (s*t).s) (γS (s*t)) X:=by
  unfold γS
  let A:=castX s; let B:=castX t; let U:=spinU s.charge s.s; let V:=spinU t.charge t.s; let P:=joinX A B; let Q:= V*whiten t.charge U; let b:=s.charge.xor t.charge
  let W:=siteU A s.charge U N; let W':=siteU B t.charge V N
  change lotY t.charge (detX t.s) W' (lotY s.charge (detX s.s) W X)=_
  rw [spin_pair _ _ _ _ _ _ x]; change (1:ℂ) • _= _; rw [one_smul]
  have hy: W'*whiten t.charge W= siteU P b Q N:=Levier.turns ..
  rw [hy,←det_p]; change lotY b (detX P.s) _ _=lotY b (detX P.s) (siteU (castX (s*t)) b (spinU b P.s) N) X
  have hv:(s*t)= Levier.ray b P:= by unfold P b; rw [←ray_join,show ray s.charge A=s from ray_i s,show ray t.charge B=t from ray_i t]
  rw [hv,wrapSpin b x]; exact pin_paid b x _ _ _ (shineU s.charge A t.charge _ _ _ (spinZ ..) (spinZ ..)) (spinZ ..)
lemma spin_one : sauce (1:Sweep N).charge (detX (1:Sweep N).s) (γS 1) X=X:=by
  have p:=spin_spin x 1 1; rw [one_mul ] at p; rw [show detX (1:Sweep N).s=false from det_i] at p ⊢; apply twist _ |>.injective p

end YM.CF.Sour.Turning
