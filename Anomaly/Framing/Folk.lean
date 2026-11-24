import YM.CF.Ione.Tick
import YM.CF.Sault.Crown
import YM.CF.Sour.Tile
/-! Extension of Spin accounting to the full Sector operators. Reuses
sector induction and the project's loan (ION) for Clasp. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Sour.Turning
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
open Ione
local notation "G" => (V*whiten c U)
lemma spin_pair {u:Bool}{S:Finset (LeanV n)}{X:FC (LeanV n)} (h:Sector S u X):
    lotY c t V (lotY b r U X)= (if u then (feeJ r (t.xor c)) else 1) • lotY (b.xor c) (r.xor t) G X:= by
  induction h with
  | one => simp only [map_one]; exact (one_smul ..).symm
  | zero => simp only [map_zero, smul_zero]
  | up i _=>exact Ione.honey ..
  | down i _=>
    unfold takeF
    simp_rw [show ∀ (a k:Bool)(S:UNI n)(A:FC (LeanV n)),lotY a k S (star A)=star (lotY a k S A) from fun _ _ _ _=> Sault.handL ..]
    obtain ⟨j,i⟩:= i; rw [Ione.honey,star_smul]; congr 1; unfold feeJ; split_ifs <;> simp
  | add _ _ e f=>rw [map_add,map_add,map_add,e,f,smul_add]
  | @mul d e X Y _ _ i j=>
    rw [map_mul,map_mul,map_mul,i,j,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
    congr 1
    cases d <;> cases e <;> cases c <;> cases t <;> cases r <;> simp [feeJ]
  | @scale u X h z i =>
    rw [G_lot,G_lot,G_lot,i,smul_comm (cSignX _ _)]; congr 1
    cases b <;>cases r<;>cases c<;>cases t<;> simp [cSignX]

lemma spin_gauge {N:Side}(s:Sweep N)(g:Seat N→E){X:FC (Dwell N)}{S} (p:Sector S false X) :let W:=((polarT s.charge ∘g) ∘ (castX s).anon N);let H:= sauce s.charge (detX s.s) (Sour.γS s);lotY false false (tradew N W) (H X)=H (sauce false false (tradew N g) X):=by
 intro W H
 exact Eq.symm (calc lotY s.charge (detX s.s) (γS s) (lotY false false (tradew N g) X)= lotY false false (tradew N W) (lotY s.charge (detX s.s) (γS s) X) := by
                        rw [spin_pair _ _ _ _ _ _ p,spin_pair _ _ _ _ _ _ p,Hive.tr_s]; simp only [γS,W,site_ui,Bool.xor_false,Bool.false_xor,whiten,Bool.false_eq_true,↓reduceIte]; rw [Nacre.envoy])

variable {N:Side}
local notation "aura" => Finset (Dwell N)
lemma spin_step_e {u:Bool} (X:Support (More N))(T:FC (Dwell N))(s:Sweep N)(p:Sector (camp X) u T): Sector (camp (actY s X)) u (sauce s.charge (detX s.s) (γS s) T):=by
 let S:=lotY s.charge (detX s.s) (γS s)
 let R:=camp X; let Z:=camp (actY s X)
 have he (j:Dwell N)(u:j∈R):Sector Z true (S (put j)):=by
    obtain ⟨b,k⟩:=j
    change Sector Z true (sauce s.charge (detX s.s) (γS s) (put (b,k)))
    rw [leafU] -- implicit v unpack
    apply Sector.sumS; intro i _; let j:Dwell N:=(b.xor (detX s.s),i)
    by_cases p:(praise s).val j (b,k)=0
    · rw [p,zero_smul]; apply Sector.zero
    have hv:boxA s (cod_A j)∈ X := (price_Q s _ _ p).symm ▸ (show cod_A ((b,k):Dwell N)∈ X from (mem_filter.mp u).2)
    exact (Sector.up j (show j∈Z from mem_filter.mpr ⟨mem_univ _,Finset.mem_map_equiv.mpr hv⟩)).scale _
 change Sector Z u (S T)
 induction p with
 |one=> rw [map_one]; exact Sector.one
 |zero=> rw [map_zero]; apply Sector.zero
 |up i hx=>exact he i hx
 |down i h=>rw [takeF,show S (star _)= _ from Sault.handL ..]; exact (he i h).contr
 |mul _ _ i j=>rw [map_mul]; exact i.mul j
 |scale _ h i => unfold S at *; rw [G_lot]; exact i.scale _
 |add _ _ i j=> rw [map_add]; exact i.add j
end YM.CF.Sour.Turning
