import GaugeFieldConstruction.Freizes
import YM.CF.Prism.Homic
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 45000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open FlightFlux Fluxim
open Labels Source Source.Drops Analysis MultiNext.SignedSource Mom Pattern
open Cube
namespace Axon
local notation "GS"=> SU.group
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
-- Euclidean polynomial supply
lemma xyz_l (x y:Cover): Pattern.xyz (x+y)=Pattern.xyz x+ Pattern.xyz y:=by ext i; simp [Pattern.xyz]
lemma xyz_t (x:Cover)(t:Axis): Pattern.xyz (x+step t)=Pattern.xyz x+ basis t:=by exact xyz_step ..
lemma shine (f:E4→E)(p:Powers.home f 1): Paper 2 (fun x:Cover=> f (Pattern.xyz x)):=by
 rw [Powers.tensor_form p]; rw [paper_leg]; intro i; let V:= Tensor.coeff f 1 0; let A:= fun x:Cover=>Tensor.diagonal V (Pattern.xyz x)
 have he: FlightFlux.advance i A=fun _=> Tensor.diagonal V (basis i):=by
    funext x; unfold FlightFlux.advance; unfold A; rw [show Pattern.xyz _= _ from (show Pattern.xyz (x+Pi.single i 1)= _ from xyz_t x i)]
    unfold Tensor.diagonal
    let w(z:E4): Fin 1→ E4:= fun _=> z
    have hz(x y:E4) : V (w (x+y))=V (w x)+V (w y):=by
       let f:= (fun _:Fin 1=> (0:E4)); have hx(z:E4): w z= Function.update f 0 z:= funext fun i=>by fin_cases i; simp [w]
       rw [hx,hx,hx]; exact V.map_update_add .. -- tune
    rw [hz]; abel
 rw [show advance i (fun x: Cover=> Tensor.diagonal _ (Pattern.xyz x))= advance i A from rfl,he]; exact paper_const _ -- tune qualify advance
lemma shone (f:E4→E)(p:Powers.home f 2): Paper 3 (fun x:Cover=> f (Pattern.xyz x)):=by
 let V:= Tensor.coeff f 2 0; let A:=fun x:Cover=>Tensor.diagonal V (Pattern.xyz x); let P:=fun x y:E4=>V ![x,y]
 have he(u:E4): Tensor.diagonal V u=P u u:=congrArg V (funext fun i=>by fin_cases i <;>rfl) -- tune
 have ht(i j k:E4): P (i+j) k=P i k+ P j k:=by
    let F:=![i,k]; have hd(z:E4): ![z,k]=Function.update F 0 z:=by ext1 i; fin_cases i <;> simp [F]; -- syntax colon spacing! 
    unfold P; rw [hd,hd,hd]; exact V.map_update_add ..
 have hx(i j k:E4): P i (j+k)= P i j+P i k:=by
    let F:=![i,k]; have hd(z:E4): ![i,z]=Function.update F 1 z:=by ext1 i; fin_cases i <;> simp [F];
    unfold P; rw [hd,hd,hd]; exact V.map_update_add ..
 have hp(i:Axis)(x:Cover):advance i A x=P (basis i) (Pattern.xyz x)+P (Pattern.xyz x) (basis i)+P (basis i) (basis i):=by
    unfold advance A; rw [show Pattern.xyz (x+Pi.single i 1)=Pattern.xyz x+basis i from xyz_t x i,he,he,hx,ht,ht]; abel
 rw [Powers.tensor_form p]; rw [paper_leg]; intro i; rw [paper_leg]; intro j; have hy: advance j (advance i A)=fun _=> P (basis i) (basis j)+P (basis j) (basis i):=by
    funext x; change advance i A (x+step j)-_= _; rw [hp,show advance i A x= _ from hp i x,xyz_t,hx,ht]; abel
 exact (hy.symm ▸ (paper_const (P (basis i) (basis j)+P (basis j) (basis i)))) -- tune
lemma toE4 (k:ℕ)(h:k≤2)(f:E4→E)(p:f∈Powers.space E4 E k):Paper (k+1) (f ∘ Pattern.xyz):=by
 cases k
 · have he:=Mom.base p; have ht(x:E4): f x=f 0:=by simpa using (he.2 0 x).symm
   have hp:f ∘ Pattern.xyz= fun _=> f 0:=funext fun _=>ht _; rw [hp]; exact paper_const _
 next k=>
 obtain ⟨A,B,a,b,h'⟩:=Mom.roof p; rw [h']; apply paper_add; rotate_left
 · apply paper_low (toE4 k (by omega) B b) (Nat.le_succ _)
 rcases k with _|k; · exact shine A a
 rw [Nat.succ_le_succ_iff,Nat.succ_le_succ_iff] at h; have ht:k=0:=by omega
 subst k; exact shone A a
private def polarVx(u:Axis→E)(x:E4):=∑ i:Axis,(x i) • u i
lemma pole_P (u: Axis→E): Powers.home (polarVx u) 1:=by
 constructor; · exact ContDiff.sum (fun i p=> ((EuclideanSpace.proj i: E4→L[ℝ]ℝ).contDiff.smul contDiff_const)) -- name tune
 intro t x; unfold polarVx; simp only [WithLp.ofLp_smul,Pi.smul_apply,pow_one, Finset.smul_sum]; apply sum_congr rfl; intro i _; exact mul_smul ..
private def poricV (i j:Axis)(x:E4):ℝ:= x i * (x j - hit i j) /2
lemma pole_T (i j:Axis): poricV i j∈Powers.space E4 ℝ 2:=by
 let A(x:E4):ℝ:= x i*x j/2; let B(x:E4):ℝ:= -(x i*hit i j/2)
 have hv(a:Axis): ContDiff ℝ ω (fun x:E4=> x a):= (EuclideanSpace.proj a: E4→L[ℝ]ℝ).contDiff
 rw [show poricV i j =A+B from funext (fun x=>by unfold poricV; rw [Pi.add_apply]; unfold A B; ring)]
 apply (Powers.space ..).add_mem
 · apply Powers.residence (k:=2) _ le_rfl; refine ⟨((hv i).mul (hv j)).div_const _,fun t x=>?_⟩; unfold A; change t* x i*(t*x j)/2=t^2 * (x i*x j/2); ring
 apply Powers.residence (k:=1) _ (by decide); refine ⟨(((hv i).mul contDiff_const).div_const _).neg,fun t x=>?_⟩; unfold B; change -(t*x i*hit i j/2)= t^1 * (-(x i*hit i j/2)); ring
lemma panels (k:ℕ)(t:k≤2)(f:Cover→E)(p:Paper (k+1) f):∃ Z∈ Powers.space E4 E k, Z ∘ Pattern.xyz=f:=by
 have he(g)(e:Paper 1 g):= paper_firm (I:=Axis) (E:=E) g|>.mp e
 let L:Axis→E:=fun i=> FlightFlux.advance i f 0
 let X:=fun x:E4=> f 0+polarVx L x; have hx: X ∘ Pattern.xyz= dock f:=rfl -- tune
 cases k
 · obtain ⟨c,e⟩:= he f p; exact ⟨(fun _=>c),Powers.constants c _,e.symm⟩
 next k=>
 have hP: X ∈ Powers.space E4 E (k+1):=Powers.add (Powers.constants _ _) (Powers.residence (pole_P L) (by omega))
 cases k
 · exact ⟨X,hP,hx.trans (dock_sewn f p)⟩
 next k=>
 have ht:k=0:=by omega
 subst k
 let Wx(x:E4):=∑ i:Axis, ∑ j:Axis,poricV i j x • loom [i,j] f 0
 have ht:X+Wx∈Powers.space E4 E 2:= (Powers.space ..).add_mem hP (Powers.sums _ _ (fun i _=>Powers.sums _ _ (fun j _=> Powers.carried ((ContinuousLinearMap.id ℝ ℝ).smulRight _) (pole_T i j))))
 exact ⟨X+Wx,ht,hitch_sewn f p⟩
end Axon
end YM.CF.TableF
end
