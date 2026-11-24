import YM.CF.Hove.Cite
import YM.CF.Hove.Canon
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
import YM.CF.Hove.Prune
import Compass.Match
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Hake Levier Hove
-- adapt Mantel. sign.
-- check base
open Nacre Ione
open Matrix
variable {a b f m:Type*}
-- restrict windX.Make
abbrev foreQ(q:Bool)(A:Matrix a b ℂ):Matrix a b ℂ:= Matrix.of fun i j=>cSignX q (A i j)
lemma foreS {a:Type*}(M:Op a)(q:Bool): foreQ q M=windX q M:=by cases q<;>rfl
lemma sealG(x y:ℂ)(q:Bool):cSignX q (x*y)=cSignX q x*cSignX q y:=by cases q<;>simp [cSignX]
lemma sealV(v:ℝ)(q:Bool):cSignX q (v:ℂ)=(v:ℂ):=by cases q<;>simp [cSignX]
lemma seal_I (n:ℤ)(q:Bool):cSignX q (n:ℂ)=(n:ℂ):=by cases q<;>simp [cSignX]
lemma seal_T (n:ℂ)(q:Bool):cSignX q (star n)=star (cSignX q n):=by cases q<;>rfl
lemma seal_0(q:Bool):cSignX q 0=0:=Ione.sign0 ..
lemma fore_adj(q:Bool)(A:Matrix a b ℂ): foreQ q Aᴴ=(foreQ q A)ᴴ:= Matrix.ext fun i j=> seal_T (A j i) q
lemma fore_mul [Fintype b](q:Bool)(A:Matrix a b ℂ)(B:Matrix b m ℂ):foreQ q (A*B)=foreQ q A*foreQ q B:=by cases q; rfl; ext i j; change star ((A*B) i j)=_; simp only [Matrix.mul_apply,star_sum,star_mul]; simp [foreQ,cSignX,mul_comm]
lemma sum_entry(N:Side)(A:Shape)(U:UNI SpinIdx)(p:Bool)(o:Site N)(j:SpinIdx)(k:Slot)(G:Single N→ℂ):
 ∑ i:Single N,(siteU A p U N).val ((o,j),k) i * G i = ∑ i:Kt,(A.payA o * (twoU U p).val (j,k) i) *G ((Tofu A N o, i.1),i.2):=by
 have e (x:Site N)(y: SpinIdx)(l:Slot): (siteU A p U N).val ((o,j),k) ((x,y),l)= if x= Tofu A N o then A.payA o*(twoU U p).val (j,k) (y,l) else 0:=by change jump (Tofu A N) (fun i=>(milU A U (xtra p) i).val) _ _= _; rw [jump_apply]; split_ifs <;> first| rfl|exfalso; tauto
 -- control unfold manually
 rw [Fintype.sum_prod_type]; change ∑ i:Site N × SpinIdx, (∑ t:Slot,_)=_
 rw [Fintype.sum_prod_type]; change ∑ (x:Site N),∑ (d:SpinIdx), ∑ (t:Slot), (siteU A p U N).val ((o,j),k) ((x,d),t)*G ((x,d),t)=_; rw [sum_congr rfl (g:=fun x:Site N=>∑ i:SpinIdx,∑ l:Slot,(if x=Tofu A N o then A.payA o*(twoU U p).val (j,k) (i,l) else 0)*G ((x,i),l)) (fun x _=> sum_congr rfl (fun i _=>sum_congr rfl (fun t _=> congrArg (· *G ((x,i),t)) (e x i t))))]
 rw [sum_eq_single (Tofu A N o)]; swap; · intro x _ z; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; exact (ite_mul ..).trans (if_neg z|>.trans (zero_mul ..))
 swap; · simp
 have he(i:Kt): (if Tofu A N o=Tofu A N o then A.payA o*(twoU U p).val (j,k) i else 0)*G ((Tofu A N o,i.1),i.2)= (A.payA o*(twoU U p).val (j,k) i)*G ((Tofu A N o,i.1),i.2):= congrArg (· *_) (if_pos rfl)
 calc
   _ = ∑ i:SpinIdx, ∑ t:Slot, (A.payA o*(twoU U p).val (j,k) (i,t))*G ((Tofu A N o,i),t):= sum_congr rfl (fun i _=>sum_congr rfl (fun t _=>he (i,t)))
   _ = _ := (Fintype.sum_prod_type (fun i:Kt=>A.payA o * (twoU U p).val (j,k) i * G ((Tofu A N o,i.1),i.2))).symm

#print axioms fore_mul
end YM.CF.Compass
