import YM.CF.Matter.Mass
import YM.SU5.Six.Extinguish
set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
namespace Xara
/- Explicit tests for barr color. -/
abbrev Bun(i:Fin 3)(a:SU.F) : SU.Slot:= (i,.inr a)
lemma bun (s:SU.Slot)(h:(family s).2=false):∃ i a,s=Bun i a:=by
 rcases s with ⟨i,a|b⟩; swap
 · exact ⟨i,b,rfl⟩
 cases h
lemma bun' (i:Fin 3)(a:SU.F): (family (Bun i a)).2 = false:=rfl
variable (t:Fin 3)(a b:SU.F)(c:ℂ)(g:SU.E)
def Sends (g:SU.E)(a b:SU.F) (c:ℂ) : Prop:= ∀ i, fund g i a=if i=b then c else 0
lemma column (h:Sends g a b c) (s:SU.Slot): (matter g).val s (Bun t a)=if s=Bun t b then star c else 0:=by
 rcases s with ⟨i,s|s⟩
 · simp [matter_matrix,Bun,triple,each,Join.both]
 by_cases p:i=t <;> by_cases q:s=b<;> simp [matter_matrix,Bun,triple,each,Join.both,p,q,h _, cc_apply]
lemma stay_one : Sends 1 a a 1:= by intro i; rw [fund_one]; exact Matrix.one_apply ..
open Matrix
lemma patchSwap (h:a≠b): ∃ g:SU.E,Sends g a b (-1):=by
 let W:Op SU.F:= (-1:Op F).submatrix (Equiv.swap a b) id
 have hx(i j:SU.F): W i j= -(1:Op SU.F) ((Equiv.swap a b) i) j:=rfl
 have hW: star W=W:= by 
    ext i j
    have hp : (Equiv.swap a b j)=i ↔ Equiv.swap a b i=j:= by rw [Equiv.swap_apply_eq_iff,eq_comm (a:=j)]
    rw [star_apply,hx,hx,Matrix.one_apply,Matrix.one_apply]; split_ifs with e e <;> simp_all
 have hv: W * W=1:=by
    ext i j; rw [Matrix.mul_apply,sum_eq_single ((Equiv.swap a b) i)]; rw [hx,hx,Equiv.swap_apply_self]; simp
    · intro k _ p; simp [hx,one_apply,Ne.symm p]
    simp
 let A: UNI SU.F:= ⟨W, ⟨hW.symm ▸ hv, by rw [hW,hv]⟩⟩ -- check rw at lhs
 have hd: Matrix.det W=1:=by unfold W; rw [Matrix.det_permute, Equiv.Perm.sign_swap h, Matrix.det_neg]; norm_num [SU.F]
 refine ⟨(⟨A,hd⟩:SU.E),fun i=>?_⟩
 change W i a = _; simp_rw [hx,one_apply]; by_cases g:i=b <;> simp_all [Equiv.swap_apply_eq_iff]
lemma dualD (h:a ≠ b): ∃ g:SU.E, Sends g a a (Complex.I) ∧ Sends g b b (-Complex.I):=by
 let f(i:SU.F):ℂ:= if i=a then .I else if i=b then -Complex.I else 1
 let W:Op SU.F:= diagonal f
 have hd:star W=diagonal fun i=> star (f i):= by ext i j; rw [star_apply]; by_cases h:i=j <;> simp [W,h,Ne.symm]
 have hh(i:SU.F):f i*star (f i)=1:=by unfold f; split_ifs <;> simp [Complex.star_def]
 let A:UNI SU.F:= ⟨W,Matrix.mem_unitaryGroup_iff.mpr (by rw [hd]; change Matrix.diagonal f * Matrix.diagonal _=_; rw [Matrix.diagonal_mul_diagonal]; simp_rw [hh]; simp)⟩
 have hr:Matrix.det W=1:=by
    unfold W; rw [Matrix.det_diagonal,←Finset.mul_prod_erase _ _ (mem_univ a),←Finset.mul_prod_erase _ _ (show b∈ univ.erase a from mem_erase.mpr ⟨Ne.symm h,mem_univ _⟩),prod_eq_one]; simp [f,h,Ne.symm h]
    intro i p; simp only [mem_erase] at p; simp [f,p.1,p.2.1]
 refine ⟨⟨A,hr⟩,fun i=>?_,fun i=>?_⟩
 · change W i a=_; by_cases p:i=a<;>simp [W,p,f]
 change W i b=_; by_cases p:i=b<;>simp [W,p,f,Ne.symm h]
variable (o:Cover)(i:SpinIdx)(m:Side)
lemma basisMove (v:Seat m→SU.E)(e:Sends (v (wrap (More m) (nodeC o))) a b c): acts (tradew m v).val (basisC m o i (Bun t a))=star c • basisC m o i (Bun t b):=by rw [turn_basisC]; simp_rw [column t a b c _ e]; simp
#print axioms patchSwap
end Xara
end YM.CF.Buffered.Afterglow.Six
