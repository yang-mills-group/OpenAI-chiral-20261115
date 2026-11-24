import YM.CF.Levier.Gate
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
def starG(h:Site (More N)→E)(i:Site (More N)):=polarT b (h (a.anon N i))
lemma covB(h:Site (More N)→E)(x: Chin N): gateC b a (relayg h x)=relayg (starG b a h) (gateC b a x):=by
 funext ⟨v,i⟩ u; unfold gateC elf relayg starG; dsimp only -- tune
 cases g:a.s.flip i<;>cases u <;> simp [stamp_e,g,nectar_m,nectar_b,nectar_w]
lemma leaks_e (S:Seal (Site (More N)))(i:Well N): i∈ leaks S ↔ elf a i∈ leaks (roarD N a S):=by
 unfold leaks elf; rcases i with ⟨x,j⟩; have hx(x): a.anon N x∈ roarD N a S↔ x∈S:=by simp [roarD,a.anon_b.1.eq_iff]
 simp only [mem_filter,mem_univ,true_and]; split_ifs with h
 · have he: a.anon N (x+step j) + step (a.s.perm j)=a.anon N x:=by rw [stamp_e,if_pos h]; exact sub_add_cancel ..; -- tune
   rw [he,hx,hx,and_comm]
 rw [show a.anon N x+step (a.s.perm j)=a.anon N (x+step j) from (by rw [stamp_e,if_neg h]),hx,hx]
lemma roseC(S:Seal (Site (More N)))(x y:Chin N): fare S (gateC b a x) (gateC b a y)=fare (roarD _ a S) x y:=by
 have ht: (leaks S).image (elf a)=leaks (roarD _ a S):=by ext i; obtain ⟨i,rfl⟩:=(elf_e a).2 i; simp only [mem_image, (elf_e a).1.eq_iff, exists_eq_right]; exact leaks_e ..
 unfold fare; rw [←ht, sum_image (fun _ _ _ _ h=> (elf_e a).1 h)]; apply sum_congr rfl; exact fun i _=> gate_i ..
private lemma stemX(x: Site (More N)): (incX (1:Signed)).anon N x=x:=by unfold Shape.anon affine; simp [incX]
lemma dayK(x:Site (More N))(c:Shape): (joinX a c).anon N x=a.anon N (c.anon N x):=by rw [←nat_true x,Shape.anno,palm,←Shape.anno,←Shape.anno]
lemma keep_r(c:Shape)(S:Seal (Site (More N))):roarD N a (roarD N c S)=roarD N (joinX a c) S:=by unfold roarD; rw [image_image]; exact congr_arg (fun f=> S.image f) (funext fun x=>(dayK ..).symm)
lemma reed(S: Seal (Site (More N))):roarD N (incX 1) S=S:=by rw [roarD, show (incX 1).anon N=id from funext fun x=>stemX .., image_id] -- stemX has shape unused
lemma efo(i:Well N)(c:Shape): elf (joinX a c) i= elf a (elf c i):=by
 rcases i with ⟨x,j⟩; unfold elf; simp only [show (joinX a c).s= a.s*c.s from rfl,Signed.mul_perm_apply,Signed.mul_flip]; congr 1; rw [dayK,dayK]; -- first coord
 cases h:a.s.flip (c.s.perm j) <;>cases p:c.s.flip j <;>simp [stamp_e,h,p]
lemma nectar_v(t:Bool)(x:Tulip.Twig): nectar b (nectar t x)=nectar (t.xor b) x:=by cases b<;>cases t; rfl; rfl; rfl; apply Prod.ext; exact cc_cc _; exact cc_cc _
lemma stanceB(t:Bool)(c:Shape)(x:Chin N):gateC b c (gateC t a x)=gateC (t.xor b) (joinX a c) x:=by
 funext i k; simp only [gateC,nectar_v,efo]; change nectar _ (x _ _)=nectar _ (x _ (k.xor ((a.s*c.s).flip i.2)))
 rw [Signed.mul_flip]; congr 2; rw [Bool.xor_assoc]; congr 1; rw [Bool.xor_comm]; -- tune
 rfl
lemma wone(x:Chin N):gateC false (incX 1) x=x:=by
 funext ⟨v,i⟩ u; unfold gateC elf; rw [show (incX 1).s=(1:Signed) from rfl]; change nectar false (x (_,i) (u.xor false))= x _ u; simp only [Signed.one_flip,Bool.false_eq_true,ite_false,Bool.xor_false]; rw [stemX]; rfl
end YM.CF.Levier
