import YM.CF.Levier.Culler
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
abbrev Well(N:Side):=Edge (Site (More N))
def elf (i:Well N):Well N:=(if a.s.flip i.2 then a.anon N (i.1+step i.2) else a.anon N i.1,a.s.perm i.2)
def nectar (t:Tulip.Twig):Tulip.Twig:=(windX b t.1,windX b t.2)
def gateC (x:Chin N):Chin N:=fun i t=> nectar b (x (elf a i) (t.xor (a.s.flip i.2)))
lemma elf_e : Bijective (elf (N:=N) a):= by
 apply Function.Injective.bijective_of_finite
 rintro ⟨x,i⟩ ⟨y,j⟩ h; have he:= a.s.perm.injective (show a.s.perm i=a.s.perm j from congr_arg Prod.snd h); subst j
 unfold elf at h; simp only [Prod.mk.injEq,and_true] at h; split at h
 · rw [add_right_cancel (a.anon_b.1 h)]
 · rw [a.anon_b.1 h]
lemma nectar_n(t:Tulip.Twig): ‖nectar b t‖=‖t‖:=by cases b; rfl; rw [Prod.norm_def,Prod.norm_def]; exact congr_arg₂ max (norm_cc t.1) (norm_cc t.2)
lemma nectar_s(t f:Tulip.Twig): nectar b (t-f)=nectar b t-nectar b f:=Prod.ext (win_l ..) (win_l ..)
lemma gate_i(x y: Chin N)(i:Well N): ‖(gateC b a x-gateC b a y) i‖=‖(x-y) (elf a i)‖:=by
 have he(t):‖(gateC b a x i-gateC b a y i) t‖= ‖(x (elf a i)-y (elf a i)) (t.xor (a.s.flip i.2))‖:=by simp only [Pi.sub_apply,gateC, ←nectar_s,nectar_n]
 apply le_antisymm <;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun t=>?_
 · change ‖(gateC b a x i-gateC b a y i) t‖≤_; rw [he]; exact norm_le_pi_norm _ _
 · have hp: (t.xor (a.s.flip i.2)).xor (a.s.flip i.2)=t:=by simp; -- tune
   rw [←hp,show (x-y) _ ((t.xor _).xor _) =(x (elf a i)-y (elf a i)) _ from rfl,← he]; exact norm_le_pi_norm _ _
lemma gate_n (x y:Chin N): ‖gateC b a x-gateC b a y‖=‖x-y‖:=by
 apply le_antisymm <;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> ?_
 · rw [gate_i]; exact norm_le_pi_norm _ _
 obtain ⟨i,rfl⟩:= (elf_e a).2 i; rw [← gate_i b]; exact norm_le_pi_norm _ _
lemma nectar_w(t:Tulip.Twig): star (nectar b t)=nectar b (star t):=Prod.ext (win_s ..).symm (win_s ..).symm
lemma nectar_m(t k:Tulip.Twig): nectar b (t*k)=nectar b t*nectar b k:= Prod.ext (win_m ..) (win_m ..)
lemma nectar_b(x:E): brand (polarT b x)=nectar b (brand x):= Prod.ext (matterX b x) (polar_val b x)
lemma stamp_e(x:Site (More N))(i:Axis):a.anon N (x+step i)= if a.s.flip i then a.anon N x-step (a.s.perm i) else a.anon N x+step (a.s.perm i):=by rw [show step i=(posDir i).vec from rfl, salt]; cases h:a.s.flip i <;> simp [Step.rotate,h,posDir,Step.vec,sub_eq_add_neg] -- tune
lemma veil_p(x:Bkg (More N)): profile (stir (xtra b) a x)=gateC b a (profile x):=by
 funext ⟨v,i⟩ t; have ht:=veil_x (xtra b) a x v (posDir i)
 unfold gateC elf; simp only [profile]; rw [show stir (xtra b) _ _ (v,i)=polarT b (((posDir i).rotate a.s).read x (a.anon N v)) from ht]; cases t <;> cases f:a.s.flip i<;> simp [posDir,Step.rotate,f,Step.read,stamp_e,brand_inv, ← nectar_w,nectar_b] <;> rfl
end YM.CF.Levier
