import GaugeFieldConstruction.LaceChiralVU
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 150000
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice.curvΝ
open Phys Calibration Cauchy Row Wick Raster Gap Function MeasureTheory Set Filter Mirror Flux.One
open Floor Flavor Finset
open Matter (Generation Slot Sheet)
open YM.Maxwell (normal Green normal_pos)
open scoped BigOperators Topology Classical
namespace LeftVU
local notation "K" => (32*(normal:ℂ))
local notation "L" => (4*(normal:ℂ))
local notation "A"=> (prism 0 apex ((2:ℝ) • apex))
def cubeVU (b:Bool):ℂ:= (if b then 10 else 5)*(-2) * K * K * L
private lemma clean0VU(s:Sheet)(x:Generation): AccountCh 0 s x= (-Complex.I) • LedgerL1 s x 0 1 + (-Complex.I) • LedgerL1 s x 1 0 :=by
 let B(t u:Spin):= LedgerL1 s x t u
 unfold AccountCh; simp_rw [Spin,Fin.sum_univ_succ]; norm_num[Hij] -- tune
private lemma clean1VU(s:Sheet)(x:Generation): AccountCh 1 s x= LedgerL1 s x 1 0 - LedgerL1 s x 0 1:=by
 unfold AccountCh; simp_rw [Spin,Fin.sum_univ_succ]; norm_num[Hij,sub_eq_add_neg,add_comm,neg_smul]; exact neg_one_smul ℂ (LedgerL1 s x 0 1)
private lemma clean2VU(s:Sheet)(x:Generation): AccountCh 2 s x= (-Complex.I) • LedgerL1 s x 0 0 + Complex.I • LedgerL1 s x 1 1:=by
 unfold AccountCh; simp_rw [Spin,Fin.sum_univ_succ]; change ((-Complex.I) • _ + ((0:ℂ) • LedgerL1 s x 0 1+0)) + (((0:ℂ) • LedgerL1 s x 1 0+(Complex.I • _+0)) + 0)=_; simp -- tune
lemma SketchαVU(s t u:Sheet) : A (AccountCh 0 s 0) (AccountCh 1 t 1) (AccountCh 2 u 2)= (if s=t∧ t=u then (-2)*K*K*L else 0):=by
 have ht(s t u:Sheet)(a b c d e f:Spin): A (LedgerL1 s 0 a b) (LedgerL1 t 1 c d) (LedgerL1 u 2 e f)= (if s=t ∧ t=u ∧ a=f ∧ b=c ∧ d=e then K*K*L else 0):= axis_vu ..
 rw [clean0VU,clean1VU,clean2VU]; simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,map_smul,LinearMap.smul_apply,ht]
 -- tune product
 by_cases h:s=t ∧ t=u
 · rcases h with ⟨rfl,rfl⟩; norm_num; ring_nf; simp -- tune
 simp only [← and_assoc]; simp [h]
#print axioms SketchαVU
abbrev ΘBillLeftVU (p: Generation × Axis)(b:Bool):Book:=Phys.dress (shells three (FamilyZN p.2 (p.1,b)))
abbrev brightBreak (z x y:E4)(b:Bool):ℂ:=prism z x y (ΘBillLeftVU (0,0) b) (ΘBillLeftVU (1,1) b) (ΘBillLeftVU (2,2) b)
private lemma triΨVU{V:Type}[AddCommGroup V][Module ℂ V](f:V→ₗ[ℂ] V→ₗ[ℂ] V→ₗ[ℂ] ℂ)(s:Finset Sheet)(a b c:Sheet→V)(Z:ℂ)(H:∀ i j k, f (a i) (b j) (c k)= if i=j∧j=k then Z else 0): f (∑ i∈s,a i) (∑ i∈s,b i) (∑ i∈s,c i)=s.card • Z:=by
 simp only [map_sum,LinearMap.sum_apply,H]; have h(t)(p:t∈s):∑ j∈s,∑ i∈s, (if i=j∧j=t then Z else 0)=Z:=by rw [sum_eq_single_of_mem t p]; simp [p]; intro z _ u; simp [u]
 rw [sum_congr rfl h,sum_const]
lemma SpectrumTraceVU (b:Bool): brightBreak 0 apex ((2:ℝ) • apex) b=cubeVU b:=by
 let S:= indL1 b
 let F(k:Generation)(a:Axis):=∑ s∈S, AccountCh a s k
 have u(k):ΘBillLeftVU k b= F k.1 k.2:= Treadα ..
 unfold brightBreak; rw [u,u,u]; change A (F 0 0) (F 1 1) (F 2 2)= cubeVU b
 unfold F; rw [triΨVU A S _ _ _ _ (SketchαVU)]; rw [show S.card=_ from countsα b]; unfold cubeVU; cases b<;>norm_num<;>ring
lemma epochπVU (b:Bool): (cubeVU b).re <0:=by have h := Maxwell.normal_pos; cases b<;> norm_num [cubeVU,Complex.mul_re,Complex.mul_im] <;> positivity
#print axioms epochπVU
#print axioms SpectrumTraceVU
end LeftVU
end YM.GaugeFieldConstruction.Invoice.curvΝ
end
