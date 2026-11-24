import GaugeFieldConstruction.Underline

/-!
# charge types for the generated section and (107)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6700
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Loft
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Row
open Floor Carat Dawn Sailing Angles
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate
attribute [local instance] iG iF iX iU iT2 iW2 iV iS floatA floatY
attribute [local instance 30000] topx topg
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}

def evoke (x:Al): Module.End ℂ Across := ((LinearMap.llcomp ..) (x five))-((LinearMap.llcomp ..).flip (x four))
lemma proceeds (x: Al) (y: Across) (z : UV four): evoke x y z=x five (y z)-y (x four z):=rfl
lemma cost₀ : evoke 0=0:= by apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; rw [proceeds]; change 0-x 0=(0:UV five); rw [map_zero,sub_zero]
lemma cop (x y:Al) (p:Across): evoke ((port Al).l x y) p = evoke x (evoke y p)-evoke y (evoke x p):= by apply LinearMap.ext; intro v; simp only [LinearMap.sub_apply,proceeds, port_at,map_sub]; abel
lemma cop_add (x y:Al): evoke (x+y)=evoke x+evoke y := by
  apply LinearMap.ext; intro p; apply LinearMap.ext; intro v; simp only [LinearMap.add_apply,Pi.add_apply,proceeds,map_add]; abel
lemma cop_c (x:Al) (a:ℝ): evoke (a • x)=(a:ℂ) • evoke x:= by
  rw [realT]; apply LinearMap.ext; intro p; apply LinearMap.ext; intro s; rw [proceeds]; change ((a:ℂ) • x five _) - p _ = (a:ℂ) • _
  rw [proceeds]; change _-p ((a:ℂ) • x four _)=_; rw [map_smul,smul_sub]
def Wey (u:M4) (T : Axis→ Across): Axis→Across := fun i=> ∑ j:Axis,(u j i:ℂ) • T j
lemma way (u v:M4) (T : Axis→Across) (i): Wey (v*u) T i=∑ j:Axis,(u j i:ℂ) • Wey v T j := by
  unfold Wey; simp_rw [Finset.smul_sum,smul_smul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Matrix.mul_apply,Complex.ofReal_sum,Finset.sum_smul]; exact Finset.sum_congr rfl (fun w _=>by rw [Complex.ofReal_mul,mul_comm])
lemma kinder (a b:M4) (T) (i): Wey (a+b) T i= Wey a T i+ Wey b T i:= by unfold Wey; simp_rw [Matrix.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
lemma forage (Q:Dawn L C u) : ∀ (a b),Nap (angleT C Q.tect) a b → (fun i=> evoke b (C.theta Q.tect i))= Wey a.val (C.theta Q.tect) ∧
    ∀ i,evoke b (P i-C.theta Q.tect i)=0 := by
  intro a b s
  let T:= C.theta Q.tect
  induction s with
  | gen a=>
    have h i:evoke (angleT C Q.tect a) (T i)=Wey a.val T i := by
      apply LinearMap.ext; intro x; simp only [proceeds,Wey,LinearMap.sum_apply, LinearMap.smul_apply]; exact C.twirling Q.bill Q.tect Q.unit .. -- check
    refine ⟨funext h,fun i=> ?_⟩
    have H : evoke (angleT C Q.tect a) (P i)=Wey a.val T i:= by apply LinearMap.ext; intro x; simp only [proceeds,Wey,LinearMap.sum_apply,LinearMap.smul_apply]; exact C.spin_d Q.bill Q.tect a i x
    change evoke _ (P i-T i)=_; rw [map_sub,h,H,sub_self]
  | zero=>
    constructor
    · exact funext fun i=> by rw [cost₀]; simp [Wey]
    intro i; rw [cost₀]; rfl
  | @add x y f g _ _ v q=>
    refine ⟨funext fun i=> ?_, fun i=>by rw [cop_add,LinearMap.add_apply,v.2,q.2,add_zero]⟩
    change evoke _ (T i)= _; rw [Submodule.coe_add,kinder,cop_add, LinearMap.add_apply]; exact congr_arg₂ (·+·) (congr_fun v.1 i) (congr_fun q.1 i)
  | @sm r x b _ v=>
    refine ⟨funext fun i=>?_,fun i=>?_⟩
    · change evoke _ (T i)=_; rw [cop_c,LinearMap.smul_apply,show evoke _ _=Wey x.val T i from congr_fun v.1 i]; unfold Wey; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; rw [smul_smul]; change _=((r*x.val j i:ℝ):ℂ) • _; push_cast; rfl
    rw [cop_c,LinearMap.smul_apply,v.2,smul_zero]
  | @fork a b c d _ _ v q=>
    refine ⟨funext fun i=>?_, fun i=>by rw [cop,q.2,v.2,map_zero,map_zero,sub_zero]⟩
    change evoke _ (T i)= _; rw [cop]
    have H i : evoke b (T i)=Wey a.val T i := congr_fun v.1 i; have G i:evoke d (T i)=Wey c.val T i:=congr_fun q.1 i
    have ht: evoke b (evoke d (T i))= Wey (a.val*c.val) T i:= by rw [G,Wey,map_sum,way]; simp_rw [map_smul,H]
    have hi: evoke d (evoke b (T i))=Wey (c.val*a.val) T i:= by rw [H,Wey,map_sum,way]; simp_rw [map_smul,G]
    rw [ht,hi]; unfold Wey; rw [← Finset.sum_sub_distrib]; change _=∑ j:Axis, (((a.val * c.val-c.val * a.val) j i:ℝ):ℂ) • _; exact Finset.sum_congr rfl fun j _=>by rw [Matrix.sub_apply, Complex.ofReal_sub]; exact (sub_smul (_:ℂ) _ (T j)).symm

namespace Valley
variable {Q : Dawn L C u} (V:Valley Q)
def portico : Summit Q.d where
  i:= V.caller four
  j:= V.caller five
  P:= P
  T:= C.theta Q.tect
  piP a:= V.pi a four
  piQ a:= V.pi a five
  trans a x:=V.turns ..
  trans' a x:=V.turns ..
  heat:= L.toBend
  hues:= C.bend _
  complete T h i j:= C.once Q.bill Q.tect i j ⟨T,h⟩ Q.unit
  wake t H:= Q.bill.first 0 t (H 0)
  bracket i b x:= by
    have h:=congr_fun (forage Q b (V.pi b) (V.paid b)).1 i
    have ht:=LinearMap.congr_fun h x; change evoke _ _ x=Wey _ _ _ x at ht; rw [proceeds,Wey,LinearMap.sum_apply] at ht; exact ht
  bracket' i b:=sub_eq_zero.mp (show _= (0:Across) from (forage Q _ _ (V.paid b)).2 i)

include V
lemma paysAll : Q.d=Stage.All:= V.portico.buys_all
lemma finish : C.theta Q.tect = P:=V.portico.enough
-- all fused S prices. all other fields. not strength or actual payoff
lemma valves (x:UV four) (i) : S.Reaches (prints Q.tect.val) (Palace.postage i) (Calibration.lift _ x) (P i x):= by rw [← congr_fun V.finish i]; exact C.law Q.tect x i -- args
lemma costly₁ (i : Signed) (h:signBit i=false) (d) (x : UV d): let A:=V.caller d; A.c (ledger Q.d d (signMot i h) x)= spinFrame d i (A.c x):= by
  intro A; rw [show ledger Q.d d (signMot i h) x = spinFrame d i x by rw [V.paysAll]; exact (Stage.mirror ..).symm,A.h]

-- (107) the formula on tests:
lemma on_conf (x : UV four) (i n v) (p : Test n) k b (q:Bulb.Works b p k): Fathom.paid k i (S.spot v k (Calibration.lift _ x)) p=Fathom.delta (Payroll.ticket i) p b q.cared (S.armed (prints Q.tect.val) (update v k (Calibration.lift _ x))) := by rw [← L.money]; exact V.valves x i n v k p b q
end Valley
end YM.GaugeFieldConstruction.Ember.Loft
