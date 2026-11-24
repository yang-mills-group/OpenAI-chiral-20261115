import Anomaly.Apert.Sync
import YM.CF.Brood.Harp
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip Pastry Hake Peaks Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Mew Salt Py Neon
open scoped Mew
open Vow Bake Rive QuadClock Stilo Roots Moto Hove Haro Tap Levier Thera
variable {N B:Side}{s:Signed}{U: UNI SpinIdx}{Z Y: ArcΦ}
-- local face yes
lemma filial (s:Signed)(Z:Skate): ‖localFace s Z‖=‖Z‖:=by
 apply le_antisymm (locale_price ..); let h:=locale_price s⁻¹ (localFace s Z); rw [local_m,inv_mul_cancel,local_one] at h; exact h
private lemma swift {A B:Type}[Fintype A][Fintype B]{E F:Type}[NormedAddCommGroup E][NormedAddCommGroup F](P:A≃B){X:A→E}{Y:B→F}(t:∀ i, ‖Y (P i)‖= ‖X i‖): ‖X‖=‖Y‖:=by
 apply le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg Y)).mpr (fun i=> (t i).symm.trans_le (norm_le_pi_norm ..)))
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr; intro i; obtain ⟨i,rfl⟩:=P.surjective i; rw [t]; exact norm_le_pi_norm X i
private lemma ηorca (A: Axis→Pal)(s:Signed)(U:UNI SpinIdx): ‖(fun i=> -star (hush (s.flip i) (twist (spinQ U (xtra false)) (A (s.perm i)))))‖= ‖A‖ ∧ ‖(fun i=> hush (s.flip i) (twist (spinQ U (xtra false)) (A (s.perm i))))‖= ‖A‖:=by
 have he(i:Axis): ‖hush (s.flip i) (twist (spinQ U (xtra false)) (A (s.perm i)))‖= ‖A (s.perm i)‖:=by cases s.flip i <;> simp [twist_norm]
 constructor <;> (apply swift (P:=s.perm); intro i)
 · simp [he]
 exact (he i).symm
lemma ariaD (U: UNI SpinIdx)(s:Signed)(V:Dome): ‖(zoomL s U V).1‖= ‖V.1‖ ∧ ‖(zoomL s U V).2‖= ‖V.2‖:=by
 unfold zoomL; split
 · refine ⟨?_,?_⟩; · change ‖-star _‖=_; rw [norm_neg,norm_star,twist_norm]
   simp only [Prod.norm_def,(ηorca V.2.1 s U).1,(ηorca V.2.2 s U).1]; exact max_comm ..
 simp only [Prod.norm_def,(ηorca V.2.1 s U).2,(ηorca V.2.2 s U).2]; exact ⟨twist_norm ..,trivial⟩
lemma aria (U: UNI SpinIdx)(s:Signed)(Z:ArcΦ): let T:=arc_s s U Z; ‖T.1‖=‖Z.1‖ ∧ ‖T.2.1‖= ‖Z.2.1‖∧ ‖T.2.2‖=‖Z.2.2‖:=⟨filial _ _,ariaD _ _ _⟩
lemma hue_add {A B:Pal}(t:Bool):hush t (A+B)=hush t A+hush t B:=by cases t<;>simp [add_comm]
lemma colorΞ (s:Signed)(U:UNI SpinIdx):arc_s s U (Z+Y)=arc_s s U Z+arc_s s U Y:=by
 apply Prod.ext
 · change localFace s⁻¹ (Z.1+Y.1)=localFace s⁻¹ Z.1 + localFace s⁻¹ Y.1; refine funext₂ (fun i j=>?_); unfold localFace; simp [Pi.add_apply,map_add,smul_add]
 refine Prod.ext ?_ (Prod.ext (funext fun i:Axis=>?_) (funext fun i:Axis=>?_)) <;> (unfold arc_s; simp_rw [zoomL]; split)
 all_goals simp [hue_add] <;> abel
lemma color_rum {I:Type}(s:Signed)(U:UNI SpinIdx)(A:Finset I)(F:I→ArcΦ): arc_s s U (∑ i∈A,F i)=∑ i∈A,arc_s s U (F i):=by induction A using Finset.induction_on with|empty=>simp [arc_s0]|insert i A w ih=>rw [sum_insert w,sum_insert w,colorΞ,ih]
-- pay law
private lemma spinφ (s:Sweep N)(p:s∈Whirl N):∀ i,Pec.pays s.s⁻¹ i = Spire.payZ s i:=by
 intro i; rw [Pec.complX,det_rev, Spire.payZ,wageZ,(whirl s|>.mp p).1,Bool.false_xor]
lemma hue_E(k:Bool)(V:Pal)(c:ℂ):hush k (c • V)= c • hush k V:=by cases k <;> simp
local notation "φX"=> (ArcΦ)
lemma colorD (s:Sweep N)(p:s∈Whirl N)(U: UNI SpinIdx)(Z:ArcΦ)(x:ℂ): arc_s s.s U (x • Z)= Spire.payZ s x • arc_s s.s U Z:=by
 have hs:= ((whirl s).1 p).1
 apply Prod.ext
 · refine funext₂ fun i j=>?_; change localFace s.s⁻¹ (x • Z.1) i j=payZ s x * localFace s.s⁻¹ Z.1 i j; unfold localFace; simp_rw [Pi.smul_apply, spinφ s p]
   simp_rw [payZ, wageZ, hs]; cases ht:detX s.s <;> (simp [cSignX,ht,Complex.real_smul,smul_eq_mul]; ring) -- tune
 refine Prod.ext ?_ (Prod.ext (funext fun i:Axis=>?_) (funext fun i:Axis=>?_)) <;> (unfold arc_s; simp_rw [zoomL]; split) <;> rename_i H
 all_goals simp_all [twist_scalar,cSignX,payZ,wageZ,hue_E]
variable {T A a b c h z:ℝ}{Q Q':ArcΦ}{t:ℝ}
lemma sameGauge (E:ℝ→ℝ→ℝ→ℝ→ℝ→ℝ→ℝ)(L:Side)(s:Signed)(U:UNI SpinIdx):κprobe E L h A T (↑z:ℂ) (arc_s s U Q)=κprobe E L h A T z Q:=by unfold κprobe; obtain ⟨u,v,w⟩:= aria U s Q; rw [u,v,w]
end YM.CF.Ione.Clock
