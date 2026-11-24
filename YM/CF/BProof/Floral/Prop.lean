import YM.CF.Mew.Pot
import YM.CF.Hype.Ace
import YM.CF.Vow.Jig
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{p:BudgetPoint} {X:Hub n}{Y:Force n}{F G:InkD n}{E E':Copy n}{a b h:ℝ}
lemma regular_plus (u: PressB p X F h a)(v:PressB p X G h b):PressB p X (F+G) h (a+b):= Larch.prop_add p X u v
lemma regular_scale (z:ℂ)(u:PressB p X F h a):PressB p X (z • F) h (‖z‖*a):=by
 obtain ⟨T,V,v,f⟩:=u.worth
 refine ⟨fun i j k=> congrArg (z • ·) (u.term i j k),fun i=> (u.fitted i).smul z,u.measureV.const_smul z, fun i j=> (congrArg (z • ·) (u.gaugeV i j)).trans (map_smul (hueV (tradew n j)) z (F i)).symm,fun i=> ‖z‖*T i,fun i=>mul_nonneg (norm_nonneg _) (V i),fun i p j=> Mew.grade_unit z _ (v i p j),?_⟩
 simp_rw [mul_left_comm _ ‖z‖,←mul_sum]; exact mul_le_mul_of_nonneg_left f (norm_nonneg _)
lemma regular_sub (u: PressB p X F h a)(v: PressB p X G h b):PressB p X (F-G) h (a+b):=by simpa [sub_eq_add_neg] using regular_plus u (regular_scale (-1:ℂ) v)
lemma regular_incr (u:PressB p X F h a)(w:a≤b):PressB p X F h b:=by obtain ⟨t,x,v,y,f,g,s,m⟩:=u; exact ⟨t,x,v,y,f,g,s,m.trans w⟩
lemma force_plus (k:ForceB p Y E h a)(v:ForceB p Y E' h b):ForceB p Y (E+E') h (a+b):=by
 obtain ⟨T,g,u,x⟩:=k.costP; obtain ⟨C,j,w,l⟩:=v.costP
 refine ⟨fun i t τ σ u h=> congrArg₂ (·+·) (k.values i t τ σ u h) (v.values i t τ σ u h),fun i=>(k.fitted i).add (v.fitted i),fun s=>by rw [k.flagsV s,v.flagsV s,add_zero],k.measureV.add v.measureV,fun i=> not_imp_comm.mp ?_,fun i τ j=>(congrArg₂ (·+·) (k.gaugeV i τ j) (v.gaugeV i τ j)).trans (map_add ..).symm,T+C,fun i=>add_nonneg (g i) (j i),fun i q j=>Prism.tack (u i q j) (w i q j),by simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add x l⟩ -- not_imp_comm signature
 intro s; simp only [Pi.add_apply, Classical.not_not.mp (mt (k.protect i) s),Classical.not_not.mp (mt (v.protect i) s),add_zero]
lemma force_scale (z:ℂ)(k: ForceB p Y E h a):ForceB p Y (z • E) h (‖z‖*a):=by
 obtain ⟨T,V,v,f⟩:=k.costP
 refine ⟨fun i t τ σ u h=> congrArg (z • ·) (k.values i t τ σ u h),fun i=>(k.fitted i).smul z,fun s=> by rw [k.flagsV s,smul_zero],k.measureV.const_smul z,fun i n=> k.protect i fun s=> n (by simp [s]),fun i τ j=>(congrArg (z • ·) (k.gaugeV i τ j)).trans (map_smul (hueV (tradew _ j)) z _).symm,fun i=> ‖z‖*T i,fun i=>mul_nonneg (norm_nonneg _) (V i),fun i p j=>Mew.grade_unit z _ (v i p j),?_⟩
 simp_rw [mul_left_comm _ ‖z‖,←mul_sum]; exact mul_le_mul_of_nonneg_left f (norm_nonneg _)
lemma force_sub (k:ForceB p Y E h a)(v:ForceB p Y E' h b):ForceB p Y (E-E') h (a+b):=by simpa [sub_eq_add_neg] using force_plus k (force_scale (-1:ℂ) v)
lemma force_incr (u:ForceB p Y E h a)(w:a≤b):ForceB p Y E h b:=by obtain ⟨t,x,v,y,p,h,f,g,s,m⟩:=u; exact ⟨t,x,v,y,p,h,f,g,s,m.trans w⟩
lemma tariff_high (v: Finset (Dwell n))(o:Seat n)(k:1≤h) :1≤ Scree.tariff p o h v:= one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by simp)) (one_le_pow₀ k)
lemma press_entry {U:Pane n}{c:Finset (Dwell n)→ℝ}(g:∀ i,0 ≤ c i)(f:∑ i:Finset (Dwell n),Scree.tariff p X.val.1 h i * c i ≤a)(q:BedP p U F X c)(u:1≤h): BedP p U F X (fun _=>a):= fun i v=> Prism.high (q i v) ((le_mul_of_one_le_left (g v) (tariff_high v _ u)).trans ((single_le_sum (f:=fun j=>Scree.tariff p X.val.1 h j*c j) (fun j _=>mul_nonneg (zero_le_one.trans (tariff_high j X.val.1 u)) (g j)) (mem_univ v)).trans f)) -- `press_entry` simplify
lemma press_high (q:PressB p X F h a)(k:1≤h)(U:Pane n): BedP p U F X (fun _=>a):=by obtain ⟨T,V,v,f⟩:=q.worth; exact press_entry V f (v U) k
lemma force_high (q:ForceB p Y E h a)(k:1≤h)(U:Orbit n)(u:pingS p.threshold (Y.val.1.val.2\Y.val.2) U.1)(z:Finset (Dwell n)): Signs p Y.val.1.val.1 (fun i=>Pastry.crumb (E (RG.increment U.1 (openG p Y.val.2 i),U.2)).val z) a:=by
 obtain ⟨T,V,v,f⟩:=q.costP; exact Prism.high (v _ u _) ((le_mul_of_one_le_left (V z) (tariff_high z _ k)).trans ((single_le_sum (f:=fun j=>Scree.tariff p Y.val.1.val.1 h j*T j) (fun j _=> mul_nonneg (zero_le_one.trans (tariff_high j _ k)) (V j)) (mem_univ z)).trans f))
end YM.CF.Floral
