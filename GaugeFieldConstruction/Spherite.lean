import GaugeFieldConstruction.Spinning
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix
abbrev optic_Q(f:Face (Per (More n)))(V:Pane n): SU.group.Color:= (stab (f.2,none)).atSite V f.1
lemma viz_D(f: Face (Per (More n))):ContDiffAt ℝ (↑(4:ℕ)) (optic_Q f ∘ increment 1) 0:=by
 let V:= mindChart; obtain ⟨H,u,t⟩:= pearl 6; have hp:=t n f.1 (stab (f.2,none)) V (stabL _) (by decide : mindChart.power≤3) (by decide : mindChart.order≤6)
 exact ((hp.rends 1 (Scree.ping_f V _)).paid).of_le (Nat.cast_le.mpr (le_trans (by decide: 4≤ 6) V.order_ge))
lemma face_v (S:Face (Per (More n))): HasFDerivAt (optic_Q S ∘ increment 1) (toga S) 0:=by
 have he:=(viz_D S).differentiableAt (by simp); rw [show toga S = fderiv ℝ (optic_Q S ∘ increment 1) 0 from ?_]; exact he.hasFDerivAt
 apply ContinuousLinearMap.ext; intro i; let Q:= linkage i (stab (S.2,none)) S.1; rw [rock_v,fanP,show rock (S.2,none)=0 from rfl,map_zero,add_zero] at Q; exact Q.unique (Push.side _ he i) -- tune
lemma optic_z(f:Face (Per (More n))):optic_Q f 1=0:=by
 have hp:= π_flat (o:=f.1) (f.2,none) mindChart; exact (smul_eq_zero.mp hp).resolve_left (inv_ne_zero mindChart.threshold_pos.ne')
abbrev Panorama (o:Seat n)(V:Pane n):Confab o:= fun i=>optic_Q i.1.val V i.2
def ocular (o:Seat n)(i:tangD n): Confab o:= Panorama o (increment 1 i)
lemma tower_D(o:Seat n):ContDiffAt ℝ (↑(4:ℕ)) (ocular o) 0:=contDiffAt_pi.mpr fun i=> ((show _ →L[ℝ] ℝ from EuclideanSpace.proj (show SU.group.ColorIndex from i.2)).contDiff.contDiffAt.comp (f:=optic_Q i.1.val ∘ increment 1) 0 (viz_D i.1.val)) -- tune
lemma clock_Ho (o:Seat n): HasFDerivAt (ocular o) (cast_P o) 0:=hasFDerivAt_pi.mpr fun i=> ((EuclideanSpace.proj i.2).hasFDerivAt.comp 0 (face_v _)) -- tune
lemma clock_Ø(o:Seat n):ocular o 0=0:=by funext i; unfold ocular Panorama; rw [G07.at_zero_increment, optic_z]; rfl -- tune
variable (o)
open Simmer
abbrev Tribute(F:Paper n)(G:Genre)(i:Wa n)(V:Pane n):= F i V - crownx G F i o (Panorama o V)
lemma typeU (i:Genre): i.orderB+1 ≤ 4:= by cases i<;>decide
structure Ztitle (F:Paper n) (G:Genre)(o:Seat n)(b c:ℝ): Prop where
 Defect(i:Wa n)(u:tangD n):‖u‖≤ c→ ‖Tribute o F G i (increment 1 u)‖ ≤b * ‖u‖^(G.orderB+1)
lemma OrderT (G:Genre)(F:Paper n) (A:AccessD G F o): ∃ b c:ℝ,1 ≤ b∧0<c ∧ Ztitle F G o b c:=by
 have he(i:Wa n):∃ b c:ℝ,1≤ b∧0<c∧∀ r:tangD n,‖r‖≤c→ ‖Tribute o F G i (increment 1 r)‖ ≤ b * ‖r‖^(G.orderB+1):=by
    let K(G:tangD n→ℂ)(v:Confab o):=G 0; let u:= PressAt (F i); let Z:=ocular o; let S:= caster o; let D:=cast_P o
    let V := u-Cook G.orderB u S∘ Z;
    have hZ: ContDiffAt ℝ 2 Z 0:= (tower_D o).of_le (by norm_num)
    let t':= Serum G hZ (clock_Ø o) (clock_Ho o) (u:=u) (Z:=S) ((A.1 i).of_le (by norm_num)) (A.2.2.1 i) (A.2.2.2 i)
    obtain ⟨c,b,h,l,u⟩:=supplyT V G.orderB (((A.1 i).sub (Serum_0 _ (tower_D o) _)).of_le (Nat.cast_le.mpr (typeU G))) t'; exact ⟨b,c,l,h,u⟩
 choose f g t l p using he; let S:=univ (α:=Wa n); let b:= S.sup' univ_nonempty f; let c:=S.inf' univ_nonempty g
 refine ⟨b,c,(t none).trans (le_sup' _ (mem_univ _)),(lt_inf'_iff _).mpr fun i _=> l i,⟨?_⟩⟩; intro i u v; exact (p i u (v.trans (inf'_le _ (mem_univ _)))).trans (mul_le_mul_of_nonneg_right (le_sup' _ (mem_univ _)) (by positivity))
lemma pitch_O (o:Seat n)(x:Confab o)(i:Wa n)(F:Paper n)(G:Genre)(r:ℝ): crownx G F i o (r • x)= r^G.orderB • crownx G F i o x:=by
 unfold crownx; have he:= (entry_H F i G.orderB).map_smul_univ (fun _=> r) (fun _=> caster o x); simp only [prod_const,card_univ,Fintype.card_fin] at he; simp_rw [map_smul]; exact Eq.trans (congrArg _ he) (smul_comm ..)
-- general linear on f. bounded sums drama.
lemma solarμ {I:Type}[DecidableEq I](T':Finset I)(Q:I→ Paper n)(v:I→ℝ)(t:∀ i∈T',ready_D (Q i))(i:Wa n)(G:Genre)(V:Confab o): crownx G (∑ i∈T',v i • Q i) i o V= ∑ k∈T', v k • crownx G (Q k) i o V:=by
 let K(k:I):= v k; let h(j:I)(x:tangD n):= PressAt (Q j i) x; let Z:=G.orderB; let r:= (Nat.factorial Z:ℝ)⁻¹
 have hd(j)(u:j∈ T'):ContDiffAt ℝ (↑Z) (h j) 0:= (t j u i).of_le (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) (typeU G)))
 have he : PressAt ((∑ i∈T',K i • Q i) i)=∑ j∈T',K j • h j:=funext fun i=>by unfold PressAt; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; rfl -- tune
 let Y:= fun _:Fin Z=> caster o V
 unfold crownx entry_H; rw [he, iteratedFDeriv_sum_apply (fun i p=> (show ContDiffAt ℝ (↑G.orderB) (K i • h i) (0:tangD n) from (hd i p).const_smul (K i))), ContinuousMultilinearMap.sum_apply]; rw [smul_sum]; apply sum_congr rfl; intro j p; rw [iteratedFDeriv_const_smul_apply (hd j p), ContinuousMultilinearMap.smul_apply]; exact smul_comm ..
-- linear closure constants and uniform
abbrev pracR (F:Paper n)(G:Genre)(i:Wa n)(S':Fin G.orderB → Frills o):ℂ:= (Nat.factorial G.orderB:ℝ)⁻¹ • entry_H F i G.orderB (fun j=>caster o (Pi.single (S' j) 1))
-- explicit polynomial
lemma crown_pay (F:Paper n)(V: Genre)(i:Wa n)(h:Confab o):crownx V F i o h=∑ j:Fin V.orderB → Frills o, (∏ t:Fin V.orderB,h (j t)) • pracR o F V i j:=by
 unfold crownx; let Z:= Frills o; let n:=V.orderB; let S:=entry_H F i V.orderB; let Y:=caster o; let R (x:Z):Confab o:=Pi.single x 1; let C:= (Nat.factorial V.orderB:ℝ)⁻¹
 have hp:caster o h=∑ i:Z,h i • caster o (R i):=by
    simp_rw [show ∀ i:Z,h i • caster o (R i)=caster o (h i • R i) from fun i=>(map_smul ..).symm] -- tune ∀ rw under
    rw [← map_sum]; apply congrArg; funext i; simp [R,Finset.sum_apply,Pi.single_apply]; rw [sum_ite_eq]; simp
 simp_rw [hp]; have hx:=S.map_sum (fun i j=> h j • Y (R j))
 change C • S (fun i=> ∑ j,h j • Y (R j))=_; rw [hx,smul_sum]; apply sum_congr rfl; intro j _; rw [show S _= _ from S.map_smul_univ (fun i=> h (j i)) (fun i=> caster o (R (j i)))]; exact smul_comm ..
end ArtCart
end MastTin
end YM.CF.XGarden
end
