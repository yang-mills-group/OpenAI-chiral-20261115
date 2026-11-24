import GaugeFieldConstruction.Spherite
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
lemma optic_cost (b:Face (Per (More n))) (V:Pane n): optic_Q b V = SU.group.curvature (faceValue V b):=by
 unfold optic_Q; rw [atSite_path,rock_v,fanP,show rock (b.2,none)=0 from rfl,map_zero,add_zero,show travel V _ _=1 from rfl]; -- adj1
 exact SU.group.adjoint_one _ -- tune
lemma orbit_run (i:Wa n)(F:Paper n)(G:Genre)(u:∀ i,LocalOn (Pach o) (F i)): LocalOn (Pach o) (Tribute o F G i):=by
 intro U V p; unfold Tribute; rw [u i U V p,show Panorama o U= Panorama o V from ?_]; funext v; unfold Panorama; let b:= v.1.val; have he:touched b⊆Pach o:= (mem_filter.mp v.1.property).2; rw [optic_cost,optic_cost,show faceValue U b=faceValue V b from ?_]; exact face_local b _ _ (fun i a v=>p i (he a) (he v)) -- tune
structure MatPays (F:Paper n)(G:Genre)(o:Seat n)(b c:ℝ):Prop where
 creds:Ztitle F G o b c
 bill(i:Wa n) (j:Fin G.orderB→Frills o) :‖pracR o F G i j‖ ≤ b
lemma matGrow(G:Genre) (A:MatPays F G o v h)(B:v≤c)(C:ℝ)(p:C ≤ h): MatPays F G o c C:=⟨⟨fun i j u=>(A.creds.Defect i j (u.trans p)).trans (mul_le_mul_of_nonneg_right B (by positivity))⟩,fun i j=> (A.bill i j).trans B⟩
lemma bred_R (G:Genre)(F:Paper n)(o:Seat n):∃ b:ℝ,1≤b∧∀ (i:Wa n)(j:Fin G.orderB→Frills o), ‖pracR o F G i j‖≤ b:=by
 let M:= Wa n × (Fin G.orderB → Frills o); let f(i:M):ℝ:= ‖pracR o F G i.1 i.2‖; let b:= ∑ i:M,f i
 refine ⟨1+b,le_add_of_nonneg_right (sum_nonneg (fun i _=>norm_nonneg _)),fun i j=>?_⟩; exact (single_le_sum (f:=f) (fun i _=>norm_nonneg _) (mem_univ (i,j))).trans (le_add_of_nonneg_left zero_le_one)
lemma pracΦp {I:Type}[DecidableEq I](W:Finset I)(F:I→Paper n)(K:I→ℝ)(p:∀ i∈W,ready_D (F i))(i:Wa n)(G:Genre)(j:Fin G.orderB→Frills o) :pracR o (∑ i∈W,K i • F i) G i j=∑ k∈W, K k • pracR o (F k) G i j:=by
 let h(z:I) := PressAt (F z i); let Y:= fun k=> K k • h k;
 have he: PressAt ((∑ i∈W,K i • F i) i)=∑ i∈W,Y i:=funext fun U=>by unfold PressAt; rw [Finset.sum_apply, Finset.sum_apply,Finset.sum_apply]; rfl
 let Q(z: I)(g:z∈ W): ContDiffAt ℝ (↑G.orderB) (h z) 0:= (p z g i).of_le (Nat.cast_le.mpr ((Nat.le_succ _).trans (typeU G)))
 unfold pracR entry_H; rw [he,iteratedFDeriv_sum_apply (fun a v=> (show ContDiffAt ℝ (↑G.orderB) (Y a) (0:tangD n) from (Q a v).const_smul (K a))), _root_.sum_apply,smul_sum]; apply sum_congr rfl; intro k v; unfold Y; rw [iteratedFDeriv_const_smul_apply (Q k v), _root_.smul_apply]; exact smul_comm .. -- tune
lemma Glamor_bid (o: Seat n)(V:Genre)(K:ℝ)(u:300<n.val): ∃ b c:ℝ,1≤ b∧0<c∧ ∀ F∈ Glamor o V K, MatPays F V o b c:=by
 obtain ⟨L,D,p,h,q⟩:= Spectrix.chief (Glamor_f o V K u);
 have he(i:Paper n):∃ v c:ℝ,1≤v∧0<c∧(i∈L → MatPays i V o v c):=by
    by_cases g:i∈L; swap; · exact ⟨1,1,le_rfl,one_pos,fun x=>(g x).elim⟩ -- tune nofun w g
    obtain ⟨v,c,hz,t,Z⟩:=OrderT o V i (matron (h g) u); obtain ⟨B,hB,V⟩:=bred_R V i o; refine ⟨v+B,c,hz.trans (le_add_of_nonneg_right (by linarith)),t,fun _=>⟨⟨fun i t h=>le_trans (Z.Defect _ _ h) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by linarith)) (by positivity))⟩,fun i j=> (V i j).trans (le_add_of_nonneg_left (by linarith))⟩⟩ -- c missing
 choose v w l t r using he
 let R (i:↥L):ℝ:= w i.val; obtain ⟨a,s,E⟩ :∃ a:ℝ,0<a∧∀ i∈L,a ≤ w i:=by
    by_cases H:L.Nonempty; · exact ⟨L.inf' H w,(lt_inf'_iff _).mpr fun i _=> t i,fun i p=>inf'_le _ p⟩
    exact ⟨1,one_pos,fun i p=>(H ⟨i,p⟩).elim⟩
 let j:= V.orderB; let Y:=∑ i∈L,D*v i; let b:=max 1 Y; refine ⟨b,a,le_max_left ..,s,fun F U=>?_⟩;
 let P(i)(h':i∈L):= r i h'; have hm(i:Paper n)(p:i∈L): ready_D i:= (matron (h p) u).1
 obtain ⟨z,x,f⟩:= (q F U).pulse; rw [←f]; unfold voices; refine ⟨⟨fun i Q c=>?_⟩,fun i J=>?_⟩
 · let W(k:Paper n):= Tribute o k V i (increment 1 Q); change ‖W _‖≤_; have hf: W (∑ i∈L,z i • i)=∑ i∈L,z i • W i:=by
       unfold W Tribute; rw [Finset.sum_apply, Finset.sum_apply, show crownx _ _ _ _ _=_ from solarμ o L (fun i=>i) z hm i V (Panorama o _), ←sum_sub_distrib]; apply sum_congr rfl; intro i _; simp_rw [smul_sub]; try rfl -- tune
   rw [hf]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)); unfold Y; rw [Finset.sum_mul]; apply sum_le_sum; intro k p; rw [norm_smul]; refine (mul_le_mul (x k p) ((P k p).creds.Defect i Q (c.trans (E k p))) (norm_nonneg _) (by positivity)).trans_eq (mul_assoc ..|>.symm)
 rw [show pracR o _ _ _ _= _ from (show pracR o (∑ i∈L,z i • i) _ i J= _ from pracΦp L (fun i=>i) z hm i V J)]; exact (norm_sum_le ..).trans ((sum_le_sum (f:=fun k:Paper n=> ‖z k • pracR o k _ i J‖) (g:=fun k=> D*v k) fun k p'=>by rw [norm_smul]; exact mul_le_mul (x k p') ((P k p').bill ..) (norm_nonneg _) p).trans (le_max_right ..))
lemma Rc_mo (n:Side)(w:300<n.val)(K:ℝ)(V:Genre):∃ b c:ℝ,1≤ b∧ 0<c ∧ ∀ (o:Seat n)(F:Paper n), F∈Glamor o V K→ MatPays F V o b c:=by
 choose f g u h U using fun i:Seat n=> Glamor_bid i V K w
 refine ⟨univ.sup' univ_nonempty f,univ.inf' univ_nonempty g,(u 0).trans (le_sup' _ (mem_univ _)), (lt_inf'_iff _).mpr fun i _=>h i,fun i F p=> matGrow _ (U i _ p) (le_sup' _ (mem_univ _)) _ (inf'_le _ (mem_univ _))⟩
end ArtCart
end MastTin
end YM.CF.XGarden
end
