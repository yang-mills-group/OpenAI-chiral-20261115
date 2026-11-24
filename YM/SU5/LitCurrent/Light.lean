import YM.SU5.LitCurrent.Pings
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Salt
variable {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
lemma offset_pose (x:Site N)(s:Sweep N)(k:ℕ): offsetMask k (pose s x)=actY s (offsetMask k x):=by
 unfold actY offsetMask; rw [←sitU, ←paysT,pose_node,map_singleton]; rfl -- tune
private lemma real_zero (s:Sweep N)(b:Bool): realR s b 0=0:=by
 cases b <;>cases h:detX s.s<;>simp [realR,Sour.bolt,Sault.hitL,Sault.doveL,foeL,Thera.jazz,h,win_z]
private lemma sibling (s:Sweep N)(D:Sa N):actY s (actY s⁻¹ D)=D:=by
 ext; simp [actY,sitU]

variable (z:Checked p K t d a k q)
local notation "L"=> roller z.angle z.roof
include z
lemma chamber (x:Site N)(U:Orbit N)(h:pingS p.threshold (offsetMask p.B x) U.1):Agrees (offsetMask k x) (K U) U.1:=by
 let Y:=offsetMask p.B x; let X:Aura N:=⟨Y,node x,halo_subset _ _ (mem_singleton_self _)⟩
 have hp:halo (q+10) (offsetMask k x) ⊆ Y:=by
    intro i w; obtain ⟨c,g,t⟩:=halo_spec.mp w; obtain ⟨m,b,hc⟩:=halo_spec.mp g; exact halo_spec.mpr ⟨_,b,(separation_triangle m c i).trans (by have h':=z.extra; omega)⟩
 intro i ui _; exact fern (X:=X) z.roof z.threshold (offsetMask k x) hp _ ⟨by rw [sdiff_empty]; exact h,empty_subset _⟩ i ui rfl U.2
lemma reachesShort (x:Site N)(E:StageTree N d (4*a) v)(h:moored (node x) E)(D:Sa N)(i j:Single N)(g:D.card<k)(w:E.W D i j≠0): D ⊆ offsetMask k x:=by
 have hp:node x∈D:=by by_contra H; exact w (by rw [h D H]; rfl)
 obtain ⟨X,t,e⟩:= ((E.coat D|>.1 ()).expo i j).triggered w
 intro l hl; exact halo_spec.mpr ⟨node x,mem_singleton_self _,((show separation _ l < D.card from X.lim _ hp _ hl).trans g).le⟩
lemma lightTravel (s:Sweep N)(b0:Bool)(x:Site N)(E V:StageTree N d (4*a) v)
    (u:moored (node x) E)(w:moored (node (pose s x)) V)
    (h:∀ (S:Sa N)(U:Pane N)(y:Openc (More N) d),y.val=profile U→
        V.F (actY s S) () (Sour.fog s d y) = realR s b0 (E.F S () y))
    (U:Pane N):
    live K p k (pose s x) V (flashA s U)=realR s b0 (live K p k x E U):=by
 let X:Orbit N:=(U,Classical.arbitrary _); let W:Orbit N:=(flashA s U,Classical.arbitrary _); let T:= pose s x
 change live K p k T V W.1= realR s b0 (live K p k x E X.1); rw [noTag T V z w,noTag x E z u]
 have hw:pingS p.threshold (offsetMask p.B T) W.1 ↔ pingS p.threshold (offsetMask p.B x) X.1:=(offset_pose x s p.B).symm ▸ glowA _ _ _ U
 by_cases ht:pingS p.threshold (offsetMask p.B x) X.1; swap; · rw [if_neg ht,if_neg (mt hw.mp ht),real_zero]
 rw [if_pos ht,if_pos (hw.mpr ht)]; let l:= L X; let y:= Sour.fog s d l; let Z:= flashA s (K X); have he:y.val=profile Z:= real_box s d (K X) _ rfl
 have hp:Agrees (offsetMask k T) Z W.1:=by
    refine flashD s (K X) U _ ?_
    change Agrees (↑((offsetMask k (pose s x)).map (boxA s).toEmbedding): Set (Seat N)) (K X) X.1
    rw [offset_pose,show (actY s (offsetMask k x)).map (boxA s).toEmbedding= _ from (show _=offsetMask k x from ?_)] -- tune
    · exact chamber z x X ht
    change (actY s _).map _ = _; unfold actY; ext; simp
 rw [runs _ _ z w W (hw.mpr ht) Z y he (fun D i j g t k v b=> (hp k (reachesShort z T V w D i j g t v) (reachesShort z T V w D i j g t b)).symm)]
 change beforePing V k y.val= _; rw [show profile (K X)=l.val from rfl]; unfold beforePing; rw [dif_pos y.property,dif_pos l.property]
 unfold retain; rw [real_f]; symm
 refine sum_bij (fun i _=>actY s i) (fun _ _=>mem_univ _) (fun i _ j _ v=> map_injective _ v) (fun i _=>⟨_,mem_univ (actY s⁻¹ i), sibling s i⟩) ?_
 intro i hi; rw [show (actY s i).card=i.card from card_map ..]; split_ifs; exact (h i (K X) l rfl).symm; exact real_zero ..

namespace Pattern
variable {P Q:SOp N}(E:Pattern P Q r d a v)(x:Site N)(e:FaceDir)
lemma rollTax (s:Sweep N)(U:Pane N): live K p k (pose s x) (E.A (pose s x)) (flashA s U) = realR s true (live K p k x (E.A x) U):= lightTravel z s true x _ _ (E.moorA _) (E.moorA _) (E.chart s x) U
lemma rollCurrent (s:Sweep N)(U:Pane N): live K p k (pose s x) (E.J (teamTravel s (x,e))) (flashA s U) = realR s false (live K p k x (E.J (x,e)) U):= by exact lightTravel z s false x (E.J (x,e)) (E.J (teamTravel s (x,e))) (E.moorJ (x,e)) (E.moorJ (teamTravel s (x,e))) (E.chartJ s (x,e)) U -- tune
lemma cabaret (U:Orbit N): live K p k x (E.J (x,axisFlip e)) U.1= -(live K p k x (E.J (x,e)) U.1):=by
 rw [noTag x _ z (show moored _ _ from E.moorJ (x,axisFlip e)),noTag x _ z (show moored _ _ from E.moorJ (x,e))]
 split; swap; · rw [neg_zero]
 let y:= L U; rw [show profile (K U)=y.val from rfl]; unfold beforePing; rw [dif_pos y.property,dif_pos y.property]
 unfold retain; rw [←sum_neg_distrib]; apply sum_congr rfl; intro S _; split_ifs; exact E.revJ _ _ S (K U) y rfl; rw [neg_zero]
lemma hatted (U:Orbit N): IsSelfAdjoint (live K p k x (E.A x) U.1):=by
 rw [noTag x (E.A x) z (E.moorA x)]; split; swap; · exact IsSelfAdjoint.zero _ -- tune
 let y:= L U; rw [show profile (K U)=y.val from rfl,beforePing,dif_pos y.property]
 change star (retain (E.A x) k y)= _; unfold retain; rw [star_sum]; apply sum_congr rfl; intro S _; split_ifs; exact E.herm _ _ (K U) y rfl; rw [star_zero]
end Pattern
end YM.CF.LitCurrent
