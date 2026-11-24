import GaugeFieldConstruction.Likeness
import GaugeFieldConstruction.Pimper
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
variable {x y:Cover}{d e:ℕ}{k:Side}
-- $moko$ preserves bill
lemma mk_sail {a:ℂ}(z:star a=a)(b p: Bool){r:ℂ}(l:star r=r){i j:Single n}{m s:Single k}(A:UNI (Single n))(B:UNI (Single k))(v:a*A.val i j=B.val m s*r):a*moko A p b i j=moko B p b m s*r:=by
 have hv:a* star (A.val i j)=star (B.val m s)*r:=by
    calc _= star (a*A.val i j) := by rw [star_mul,z]; ring
         _= _ := by rw [v,star_mul,l]; ring
 cases p <;> cases b <;> first| exact v|exact hv|skip
 all_goals simp [moko,crib,thread,filmG,ccU,cc]
 all_goals first| rw [mul_left_comm a,v,mul_assoc]| rw [mul_left_comm a,show a * (starRingEnd ℂ) (A.val i j)= (starRingEnd ℂ) _*r from hv,mul_assoc]
-- zeros if U entries zeros.
lemma mk_s_zero (b p:Bool)(A: UNI (Single n))(i j)(h:A.val i j=0):moko A p b i j=0:=by
 cases p<;>cases b<;>simp [moko,crib,thread,filmG,ccU,h,cc,star_zero] -- tune
abbrev wind_realB (i:Cover): star (winding n i) = winding n i:= fee_real _ -- Prop
lemma bill_realB(i:mort x d)(k:Side): star (billJ n k i)=billJ n k i:=by unfold billJ; rw [star_mul,wind_realB,wind_realB,mul_comm]
-- endpoint correspondence. index pos deterministic on reference i. Use no rotation in gauge case. ships on all hosts.
variable (p:Bool)
lemma sailor (g:ridge x d → ridge y e)(A:UNI (Single n))(B:UNI (Single k)) (L:∀ (i:mort x d)(j:mort y e), A.val (hereF n j) (hereF n i)≠0 → g i.1=j.1) (H:∀ (i:mort x d)(t: Single k),B.val t (hereF k i)≠0→ wrap k (g i.1).val=t.1.1)(P:∀ (i:mort x d)(j:mort y e),g i.1=j.1 → billJ n k j * A.val (hereF n j) (hereF n i)=B.val (hereF k j) (hereF k i)*billJ n k i): Ship x y d e p A B:=by
 constructor; intro b i t; let j:mort y e:=(g i.1,t.1.2,t.2); rw [Finset.sum_eq_single j]; swap
 · intro v _ h; split_ifs with hx; swap; · rfl
   have he:A.val (hereF n v) (hereF n i)=0:= Classical.byContradiction fun a=> h (Prod.ext (L i v a).symm (congrArg (fun i:Single k=> (i.1.2,i.2)) hx))
   rw [mk_s_zero b _ _ _ _ he,mul_zero]
 swap; · simp
 split_ifs with g'
 · exact (mk_sail (bill_realB ..) b p (bill_realB ..) A B (P i j rfl)).trans (by rw [g'])
 have hv:B.val t (hereF k i)=0:=Classical.byContradiction fun a=> g' (Prod.ext (Prod.ext (H _ _ a) rfl) rfl); rw [mk_s_zero b p _ _ _ hv,zero_mul]

-- grid
lemma visits_wrap {i j: (ridge x d)} (L:Side)(w:d < L.val)(p:wrap L i.val=wrap L j.val): i=j:=by
 apply Subtype.ext; apply node_cone.mp; apply cart_I d w ((ridge_spec _).1 i.property) ((ridge_spec _).1 j.property); rw [←node_of,←node_of,p]
variable {p}
lemma sailorG (v:Agora n)(u:Agora k)(w:d < n.val)(D:∀ i∈cartO x d,v (wrap (More n) i)=u (wrap (More k) i)): Ship x x d d p (tradew n v) (tradew k u):=by
 refine sailor p id _ _ (fun i j H=>?_) (fun i s H=>?_) fun i j h=>?_
 · have hx: aptK (hereF n j)=aptK (hereF n i):=Tye.birth_g _ _ _ H; exact visits_wrap _ w (Tenant.needle hx.symm)
 · have hx:aptK _=aptK _:= Tye.birth_g _ _ _ H; exact Tenant.needle hx.symm
 rcases i with ⟨i,l⟩; rcases j with ⟨j,c⟩; change i=j at h; subst i
 let f:=v (wrap (More n) (nodeC j.val)); let g:=u (wrap (More k) (nodeC j.val))
 have he:f=g:= D _ ((ridge_spec _).1 j.property)
 have ha(n:Side)(u:Agora n)(l c:SpinIdx×SU.Slot): (tradew n u).val (hereF n (show mort x d from (j,l))) (hereF n (show mort x d from (j,c)))= if l.1=c.1 then (SU.matter (u (wrap (More n) (nodeC j.val)))).val l.2 c.2 else 0:=by
    unfold hereF tradew; dsimp only; rw [jump_apply, ← node_of]; simp -- namespace jump
 unfold f g at he; rw [ha,ha,he]; change _*_= _ * (Lifted.winding n j.val* Lifted.winding k j.val); exact mul_comm ..
lemma gDress {V:Pane k}(g:Agora k): onC k (GA g V) = gauge (g ∘ wrap (More k)) (onC k V):=by
 funext i; rw [onC_spec]; unfold GA Lattice.gauge; simp [onC_spec]
-- Covariant plan in application on any hosts
lemma dock_G (g:Agora k)(i:Pane k)(w:d<n.val)(v:Pane n)(h:Agrees (cartO x d) (onC n v) (onC k i)): ∃ u:Agora n, Dockers x x d d p v (GA u v) i (GA g i) (tradew n u) (tradew k g):=by
 let u:Agora n:= fun i=>g (wrap (More k) (prospect x i)); have he(z)(w':z∈cartO x d): u (wrap (More n) z)=g (wrap (More k) z):=by unfold u; rw [prospect_F w' w]
 refine ⟨u,sailorG u g w he,h,?_⟩
 rw [gDress,gDress]; rintro ⟨i,t⟩ p q; unfold Lattice.gauge; simp only [Function.comp_apply]; rw [he _ p, he (i+step t) q, h (i,t) p q]
lemma pR_G (w:d<n.val)(f:Psu x d)(h:∀ i,LocalOn (cartO x d) (f i))(v:portable (pR n f))(m:Side): portable (pR m f):=by
 intro W g; let Z:Pane n:= snake x (onC m W); let D:Agrees (cartO x d) (onC n Z) (onC m W):= fun i p q=> (cart_L w (onC m W) i p q).symm -- tune
 obtain ⟨b,h'⟩:= dock_G (p:=false) g W w Z D; exact h'.passK w w h h (v Z b)
end ArtCart
end MastTin
end YM.CF.XGarden
end
