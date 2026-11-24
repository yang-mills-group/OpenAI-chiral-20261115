import Anomaly.Basis.Grid
import Anomaly.Ship.Pod
-- normalize extraction before call joins with kept authorization on old data. needed Bags book from all.Key requirements; also record pose comparison efforts separately. 
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill Buffered StressExchange Reed
open Vow.TreasuryFog Py Neon
variable {N B M L:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h x₀ y c s:ℝ}{k q j l:ℕ}
local notation "Tc"=> mid N B
variable {g:ℕ}{wL:Odd L.val}{H:Pricing g L wL (Thread g)} {U:Grasp H B d}{R:GramM (mid N B)}{T:Scree.Loom (mid N B)}
-- Use any finite collections.
section
local notation "KΔ"=> Mark Tc
lemma vessel_sized (x:ℂ){K: Bag (mid N B)}{X:phy (mid N B)} (y:Vessel U R T K X): Vessel U R T (x • K) (x • X):=by
 have hp:giveB (x • K)=x • giveB K:=by simp only [giveB, Pi.smul_apply, smul_sum]
 refine ⟨fun u v=> by rw [hp]; exact Leaf.ψX _ _ (y.rank u v),fun t v h w=>?_⟩; rw [hp,Pi.smul_apply,Pi.smul_apply,act_smul, act_smul, map_smul, y.science t v h w]
lemma vessel_more {K L: Bag (mid N B)}{X Y:phy (mid N B)} (y:Vessel U R T K X) (b:Vessel U R T L Y): Vessel U R T (K+L) (X+Y):=by
 have hp:giveB (K+L)=giveB K+ giveB L:=by simp only [giveB, Pi.add_apply, sum_add_distrib]
 refine ⟨fun u v=> by rw [hp]; exact Leaf.σX _ _ (y.rank u v) (b.rank u v),fun t v h w=>?_⟩; rw [hp,Pi.add_apply,Pi.add_apply,act_add, act_add,map_add,y.science t v h w,b.science t v h w]
lemma vessel_nil : Vessel U R T 0 (0:phy (mid N B)):=by
 refine ⟨fun x i=> ?_,fun x i p v=> ?_⟩ <;> rw [giveB]; · simp only [Pi.zero_apply,sum_const_zero]; exact JointJ.nil (N:=Tc) (P:=0) (Q:=0) (W:=0) |>.rank
 simp [act_zero]
variable {o:Site (mid N B)} {φ:ArcΦ}{K: Bag (mid N B)}
-- E orientation from receipt of that operator, also for ANY purchases of memberships
lemma αout (Y:RegBudget (mid N B)) (x:IncX primeU Y P h a)(p:1≤h): InΦ (pilasters l P o Y):=by
 obtain ⟨G,v,h⟩:=x.weight; let Z:= univ.filter fun X:Scree.Hub Tc=> X.val.1=node o∧ Moto.chose l P X; unfold pilasters; have hx(U:Finset (Scree.Hub Tc))(p':U⊆ Z): InΦ (∑ X∈U,Neon.pillar o (Y X) P):=by
    induction U using Finset.induction_on with
    | empty=> rw [sum_empty]; exact ⟨mind_A.zero_mem,mind_B.zero_mem,mind_C.zero_mem⟩
    | insert i U q ih=> rw [sum_insert q]; obtain ⟨u,Q,w⟩:=ih (subset_trans (subset_insert _ _) p'); obtain ⟨y,z,P⟩:=in_Φ o i _ _ _ _ (zero_le_one.trans p) (v i) (mem_filter.mp (p' (mem_insert_self ..))).2.1; exact ⟨mind_A.add_mem y u,mind_B.add_mem z Q,mind_C.add_mem P w⟩
 exact hx _ (Subset.refl _)
-- E stamp ideal after exact correction please no triangular stale in step
lemma drill_ray (r:Drill P q k l o h s K φ a c t) (τ:Ids (mid N B)) {G F:Aura (mid N B)→ℝ}(E:∀ i,Flight P q i h (K i) (G i) (F i)) :let Z:= singlePole τ K E (node o); Drill P q k l o h s K (pilasters l P o Z) a c 0:=by
 intro Z; refine ⟨r.yard,fun W X t B'=>?_⟩; let p:=r.stamp G F τ E; rw [booth_one E τ _ B' t]; refine ⟨p.rights,?_,p.zeroish⟩; dsimp only [Z]; simp only [sub_self,norm_zero,zero_mul,le_refl,and_self]
lemma drill_nil (hv:1≤h): Drill P q k l o h s 0 0 0 0 0:=by
 refine ⟨Barrage.zeroR,fun W X t B'=>?_⟩; let Q:=singlePole (P:=P) t 0 B' (node o); have he: Q=0:=by
    funext X V; apply Subtype.ext; by_cases p:X.val.1=node o; swap; · unfold Q; rw [show singlePole _ _ _ _ X=0 from station _ _ _ (fun (_:Fin 1) i=>B' i) _ _ (0:Fin 1) X p]; rfl
    unfold Q; rw [pole_value _ _ _ _ p]; simp [coll_T,Sault.rind]
 unfold Q at he; rw [he]; have h:= AxStamp.simple (o:=o) (L':=l) (C:=P) (M:=0) (Vale.lye primeU P h).1 hv (fun _ _=>rfl); simpa only [AxStamp.Ρpost,mul_zero] using h
end
variable {ι:Type}
open Eire Lor
structure Totem (U:Grasp H B d)(R:GramM (mid N B))(T:Scree.Loom (mid N B))(q l k m:ℕ)(o:Site (mid N B))(E: Bag (mid N B))(X:Mark (mid N B))(V:phy (mid N B))(Φ:ArcΦ)(h s a c y z:ℝ) : Prop where
   tag: WindowTag X o m z
   true': Contact T (offsetMask m o) X V
   step:Vessel U R T E V
   bill: Drill R.p q k l o h s E Φ a c y
namespace Totem
variable {M M':Mark (mid N B)}{X Y:phy (mid N B)}{K K':Bag (mid N B)}{u v w x z:ℝ}{F V:ArcΦ}{o:Site (mid N B)}
variable (A:Totem U R T q l k j o K M X F h s a c y z)(B':Totem U R T q l k j o K' M' Y V h s u v w x) (p:1≤h)
include p
lemma zeroP :Totem U R T q l k j o 0 0 0 0 h s 0 0 0 0:=⟨WindowTag.zero,⟨AtSupport.zeroM,fun _=>Sector.zero _,fun _=>rfl⟩,vessel_nil,drill_nil p⟩
include A
lemma scaleP (u:ℂ):Totem U R T q l k j o (u • K) (u • M) (u • X) (u • F) h s (‖u‖*a) (‖u‖*c) (‖u‖*y) (‖u‖*z):= ⟨A.tag.scale u,A.true'.scale u,vessel_sized u A.step,A.bill.sizes u p⟩
lemma dawnV (v:a≤u)(g:c≤ w)(Y:y≤x)(X':z≤x₀): Totem U R T q l k j o K M X F h s u w x x₀:= ⟨{A.tag with price:=fun i=>(A.tag.price _).trans X'}, A.true',A.step, A.bill.raiseP v g Y⟩
include B'
lemma combo :Totem U R T q l k j o (K+K') (M+M') (X+Y) (F+V) h s (a+u) (c+v) (y+w) (z+x):= ⟨A.tag.add B'.tag,A.true'.add B'.true',vessel_more A.step B'.step,A.bill.gain B'.bill p⟩
omit A B'
lemma span (S:Finset ι)(K:ι→Bag (mid N B))(M:ι→ Mark (mid N B))(X:ι→phy (mid N B))(Z:ι→ArcΦ)(a b c z:ι→ℝ)(H:∀ i∈S, Totem U R T q l k j o (K i) (M i) (X i) (Z i) h s (a i) (b i) (c i) (z i)): Totem U R T q l k j o (∑ i∈S,K i) (∑ i∈S,M i) (∑ i∈S,X i) (∑ i∈S,Z i) h s (∑ i∈S,a i) (∑ i∈S,b i) (∑ i∈S,c i) (∑ i∈S,z i) := by induction S using Finset.induction_on with|empty=> simp only [sum_empty]; exact zeroP p|insert i S t ih=> simp only [sum_insert t]; exact (H _ (mem_insert_self ..)).combo (ih (fun i v=> H i (mem_insert_of_mem v))) p
end Totem
end YM.CF.Swell.Porticus
