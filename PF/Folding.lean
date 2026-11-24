import PF.Powers
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.WickLabels
open Hake Hive Sault Pastry Set
variable {N:Type}[LinearOrder N][Fintype N]
namespace Bill
open Branch Material
variable {D X : Type}[TopologicalSpace D][Fintype X][DecidableEq X]{H:Host X N D}
variable {ν Δ : D→ℝ}{S T pad:Seal X}{a h c B y:ℝ}
namespace Docket
private lemma shot_to {u w:N}{c:ℝ}{f:D→ℂ}(h:Material.Bit H ν S T u w c f):Bill.Tag H ν S T f c:=⟨h.pos,h.load,h.listens,h.inputs,fun v=>⟨(h.stake v).1,(h.stake v).2.1⟩⟩
lemma distribute {G:Raw D N}(Y:Seal X→Raw D N)(W: Seal X→ Toll N) (v:∀ S:Seal X,Endor H ν pad S (W S) (Y S))(l:∀ x,G x=∑ S,Y S x)(w:∑ i:N,∑ j:N, saleM a W i j ≤ B)(p:0 ≤ a){c:ℝ}: Docket H ν pad a c (fun x=>dg (G x)) (B*c^2):=by
 let L(i j:N):List (Oboe N):=[(true,i),(false,j)]
 let F(x:Seal X × N×N)(u:D):=(Y x.1 u x.2.1 x.2.2) • Hive.drum (L x.2.1 x.2.2); let C (x:Seal X × N×N):=Branch.rent a (x.1\pad)*c^(2:ℕ)*W x.1 x.2.1 x.2.2
 have unit (x:Seal X × N×N): Docket H ν pad a c (F x) (C x):=Docket.single (L _ _) (S:=x.1) (shot_to ((v _).block ..)) fun u j v'=> by
   have hv:= ((v x.1).block x.2.1 x.2.2).stake u; rcases (List.mem_cons.mp (show j ∈ _ from v')) with o|o; rw [o]; exact hv.2.2.1; have :=List.mem_singleton.mp o; rw [this]; exact hv.2.2.2
 have he(t:ℝ):0≤t^2:=sq_nonneg t
 have hf:∑ x,C x≤ B*c^2:=by
   rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
   refine le_trans (b:=∑ i:N,∑ j:N, ∑ S:Seal X, (Branch.rent a S*W S i j) * c^2) ?_ (le_trans ?_ (mul_le_mul_of_nonneg_right w (he _)))
   · rw [sum_comm]; apply sum_le_sum; intro i hi; rw [sum_comm]; apply sum_le_sum; intro y _; apply sum_le_sum; intro s _; unfold C
     have ht:= ((v s).block i y).pos
     refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show Branch.rent a (s\pad) ≤ Branch.rent a s from ?_) (he c)) ht).trans_eq (by ring)
     unfold Branch.rent; gcongr; exact Finset.sdiff_subset
   simp only [← sum_mul]; exact le_rfl
 have hx:= (Docket.summers univ F C (fun i _=>unit i)).up hf
 convert hx using 1; funext x; rw [l,Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; unfold dg F L Fock.dyad Hive.drum; simp only [Matrix.sum_apply, Finset.sum_smul,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,Hake.bell, ite_true, Bool.false_eq_true,ite_false]
 symm; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_comm]
-- one transported comb. coefficients Y. read c-r basis ordered words Hake. ol d etc.
private def place (Z:Op N)(b:Bool)(i:N) : FC N:=if b then Fock.create (acts Z (basisKet i)) else Fock.remove (acts Z (basisKet i))
lemma placeCost {c:ℝ}(P:D→Op N)(p:Shot H (fun _=>1) ∅ a B P)(pad:Seal X)(i:N)(v:H.port i∈pad)(t:Grove H.space pad)(g:0≤a)(hc:0 ≤ c)(b:Bool): Docket H (fun _=>1) pad a c (fun x=> place (P x) b i) (c*B):=by
 obtain ⟨Y,K,L,U,N0⟩:=p
 let S(k:Seal X × N):= k.1 ∪ pad
 let Q(k:Seal X× N)(x:D):=let z:=Y k.1 x k.2 i; if b then z else star z
 let M(k:Seal X × N):= K k.1 k.2 i
 let F(k:Seal X × N):List (Oboe N):=[(b,k.2)]
 have hT(k:Seal X × N):Bill.Tag H (fun _=>1) pad (S k) (Q k) (M k):=by
    let w:=(L k.1).block k.2 i; have hr:Bill.Tag H (fun _=>1) pad (S k) (fun x=>Y k.1 x k.2 i) (K k.1 k.2 i):=⟨w.pos,w.load,w.listens,fun x y v=>w.inputs _ _ (H.relay subset_union_left v),fun h=>⟨subset_union_right,(w.stake h).2.1.unite t (w.stake h).2.2.2 v⟩⟩
    refine ⟨hr.pos,fun x=>?_,?_,fun x y p=>?_,hr.resource⟩
    · cases b; unfold Q; simp only [Bool.false_eq_true, ite_false,norm_star]; exact hr.price _; exact hr.price _
    · cases b; exact hr.cont.star; exact hr.cont
    unfold Q; rw [show Y _ x k.2 i = Y _ y k.2 i from hr.portal _ _ p]
 have hr : ∑ k:Seal X×N,Branch.rent a (S k\pad)*c*M k≤ c*B:=by
   refine le_trans ?_ (mul_le_mul_of_nonneg_left (U.cols i) hc)
   simp only [Branch.saleM,mul_sum]; rw [Fintype.sum_prod_type,sum_comm]; apply sum_le_sum; intro j _; apply sum_le_sum; intro A _
   unfold S M; dsimp only; rw [Finset.union_sdiff_distrib,Finset.sdiff_self,Finset.union_empty]; have he:0≤K A j i:=((L A).block j i).pos
   refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show Branch.rent a (A\pad) ≤ Branch.rent a A from ?_) hc) he).trans_eq (by ring)
   unfold Branch.rent; gcongr; exact Finset.sdiff_subset
 have hf(k:Seal X × N):Docket H (fun _=>1) pad a c (fun x=> Q k x • Hive.drum (F k)) (Branch.rent a (S k\pad)*c*M k):=by
    convert Docket.single (F k) (hT k) (c:=c) (a:=a) (fun h j hj=> by rw [List.mem_singleton.mp hj]; exact mem_union_left _ (((L k.1).block k.2 i).stake h).2.2.1) using 1; simp [F]
 convert (Docket.summers Finset.univ _ _ (fun k _=> hf k)).up hr using 1; funext x; cases b <;> rw [Fintype.sum_prod_type,sum_comm] <;> unfold place
 · rw [if_neg Bool.false_ne_true, Fock.remove_def]; apply sum_congr rfl; intro k _; rw [basis_act,N0,Matrix.sum_apply,star_sum, Finset.sum_smul]; unfold Hive.drum Q F; simp [Hake.bell]
 rw [if_pos rfl, Fock.create_def]; apply sum_congr rfl; intro k _; rw [basis_act,N0,Matrix.sum_apply,Finset.sum_smul]; unfold Hive.drum F Q; simp [Hake.bell]
-- conjugation on both so Expense no quant global factor. linked label anchored `pad` containing starting word legs.
lemma torn {c:ℝ}(P Q:D→ Op N)(p:Shot H (fun _=>1) ∅ a B P)(q:Shot H (fun _=>1) ∅ a B Q)(ht:∀ x,P x*Q x=1)(hu:∀ x,Q x*P x=1)(g:0≤a)(hc:0 ≤ c)(l:List (Oboe N))(pad:Seal X)(hd:Grove H.space pad)(v:pad.Nonempty)(hw:∀ i∈l,H.port i.2 ∈pad):
    Docket H (fun _=>1) pad a c (fun x=> quant (P x)* Hive.drum l*quant (Q x)) ((c*B)^l.length):=by
 have he(k:Oboe N)(v:H.port k.2∈pad):Docket H (fun _=>1) pad a c (fun x=> quant (P x)*Hake.bell k*quant (Q x)) (c*B):=by
   obtain ⟨t,i⟩:=k; cases t
   · convert placeCost (H:=H) (fun x=>star (Q x)) q.starP pad i v hd g hc false using 1; funext x; change quant (P x)*takeF i*quant (Q x)=_
     rw [mul_assoc, ←remove_take,quant_ann, ←mul_assoc, ←quant_mul,ht,quant_one,one_mul]; rfl
   convert placeCost P p pad i v hd g hc true using 1; funext x; change quant (P x)*Fock.put i*quant (Q x)=_; rw [quant_put,mul_assoc,←quant_mul,ht,quant_one,mul_one]; rfl
 induction l with
 | nil=> simpa only [List.length_nil,pow_zero,show Hive.drum ([]:List (Oboe N))=1 from rfl,mul_one,←quant_mul,ht, quant_one] using Docket.one (c:=c) (a:=a) hd
 | cons i L ih=>
    have hi(x:D): quant (P x)*Hive.drum (i::L)*quant (Q x)=(quant (P x)*Hake.bell i*quant (Q x))*(quant (P x)*Hive.drum L*quant (Q x)):=by simp only [Hive.drum,List.map_cons,List.prod_cons,mul_assoc,← mul_assoc (quant (Q _)) (quant _),← quant_mul,hu,quant_one,one_mul]
    simp_rw [hi,List.length_cons,pow_succ']; convert (he i (hw i List.mem_cons_self)).product (ih (fun j u=>hw _ (List.mem_cons_of_mem _ u))) v hc g using 1; ext; simp

-- Results in PF.PhaseL. want append price of baseline Visa with mandatory support before assembling power. 
lemma import_preamble (Y:Seal X){q:ℂ}(u:Grove H.space Y) (l:List (Oboe N))(w:∀ i∈ l,H.port i.2∈ Y):Docket H (fun _=>1) Y a c (fun _:D=> Hive.drum l) (c^l.length):= by
 convert single l (S:=Y) (H:=H) (ν:=fun _=>1) (B:=1) (g:=fun _=>1) (a:=a) (c:=c) (pad:=Y)
    (show Bill.Tag H (fun _=>1) Y Y (fun _=>1) 1 from ⟨zero_le_one,fun _=>by simp,continuous_const,fun _ _ _=>rfl,fun _=>⟨Finset.Subset.refl _,u⟩⟩) (fun _=>w) using 1; funext x; rw [one_smul]; simp [Branch.rent]
lemma gifted (p:pad ⊆ T){Y:D→ℂ}(q:Bill.Tag H ν pad T Y y){c:ℝ}(g:0 ≤ a)(e:0≤ c){F:D→ FC N}(h:Docket H (fun _=>1) T a c F B) : Docket H ν pad a c (fun x=>Y x • F x) (rent a (T\pad)*y*B):=by
 obtain ⟨I,i,S,L,E,K,U,V,W,Q⟩:=h
 have Yp:=q.pos
 refine ⟨I,i,S,L,fun i x=>Y x*E i x,fun i=>y*K i,(fun i=>?_ ),fun i u j hj=>V i (right_ne_zero_of_mul u) j hj,?_,?_⟩
 · by_cases ht:K i=0
   · simp only [show ∀ x,E i x=0 from fun x=> Bill.Tag.zero (U i) ht x,mul_zero,ht]; refine ⟨le_rfl,fun _=>by simp,continuous_const,fun _ _ _=>rfl,by simp⟩
   obtain ⟨v,hp⟩:= (U i).resource ht
   refine ⟨mul_nonneg Yp (U i).pos,fun x=>?_,q.cont.mul (U i).cont,fun x z t=> congrArg₂ (·*·) (q.portal _ _ (H.relay v t)) ((U i).portal _ _ t),fun _=>⟨p.trans v,hp⟩⟩
   rw [norm_mul]; exact (mul_le_mul (q.price x) ((U i).price x) (norm_nonneg _) ((norm_nonneg _).trans (q.price x))).trans_eq (by ring)
 · refine le_trans ?_ (mul_le_mul_of_nonneg_left W (mul_nonneg (rent_pos ..).le Yp))
   rw [mul_sum]; apply sum_le_sum; intro i _; by_cases ht:K i=0; simp [ht]
   obtain ⟨v,hp⟩:= (U i).resource ht; dsimp only
   have he: S i\pad=T\pad∪(S i\T):=by ext j; simp; grind
   refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he ▸ rent_join (T\pad) (S i\T) g) (pow_nonneg e _)) (mul_nonneg Yp (U i).pos)).trans_eq (by ring)
 intro x; change Y x • F x=_; rw [Q,Finset.smul_sum]; exact sum_congr rfl fun i _=>by simp [smul_smul]
end Docket
end Bill
end PureForce.WickLabels
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
