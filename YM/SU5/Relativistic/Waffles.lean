import YM.SU5.Relativistic.Kholt
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Lifted Pea Omelet
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {X:Type*}[LinearOrder X][Fintype X][Nonempty X]{B:Op X}
def ease (b:Bool)(P:Op X):= if b then P else 1-P
def comfy(S:Finset X)(b:Bool)(P:Op X)(K:Ket X)(k:ℝ):Prop:= ‖acts (1-cutM S) (acts (ease b P) K)‖≤k
private lemma lens_met (p:IsStarProjection B)(x:Ket X):‖acts B x‖≤‖x‖:=(opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
private lemma markerP(b:Bool)(p:IsStarProjection B):IsStarProjection (ease b B):=by cases b; exact p.one_sub; exact p
private lemma refund(b:Bool)(p:IsStarProjection B):repay B b =1-ease b B:=by
 cases b; · change _=1-(1-B); rw [sub_sub_cancel]; rfl
 rfl
lemma honors (L:List Bite)(k:ℝ)(p:0<k) (ε:ℝ)(t:0<ε): ∃ δ> (0:ℝ),∀ {n:Side} {P:Op (Single n)}{W:Finset (Single n)}(b:IsStarProjection P)(Y:Bite→Ket (Single n)), (∀ i∈ L,‖Y i‖≤k)→ (∀ i∈L,∀ u:Bool,comfy W u P (Y i) δ) →∃ A:Pea (Single n),Shell A W ∧ A.leak P≤ε∧∀ i∈L, met A (Y i) ε:=by
 let G:=L ×ˢ [true,false]; let a:=ε/4; have hx:0<a:= by unfold a; positivity
 obtain ⟨δ,u,H⟩:= theca k G.length p a hx
 refine ⟨min δ a,lt_min u hx,?_⟩; intro n P W b Y hk c
 let Q:=cutM W; let X(i:Bite)(x:Bool):=acts (ease x P) (Y i); let T (i:Bite)(x:Bool):= acts Q (X i x)
 let G'(q:Bite × Bool):= (q.2,T q.1 q.2)
 have q(i: Bite)(h:i∈L)(x:Bool): ‖X i x-T i x‖ ≤ min δ a:=by rw [show X i x-T i x=acts (1-Q) (X i x) from (by rw [act_sub,act_one])]; exact c i h x
 have he: spoken W (G.map G') P k δ:=by
    intro i p; obtain ⟨⟨j,d⟩,v,rfl⟩:= List.mem_map.mp p; obtain ⟨h,t⟩:= List.mem_product.mp v; let K:=X j d
    have hd: acts (repay P d) K=0:=by unfold K X; rw [←act_mul, refund d b,show (1-ease d P)*ease d P=0 from by rw [sub_mul,one_mul,(markerP d b).isIdempotentElem.eq,sub_self],act_zero]
    let T':= T j d
    have hs: ‖acts (repay P d) T'‖≤δ:=by rw [show acts (repay P d) T'=acts (repay P d) (T'-K) from (by rw [map_sub,hd,sub_zero])]; apply (lens_met (show IsStarProjection (repay P d) from (by rw [refund d b]; exact (markerP d b).one_sub)) _).trans; rw [norm_sub_rev]; exact (q _ h d).trans (min_le_left ..)
    refine ⟨hs,?_ ,(lens_met (cutM_idp _) _).trans ((lens_met (markerP d b) _).trans (hk _ h))⟩; change acts Q (acts Q K)= _; rw [←act_mul,(cutM_idp W).isIdempotentElem.eq]
 obtain ⟨A,hp,r,v⟩:= H b _ (List.length_map ..) he; let P':= 1-A.robe; refine ⟨A,hp,r.2.2.trans (show a≤ε by unfold a; linarith),fun i t=>?_⟩
 have hz(d): ‖acts P' (X i d)‖≤a+a:=by
    have he: (i,d)∈ G:=List.mem_product.mpr ⟨t,by cases d<;> simp⟩
    rw [show acts P' (X i d)=acts P' (X i d-T i d)+acts P' (T i d) from (by rw [map_sub,sub_add_cancel])]; apply (norm_add_le ..).trans; exact add_le_add ((lens_met A.robe_p.one_sub _).trans ((q i t d).trans (min_le_right ..))) (v (G' (i,d)) (List.mem_map.mpr ⟨_,he,rfl⟩))
 unfold met; rw [show Y i=X i true+X i false from (by change Y i=acts P (Y i)+acts (1-P) (Y i); rw [←act_add, add_sub_cancel,act_one]),map_add]; apply (norm_add_le ..).trans; exact ((add_le_add (hz true) (hz false)).trans_eq (by unfold a; ring))
end YM.CF.Papyrus.Franc.Loaves
