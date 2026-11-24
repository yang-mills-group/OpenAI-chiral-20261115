import YM.CF.Vp929.Roof.Paper
import YM.CF.Skye.Pine
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Guide MeasureTheory Palace Mos Mesa Cube Lat Skye Read Cane Spire Scroll Laurent Paper
open scoped Topology Classical NNReal Matrix.Norms.Frobenius
variable (C:Side)(K:ℕ→ℝ)(n:Side)(p:2*(spanR* Bolt C)<(More n).val)
variable (r:ℕ)(u d:ℝ)
namespace Braid

variable {I:Type*}(Q:I→Pane n→Pane n)(samp:Finset (Seat n)→ℝ→I)
variable (h:∀ i,Basic n (Q i) u d r)(sw:∀ (S:Finset (Seat n))(t:Sweep n),samp (S.map (boxA t).symm.toEmbedding)=samp S)
def sprout (S:Finset (Seat n))(a:Ids n)(V:Pane n): Pane n:=
 let x:=a (greet S (priorP a)); mend (Q (samp S x.1)) x.2.1 V
def join (M:Finset (Seat n))(a:Ids n)(V:Pane n):Pane n:= fun i=> if (soup M r i).Nonempty then sprout n Q samp (soup M r i) a V i else V i
def story(V:Pane n)(a:Ids n): Pane n:= join n r Q samp (RG.flags u V) a V
def spring (x:Orbit n):Pane n:= gauge (frameP x.2)⁻¹ (story n r u Q samp (gauge (frameP x.2) x.1) x.2)
local notation "P"=>story n r u Q samp
local notation "P'"=>spring n r u Q samp
local notation "S"=> sprout n Q samp
include sw
lemma sway(t:Sweep n)(V:Pane n)(a:Ids n)(p:Injective (priorP a)) : story n r u Q samp (flashA t V) (bun t a)=flashA t (story n r u Q samp V a):=by
 funext e; rw [Skye.flash]; let M:=soup (RG.flags u V) r (lane t e); let M':= M.map (boxA t).symm.toEmbedding; unfold story join; rw [flagsA,soupS]; change (if M'.Nonempty then _ else _)= polarT _ (if _ then ((if M.Nonempty then _ else _))⁻¹ else (if M.Nonempty then _ else _)); by_cases h:M.Nonempty; swap; · rw [if_neg (mt map_nonempty.mp h), if_neg h] ; exact flash t V e
 rw [if_pos (map_nonempty.mpr h),if_pos h]; have hu: bun t a (greet M' (priorP (bun t a)))=man t (a (greet M (priorP a))):= congrArg (fun y=>man t (a y)) (mast_rev _ t r (lane t e) a h p)
 unfold sprout; rw [hu]; change mend (Q (samp M' (a _).1)) (t⁻¹*_) _ _=_; rw [sw M t, mends, flash]
lemma springV(V:Pane n)(a:Ids n)(s:Sweep n)(p:Injective (priorP a)): P' (flashA s V,bun s a)=flashA s (P' (V,a)):=by
 unfold spring; simp only [boong,sway n r u Q samp sw s _ a p]; rw [Skye.revG]; congr 2; funext i; unfold frameP; simp only [bun,man,Pi.inv_apply,map_inv]
omit sw
lemma springG(g:Seat n→SU.E)(V:Pane n)(a:Ids n):P' (gauge g V,threadG g a)=gauge g (P' (V,a)):=by
 unfold spring; have h:frameP (threadG g a)=frameP a*g⁻¹:= rfl; have z(V:Pane n):P V (threadG g a)=P V a := rfl
 simp only [h,_root_.mul_inv_rev,inv_inv, Skye.gauge_sq, z,_root_.inv_mul_cancel_right, mul_inv_cancel_right]
lemma springLamp (V: Pane n)(a:Ids n)(i:reach n)(h:Disjoint (RG.flags u V) (win r i)): P' (V,a) i= V i:=by
 have hv:P (gauge (frameP a) V) a i=gauge (frameP a) V i:=by unfold story join; rw [if_neg]; rw [RG.gauge_flags]; exact fun v=> ((pieV ..).mp v) h
 unfold spring Lattice.gauge; simp only; change _* P (gauge (frameP a) V) a i *_=_; rw [hv]; exact congrFun (noon ..) _
include h
lemma paysV [Nonempty I](V:Pane n)(τ:Ids n): RG.flags d (P V τ)=∅:=by
 apply Skye.broad; intro i; let M:= RG.flags u V; let A:= RG.touched i
 obtain ⟨T,H⟩:∃ T:Pane n,RG.flags d T=∅∧Agrees A (P V τ) T:= by
    by_cases g:∃ e:reach n,ends e⊆A∧(soup M r e).Nonempty; swap
    · let k:= Classical.arbitrary I; refine ⟨Q k V,(h k).legal _,fun e p₁ p₂=>?_⟩; have hx: ¬ (soup M r e).Nonempty:= fun v=> g ⟨_,insert_subset_iff.mpr ⟨p₁,singleton_subset_iff.mpr p₂⟩,v⟩; change (if (soup M r e).Nonempty then _ else _)=_; rw [if_neg hx,(h k).covers _ _ (of_not_not fun u=>hx ((pieV ..).mpr u))]
    obtain ⟨e,t,p⟩:=g; let s' : Pane n→Pane n:= S (soup M r e) τ; have y:Basic n s' u d r:= mine (h (samp _ _)) _; refine ⟨s' V,y.legal _,fun a v w=>?_⟩; have hp:ends a⊆ A:= insert_subset_iff.mpr ⟨v,singleton_subset_iff.mpr w⟩; change (if _ then S (soup M r a) _ _ _ else _) = _; split; swap; next l=>exact (y.covers _ _ (of_not_not fun u=>l ((pieV ..).mpr u))).symm
    next U=>
     have hg(y:Seat n)(hy:y∈A)(x:Seat n)(hx:x∈ A):separation x y ≤ 20:=by have ht:=Work.E01.sep_touched i x hx; have hp:=Work.E01.sep_touched i y hy; have hv:=separation_triangle x i.1 y; rw [separation_comm x i.1] at hv; omega
     rw [Finset.Subset.antisymm (dives p (fun i x j y=> hg j (t y) i (hp x))) (dives U (fun i x j y=>hg j (hp y) i (t x)))]
 by_contra! k; apply absurd (show i.1 ∈ RG.flags d T from (RG.flags_spec d T i.1).mpr ⟨i,by simp [A,RG.touched,square,visits], ?_⟩) (by simp [H.1])
 rw [show faceValue T i=faceValue (P V τ) i from Eq.symm (travel_local _ _ _ _ (fun e t x=> H.2 e (List.mem_toFinset.mpr t) (List.mem_toFinset.mpr x)))]; exact k
lemma transmis (V W:Pane n)(t z:Ids n)(X L:Support (More n))(p:X∩ RG.flags u V=X∩RG.flags u W)(f: Week X L (RG.flags u V) r)(g: Week X L (RG.flags u W) r)(k:Agrees X V W)(m:Set.EqOn t z X): Agrees L (P' (V,t)) (P' (W,z)):=by
 intro i vi wi; let A:=gauge (frameP t) V; let B:=gauge (frameP z) W; let D:=RG.flags u V; let J:=RG.flags u W; have hx:Agrees X A B:=tied _ _ _ _ _ k (fun i v=>by simp only [frameP,m v]); have ht:ends i⊆L:=insert_subset_iff.mpr ⟨vi,singleton_subset_iff.mpr wi⟩; have hp:ends i⊆ X:=Subset.trans (halo_subset r _) (f.all i ht)
 have hl:soup D r i=soup J r i:= Skye.suppC D J _ _ _ (by rw [inter_comm, inter_comm J]; exact p) (f.all _ ht) (f.mask _ ht) (g.mask _ ht)
 have hy : P A t i=P B z i:=by
    have he:RG.flags u A = D := RG.gauge_flags ..; have hv:RG.flags u B=J:=RG.gauge_flags ..; unfold story join; rw [he,hv,hl]; by_cases q:(soup J r i).Nonempty; swap; · rw [if_neg q,if_neg q]; exact hx i (hp (by simp)) (hp (by simp))
    have ht'(x)(e:x∈soup J r i):x∈X:= g.mask i ht _ e (halo_subset _ _ (mem_singleton_self x)); rw [if_pos q,if_pos q]; unfold sprout; rw [mastL _ _ (priorP z) (fun x v=>congrArg Prod.fst (m (ht' x v))),m (ht' _ (mastP _ q _).1),(mine (h _) _).shore A B i (agrees_mono hx (f.all _ ht))]
 unfold spring Lattice.gauge; simp only [show ∀ i,(frameP t)⁻¹ i=(t i).2.2⁻¹ from fun _=>rfl,show ∀ i,(frameP z)⁻¹ i=(z i).2.2⁻¹ from fun _=>rfl]; rw [m (show i.1∈↑X from hp (by simp)),m (show i.1+step i.2∈↑X from hp (by simp))]; exact congrArg (fun v=>_*v*_) hy
end Braid
end YM.CF.VolumeCape
