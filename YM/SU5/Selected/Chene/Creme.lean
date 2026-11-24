import YM.Next.RANK.Axial
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
import YM.SU5.Selected.Chene.Crown
/-! The unimodular charts on the topology of actual positive bonds. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Chene.Trunk
open Function Filter Matrix Lattice Tree SectorNext.Vacuum.FlatTree Finset Next.Rank.Axial Pad
open scoped Topology BigOperators Matrix
variable {c f : Side}(g:Ratio c f)
abbrev pillar (n:Side):= {i:Site n//i≠0}
abbrev Reed (n:Side):= Edge (Site n)
-- choose coefficients explicit ±1 only, not the adjoint map V potential
abbrev atKey (k : Site f)(j:pillar f)(T:Type*)[Zero T][One T] : T:= if k=j.val then 1 else 0
def chartZ(T:Type*)[Ring T](p:Site c→Site f) : Matrix (Reed c) (pillar f) T:= of fun i j=> atKey (p i.1) j T-atKey (p (i.1+step i.2)) j T
def press {m:Side}(p:Site c→Site m) := chartZ ℤ p
@[simp] lemma liftPress {m:Side}(p:Site c→Site m): realM (press p)= chartZ ℝ p:=by ext i j; simp [realM,press, chartZ, atKey]
def seed (n:Side){T:Type*}[Zero T] (f:pillar n→ T) (x:Site n):T:=if h:x=0 then 0 else f ⟨x,h⟩
@[simp] lemma seed_at {T:Type*}[Zero T](v:pillar f→ T)(x:pillar f): seed f v x.val = v x:=by unfold seed; rw [dif_neg x.property]
@[simp] lemma seed_zero {T:Type*}[Zero T](v:pillar f→ T): seed f v 0=0:=by unfold seed; rw [dif_pos rfl]
lemma stems {T:Type*}[Ring T](v:pillar f→ T)(x:Site f) : ∑ i, atKey x i T*v i=seed f v x := by
 rcases eq_or_ne x 0 with e|e
 · subst x; rw [seed_zero]; exact sum_eq_zero fun i _=>by rw [atKey,if_neg i.property.symm,zero_mul]
 let q:pillar f:= ⟨x,e⟩; rw [sum_eq_single q,atKey, if_pos rfl, _root_.one_mul]; exact (seed_at v q).symm; intro b _ u; rw [atKey, if_neg (fun y=> u (Subtype.ext y.symm)),zero_mul]; simp
lemma speedZ {T:Type*}[Ring T](p:Site c→Site f)(v:pillar f→T) : chartZ T p *ᵥ v=SectorNext.Vacuum.FlatTree.climb (seed f v∘p):=by funext i; unfold mulVec dotProduct chartZ; simp_rw [Matrix.of_apply,_root_.sub_mul,sum_sub_distrib,stems]; rfl
abbrev sky(n:Side) := press (@id (Site n))
abbrev arena(g:Ratio c f):= stance (sky f) (press g.embed)
theorem arbor_current (T:Finset (Reed f))(p: Arbor (sky f) T) : Arbor (arena g) (T.disjSum ∅):=by
 let f'(x:pillar f→ℤ):= ((sky f).submatrix (Subtype.val:↥T→Reed f) id).mulVec x; let hP(a:↥T): ↥(T.disjSum (∅ : Finset (Reed c))):= ⟨.inl a.val,(Finset.inl_mem_disjSum.mpr a.property)⟩
 constructor; intro x y h; exact p.1 (funext fun i=> congrFun h (hP i)) -- type infer
 intro y; obtain ⟨z,v⟩:=p.2 (y ∘ hP); refine ⟨z,?_⟩; funext ⟨i,q⟩; obtain a|b:=i
 · exact congrFun v ⟨_,(inl_mem_disjSum.mp q)⟩
 simp at q
lemma climb_diff {K:Type*}[AddCommGroup K](v w:Site c→K): climb (v-w)= climb v -climb w:= by funext x; unfold climb; simp; abel
lemma root_home(g:Ratio c f): g.embed 0=0:= by rw [← Ratio.root_embed,_root_.map_zero]
lemma parent_home(g:Ratio c f): g.parent 0=0:=by conv_lhs=>rw [←root_home g,g.embed_parent]
section
variable {g} (F:Forest g)
open SectorNext.Vacuum
lemma trunk_site {K:Type*}[AddCommGroup K](x:Site f→K)(h:∀ i∈ F.trunks,climb x i=0) : ∀ i:Site f,x i=x (g.embed (g.parent i)):=by
 intro i; induction i using Forest.hike.induct F with
 | case1 i hi ih=>
    rw [F.stays _ hi] at ih
    let p(i'):=F.up i'; have he:= h ((F.up i).used i) ((F.trunk_mem_iff _).2 ⟨i,hi,rfl⟩)
    apply Eq.trans ?_ ih
    cases k: F.up i with
    | mk a b=>
        rw [k] at he; unfold climb Step.used at he; cases b
        · exact sub_eq_zero.mp he
        · rw [if_pos rfl] at he; dsimp only at he; rw [sub_add_cancel] at he; change x i=x (i+ -step a); rw [← sub_eq_add_neg]; exact (sub_eq_zero.mp he).symm
 | case2 i hi=> congr; exact Classical.not_not.mp hi
lemma solve_forest {K:Type*}[AddCommGroup K](v:↥F.trunks→K) : ∃ x:Site f→K,(∀ j:Site c,x (g.embed j)=0) ∧ ∀ a:↥F.trunks,climb x a.val=v a:=by
 let y(i: Reed f):= if h:i∈ F.trunks then v ⟨i,h⟩ else 0
 let x:= leafWard F y; refine ⟨-x,fun j=> by change -(x (g.embed j))=0; unfold x; rw [root_clear,neg_zero],?_⟩; intro a; have he1:y a.val=v a:=by unfold y; rw [dif_pos a.property]
 change (- _) - (- _)=_; have he:= trunk_clear F y a.val a.property; change y a.val+(x a.val.1-x _) = 0 at he; have hv:v a= -(x a.val.1-x (a.val.1+step a.val.2)):= he1 ▸ eq_neg_of_add_eq_zero_left he; rw [hv]; abel
end
variable (F:Forest g)
section
lemma allSite {T:Type*}[Zero T](v:Site c→T)(p:v 0=0) : seed c (fun x:pillar c=>v x.val) = v:=by
 funext x; by_cases e:x=0; simp [e,p]; exact seed_at _ (⟨x,e⟩:pillar c)
abbrev down_port (c:Side): Forest (whole c):= axle c
lemma legal (c:Side)(F:Forest (whole c)): Arbor (sky c) F.trunks :=by
 let X:= F.trunks; let P:= sky c
 have he(v:pillar c→ℤ):P.mulVec v=climb (seed c v):=speedZ _ _
 constructor
 · intro a b p; let K:=seed c a - seed c b; have hp:∀ i∈ F.trunks,climb K i=0:=by
      intro i t; rw [climb_diff,←he,←he,Pi.sub_apply]; exact sub_eq_zero.mpr (congrFun p ⟨_,t⟩)
   funext i; refine sub_eq_zero.mp (show a i-b i=0 from ?_); let j:Site (1:Side):=0; have hr(i:Site (1:Side)): i=j:=by exact funext (fun k=> Subsingleton.elim (α:=ZMod 1) _ _)
   have ht:= trunk_site F _ hp i.val; rw [hr ((whole c).parent i.val), root_home (whole c)] at ht; simpa [K] using ht
 intro a; obtain ⟨x,p,f⟩:= solve_forest F a; let y(i:pillar c):= x i.val; have hh:x 0=0:= root_home (whole c) ▸ p 0
 refine ⟨y,funext fun i=>?_⟩; change (P *ᵥ y) i.val= _; rw [he,allSite _ hh]; apply f
lemma effort (S:Finset (Reed c))(x:Arbor (sky c) S)(v:Site c→ℤ)(p:v 0=0)(h:∀a∈S,climb v a=0) : v=0:=by
 let f(i:pillar c):=v i.val; have hv:seed c f=v:=allSite _ p; let P:=sky c; have hw : P*ᵥ f=climb v:= by rw [show P=chartZ ℤ (@id (Site c)) from rfl,speedZ,hv]; rfl
 have he:f=(0: pillar c→ℤ):=x.1 (funext fun i=>by rw [Matrix.mulVec_zero]; change (P*ᵥf) i.val=0; rw [hw,h i.val i.property]); rw [←hv,he]; funext i; unfold seed; split <;> rfl
lemma buildup (S:Finset (Reed c))(x: Arbor (sky c) S) : Arbor (arena g) (F.trunks.disjSum S):=by
 let P:= sky f; let I:= F.trunks; let B:= I.disjSum S; let N:=arena g; let Q:= sky c; let G:= press g.embed
 have hx(v:pillar f→ℤ):P*ᵥv=climb (seed f v):=speedZ _ _; -- this line have2?
 have ha(v:pillar f→ℤ)(j:Reed f):(N*ᵥ v) (.inl j) = climb (seed f v) j:=congrFun (hx v) j
 have hb(v:pillar f→ℤ)(j:Reed c):(N*ᵥ v) (.inr j) = climb (seed f v ∘ g.embed) j:=congrFun (speedZ _ v) j
 constructor
 · intro a b e; let f'(i:Site f):= seed f a i-seed f b i; have he: f' 0=0:=by simp [f']
   have hu: f' ∘ g.embed=0:=by
      apply effort S x _ (by simpa only [Function.comp_apply, root_home] using he); intro i v; change climb (((seed f a) ∘g.embed)- ((seed f b) ∘g.embed)) _=_; rw [climb_diff,Pi.sub_apply,← hb,←hb]; exact sub_eq_zero.mpr (congrFun e ⟨_,inr_mem_disjSum.mpr v⟩)
   have hg(i:Site f): f' i=0:=by
      have hw(i): f' (g.embed i)=0:=congrFun hu i
      apply (trunk_site F f' (fun i v=> ?_) _).trans (hw _)
      change climb (seed f a-seed f b) _=0; rw [climb_diff, Pi.sub_apply,← ha,←ha]; exact sub_eq_zero.mpr (congrFun e ⟨_,inl_mem_disjSum.mpr v⟩)
   funext i; have he:=hg i.val; simpa [f',sub_eq_zero] using he
 intro c'; let A(j:↥F.trunks):= c' ⟨Sum.inl j.val,inl_mem_disjSum.mpr j.property⟩; let D(j:↥S):= c' ⟨Sum.inr j.val,inr_mem_disjSum.mpr j.property⟩
 obtain ⟨y,hp,hQ⟩:= solve_forest F A; obtain ⟨z,hz⟩:= x.2 D
 let W:=seed c z
 let v:= y+ W∘g.parent
 have hv: v 0=0:=by unfold v; rw [Pi.add_apply,Function.comp_apply,parent_home]; have hx:y 0=0:= root_home g ▸ hp 0; rw [hx,show W 0=0 from seed_zero _,add_zero]
 let L:= fun i:pillar f=> v i.val; have ht:seed f L=v:= allSite _ hv
 refine ⟨L,?_⟩; funext ⟨i,h⟩; obtain i|i:=i
 · have hk:i∈ F.trunks:=inl_mem_disjSum.mp h
   change (N*ᵥ L) (Sum.inl _)=A ⟨i,hk⟩; rw [ha,← hQ]; rw [ht]; unfold v climb; simp only [Pi.add_apply, Function.comp_apply,F.trunk_internal hk]; abel -- tutor
 change (N*ᵥL) (Sum.inr i)=D ⟨i,inr_mem_disjSum.mp h⟩; rw [hb, ht, show v ∘ g.embed=W from (by funext i; unfold v; simp only [Function.comp_apply,Pi.add_apply,hp,g.embed_parent,zero_add])]; rw [show climb W=Q*ᵥz from (speedZ id z).symm]; exact congrFun hz ⟨i,inr_mem_disjSum.mp h⟩
end
end YM.Chene.Trunk
#print axioms YM.Chene.Trunk.legal
#print axioms YM.Chene.Trunk.buildup
