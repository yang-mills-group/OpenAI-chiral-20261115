import YM.CF.Fixed.Pivots
/-! # global gauge free determinant work. Flux pins. `N≥2`.
Tree coboundaries and cycle basis over ANY abelian group. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots
open scoped BigOperators
variable {N: Side} {G:Type*}[AddCommGroup G]
abbrev Vtx (N:Side) := Site N
abbrev Bond (N:Side) := Fixed.Pivots.Link N
def Curl (F:Bond N→G)(p:Face (Per N)) := F (p.1,p.2.val.1)+F (p.1+step p.2.val.1,p.2.val.2) - (F (p.1+step p.2.val.2,p.2.val.1)+F (p.1,p.2.val.2))
def Closed (F:Bond N→G):Prop := ∀ p,Curl F p=0

def extra (t:Axis→G)(e: Bond N):G:= if (e.1 e.2).val+1=N.val then t e.2 else 0

def differ (v:Vtx N→G)(e:Bond N):G := v (reach e)-v e.1
def Fl (v : Vtx N→G)(t:Axis→G) (e:Bond N):G:= differ v e+extra t e
lemma diff_closed(v:Vtx N→G):Closed (differ v):= by
 rintro ⟨x,⟨⟨i,j⟩,e⟩⟩; simp only [Curl,differ,reach,add_right_comm x (step j) (step i)]; abel
lemma flux_cross (t:Axis→G)(x:Site N)(i j:Axis)(v:i≠j):extra t (x+step i,j)=extra t (x,j):=by simp [extra,v.symm]
lemma fl_closed (v: Vtx N→G)(t:Axis→G):Closed (Fl v t):=by
 rintro ⟨x,⟨⟨i,j⟩,e⟩⟩; have he:= diff_closed v (x, ⟨(i,j),e⟩)
 simp only [Curl,Fl,flux_cross t x i j (ne_of_lt e),flux_cross t x j i (ne_of_gt e),show ∀ a b c d e f g h:G,a+b+(c+d)-(e+f+(g+h))=a+c-(e+g)+(b+d-(f+h)) from fun a b c d e f g h=>by abel]; rw [show differ v (x,i)+differ v (x+step i,j)-(differ v (x+step j,i)+differ v (x,j))=0 from he]; abel
-- pivots triangular.Implicates Closed rank. Need distinct sheet.
lemma unique(p:2 ≤ N.val){X Y:Bond N→G} (x:Closed X)(y:Closed Y)(h:∀ i, ¬Fixed.Pivots.Active i→ X i=Y i):X=Y:=by
 suffices w:∀ k:ℕ,∀ i:Bond N,originSum i.1=k→ X i=Y i by exact funext fun i=> w _ _ rfl
 intro k; induction k using Nat.strong_induction_on with
 | h k ih =>
  rintro ⟨x',i⟩ s
  by_cases e:Fixed.Pivots.Active (x',i); swap; · exact h _ e
  let A:=mark (x',i) e; let ω:= support A
  have hf(a:Bond N)(g:a∈ω)(t:a≠(x',i)):X a=Y a:=by
   by_cases hV:Fixed.Pivots.Active a; · exact ih _ (s ▸ behind _ e a hV g t) _ rfl -- s rewrite motive
   exact h a hV
  let z:= tooth (x',i) e; let u:= x'-step z
  have he:z ≠ i:=(tooth_spec _ e).1; have hp':u+step z=x':=sub_add_cancel ..
  have hx:1 ≠ (0:Per N):=by
    intro g; have hev := congrArg ZMod.val g; rw [ZMod.val_one_eq_one_mod, ZMod.val_zero,Nat.mod_eq_of_lt (by omega)] at hev; simp at hev -- perp
  have hv:u ≠ x':= fun g=> hx (by
    have he': u+step z=u:=hp'.trans g.symm
    have hh := congrFun he' z; simpa using hh) -- cancel
  have hg:ω=window u i z:= mark_window x' i e
  have hK:= hf (u,i) (by rw [hg]; simp [window]) (fun g=>hv (congrArg Prod.fst g)); have hr:=hf (u+step i,z) (by rw [hg]; simp [window]) (fun g=> he (congrArg Prod.snd g)); have hl:= hf (u,z) (by rw [hg]; simp [window]) (fun g=> he (congrArg Prod.snd g))
  have hy':= y A; have hx':= x A; change Curl X (u, ⟨(min i z,max i z),_⟩)=0 at hx'; change Curl Y (u,⟨(min i z,max i z),_⟩)=0 at hy'
  unfold Curl at hx' hy'; dsimp only at hx' hy'
  rcases le_total i z with l|l
  · rw [min_eq_left l,max_eq_right l, hp',hK,hr,hl] at hx'; rw [min_eq_left l,max_eq_right l,hp'] at hy'
    exact add_right_cancel ((sub_eq_zero.mp hx').symm.trans (sub_eq_zero.mp hy'))
  rw [min_eq_right l,max_eq_left l,hp',hK,hr,hl] at hx'; rw [min_eq_right l,max_eq_left l,hp'] at hy'
  exact add_left_cancel ((sub_eq_zero.mp hx').trans (sub_eq_zero.mp hy').symm)
-- tree interpolation.T equals bond lifts. Zero-tree coords.
def along (F: Bond N→G)(x:Vtx N):G := if p:x=0 then 0 else along F (parentLink x p).1+F (parentLink x p)
termination_by originSum x
decreasing_by exact Nat.lt_of_succ_le (reduced x (gapAxis x p) (gapAxis_nonzero _ _)).le
lemma match_tree(F:Bond N→G)(x:Bond N)(hx: Tree x) (t:Axis→G):Fl (along F) t x=F x:=by
 unfold Fl differ extra; rw [along,dif_neg (reach_tree x hx),tree_reduces x hx, if_neg hx.1.ne]; abel
private def cutEnd (i:Axis): Bond N := (- (step i),i)
private lemma neg_wind : (- (1:Per N)).val+1=N.val:=by
 obtain ⟨_|k,h⟩:=N; · simp at h
 change (- (1:ZMod (k+1))).val+1=k+1; rw [ZMod.val_neg_one]
lemma canon (x:Bond N)(p:Gen x) : x=cutEnd x.2:=by
 refine Prod.ext ?_ rfl; funext j; apply ZMod.val_injective
 obtain g|g:= eq_or_ne j x.2
 · subst j; unfold cutEnd; simp only [Pi.neg_apply,step_apply,ite_true,↓reduceIte]
   exact Nat.add_right_cancel (p.1.trans neg_wind.symm)
 simp [cutEnd,p.2 j g,g] -- neg zero
lemma cut_part (N:Side)(i:Axis): Gen (cutEnd (N:=N) i):=by
 refine ⟨?_,fun j p=>?_⟩; unfold cutEnd; simpa using (neg_wind (N:=N) : _)
 change j≠i at p; simp [cutEnd,p]
-- interpolation & splitting all. TRUE decomposition, integral lattice.
def weightPins (F:Bond N→G)(i:Axis):G:=F (cutEnd i)-differ (along F) (cutEnd i)
lemma pin_answer (F:Bond N→G) (a:Bond N)(h:¬ Fixed.Pivots.Active a):Fl (along F) (weightPins F) a=F a:=by
 by_cases t:Tree a; · exact match_tree _ _ t _ -- tune
 have hp:Gen a:=by by_contra v; exact h ⟨t,v⟩
 unfold Fl extra; rw [if_pos hp.1]; unfold weightPins; rw [←canon a hp]; abel
lemma closed_as (p:2 ≤N.val)(F:Bond N→G)(h:Closed F): F=Fl (along F) (weightPins F):=unique p h (fl_closed _ _) fun i v=>(pin_answer F _ v).symm
lemma weight_defined (t:Site N→G)(v: Axis→G) : weightPins (Fl t v)=v:=by
 let F:=Fl t v; have ht:(along F) = fun x=> t x-t 0:= by
    suffices h:∀ k:ℕ,∀ x:Site N, originSum x=k→ along F x=t x-t 0 by exact funext fun i=> h _ _ rfl
    intro k; induction k using Nat.strong_induction_on with
    | h k ih=>
       intro i hi; rw [along]; split
       · next he => rw [he,sub_self]
       next he =>
         let y:=parentLink i he; have he':Tree y:=tree_is i he
         change along F y.1+F y=_; rw [ih _ (slt i he k hi) _ rfl]; unfold F Fl extra differ; rw [if_neg he'.1.ne,show reach y=i from origin_child ..]; abel
 funext i; let x:=cutEnd (N:=N) i; change F x-differ (along F) x=v i; rw [ht]; change t (reach x)-t x.1+extra v x-( (t (reach x)-t 0)-(t x.1-t 0))=v i; rw [show extra v x=v i by unfold extra; exact if_pos (cut_part N i).1]; abel
where
 slt (x:Site N)(p:x≠0)(k:ℕ)(h:originSum x=k): originSum (parentLink x p).1 < k:= h ▸ Nat.lt_of_succ_le (reduced x (gapAxis x p) (gapAxis_nonzero _ _)).le
lemma diff_same {v w: Site N→G}(h:differ v=differ w) (e: v 0=w 0): v=w:= by
 suffices p:∀ k:ℕ,∀ i:Site N,originSum i=k → v i=w i by exact funext fun i=> p _ _ rfl
 intro k; induction k using Nat.strong_induction_on with
 | h k ih=>
    intro i p; by_cases hx : i=0; · rw [hx,e]
    let x:=parentLink i hx; have he:=congrFun h x; unfold differ at he; rw [show reach x=i from origin_child .., show v x.1=w x.1 from ih (originSum x.1) (p ▸ Nat.lt_of_succ_le (reduced i (gapAxis i hx) (gapAxis_nonzero i hx)).le) _ rfl] at he; exact sub_left_inj.mp he
end YM.CF.Papyrus.GaugeFlux
#print axioms YM.CF.Papyrus.GaugeFlux.weight_defined
