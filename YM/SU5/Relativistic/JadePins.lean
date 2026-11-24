import YM.SU5.Relativistic.CoarseLight
import YM.SU5.Relativistic.Compressions
/-! # Integer volumes; forests. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter Lattice Wilson
open RG Precision Exterior MinorPins Tree
open scoped Matrix BigOperators
variable {N:Side}{C:Side}(S:StepData C N){J:Type}[Fintype J][DecidableEq J]
open Fixed.Pivots
-- design rectangular atlas supports later

def closedC (J:Type)[Fintype J](N:Side):Submodule ℝ ((Bond N × J)→ℝ) where
 carrier := {x|∀ i, Closed (fun a=>x (a,i)) }
 zero_mem':=fun i p=>by simp [Curl]
 add_mem':= by intro f g h t i a; rw [show Curl (fun b => (f+g) (b,i)) a=Curl (fun b=>f (b,i)) a+Curl (fun b=>g (b,i)) a by unfold Curl; simp only [Pi.add_apply]; ring,h i,t i,add_zero] -- tune
 smul_mem':=by intro c f h i a; change Curl (fun p=> c • f (p,i)) a=0; unfold Curl; rw [← smul_add,← smul_add, ←smul_sub,(show f (_,i)+f (_,i)-(f (_,i)+f (_,i))= 0 from h i a),smul_zero] -- tune

def interior (J:Type)[Fintype J][DecidableEq J](N:Side):= pivots N ×ˢ (univ:Finset J)
private lemma integerFl (t:Site N→ℤ)(v:Axis→ℤ)(i:Bond N) : Fl (fun a=>(t a:ℝ)) (fun i=>(v i:ℝ)) i=(Fl t v i:ℤ):=by unfold Fl differ extra; split <;>push_cast<;>rfl
lemma pivSlit {G:Type*}[AddCommGroup G](F:Bond N→G)(i:Bond N)(h:i∉pivots N): Fl (along F) (weightPins F) i=F i:= pin_answer F i (fun t=> h (mem_filter.mpr ⟨mem_univ _,t⟩))
-- adapt avoid empty J. ext Data
lemma grates (N:Side)(e:2≤N.val) : Grates (interior J N) (closedC J N):=by
 let A:=interior J N
 have h(p:Bond N×J):p∈ Aᶜ↔ p.1∉pivots N:=by simp [A,interior]
 let U{G:Type}[AddCommGroup G](x:↥(Aᶜ)→G)(j:J)(i:Bond N):G:=if hx:(i,j)∈ Aᶜ then x ⟨_,hx⟩ else 0
 have hp{G:Type}[AddCommGroup G](p:↥(Aᶜ))(x:↥(Aᶜ)→G): Fl (along (U x p.val.2)) (weightPins (U x p.val.2)) p.val.1=x p:= (pivSlit (U x p.val.2) p.val.1 ((h _).mp p.property)).trans (by obtain ⟨i,t⟩:=p; unfold U; simp [t])
 constructor
 · intro F k w; funext i; obtain ⟨p,j⟩:=i; exact congrFun (unique e (k j) (show Closed (0:Bond N→ℝ) from fun i=>by simp [Curl]) (fun i t=>congrFun w ⟨(i,j),(h _).mpr (fun x=>t (mem_filter.mp x).2)⟩)) p
 · intro x; let f(i:Bond N×J):= Fl (along (U x i.2)) (weightPins (U x i.2)) i.1; exact ⟨f,fun i=> fl_closed (along (U x i)) (weightPins (U x i)),funext fun i=>hp i x⟩
 intro f p; choose j hj using p; let l i:=U j i; let g(i:Bond N × J):= Fl (fun a : Site N=>((along (l i.2) a : ℤ):ℝ)) (fun a : Axis=> ((weightPins (l i.2) a:ℤ):ℝ)) i.1
 refine ⟨g,fun i=> fl_closed (fun a =>((along (l i) a:ℤ):ℝ)) (fun a=> ((weightPins (l i) a:ℤ):ℝ)),fun i=>⟨_,integerFl _ _ _⟩,funext fun i=> ?_⟩
 change g i=f i; rw [hj,show g i = _ from integerFl _ _ _]; exact congrArg _ (hp i j) -- tune

-- arbitrary pins without transport when all fine anchors blocked
abbrev Twin (N C:Side)(J:Type) := (Bond N × J) ⊕ (Bond C × J)
def probePair (S:StepData C N)(J:Type)[Fintype J]:Submodule ℝ (Twin N C J→ℝ) where
 carrier:={x | (x∘Sum.inl) ∈ closedC J N ∧ ∀ i x',x (Sum.inr (x',i))=pressB S (fun p=>x (Sum.inl (p,i))) x'}
 zero_mem':= ⟨(closedC J N).zero_mem,fun i a=>by change (0:ℝ)=pressB S 0 _; rw [map_zero]; rfl⟩
 add_mem':= fun {x y} p t=> by
    refine ⟨(closedC J N).add_mem p.1 t.1,fun i a=> ?_⟩; change x _+y _=pressB S ((fun p=>x (Sum.inl (p,i)))+fun p=>y (Sum.inl (p,i))) a; rw [p.2,t.2,map_add]; rfl
 smul_mem':= fun α x h=> by refine ⟨(closedC J N).smul_mem α h.1,fun i a=> ?_⟩; change α • x _=pressB S (α • (fun p=> x (Sum.inl (p,i)))) a; rw [h.2,map_smul]; rfl

variable (F:Forest S.ratio)
def newJoint:= (interior J N).disjSum (univ:Finset (Bond C × J))
def oldJoint:= (F.trunksᶜ ×ˢ (univ:Finset J)).disjSum (interior J C)

-- ribbon chart graph. lifting real/int. h uses trunk orientation.
private def rider {G:Type}[AddCommGroup G](U:Site N→(J→G))(v:Axis→J→G):Twin N C J→G:=Sum.elim (fun p=>Fl U v p.1 p.2) (fun p=> Fl (U∘ S.ratio.embed) v p.1 p.2)
private lemma packX {G:Type}[AddCommGroup G](U:Site N→(J→G))(v: Axis→J→G)(a: J) : (fun p:Bond N=> Fl U v p a)= Fl (fun i=>U i a) (fun i=>v i a):=by funext p; unfold Fl differ extra; split<;>rfl
private lemma riddled (U:Site N→(J→ℝ))(v:Axis→J→ℝ):rider S U v∈probePair S J:=by
 refine ⟨fun i=>?_,fun i a=>?_⟩; change Closed (fun p=> Fl U v p i); rw [packX]; exact fl_closed _ _
 change Fl (U∘ S.ratio.embed) v a i=pressB S (fun p=> Fl U v p i) a; rw [packX,fl_block]; exact congrFun (packX (U ∘ S.ratio.embed) v i) _
private lemma yr (U:Site N→J→ℤ)(v: Axis→J→ℤ)(i) : rider S (fun a j=>(U a j:ℝ)) (fun a j=>(v a j:ℝ)) i=(rider S U v i:ℤ):=by cases i<;> unfold rider<;> simp only [Sum.elim_inl,Sum.elim_inr]<;> unfold Fl differ extra<;> split <;> simp [Function.comp_def]
-- fine-pins chart
lemma nowpins (p:2≤ N.val):Grates (newJoint (J:=J)) (probePair S J):=by
 let A:=newJoint (J:=J) (C:=C) (N:=N); let B:= interior J N
 have h(i:Twin N C J) : i∈ Aᶜ → ∃ a:↥(Bᶜ), i= Sum.inl a.val:= by
    cases i with
    | inl i=> intro p; exact ⟨⟨i,by simpa [B,A,newJoint] using p⟩,rfl⟩ -- tune
    | inr i=> simp [A,newJoint]
 have hx(j:J)(i:Bond N): Sum.inl (i,j)∈ Aᶜ↔ i∉ pivots N:=by simp [A,newJoint,interior]
 have hp{G:Type}[AddCommGroup G](x:↥(Aᶜ)→G):∃ (U:Site N→ J→G) (v:Axis→J→G),hide A (rider S U v)=x:=by
    let F(i:Bond N)(j:J) := if t:Sum.inl (i,j)∈ Aᶜ then x ⟨Sum.inl (i,j),t⟩ else 0
    refine ⟨along F,weightPins F,funext fun i=>?_⟩
    obtain ⟨a,r⟩:= i; obtain ⟨⟨⟨l,j⟩,v⟩,rfl⟩:= h a r
    change Fl (along F) (weightPins F) l j =_
    rw [pivSlit F l ((hx _ _).mp r)]; unfold F; rw [dif_pos r]
 constructor
 · intro x u y; obtain ⟨g,z⟩:= u; let L:= x ∘ Sum.inl; have he:L=0:=(grates N p).fade L g (funext fun i=>congrFun y ⟨Sum.inl i.val,(hx i.val.2 i.val.1).mpr (fun p=>(mem_compl.mp i.property) (mem_product.mpr ⟨p,mem_univ _⟩))⟩)
   funext i; cases i with
   | inl i=> exact congrFun he _
   | inr i=> change _=0; rw [show x (Sum.inr i)=_ from z i.2 i.1, show (fun p=> x (Sum.inl (p,i.2))) = 0 from funext fun p=>congrFun he (p,i.2), map_zero]; rfl
 · intro f; obtain ⟨U,v,x⟩:= hp f; exact ⟨_,riddled S U v,x⟩
 intro f p; choose F h using p; obtain ⟨U,v,x⟩:=hp F
 refine ⟨_,riddled S (fun a j=>(U a j:ℝ)) (fun a j=>(v a j:ℝ)),fun i=>⟨_,yr S U v i⟩,funext fun i=>?_⟩
 unfold hide; rw [h,yr]; exact congrArg _ (congrFun x i)

-- lift potential matching coarse pins and trunks
variable {G:Type}[AddCommGroup G]
def cur {N:Side} (f:Bond N→G)(x: Site N)(s:Step):G:= if s.neg then -f (s.used x) else f (s.used x)
private def peel(U:Site C→G)(q:Bond N→G)(x:Site N):G:= if h: Tree.leaf S.ratio x then peel U q (x+(F.up x).vec)-cur q x (F.up x) else U (S.ratio.parent x)
termination_by F.height x
decreasing_by exact F.rise _ h
lemma cur_g (v:Site N→G)(x:Site N)(s:Step): cur (differ v) x s=v (x+s.vec)-v x:=by
 rcases s with ⟨i,h⟩; cases h <;>simp [cur,Step.used,differ,Fixed.Pivots.reach,Step.vec,sub_eq_add_neg]
lemma peeled_r (U:Site C→G)(q:Bond N→G): peel S F U q ∘ S.ratio.embed=U:=by
 funext i; unfold Function.comp; rw [peel,dif_neg (show ¬leaf S.ratio (S.ratio.embed i) from fun h=>h (by rw [Ratio.embed_parent])),Ratio.embed_parent]
lemma charge (U:Site C→G)(q:Bond N→G)(e:Bond N)(h:e∈ F.trunks):differ (peel S F U q) e=q e:=by
 obtain ⟨i,hP,rfl⟩:=(F.trunk_mem_iff _).mp h; let s:=F.up i; let v:=peel S F U q; have hx:v i=v (i+s.vec)-cur q i s:=by conv_lhs=> unfold v; rw [peel,dif_pos hP]
 have hp: cur (differ v) i s=cur q i s:= by rw [cur_g,hx]; abel
 unfold cur at hp; split at hp<;> first | exact hp|exact neg_injective hp

lemma beforepins (t:2≤ N.val)(p:2 ≤ C.val):Grates (oldJoint S F (J:=J)) (probePair S J):=by
 let A:=oldJoint S F (J:=J); let U:= interior J C
 have hp(j:J)(a: Bond C): Sum.inr (a,j)∈ Aᶜ↔ a∉pivots C:=by simp [A,oldJoint,interior]
 have hx(j:J)(a:Bond N):Sum.inl (a,j)∈ Aᶜ↔a∈F.trunks:=by simp [A,oldJoint]
 have hr{G:Type}[AddCommGroup G](x:↥(Aᶜ)→G):∃ (U:Site N→ J→G) (v:Axis→J→G),hide A (rider S U v)=x:=by
    let f(i: Bond C)(j:J):=if h:Sum.inr (i,j)∈ Aᶜ then x ⟨_,h⟩ else 0
    let F'(i:Bond N)(j:J):=if h:Sum.inl (i,j)∈Aᶜ then x ⟨_,h⟩ else 0
    let X:=along f; let v:=weightPins f
    let g:=F'-extra v; let P:= peel S F X g
    refine ⟨P,v, funext fun i=>?_⟩; obtain ⟨a,h⟩:=i; cases a with
    | inl i=>
       change Fl P v i.1 i.2=_; rw [show Fl P v i.1=F' i.1 from ?_]; swap
       · unfold Fl; rw [show differ P i.1=g i.1 from charge S F X g _ ((hx _ _).mp h)]; exact sub_add_cancel ..
       unfold F'; rw [dif_pos h]
    | inr i=> change Fl (P∘ S.ratio.embed) v i.1 i.2=_; rw [peeled_r (F:=F), show Fl X v i.1=f i.1 from pivSlit f _ ((hp _ _).mp h)]; unfold f; rw [dif_pos h]
 constructor
 · intro x u y; obtain ⟨u,v⟩:=u; let x'(p:Bond N)(i:J):=x (Sum.inl (p,i)); have he:Closed x':=fun i=> funext fun j=> u j i
   let g:= along x'; let l:=weightPins x'; have h₁: x'=Fl g l:= closed_as t _ he
   let z:=rider S g l; have H : x=z:= by
      funext i; cases i with
      | inl i=> exact congrFun (congrFun h₁ _) i.2
      | inr i=> rw [show x _=pressB S _ i.1 from v i.2 i.1, show z _=pressB S _ i.1 from (riddled S g l).2 i.2 i.1,show (fun p=>x (Sum.inl (p,i.2)))= _ from (show (fun p=>x (Sum.inl (p,i.2)))=(fun p=>z (Sum.inl (p,i.2))) from funext fun j=> congrFun (congrFun h₁ _) i.2)]
   rw [H] at y ⊢
   let l':= g ∘ S.ratio.embed; have hG:Fl l' l=0:=by
      apply unique p (fl_closed _ _) (show Closed (0:Bond C→J→ℝ) from fun i=>by simp [Curl]); intro i t; exact funext fun j=> congrFun y ⟨Sum.inr (i,j),(hp _ _).mpr (fun x=> t (mem_filter.mp x).2)⟩
   have hV (N:Side)(i:Bond N):extra (0:Axis→J→ℝ) i=0:=by unfold extra; split<;>rfl
   have hz (N:Side):Fl (0:Site N→J→ℝ) 0=0:=by ext i j; simp [Fl,hV,differ]
   have hu:l=0:= (weight_defined l' l).symm.trans ((congrArg _ (hG.trans (hz C).symm)).trans (weight_defined _ _))
   have hg:S.ratio.embed 0=0:= S.ratio.root.map_zero
   have hc: g 0=0:=by unfold g; rw [along,dif_pos rfl]
   have hh:l'=0:=by
       apply diff_same _ (show l' 0=0 from (by change g (S.ratio.embed _)= _; rw [hg,hc]))
       rw [hu] at hG; funext i; apply add_right_cancel (b:= extra (0:Axis→J→ℝ) i) -- tune
       exact congrFun (hG.trans (hz C).symm) _
   have ht(X:Site N):g X=0:= by
       induction X using Forest.hike.induct F with
       | case1 X hx' ih=>
           let v:=F.up X; have hv: differ g (v.used X)=0:=by
             have he: Fl g l (v.used X)=0:= funext fun j=>congrFun y ⟨_, (hx j _).2 ((F.trunk_mem_iff _).mpr ⟨X,hx',rfl⟩)⟩; unfold Fl at he; rwa [hu,hV,add_zero] at he
           have hk:cur (differ g) X v=0:=by unfold cur; rw [hv]; split<;>simp
           rw [cur_g,sub_eq_zero] at hk; rw [←hk]; exact ih
       | case2 X hx' => rw [show X=S.ratio.embed (S.ratio.parent X) from Classical.not_not.mp hx']; exact congrFun hh _
   funext i; cases i with
   | inl i=> change Fl g l _ _ =0; rw [hu,show g=0 from funext ht,hz]; rfl
   | inr i=> change Fl l' l _ _=0; rw [hG]; rfl
 · intro f; obtain ⟨U,v,x⟩:=hr f; exact ⟨_,riddled S U v,x⟩
 intro f h; choose F h using h; obtain ⟨U,v,x⟩:=hr F
 refine ⟨_,riddled S (fun a j=>(U a j:ℝ)) (fun a j=>(v a j:ℝ)),fun i=>⟨_,yr S U v i⟩,funext fun i=>?_⟩
 unfold hide; rw [h,yr]; exact congrArg _ (congrFun x i)
end YM.CF.Papyrus.GaugeFlux
#print axioms YM.CF.Papyrus.GaugeFlux.beforepins
