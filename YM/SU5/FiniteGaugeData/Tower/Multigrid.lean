import YM.SU5.FiniteGaugeData.Tower.Accord
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
/- Multidimensional shifted average. Freely commutable ℤ copies. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Set Function Filter Metric Finset ContinuousLinearMap
open scoped Topology NNReal InnerProductSpace BigOperators Classical
namespace Average
variable {A B S:Type*}[Fintype A][Fintype B]{H:Type*}[NormedAddCommGroup H][NormedSpace ℂ H]
-- express ignoring/removing one coordinate without swapping dependent binders
abbrev Other (_T:Type*) (x:_T):= {a:_T//a≠x}
@[simp]
lemma stops(a:A)(i:B×(Other A a→B)):(Equiv.funSplitAt a B).symm i a=i.1:=by simp
@[simp]
lemma stands(a:A)(i:B×(Other A a→B))(j:A)(t:j≠a):(Equiv.funSplitAt a B).symm i j=i.2 ⟨j,t⟩:=by simp [t]
lemma point(a:A)(h:(A→B)→H):(center h)=center (fun x:B=>center (fun y:Other A a→ B => h ((Equiv.funSplitAt a B).symm (x,y)))):=by
 let E:=Equiv.funSplitAt a B
 rw [← Average.trade E.symm h, Average.domino]

-- fold independent translations by arbitrary I labels (later erasable). Act on H.
end Average
open Average
variable {A:Type*}{H:Hilbert}
structure Moving (A:Type*)(H:Hilbert) where -- replace
 move : A→Rolls H
 separate (i j:A)(x y:ℤ): ((move i).wind x).comp ((move j).wind y)= ((move j).wind y).comp ((move i).wind x)
namespace Moving
variable (P:Moving A H)
-- can use list (arbitrary enumeration), whole shifts use Set A->ℤ
noncomputable def gallery (p: List A)(u:A→ ℤ):H.Op:=p.foldr (fun i (z:H.Op)=>((P.move i).wind (u i)).comp z) (ContinuousLinearMap.id ℂ H)
lemma entry(i:A)(l:List A)(u:A→ℤ):P.gallery (i::l) u=((P.move i).wind (u i)).comp (P.gallery l u):=rfl
lemma inter {s:H.Op}(q:∀i x,((P.move i).wind x).comp s=s.comp ((P.move i).wind x))(p:List A)(u): (P.gallery p u).comp s=s.comp (P.gallery p u):=by
 induction p with
 | nil=> rfl
 | cons i p ih=>rw [entry,ContinuousLinearMap.comp_assoc,ih, ←ContinuousLinearMap.comp_assoc,q];rfl
lemma plus(p:List A)(u v:A→ℤ):P.gallery p (u+v)=(P.gallery p u).comp (P.gallery p v):=by
 induction p with
 | nil=>rfl
 | cons i p ih=>
    have e: (P.gallery p u).comp ((P.move i).wind (v i))=((P.move i).wind (v i)).comp (P.gallery p u):=P.inter (fun j x=>P.separate ..) _ _
    rw [entry,entry,entry,ih,Pi.add_apply, ← (P.move i).along,ContinuousLinearMap.comp_assoc,←ContinuousLinearMap.comp_assoc ((P.move i).wind (v i)),←e]; rfl
lemma along(p:List A)(u v:A→ℤ)(x:H):P.gallery p u (P.gallery p v x)=P.gallery p (u+v) x:=by rw [P.plus]; rfl
lemma void(p:List A): P.gallery p 0=ContinuousLinearMap.id ℂ H:=by induction p with
 | nil=>rfl
 | cons i p ih=>rw [entry,ih,Pi.zero_apply,(P.move i).nil]; rfl
lemma rigid(p:List A)(u:A→ℤ)(x:H):‖P.gallery p u x‖=‖x‖:=by induction p generalizing x with
 | nil=> rfl
 | cons i p ih=> rw [entry,ContinuousLinearMap.comp_apply,Rolls.solid,ih]
lemma wind_distrib {u:H.Op}(a:List A)(h:∀i∈a,∀x:ℤ, u.comp ((P.move i).wind x)=((P.move i).wind x).comp u)(p:A→ℤ):u.comp (P.gallery a p)=(P.gallery a p).comp u:=by induction a with
 | nil=>rfl
 | cons i a ih=> rw [entry,←ContinuousLinearMap.comp_assoc,h i (List.Mem.head ..),ContinuousLinearMap.comp_assoc,ih (fun j v=>h j (List.Mem.tail _ v))]; rfl

def aligned (p:List A):Submodule ℂ H := ⨅ i:A, ⨅ _ : i∈p, ((P.move i).wind 1).eqLocus (1:H.Op)
lemma aligned_ok {p:List A}{x:H}: x∈P.aligned p ↔ ∀i∈p,∀j, (P.move i).wind j x=x:=by
 unfold aligned; simp only [Submodule.mem_iInf]; apply forall_congr'; intro i; apply forall_congr'; intro h
 suffices q:x∈((P.move i).wind 1).eqLocus (1:H.Op) ↔ (P.move i).calm x=x from q.trans ((P.move i).calm_mem _)
 exact Submodule.starProjection_eq_self_iff.symm
instance settled (p:List A): CompleteSpace (P.aligned p) :=by
 let S:=P.aligned p
 have ht:(S:Set H)= ⋂ i∈ {i:A|i∈p}, ⋂ j:ℤ, {x:H|(P.move i).wind j x=x}:=Set.ext fun i=> by simp [S, P.aligned_ok]
 have he : IsClosed (S : Set H):= by rw [ht]; exact isClosed_iInter fun i=> isClosed_iInter fun h=> isClosed_iInter fun j=> isClosed_eq ((P.move i).wind j).continuous continuous_id
 exact he.completeSpace_coe
noncomputable def pause(p:List A):H.Op:= (P.aligned p).starProjection
lemma par(p:List A)(x:H):P.pause p x∈P.aligned p:=(P.aligned p).starProjection_apply_mem _
lemma pin {p:List A}(x:H)(h:x∈P.aligned p):P.pause p x=x:=Submodule.starProjection_eq_self_iff.mpr h
lemma stable(p:List A)(x:H)(u:A→ℤ)(t:List A)(h:t⊆p):P.gallery t u (P.pause p x)=P.pause p x:=by induction t with
 | nil=> rfl
 | cons i t ih=> rw [entry,ContinuousLinearMap.comp_apply,ih (fun j v=>h (List.Mem.tail _ v))]; exact P.aligned_ok.mp (P.par p x) _ (h (List.Mem.head ..)) _
lemma pause_nil:P.pause []=ContinuousLinearMap.id ℂ H:=by ext1 x; apply P.pin; exact P.aligned_ok.mpr (by simp)
lemma swing(p:List A)(x y:H):inner ℂ (P.pause p x) y=inner ℂ x (P.pause p y):=(P.aligned p).inner_starProjection_left_eq_right _ _
lemma stages(i:A)(x y:H):inner ℂ ((P.move i).calm x) y=inner ℂ x ((P.move i).calm y):=(((P.move i).wind 1).eqLocus (1:H.Op)).inner_starProjection_left_eq_right _ _
lemma still(i:A)(x:H)(h:(P.move i).wind 1 x=x):(P.move i).calm x=x:=Submodule.starProjection_eq_self_iff.mpr h
lemma compose(i:A)(p:List A):P.pause (i::p)= ((P.move i).calm).comp (P.pause p):=by
 let S:=P.aligned (i::p)
 let U:= (P.move i).calm
 ext1 x
 change S.starProjection x=U (P.pause p x)
 apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
 · apply P.aligned_ok.mpr
   intro j g k; rcases List.mem_cons.mp g with rfl|g
   · exact (P.move _).projected k _
   have he:= (P.move i).calm_commutes (fun v=> P.separate j i k v)
   unfold U; rw [←ContinuousLinearMap.comp_apply,he,ContinuousLinearMap.comp_apply,P.aligned_ok.mp (P.par p x) j g k]
 intro y h; have e:=P.aligned_ok.mp h
 have t:U y=y:=P.still i y (e _ (List.Mem.head ..) _)
 have u:P.pause p y=y:=P.pin y (P.aligned_ok.mpr (fun j a k=>e j (List.Mem.tail _ a) k))
 rw [inner_sub_left,P.stages,t,P.swing,u,sub_self]

lemma ignores{X Y:A→ℤ}{p:List A}(h:∀i∈p,X i=Y i):P.gallery p X=P.gallery p Y:=by induction p with
 | nil=>rfl
 | cons i p ih=>rw [entry, entry,h i (List.Mem.head ..), ih (fun _ a=>h _ (List.Mem.tail _ a))]
section jitter
variable [Fintype A]
-- unit intervals bumped at each coordinate
noncomputable def crew(n:ℕ)(p:A→ℤ)(v:A→ Fin (n+1))(i:A):ℤ:=p i + v i
noncomputable def levels(i:A){n:ℕ}(v:Other A i → Fin (n+1)):A→ Fin (n+1):= fun j=> if h:j=i then 0 else v ⟨j,h⟩
lemma trimming(i:A)(p:List A)(h:i∉p)(q:A→ℤ)(x:H){n:ℕ}(u:Fin (n+1))(v:Other A i→Fin (n+1)):
 P.gallery p (crew n q ((Equiv.funSplitAt i _).symm (u,v))) x=P.gallery p (crew n q (levels i v)) x:=by
 congr 1
 apply P.ignores; intro j t; have he:j≠ i:=fun v=>h (v ▸ t)
 rw [crew,crew,Average.stands _ _ _ he,levels,dif_neg he]
lemma median(p:List A)(q:ℕ→A→ℤ)(x:H)(h:p.Nodup):Tendsto (fun n:ℕ=> Average.center (fun c:A→ Fin (n+1)=>P.gallery p (crew n (q n) c) x)) atTop (𝓝 (P.pause p x)) :=by
 induction p with
 | nil=>simp_rw [pause_nil]; simpa only [gallery,List.foldr_nil,ContinuousLinearMap.id_apply,Average.constant] using (tendsto_const_nhds (x:=x) (f:=atTop (α:=ℕ))) -- direction
 | cons i t ih=>
    obtain ⟨he,hu⟩:=List.nodup_cons.mp h
    let f(n:ℕ):H:= Average.center (fun c:A→ Fin (n+1)=>P.gallery t (crew n (q n) c) x)
    have hf(n): f n = Average.center (fun v:Other A i→ Fin (n+1)=>P.gallery t (crew n (q n) (levels i v)) x):=by
       unfold f; rw [Average.point i]
       simp_rw [P.trimming i t he, Average.constant]
    rw [compose]; have key(n):
       Average.center (fun c:A→Fin (n+1)=>P.gallery (i::t) (crew n (q n) c) x)=
       Average.center (fun v:Fin (n+1)=> (P.move i).wind (q n i+v) (f n)):=by
       rw [Average.point i,hf]; apply Average.eq_of; intro v
       simp_rw [entry, ContinuousLinearMap.comp_apply,P.trimming i t he]
       simp only [crew,Average.stops]; rw [Average.natural]
    simp_rw [key]; exact (P.move i).steers (q · i) (ih hu)
end jitter
end Moving
end YM.CF.Buffered.Afterglow.Tower.Vacancy
