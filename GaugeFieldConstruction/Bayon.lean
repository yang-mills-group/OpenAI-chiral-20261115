import GaugeFieldConstruction.Burst
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
variable (ι:G→J)(a b h r:ℝ)(U:G→ G→Toil I J B)(c d:ℝ)(p:FumedH a b ι U c d)(q:Book0 I J G B)(D:ℝ)(t:Puffion ι q)(s:MajorZ a b h q D)
variable (hr:0≤r)(ha:0≤a)(hb:0≤b)(ht:1≤h)
local notation "WG"=>weightV a b
local notation "WX"=>bil a b
variable (X:I→Book0 I J G B)
def buried (Q:List (Lem I J V B)):Prop:=∀ i∈ Q,i.keys≠[]
def spent (Q:List (Lem I J V B)):Prop:=∀ i∈Q,i.keys=[]
def stabH : Prop:= ∀ i j:G,spent (U i j)
def stampK (l:List I): Prop:= ∀ i∈ l,∀ k∈X i,k.keys=[i]
local notation "V0"=> Lem I J (Option (G×G)) B
local notation "Hk"=> Lem I J Unit B
local notation "Sν"=> Lem I J G B
local notation "Kζ"=>Keeps U r X
local notation "Fζ" =>frond U r
variable (E:Book0 I J G B)
lemma Keype_H(g:Lem I J V B)(X:Finset J)(z:Key I)(y:B)(u:g.keys=[]):egest g X z y=egest g X 0 y:=by simp only [egest,stalk,u,List.map_nil,List.prod_nil]
lemma cry_H (p:stabH U)(Z:Finset J)(x:B)(z:Key I):cryH U Z z x= cryH U Z 0 x:=by funext i j; exact paidA _ _ _ (fun v h=> Keype_H _ _ _ _ (p i j v h)) -- dotdot
lemma front_U (k:I)(Q: Book0 I J G B)(X:Finset J)(y:B)(v:Key I)(p:∀ q∈Q,q.keys=[k]): cryY X v y Q=v k • cryY X 1 y Q:=by
 unfold cryY; rw [scaleA]; refine paidA _ _ _ fun z u=>?_; rw [smul_smul]; unfold egest; by_cases t:z.seat⊆ X <;> simp [t,p z u,stalk]
lemma deepH (l:List I)(p:stampK X l): buried (Kζ l):=by
 induction l with
 | nil=> intro i h; simp [Keeps] at h
 | cons i l ih=>
    intro j t; unfold Keeps at t; cases List.mem_append.mp t with
    | inl h=>exact ih (fun k u=>p k (List.mem_cons_of_mem _ u)) j h
    | inr h=>
       obtain ⟨x,v,h⟩:=List.mem_flatMap.mp h; have hx:=p i List.mem_cons_self x v; unfold growL at h; split at h; rw [List.mem_singleton.mp h,hx]; exact List.cons_ne_nil _ _; obtain ⟨k,w,rfl⟩:=List.mem_map.mp h; simp [joint,hx]
lemma πlong (i:G)(p:buried q):let D:=q.flatMap (feint U r i); buried D ∧ frond U r q i= leaf i :: D:=by
 intro D; refine ⟨fun x u=>?_,rfl⟩; obtain ⟨v,z,w⟩:=List.mem_flatMap.mp u; unfold feint at w; cases ht:v.val with
 | none=> simp [ht] at w
 | some k =>
    simp only [ht,Option.elim_some,List.mem_append,List.mem_map] at w; have he:=p v z
    cases w <;> next w=> obtain ⟨q,t,rfl⟩:=w; simp [merP,joint,he]
 -- tune
lemma filterA{A B:Type}(L:List A)(F:A→List B)(p:B→Bool): (L.flatMap F).filter p= L.flatMap (fun i=>(F i).filter p):= List.filter_flatMap -- tune
lemma tooth_filter (u v:G)(p:stabH U)(h:buried q): let T:=toothW U r; (T q u v).filter (fun i=>i.keys==[]) =T [] u v:=by
 intro T; let A:=q.flatMap (feint U r u); let V:= q.flatMap (feint U r v); let f:=πlong r U q u h; let g:=πlong r U q v h;
 let i0:Lem I J G B:=leaf u; let j0:Lem I J G B:=leaf v
 let F(e:Lem I J G B)(k:Lem I J G B):V0:=joint e k r (some (e.val,k.val)); let Z(e:Lem I J G B)(k:Hk):V0:=joint e k r none; let Q(e:V0):Bool:=e.keys==[]; have hu: Q (F i0 j0)=true:=by simp [Q,F,i0,j0,joint]
 have hv:List.filter Q ((U u v).map (Z j0))= (U u v).map (Z j0):=by
    apply List.filter_eq_self.mpr; intro i z; obtain ⟨e,w,rfl⟩:=List.mem_map.mp z; exact beq_iff_eq.mpr (by change []++e.keys=[]; rw [p u v e w]; rfl)
 have h1: List.filter Q (A.flatMap fun a=>(j0::V).map (F a))=[]:=by
    apply List.filter_eq_nil_iff.mpr; intro e u; obtain ⟨i,t,h⟩:=List.mem_flatMap.mp u; obtain ⟨j,k,rfl⟩:=List.mem_map.mp h; have hx:=f.1 i t; simp [Q,F,joint,hx] -- fi
 have h2: List.filter Q (V.map (F i0))=[]:=by apply List.filter_eq_nil_iff.mpr; intro e u; obtain ⟨i,t,rfl⟩:=List.mem_map.mp u; have hx:=g.1 i t; simp [Q,F,joint,hx]
 have h3: List.filter Q (V.flatMap fun e=>(U u e.val).map (Z e))=[]:=by apply List.filter_eq_nil_iff.mpr; intro e u; obtain ⟨i,t,s⟩:=List.mem_flatMap.mp u; obtain ⟨j,b,rfl⟩:=List.mem_map.mp s; have hx:=g.1 i t; simp [Q,Z,joint,hx]
 change List.filter Q ((i0::A).flatMap (fun a=>(j0::V).map (F a))++ (j0::V).flatMap fun a=>(U u a.val).map (Z a))= List.flatMap (fun a=>[j0].map (F a)) [i0] ++ List.flatMap (fun a=>(U u a.val).map (Z a)) [j0]
 simp_rw [List.map_cons] at h1; simp only [List.filter_append,List.flatMap_cons,List.map_cons,List.map_nil,List.filter_cons,hu,↓reduceIte,h1,h2,h3,List.append_nil,List.flatMap_nil]; change _= _; rw [show j0.val=v from rfl,hv]
-- core size stamps admits all.Bill true singles & pad.T labels no h
abbrev SmallF {V:Type}(i:Lem I J V B):Bool:=decide (i.keys.length≤1)
lemma sage (e:Lem I J (Option (G×G)) B)(p:e.keys.length=1)(u:buried q)(v:stabH U): (growL U r q e).filter SmallF=growL U r [] e:=by
 unfold growL; split -- tune
 · simp [SmallF,p]
 next i v₀ h => -- tune binder
    -- tooth filter
    let T:=toothW U r; let F (v:V0):V0:=joint e v r v.val
    let A(r:V0):Bool:= r.keys==[]
    have hp: SmallF ∘ F=A:=by funext x; simp [A,F,joint,SmallF,p]; cases x.keys <;> simp -- test simp
    rw [List.filter_map,hp,tooth_filter r U q i v₀ v u]

lemma top_sage (v:stabH U)(u:buried q)(k:Book0 I J G B)(p:∀ i∈ k,i.keys.length=1): (topL U r q k).filter SmallF= topL U r [] k:=by
 unfold topL; rw [filterA]; induction k with|nil=>rfl|cons i k ih=>simp only [List.flatMap_cons,sage r U q i (p i List.mem_cons_self) u v,ih fun j t=>p j (List.mem_cons_of_mem _ t)]
lemma Keep_sage (v:stabH U)(l:List I)(w:stampK X l) : (Kζ l).filter SmallF= l.reverse.flatMap fun i=>topL U r [] (X i):=by
 induction l with|nil=>rfl|cons i l h=> have hp: stampK X l:= fun j t=> w j (List.mem_cons_of_mem _ t); rw [Keeps,List.filter_append,h hp,top_sage _ U _ v (deepH r U X l hp) _ (fun j t=>by rw [w i List.mem_cons_self j t]; rfl),List.reverse_cons,List.flatMap_append,List.flatMap_singleton]
#print axioms Keep_sage
-- pure matter.True every no contraction
abbrev foli (E:List (Lem I J V B)): List (Lem I J V B):= E.filter (fun e=>e.pure)
abbrev thaw (e:Lem I J V B)(x:G): Lem I J G B:= {seat:= e.seat, val:=x,amt:=e.amt, keys:=e.keys, won:=e.won,pure:=e.pure}
def durW (e:Lem I J (Option (G×G)) B): Lem I J (Option (G×G)) B:= match e.val with|none=> e|some _=> {e with won:=r*e.won*r } -- joint product R^2
abbrev darkH (U:G→ G→ Toil I J B):Prop:= ∀ i j:G,∀ w∈ U i j,w.pure=false
abbrev linkedP (e:Lem I J (Option (G×G)) B)(j:G)(u:Lem I J Unit B): Lem I J (Option (G×G)) B:=joint e (joint (leaf j) u r (none:Option (G×G))) r none
lemma Grow_D (i j:G)(x:Lem I J (Option (G×G)) B)(p:x.val=some (i,j)): growL U r [] x=durW r x :: (U i j).map (linkedP r x j):=by
 unfold growL durW; rw [p]; simp only [toothW,frond,List.flatMap_nil,seedX,List.flatMap_cons,List.map_cons,List.map_nil,sprigW,leaf,List.append_nil, List.map_append,List.map_map,List.cons_append,List.nil_append]; congr 1; simp [joint,p] -- tune
lemma grow_Stamp (i:I)(e:Lem I J (Option (G×G)) B)(v:e.keys=[i])(p:stabH U): stampK (fun _=>growL U r [] e) [i]:=by
 intro j t k w; rw [List.mem_singleton.mp t]; by_cases h:e.val=none; unfold growL at w; rw [h] at w; exact List.mem_singleton.mp w ▸ v
 cases g:e.val with|none=> contradiction|some q=>obtain ⟨k',j'⟩:=q; rw [Grow_D r U _ _ _ g] at w; cases List.mem_cons.mp w with|inl w=>rw [w,durW,g]; exact v|inr w=>obtain ⟨V,X,rfl⟩:=List.mem_map.mp w; simp [linkedP,joint,v,p k' j' V X]
lemma Pure_P (e:Lem I J (Option (G×G)) B)(v:darkH U): foli (growL U r [] e)= if e.pure then [durW r e] else []:=by
 cases g:e.val with
 | none=> unfold growL; rw [g]; unfold durW; rw [g]; cases h:e.pure with|false=> unfold foli; simp_all|true=>unfold foli; simp_all -- lost eq
 | some w=>
    rw [Grow_D r U w.1 w.2 e g]; have he:List.filter Lem.pure (List.map (linkedP r e w.snd) (U w.fst w.snd))=[]:= by apply List.filter_eq_nil_iff.mpr; intro i t; obtain ⟨V,h,rfl⟩:=List.mem_map.mp t; simp only [linkedP,joint,v w.1 w.2 V h]; simp
    unfold foli; rw [List.filter_cons]; simp only [he,durW,g] -- cases

lemma raw_pure (e:Lem I J (Option (G×G)) B)(v:0≤e.won)(p:darkH U)(u:e.pure=true)(P:FumedH a b ι U c d)(hr:0≤r)(ha:0≤a)(hb:0≤b): Lee ((growL U r [] e).filter fun x=>!x.pure) (wageL a b h) ≤ (if e.val=none then 0 else r^2*c)*weightV a b e:=by
 cases g:e.val with
 | none=> simp only [growL,g]; simp [u,Lee]
 | some w=>
    have hs: ∀ v∈ U w.fst w.snd,(linkedP r e w.snd v).pure=false:=fun v h=>by simp [linkedP,joint,p _ _ v h]
    let X:= U w.1 w.2
    let V:= X.map (linkedP r e w.2)
    have he: (durW r e).pure=true:=by unfold durW; rw [g]; exact u
    rw [Grow_D r U _ _ _ g,List.filter_cons]; simp only [he,g, Bool.not_true,false_eq_decide_iff, Bool.false_eq_true, if_false, reduceCtorEq, ↓reduceIte]; rw [List.filter_eq_self.mpr (fun t v=>?_)]
    swap; · obtain ⟨jν,h,rfl⟩:= List.mem_map.mp v; simp [hs jν h]
    rw [mapA]; refine le_trans (lea_p _ _ (fun v=> (r^2*WG e)*WG v) fun i z=>?_) ((lea_scale _ _ _).le.trans ?_)
    · let k:=joint (leaf w.2) i r (none:Option (G×G)); have hx:0≤ k.won:=mul_nonneg (mul_nonneg hr zero_le_one) (P.fee0 _ _ _ z)
      have hw:=WP_pair a b r (leaf w.2) i ha hb hr zero_le_one (P.fee0 _ _ _ z) (none:Option (G×G)); rw [show weightV a b (leaf (J:=J) (I:=I) (B:=B) w.2)=1 from by simp [weightV],mul_one] at hw
      change 1*WG (joint e k r (none:Option (G×G)))≤ _; rw [one_mul]; refine (WP_pair a b r e k ha hb hr v hx _).trans ((mul_le_mul_of_nonneg_left hw (mul_nonneg hr (WP_v a b e hb v))).trans_eq ?_); ring
    apply le_trans (mul_le_mul_of_nonneg_left (raw_w _ b _ U _ _ hb P _ _) (mul_nonneg (sq_nonneg _) (WP_v _ _ _ hb v))); apply le_of_eq (mul_right_comm ..) -- tune $le
#print axioms Grow_D
end YM.CF.Fock.Wosk
end
