import YM.CF.Font.Cork
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Finset Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n:Side}{C:Type*}[AddCommGroup C]
def Yelp(x: Site n)(J:Links (Per n) C)(f:List (Wind n × Bool)): C:= (f.map fun z=> seal_t z.2 (heat x J z.1)).sum
lemma p_add (x:Site n)(a b:List (Wind n × Bool))(J:Links (Per n) C):Yelp x J (a++b)=Yelp x J a+Yelp x J b:=by simp [Yelp]
private lemma polish(x:Site n)(J:Links (Per n) C)(a:Axis)(b:Bool): linkSum J x (List.replicate n.val (⟨a,b⟩:Step))=seal_t b (heat x J (.inr a)):=by
 cases b; rfl; let s:=swirl n a; have ht:=aturn x J s; rw [swirl_stop] at ht; rw [show reverse s=_ from (show reverse s=List.replicate n.val (negDir a) from by simp [s,reverse,swirl])] at ht -- ambiguous
 change _= -linkSum J x s; exact ht
variable (C) in
lemma honey (x:Site n)(w: Walk)(a:Axis)(h:∀ i∈w,i.dir=a):∃ b:Bool,∃ j:ℕ, let v:=List.replicate j (⟨a,b⟩:Step); j ≤ w.length∧ stop x v=stop x w∧∀ J: Links (Per n) C, linkSum J x v= linkSum J x w:=by
 induction w generalizing x with
 | nil=> exact ⟨true,0,Nat.zero_le _,rfl,fun _=>rfl⟩
 | cons i w ih=>
    rcases i with ⟨k,t⟩; have he:k=a:=h ⟨k,t⟩ (by simp); subst k
    let d:Step:= ⟨a,t⟩; let y:= x+d.vec; obtain ⟨b,r,q,p,f⟩:= ih y (fun _ he=> h _ (List.mem_cons_of_mem _ he)) -- v let
    by_cases hp:t=b
    · subst t; refine ⟨b,r+1,?_⟩; dsimp only [List.length_cons]; rw [List.replicate_succ]; exact ⟨by omega, p,fun J=>by rw [linkSum,linkSum]; exact congrArg (_+·) (f _)⟩
    cases r with
    | zero=> refine ⟨t,1,by simp,p,fun A=>?_⟩; change ask d A x+0=ask d A x+linkSum A y w; rw [← f]; rfl
    | succ r=>
       let L:=List.replicate r d.rev
       have hx:d.rev=⟨a,b⟩:=by unfold d Step.rev; cases b<;>cases t<;>simp_all
       have hv: List.replicate (r+1) (⟨a,b⟩:Step)=d.rev :: L:=by rw [List.replicate_succ]; unfold L; rw [hx]
       have hh:y+d.rev.vec=x:=by unfold y; rw [Step.vec_rev,add_neg_cancel_right]
       refine ⟨b,r,?_⟩; rw [←hx]; refine ⟨by simp; omega,?_,?_⟩
       · change stop x L=stop y w; rw [← p, hv,stop,hh]
       intro J; rw [linkSum]; change linkSum J x L = ask d J x+linkSum J y w; rw [←f,hv,linkSum]; change _= _+(ask d.rev J y+_); rw [bin_reverse,hh]; abel -- tun
variable (C) in
lemma belt (x:Site n)(w:Walk)(a:Axis)(h:∀ i∈w,i.dir=a)(e: stop x w=x):∃ f : List (Wind n× Bool),f.length≤ w.length ∧(∀ i∈f,dial x i.1≤w.length)∧∀ J:Links (Per n) C, linkSum J x w=Yelp x J f:=by
 obtain ⟨b,L,v⟩:= honey C x w a h; dsimp only at v
 obtain ⟨u,p,q⟩:=v
 obtain ⟨d,hd⟩:= (reps x a b L).1 (p.trans e); subst L
 let i:Wind n×Bool:=(.inr a,b); let t:Step:=⟨a,b⟩
 refine ⟨List.replicate d i,by rw [List.length_replicate]; exact le_trans (Nat.le_mul_of_pos_left _ n.property) u,fun z hp=>?_,fun J=>?_⟩
 · cases d; simp at hp; next d=>simp at hp; rw [hp]; change n.val ≤ w.length; nlinarith
 rw [← q]
 suffices ht:∀ d:ℕ, linkSum J x (List.replicate (n.val*d) t)=Yelp x J (List.replicate d i) from ht _
 intro d; induction d with
 | zero=> simp [linkSum,Yelp]
 | succ d ih=>
    rw [Nat.mul_succ,add_comm, List.replicate_add,amix, show stop x _=x from (reps x a b n.val).2 dvd_rfl, ih,List.replicate_succ]; rw [show linkSum _ x _=_ from polish x J a b]; simp only [Yelp,List.map_cons,List.sum_cons]; rfl -- tune
private lemma apart (w:Walk)(x:Site n)(a:Axis)(h:∀ i∈w,i.dir≠a) : stop x w a=x a:=by
 induction w generalizing x with
 | nil=>rfl
 | cons d w ih=> rw [stop,ih _ (fun i e=> h i (List.mem_cons_of_mem _ e))]; have hx:=h d (by simp); simp [Step.vec,hx,Ne.symm]; split<;>simp [hx,Ne.symm] -- tune
variable (C) in
lemma palace (x:Site n)(w:Walk)(t:Finset Axis)(v:∀ i∈w,i.dir∈t)(e:stop x w=x):∃ f: List (Wind n × Bool),f.length≤ t.card*(w.length+1)^2∧(∀ i∈f,dial x i.1≤ w.length+1)∧∀ J:Links (Per n) C,linkSum J x w=Yelp x J f:=by
 induction t using Finset.induction_on generalizing w with
 | empty=> cases w; exact ⟨[],Nat.zero_le _,by simp,fun _=>rfl⟩; rename_i b w; exact False.elim ((notMem_empty b.dir) (v _ (by simp)))
 | @insert a t h ih=>
   let y:=w.filter fun b=>decide (a=b.dir); let z:=w.filter fun b=>decide (a≠b.dir); let W:= stop x y; obtain ⟨q,p⟩:= (grove C x w a : y.length+z.length=w.length ∧ Mice x (w) (y++z) (w.length^2) (w.length+1) C)
   change y.length+z.length=w.length at q; change Mice x w (y++z) _ _ C at p
   obtain ⟨u,F,k,H,Q⟩:=p
   have he(i)(e:i∈y): i.dir=a:= (of_decide_eq_true (List.mem_filter.mp e).2).symm
   have hg(i)(h:i∈z): a≠i.dir:= of_decide_eq_true (List.mem_filter.mp h).2
   have hl: stop W z=x:=by rw [←e,u,stop_append]; -- rw x?
   have hv:W=x:=by
      funext i; by_cases p:i=a; subst i; have hx:=apart z W a fun d p=> Ne.symm (hg d p); rw [hl] at hx; exact hx.symm
      exact apart y x i fun d e=> (he d e) ▸ (Ne.symm p)
   obtain ⟨v',hp,H',p⟩:=ih z (fun i he=> (mem_insert.mp (v _ (List.mem_filter.mp he).1)).resolve_left (Ne.symm (hg i he))) (by rw [hv] at hl; exact hl)
   obtain ⟨f,h',g,hz⟩:= belt C x y a he hv
   let P: List (Wind n × Bool):= F.map fun i=> (Sum.inl i.1,i.2)
   refine ⟨f++v'++P,?_,?_,fun J=>?_⟩
   · rw [card_insert_of_notMem h, List.length_append,List.length_append]; unfold P; rw [List.length_map]; nlinarith [pow_le_pow_left₀ (Nat.zero_le (z.length+1)) (by omega : z.length+1≤w.length+1) 2]
   · intro i hp; rcases List.mem_append.mp hp with hx|hx
     · rcases List.mem_append.mp hx with e|e; specialize g i e; omega; specialize H' i e; omega
     obtain ⟨j,p,rfl⟩:= List.mem_map.mp hx; exact H _ p
   rw [Q, amix, show stop x y=x from hv,p,hz,p_add,p_add]; congr 2; unfold book Yelp P; rw [List.map_map]; rfl
end YM.CF.Font
