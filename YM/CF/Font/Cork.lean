import YM.CF.Font.Isle
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Finset MeasureTheory Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n:Side}{C:Type*}[AddCommGroup C]
namespace Mice
variable {x:Site n}{a b c:Walk}{r s j k:ℕ}
lemma snap (C:Type*) [AddCommGroup C] (x:Site n)(a:Walk)(r j:ℕ):Mice x a a j r C:=⟨rfl,[],Nat.zero_le _,by simp,by simp [book]⟩
lemma more(h:Mice x a b j r C)(g:r≤s)(e:j≤k):Mice x a b k s C:=by obtain ⟨x,u,y,H,h⟩:=h; exact ⟨x,u,y.trans e,fun i p=> (H i p).trans g,h⟩
lemma move(h:Mice x a b j r C)(e: Mice x b c k r C):Mice x a c (j+k) r C:=by
 obtain ⟨l,u,p,H,f⟩:=h; obtain ⟨v,w,h,W,g⟩:=e; refine ⟨l.trans v,w++u,by simp; omega,fun i h=> (List.mem_append.mp h).elim (W _) (H _),?_⟩; intro J; rw [f,g,pays,add_assoc]
lemma bouquet(d:Step)(h:Mice (x+d.vec) a b j r C) : Mice x (d::a) (d::b) j (1+r) C:=by
 obtain ⟨t,f,l,H,g⟩:= h; refine ⟨t,f,l,fun i h=>(separation_triangle x (x+d.vec) _).trans (add_le_add (small _ _) (H i h)),fun A=>?_⟩; rw [linkSum,linkSum,g,add_assoc]
lemma trail (l:Walk)(h:Mice x a b j r C):Mice x (a++l) (b++l) j r C:=by
 obtain ⟨t,f,z,h,g⟩:=h; refine ⟨by rw [stop_append,stop_append,t],f,z,h,fun A=>?_⟩; rw [amix,amix,g,t]; abel
end Mice
variable (C) in
lemma coat (x:Site n)(a:Step)(p:Walk)(h:∀ i∈p,a.dir≠i.dir):Mice x (a::p) (p++[a]) p.length (p.length+1) C:=by
 induction p generalizing x with
 | nil=> exact Mice.snap ..
 | cons b p ih=>
    have he:= Mice.trail p (curves C x a b (h _ (by simp))); have hx:= Mice.bouquet b (ih (x+b.vec) (fun i e=> h i (List.mem_cons_of_mem b e)))
    exact (Mice.move (c:=b::(p++[a])) (he.more (Nat.le_add_left 2 p.length |>.trans (by omega)) le_rfl) hx).more (by simp; omega) (by simp; omega)
variable (C) in
lemma grove (x:Site n)(p:Walk)(a:Axis) : let v:=p.filter fun b=>decide (a=b.dir); let w:=p.filter fun b=>decide (a≠ b.dir)
 v.length+w.length=p.length∧ Mice x p (v++w) (p.length^2) (p.length+1) C:=by
 induction p generalizing x with
 | nil=> exact ⟨rfl,Mice.snap ..⟩
 | cons i p ih=>
    let y:=x+i.vec; obtain ⟨u,h⟩:= ih y; intro v w; let f:= p.filter fun b=> decide (a=b.dir); let g:=p.filter fun b=>decide (a≠b.dir)
    change f.length+g.length=p.length at u; change Mice y p (f++g) _ _ _ at h
    by_cases hi:a=i.dir
    · rw [show v=i::f by simp [v,f,hi],show w=g by simp [w,g,hi]]; exact ⟨by simp; omega,(Mice.bouquet i h).more (by simp; omega) (by simp; gcongr; omega)⟩ -- power omega?
    rw [show v=f by simp [v,f,hi],show w=i::g by simp [w,g,hi]]; refine ⟨by simp; omega,?_⟩
    have he : Mice x (i::(f++g)) (f++i::g) f.length (p.length+1+1) C :=by
       let v:=coat C x i f (fun d h=> fun p=> hi ((of_decide_eq_true ((List.mem_filter.mp h).2)).trans p.symm))
       convert ((v.trail g).more (by omega : f.length+1≤p.length+1+1) le_rfl) using 1 <;> simp
    refine ((Mice.bouquet i h).more (by omega : 1+(p.length+1) ≤ p.length+1+1) le_rfl |>.move he).more (by simp) ?_; simp only [List.length_cons]; nlinarith
lemma replic_l (x:Site n)(j:ℕ)(d:Step): stop x (List.replicate j d)= x+j • d.vec:=by induction j generalizing x with | zero=>simp [stop] | succ j ih=>rw [List.replicate_succ,stop,ih,succ_nsmul]; abel
lemma reps(x:Site n)(a: Axis)(b:Bool)(j:ℕ): stop x (List.replicate j ⟨a,b⟩)=x ↔ n.val ∣ j:=by
 let c:=n.val
 rw [replic_l,add_eq_left];
 have hx : j • (step a: Site n)=0 ↔ n.val ∣ j:=by
   constructor; · intro h; have hp:=congr_fun h a; simp at hp; exact (ZMod.natCast_eq_zero_iff ..).1 hp -- tune
   intro h; funext i; by_cases e:i=a <;> simp [e, show (j:Per n)=0 from (ZMod.natCast_eq_zero_iff ..).2 h]
 cases b
 · exact hx
 simp only [Step.vec,ite_true, smul_neg,neg_eq_zero]; exact hx
lemma swirl_stop(x:Site n)(a:Axis):stop x (swirl n a)=x:= (reps x a false n.val).mpr dvd_rfl
end YM.CF.Font
