import YM.CF.Font.Stone
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Finset Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n:Side}{C:Type*}[NormedAddCommGroup C][NormedSpace ℝ C]
def shiftH (x y:Site n): Walk:= route 0 (lift (y-x)) 1
lemma stopH(x y:Site n): stop x (shiftH x y)=y:=by
 let W:=shiftH x y; let v:=lift (y-x)
 have he (p:Walk)(z:Cover):stop (x+wrap _ z) p=x+wrap n (stop z p):=by
    induction p generalizing z with
    | nil=> rfl
    | cons d p H=> rw [stop,←wrap_vec _ d,add_assoc,←map_add,H]; rfl
 change stop x W=y; rw [show stop x W=x+ wrap n (stop 0 W) from ?_]; swap; · simpa using he W 0
 unfold W shiftH; rw [route_end,wrap_lift,add_sub_cancel]
lemma short(x y:Site n): (shiftH x y).length≤4*separation x y:=by
 rw [separation_comm]
 let f:= lift (y-x)
 have he(i:Axis): (f i).natAbs≤separation y x:= component_le (y-x) _
 have hp(L:List Axis): (axisRoute 0 f L).length ≤ L.length*separation y x:=by
    induction L with
    | nil=>simp [axisRoute]
    | cons i v ih=> rw [show axisRoute 0 f (i::v)= straight i (f i-0)++axisRoute 0 f v from rfl]; simp only [List.length_append, straight, List.length_replicate,sub_zero,List.length_cons]; rw [add_mul,one_mul]; linarith [he i]
 simpa only [shiftH,f,route,allAxes,List.length_finRange, List.length_map] using hp (allAxes 1)
abbrev Blip(n:Side):=Edge (Site n)
def train(x:Site n)(e:Blip n): Walk:=shiftH x e.1++[posDir e.2]++reverse (shiftH x (e.1+step e.2))
def slope(x:Site n)(e:Blip n):ℕ:=9*(separation x e.1+1)
lemma upcoming(x:Site n)(e:Blip n): (train x e).length ≤ slope x e :=by
 let d:Site n:=step e.2; have hx:= short x e.1; have hm:=short x (e.1+d); have hs : separation x (e.1+d)≤ separation x e.1+1:= (separation_triangle ..).trans (Nat.add_le_add_left (small _ (posDir e.2)) _)
 unfold slope train; simp only [List.length_append,List.length_singleton,reverse,List.length_reverse, List.length_map]; change _+(shiftH x (e.1+d)).length≤ _; omega
lemma halts(x:Site n)(e:Blip n): stop x (train x e)=x:=by
 unfold train; simp only [stop_append,stopH,stop, Step.vec_pos]; exact Eq.trans (congr_arg (fun y=> stop y _) (stopH x _).symm) (reverse_stop ..)
private lemma beads(f:List (Wind n×Bool))(x:Site n) : ∃ a:Wind n→ℝ,(∑ i, |a i|)≤ f.length ∧ (∀ i,a i ≠0→ ∃ p,(i,p)∈f)∧∀ J:Links (Per n) C,Yelp x J f= ∑ i,a i • heat x J i:=by
 induction f with
 | nil=> exact ⟨fun _=>0,by simp,by simp,by simp [Yelp]⟩
 | cons b t ih=>
    rcases b with ⟨i,p⟩; obtain ⟨a,v,h,k⟩:= ih; let r:ℝ:= if p then -1 else 1; let G(u):= if i=u then r else 0
    refine ⟨a+G,?_,?_,?_⟩
    · have he:(∑ i,|G i|)=1:=by rw [sum_eq_single i (fun b _ h=>by simp [G,h,Ne.symm]) (by simp)]; cases p<;>simp [G,r]
      refine (sum_le_sum (g:=fun i=> |a i|+|G i|) (fun _ _ => abs_add_le ..)).trans ?_; rw [sum_add_distrib,he]; simpa using v
    · intro u he; by_cases v:i=u; exact ⟨p,by simp [v]⟩; obtain ⟨z,hz⟩:= h u (by simpa [G,v] using he); exact ⟨z,List.mem_cons_of_mem _ hz⟩
    intro J; rw [show Yelp x J ((i,p)::t)= _ from (p_add x [(i,p)] t J), k]; simp only [Pi.add_apply,add_smul,sum_add_distrib]; unfold G; simp only [ite_smul,zero_smul,sum_ite_eq,mem_univ,ite_true]
    rw [add_comm]; unfold Yelp; cases p<;>simp only [r,List.map_cons,List.map_nil, seal_t,List.sum_singleton,ite_true, one_smul,neg_smul, Bool.false_eq_true,not_false_eq_true, if_false]

def pure (x:Site n→C):Links (Per n) C:=fun e=> x (e.1+step e.2)-x e.1
def sap (x:Site n)(u:Links (Per n) C) : Site n→C := fun j=> linkSum u x (shiftH x j)
lemma runoff (x:Site n)(u:Links (Per n) C)(e:Blip n) : (u-pure (sap x u)) e=linkSum u x (train x e):=by
 simp only [train,amix, stopH,stop_append,stop,Step.vec_pos]; let y:=e.1+step e.2
 change u e-(linkSum u x (shiftH x y)-linkSum u x (shiftH x _))=linkSum u x _+(u e+0)+linkSum u y _
 rw [show linkSum u y _= _ from Eq.trans (congr_arg (fun y'=>linkSum u y' (reverse (shiftH x y))) (stopH x y).symm) (aturn ..)]; abel -- tune
variable (C) in
theorem funnel (x:Site n)(e:Blip n): ∃ a:Wind n→ℝ,(∑ i, |a i|)≤4*(↑(slope x e)+1)^2∧(∀ i,a i≠0→dial x i ≤ slope x e+1)∧∀ J:Links (Per n) C,(J-pure (sap x J)) e=∑ i,a i • heat x J i:=by
 obtain ⟨p,h,g,H⟩:=palace C x (train x e) univ (fun i _=> mem_univ _) (halts x e)
 obtain ⟨a,r,q,Q⟩:= beads (C:=C) p x; have hr:=upcoming x e; refine ⟨a,r.trans ?_,fun i h=> (g (i,_) (q _ h).choose_spec).trans (by omega),fun i=>?_⟩
 · exact_mod_cast (le_trans (b:=4*((train x e).length+1)^2) h (show _ ≤ 4*((slope x e)+1)^2 by gcongr))
 rw [runoff,H,Q]
end YM.CF.Font
