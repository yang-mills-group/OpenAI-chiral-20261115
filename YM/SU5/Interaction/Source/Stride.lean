import YM.CF.Font.Trail
/- # Tile telescoping. Faces through occupied sites; pay W weights half on them,
 no disjointness requirement. Travels Commute via linear convolution with BOTH half-shifts.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.StressExchange
open Function Filter Metric Lattice Finset
open scoped Topology BigOperators Classical
variable {X M:Type*}[AddCommGroup X] [AddCommGroup M]
/- Avoid fractions; sum has weight 2 per internal, 1 on faces at distance m, AND applies twice in each dimension. -/
def grain (d:X)(f:X→M) (x:X) : M := f x+f (x-d)
-- centered sum of shell f(x+k)+f(x-k) twice, up to r, half face
def rake (d:X)(f:X→M):ℕ→ X→ M
 | 0, _ => 0
 | r+1, x => rake d f r x+f (x+r • d)+f (x-r • d)+f (x+(r+1) • d)+f (x-(r+1) • d)
lemma stride (d:X)(f:X→M)(r:ℕ)(x:X) : rake d (fun x=>f x-f (x-d)) r x=
    grain d f (x+r • d)-grain d f (x-r • d):=by
 induction r with
 | zero=> simp [rake]
 | succ i h=>
   rw [rake,h]; have u:x+(i+1) • d-d=x+i • d:=by rw [add_smul,one_smul]; abel
   have v:x-i • d-d=x-(i+1) • d:=by rw [add_smul,one_smul]; abel
   simp only [grain,u,v]; abel
lemma rake_add (d:X)(f g:X→M)(r:ℕ)(x:X):rake d (f+g) r x=rake d f r x+rake d g r x:=by induction r with|zero=>simp [rake]|succ j p=>simp only [rake,Pi.add_apply,p]; abel
lemma rake_sub (d:X)(f g:X→M)(r:ℕ)(x:X):rake d (f-g) r x=rake d f r x-rake d g r x:=by rw [eq_sub_iff_add_eq,←rake_add,sub_add_cancel]
lemma rake_neck (G:X→M)(h:ℕ)(x y d:X): rake d (fun z=>G (z+y)) h x = rake d G h (x+y):=by
 induction h with
 | zero=> rfl
 | succ i p=> rw [rake,rake,p,add_right_comm x (i • d),show x-i • d+y=x+y-i • d from (by abel),add_right_comm x ((i+1) • d),show x-(i+1) • d+y=x+y-(i+1) • d from (by abel)] -- tune
lemma rake_natural {B:Type*}[AddCommMonoid B] -- B group for target
    {M':Type*}[AddCommGroup M'](F:M→+ M')(G:X→M)(d:X)(h:ℕ)(x:X): F (rake d G h x)=rake d (F ∘ G) h x:=by induction h with |zero=> exact map_zero F|succ j p=>simp only [rake,map_add, p,Function.comp_apply]
lemma rake_comm (a b:X)(r:ℕ)(G:X→M)(s:ℕ): rake a (rake b G s) r = rake b (rake a G r) s:=by
 induction r with
 | zero=>
    funext x; induction s with|zero=>rfl|succ u p=> change (0:M)=_; rw [rake,←show (0:M)=rake b _ u _ from p]; simp only [rake,add_zero]
 | succ i h=>
    let T (d:X):X→M:=fun x=>G (x+d)
    have he:rake a G (i+1)= rake a G i+ T (i • a)+T (-(i • a))+T ((i+1) • a)+T (-((i+1) • a)):=by ext; simp [rake,T, sub_eq_add_neg]
    funext x; rw [he]; simp_rw [rake_add,T,rake_neck]; rw [rake,h, ← sub_eq_add_neg, ←sub_eq_add_neg]
variable {N: Side}
def cubelet (r:ℕ)(u:List Axis)(f:Site N→M): Site N→M:= u.foldr (fun i g=> rake (step i) g r) f
lemma cubelet_cons (r:ℕ)(a:Axis)(v:List Axis)(f:Site N→M):cubelet r (a::v) f=rake (step a) (cubelet r v f) r:=rfl
lemma cookie (r:ℕ)(a:Axis)(v:List Axis)(f:Site N→M):cubelet r (a::v) f=cubelet r v (rake (step a) f r):=by
 induction v with
 | nil=> rfl
 | cons i v h=>
    rw [cubelet_cons,cubelet_cons,cubelet_cons,rake_comm (step a), show rake (step a) (cubelet r v f) r= _ from h] -- tune
lemma cubelet_perm (r:ℕ){v l:List Axis}(h:v.Perm l)(f:Site N→M): cubelet r v f=cubelet r l f:=by induction h with| nil=>rfl| cons a _ ih=>rw [cubelet_cons,cubelet_cons,ih]| swap a b v=> rw [cubelet_cons,cubelet_cons,cubelet_cons,cubelet_cons,rake_comm]| trans _ _ hg hz=>exact hg.trans hz
lemma cubelet_add (r:ℕ)(v:List Axis)(f g:Site N→M): cubelet r v (f+g)=cubelet r v f+cubelet r v g:=by induction v with|nil=>rfl| cons a v t=> simp only [cubelet_cons,t]; exact funext (fun _=>rake_add ..)
lemma cubelet_zero (r:ℕ)(v:List Axis):cubelet (M:=M) r v (0:Site N→M)=0:= by have ht:=cubelet_add r v (0:Site N→M) 0; rw [zero_add,eq_comm] at ht; apply add_left_cancel (a:=cubelet r v (0:Site N→M)); rwa [add_zero] -- maybe name
lemma cubelet_jump (r:ℕ)(v:List Axis)(f:Site N→M)(d x:Site N): cubelet r v (fun x=> f (x+d)-f (x-d)) x=cubelet r v f (x+d) - cubelet r v f (x-d):=by
 induction v generalizing x with
 | nil=>rfl
 | cons i v h=>
   rw [cubelet_cons,cubelet_cons]; rw [show cubelet r v (fun x=>_)=(fun x=>cubelet r v f (x+d))-(fun x=>cubelet r v f (x+ -d)) from (funext fun x=>(h x).trans (by rw [sub_eq_add_neg x d]; rfl)), rake_sub,rake_neck,rake_neck,←sub_eq_add_neg] -- tune
lemma cubelet_natural {M':Type*}[AddCommGroup M'](F:M→+M')(G:Site N→M)(r:ℕ)(v:List Axis): F ∘ cubelet r v G=cubelet r v (F ∘ G):=by induction v with|nil=>rfl| cons i v h=>rw [cubelet_cons,cubelet_cons,show F ∘ rake (step i) (cubelet r v G) r=rake (step i) (F ∘ cubelet r v G) r from funext (fun _=>rake_natural (B:=ℕ) ..),h]
end YM.CF.StressExchange
