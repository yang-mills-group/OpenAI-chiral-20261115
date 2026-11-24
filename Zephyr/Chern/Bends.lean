import Zephyr.Chern.Amber
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology YM.CF YM.CF.Tulip YM.CF.Cube YM.CF.Lat YM.CF.Rush YM.Laurent


open Finset

lemma comp_size (x:Cover)(i:Axis):(x i).natAbs ≤ size x :=
  single_le_sum (f:=fun i=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i)

lemma size_two (x:Cover) : size ((2:ℕ) • x)=2*size x := by
  simp [size,Int.natAbs_mul,mul_sum]

lemma step_size(i:Axis):size (step i : Cover)=1:= by
  rw [size,Finset.sum_eq_single i] <;> simp +contextual

variable {N:Side}
lemma close_wrap (x:Cover)(h:2*size x<N.val): lift (wrap N x)=x :=
  lift_eq_iff.mpr ⟨rfl,fun i=>by have c:=comp_size x i;omega⟩

lemma pdist_wrap (N:Side)(x:Cover): pdist (wrap N x)≤size x := by
  by_cases t:2*size x<N.val
  · simp only [pdist,close_wrap _ t]
    exact Finset.sup_le (fun i _=>comp_size x i)
  refine Finset.sup_le (fun i _=>?_)
  have h:= lift_centers (wrap N x) i
  omega

lemma size_lift (p:Site N):size (lift p)≤4*pdist p :=
  sum_le_card_nsmul univ _ (pdist p) (fun i _=>component_le p i) |>.trans (by simp [Axis])

lemma node_wrap (N:Side)(x:Cover) : node (wrap N x)
    =wrap (More N) ((2:ℕ) • x)+1 := by
  rw [node,Ratio.root_embed,Ratio.embed_wrap]
  rfl

lemma under_node (x:Cover)(c:lift (wrap N x)=x):
    size x ≤ 2 * separation (node (wrap N (-x))) 1 := by
  have h:lift (wrap (More N) ((2:ℕ) • x))=(2:ℕ) • x := by
    have k:= (lift_eq_iff.mp c).2
    apply lift_eq_iff.mpr
    refine ⟨rfl,fun i=>?_⟩
    have z:((More N).val:ℤ)=(N.val:ℤ)*2:= by simp [More]
    specialize k i
    rw [two_smul,Pi.add_apply,z]
    omega
  have b:=size_lift (wrap (More N) ((2:ℕ) • x)); rw [h,size_two] at b
  rw [node_wrap, separation, add_sub_cancel_right, smul_neg, map_neg, pdist_neg]
  omega

/-- Two oriented unit fluxes. -/
def flux (x y:Cover) : ℝ :=
   ((x 0:ℝ)*y 1-x 1*(y 0:ℝ))+
     ((x 2:ℝ)*y 3-x 3*(y 2:ℝ))

lemma flux_left(x y z:Cover) : flux (x+y) z = flux x z + flux y z:=by
  simp only [flux,Pi.add_apply,Int.cast_add];ring
lemma flux_switch(x y:Cover) : flux x y= -flux y x:=by unfold flux;ring
lemma flux_right(x y z : Cover):flux x (y+z)=flux x y+flux x z:=by
  rw [flux_switch, flux_left, flux_switch y,flux_switch z,neg_add,neg_neg,neg_neg]

lemma flux_neg(x y:Cover) : flux (-x) y= -flux x y:=by
  simp only [flux,Pi.neg_apply,Int.cast_neg]; ring

lemma flux_abs (x y:Cover): |flux x y| ≤ 4 * size x * size y:=by
  have b(u v) : |(x u:ℝ)*(y v:ℝ)|≤(size x:ℝ) * size y:=by
    have e (s:Cover)(i:Axis): |(s i:ℝ)|≤ size s:=by
      exact_mod_cast (show |s i|≤(size s:ℤ) by rw [Int.abs_eq_natAbs];exact_mod_cast comp_size s i)
    rw [abs_mul]
    exact mul_le_mul (e _ _) (e _ _) (abs_nonneg _) (by positivity)
  apply le_trans (abs_add_le ..)
  apply le_trans (add_le_add (abs_sub ..) (abs_sub ..))
  nlinarith only [b 0 1,b 1 0,b 2 3,b 3 2]

def rel (u:Site N):Cover:=lift (u-1)
lemma size_rel (u:Site N):size (rel u)≤4*separation u 1:= size_lift _
lemma rel_add (x:Cover)(m:ℕ)(h:4*m+size x<N.val) (u:Site (More N))(p:separation u 1 ≤m):
    rel (u+wrap (More N) x)=rel u + x:=by
  have a : 2*size (rel u + x) < (More N).val:= by
    have b:= size_rel u
    have g:= size_add (rel u) x
    rw [show (More N).val=N.val*2 from rfl]
    omega
  have k: wrap (More N) (rel u + x)=u+wrap (More N) x -1:=by
    simp only [rel,map_add,wrap_lift]; abel
  rw [rel, ← k,close_wrap _ a]

def twistAt (x:Cover)(v:Axis): ℝ := flux x (step v) / 2
/-- Affine potential near the origin in gauge units. rel uses gauge node corresponding
to matter 0 as period center; the flux is tested on positions *adding back* 1, i.e.
affine around the fixed grid origin, not that fermion node. -/
def stream (N:Side) : StemA N := fun i=>twistAt (rel i.1+1) i.2

lemma stream_mild (N:Side) : Temper 1 (stream N) 16:=by
  refine ⟨by norm_num, ?_⟩
  intro v
  simp only [stream,twistAt, abs_div,abs_of_pos (by norm_num: (0:ℝ)<2)]
  have k := flux_abs (rel v.1+1) (step v.2); rw [step_size,Nat.cast_one,mul_one] at k
  have y:size (rel v.1+1)≤4*separation v.1 1+4:=by
    exact (size_add _ _).trans (Nat.add_le_add (size_rel v.1) (by simp [size,Axis]))
  have hx :(size (rel v.1+1):ℝ)≤4*separation v.1 1+4:=by exact_mod_cast y
  linarith [(show (0:ℝ)≤separation v.1 1 from by positivity)]

/-- Profile correction gauge after pull to the context centered at -z.
`riseA z (node 0)=0`, pins the *right* color phase to one. -/
def riseA (z:Cover)(x:Site N): ℝ :=flux z (rel x)

lemma rise_one (z:Cover):riseA z (1:Site N)=0:=by simp [riseA,rel,flux,lift]

lemma rise_abs (z:Cover)(x:Site N):|riseA z x|≤16*size z * separation x 1:=by
  have b:=size_rel x
  have t:(size (rel x):ℝ)≤4 * separation x 1:=by exact_mod_cast b
  unfold riseA
  nlinarith only [flux_abs z (rel x), mul_le_mul_of_nonneg_left t (show (0:ℝ)≤size z by positivity),
    show riseA z x=flux z (rel x) from rfl]

def transA (N:Side)(z:Cover) : StemA N:= fun i=>
  stream N (i.1+wrap _ ((2:ℕ) • -z),i.2)

def glazed (N:Side)(z:Cover) : StemA N:= fun i=>
  riseA z i.1 + stream N i - riseA z (i.1+step i.2)

def rim (z:Cover):ℝ:=100*(1+size z)

lemma step_rel (x:Cover)(u:Site N):separation (u+wrap N x) 1 ≤ size x + separation u 1:=by
  have h:separation (u+wrap N x) u ≤ size x:= by
    rw [separation,add_sub_cancel_left];exact pdist_wrap ..
  exact (separation_triangle _ _ _).trans (Nat.add_le_add h le_rfl)

lemma trans_mild (N:Side)(z:Cover):Temper 1 (transA N z) (rim z) := by
  have h:0 ≤ (size z:ℝ) := by positivity
  constructor
  · unfold rim;linarith
  intro i
  unfold transA
  apply ((stream_mild N).grow _).trans
  have hk:= step_rel ((2:ℕ) • -z) i.1;rw [size_two,size_neg] at hk
  have t:(separation (i.1+wrap _ ((2:ℕ) • -z)) 1:ℝ) ≤ 2*size z + separation i.1 1 := by exact_mod_cast hk
  dsimp only
  unfold rim
  have hy:(0:ℝ)≤separation i.1 1:=by positivity
  nlinarith only [h,hy,t,mul_nonneg h hy]

lemma glaze_mild (N:Side)(z:Cover):Temper 1 (glazed N z) (rim z):= by
  have h:0 ≤ (size z:ℝ) := by positivity
  constructor
  · unfold rim;linarith
  intro i
  have hx:(separation (i.1+step i.2) 1:ℝ) ≤ 1+ separation i.1 1:=by
    have a:= step_rel (step i.2) i.1; rw [step_size,wrap_step] at a
    exact_mod_cast a
  refine (abs_sub ..).trans (le_trans
    (add_le_add ((abs_add_le ..).trans (add_le_add (rise_abs _ _) ((stream_mild N).grow i))) (rise_abs _ _)) ?_)
  unfold rim
  have hy:(0:ℝ) ≤ separation i.1 1 := by positivity
  nlinarith only [h,hy,mul_nonneg h hy,mul_le_mul_of_nonneg_left hx h]

lemma glaze_trans (z:Cover) (m:ℕ)(n:4*m+2*size z+1<N.val)(x:Edge (Site (More N)))
    (p:separation x.1 1 < m):
    transA N z x = glazed N z x := by
  simp only [transA,glazed,stream,riseA,twistAt]
  have ha:4*m+size ((2:ℕ) • -z)<N.val := by rw [size_two,size_neg];omega
  have hb:rel (x.1+step x.2) = rel x.1 + step x.2:=by
    rw [←rel_add _ m (by rw [step_size];omega) _ p.le,wrap_step]
  rw [rel_add _ m ha _ p.le,hb]
  simp only [two_smul,flux_left,flux_neg,flux_right]
  ring

lemma rise_charge (z y:Cover) (n:2*size y<N.val):
    riseA z (node (wrap N (-y)))=2*flux y z:=by
  rw [riseA,node_wrap,rel,add_sub_cancel_right,
    close_wrap _ (by rw [size_two,size_neg]; change _<N.val*2;omega),
    two_smul, flux_switch,flux_left,flux_neg]
  ring
