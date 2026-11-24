import YM.CF.BPress.Lute.House
/- eq:B-Xz, B-pathI, B-pathII. make determinant-one filling by lifting, real interpolation and $SU$ lift. Export (smooth as asked), makes choices before prices of blocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute.Kite
open Function Filter NormedSpace Metric Set SU SU.Pair Mesa Fort Spin Spin.Paint Music Fock
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable (k:Fin 5){u v:ℝ}
abbrev height := shapeL ∘ α0
abbrev Yₖ := (matter (orb k)).val
@[simp] lemma qZ : trueS (Yₖ k):=⟨(matter (orb k)).property,triple_det (orb k)⟩
def side(x:ℝ):=hopper k (-β0 x/2)*(Yₖ k*height x)
@[simp] lemma start_side : side k 0=Yₖ k*Y:=by rw [side,height,comp_apply,α_0,sheetL.head,beta_lo0 (by norm_num),neg_zero,zero_div, hopper, rot_0,one_mul]
lemma on_east(u:ℝ): trueS (side k u):= suit_mul (special_h k _) (suit_mul (qZ k) (sheetL.special _))
lemma east_low (h:u≤1/2): cap (side k u)= swivelC (orb k) (B_theme (α0 u)):=by rw [side,cap_side,beta_lo0 h,neg_zero,zero_div,hopper,rot_0,Matrix.transpose_one,mul_one,one_mul,cap_side]; rfl
lemma east_high(h:1/2≤u):cap (side k u)= tap k (1-β0 u):=by
 rw [side,height,comp_apply,alpha_hi0 h,sheetL.tail,cap_side, cap_side, St.2, show Yₖ k*Music.basis*(Yₖ k)ᵀ=wave k from rfl,← close_t]; have he:= mix_shift k (-β0 u) 1; rw [he]; congr 1; ring
lemma topp : ∃ X:ℝ→Op Slot,Friendly Hotel X∧ X 0=S∧ X 1=side k 1∧ ∀x∈Hotel, trueS (X x)∧ cap (X x)= Music.basis:=by
 obtain ⟨V,H,θ,T,v⟩:=cap_path S (side k 1) St.1 (on_east k 1) (by rw [east_high k (by norm_num : (1:ℝ)/2≤1),β_1,sub_self,open_t,St.2]); exact ⟨V,H,θ,T, by rw [St.2] at v; exact v⟩

private structure Host (A:ℝ×ℝ→Op Slot)(k:Fin 5):Prop where
 left(x)(p:x∈Hotel): A (0,x)=height x
 low(x)(p:x∈Hotel): A (x,0)=starPath k x*Y
 high(x)(p:x∈Hotel):cap (A (x,1))=Music.basis
 right(x)(p:x∈Hotel): A (1,x)=side k x
 rail (x)(p:x∈sqX): trueS (A x)
 smooth: Friendly sqX A
private lemma host : ∃ A,Host A k:=by
 let l:=height; let r:=side k; let b(x:ℝ):=starPath k x*Y; obtain ⟨t,h,g,p,w⟩:=topp k
 let V:=sky l b t r; have hx : Compat l b t r:=by
    constructor
    · unfold b l height starPath; rw [(anchor_s k).head,triple_one,one_mul,comp_apply,α_0,sheetL.head]
    · rw [g]; unfold l height; rw [comp_apply,alpha_hi0 (by norm_num : (1:ℝ)/2≤1),sheetL.tail]
    · unfold b r starPath; rw [(anchor_s k).tail,start_side]; simp only [Yₖ,matter_matrix]
    · exact p.symm
 have ht:=sky_stock l b t r hx -- issue placeholders have
 have he : Friendly sqY V:=by
    have hg : Friendly sqX V:=sky_law _ _ _ _ (fun i _=> sheetL.smooth.contDiffAt.comp i (jog_smooth _ _).contDiffAt) (fun i _=> (smooth_p k).contDiffAt.mul contDiffAt_const) h (fun i _=> by
       unfold r side; refine (((smooth_h k).contDiffAt.of_le le_top).comp i (f:=fun x=> -β0 x/2) (by unfold β0; fun_prop)).mul (contDiffAt_const.mul (sheetL.smooth.contDiffAt.comp i (jog_smooth _ _).contDiffAt)))
    exact fun x u=> hg x u.1 -- tune position
 have hu(x:ℝ×ℝ)(p:x∈sqY):trueS (V x):=by
    obtain ⟨a,b'⟩:=x; obtain rfl|rfl|rfl|rfl:a=0∨a=1∨b'=0∨b'=1:=p.2; all_goals obtain ⟨u,v⟩:= p.1
    rw [show V _=l b' from (ht _).1]; exact sheetL.special _
    rw [show V _=r b' from (ht _).2.2.2]; exact on_east ..
    rw [show V _=b a from (ht _).2.1]; exact suit_mul (star_gate ..) Yt.1
    rw [show V _=t a from (ht _).2.2.1]; exact (w _ u).1
 obtain ⟨X,H,q,f⟩:= squareU.key V he hu; exact ⟨X,⟨fun x p=> (q (west x p)).trans (ht x).1,fun x p=> (q (south x p)).trans (ht x).2.1, fun x p=> (congrArg cap ((q (north x p)).trans (ht x).2.2.1)).trans (w x p).2,fun x p=> (q (east x p)).trans (ht x).2.2.2,f,H⟩⟩

-- simple combined path (X read via light). also on all v not clipped (stationary at 2 automatically).
private abbrev πPath(q:ℝ×ℝ):= (host k).choose (q.1,bound q.2)
private abbrev DPath(k:Fin 5)(s:ℝ × ℝ):= hopper k (bound s.1 * bound (s.2-1)/2) * πPath k s
def dict (q:ℝ×ℝ) := if k=0 then B_theme (α q.2) else cap (DPath k q)
private lemma rail_h (q:ℝ×ℝ)(p:q.1∈ Hotel) : trueS (πPath k q) ∧ ContDiffAt ℝ ∞ (πPath k) q:=by
 have h:= (host k).choose_spec; let f(s:ℝ×ℝ):= (s.1,bound s.2); have he:f q∈sqX:=⟨p,mid_bound _⟩; exact ⟨h.rail _ he,(h.smooth (f q) he).comp q (f:=f) (by unfold f; fun_prop)⟩ -- comp arg parser
lemma dict_s (q:ℝ×ℝ)(p:q.1∈Hotel): Spin.Sym (dict k q)∧ContDiffAt ℝ ∞ (dict k) q:=by
 by_cases h:k=0; swap; · have he:= (rail_h k q p); rw [show dict k= cap ∘ DPath k from funext fun _=> if_neg h]; exact ⟨capgate _ (suit_mul (special_h k _) he.1),cap_s.contDiffAt.comp q ((((smooth_h k).contDiffAt.of_le le_top).comp q (f:=fun y:ℝ×ℝ=>bound y.1 * bound (y.2-1)/2) (by fun_prop)).mul he.2) ⟩
 rw [show dict k=(fun q=> B_theme (α q.2)) from funext fun _=> if_pos h]; exact ⟨shape_cost.special _, shape_cost.smooth.contDiffAt.comp q (f:=fun x:ℝ × ℝ=> α x.2) (by fun_prop)⟩
lemma stationary (x:ℝ)(u:ℝ):dict 0 (x,u)= B_theme (α u):=if_pos rfl
@[simp] lemma light0(x:ℝ):light 0 x=embed:=by unfold light; rw [anchor,if_pos rfl,act_one]
private lemma before (x:ℝ)(h:k≠0)(p:u≤1):dict k (x,u)=cap (πPath k (x,u)):=by simp only [dict,if_neg h,DPath, bound_lo (show u-1≤1/8 by linarith),mul_zero,zero_div,hopper,rot_0,one_mul]
lemma x_z(h:u∈ Hotel): dict k (u,0)=fullM (light k u):=by
 by_cases h':k=0; · subst k; rw [stationary,light0,al0,shape_cost.head]
 rw [before k u h' (by norm_num),πPath,bounds01.1, (host k).choose_spec.low _ h, shape_light]
lemma pathII (h:u ∈ Hotel)(p:1≤v): dict k (u,v)=tap k (bound u* bound (v-1)):=by
 by_cases h':k=0; · subst k; rw [tap_idle,stationary,alpha_final (by linarith),shape_cost.tail]
 rw [dict,if_neg h',DPath,cap_side,show cap (πPath k (u,v))= Music.basis from ?_,half_cong]; change cap ((host k).choose (u,bound v))=_; rw [bound_hi (by linarith)]; exact (host k).choose_spec.high _ h
lemma edge_1 (h:u∈ Hotel): dict k (u,1)=Music.basis:=by rw [pathII k h le_rfl,sub_self,bounds01.1,mul_zero,open_t]
lemma edge_west (u:ℝ): dict k (0,u)= B_theme (α u):=by
 by_cases h:k=0; · subst k; exact stationary ..
 rw [dict,if_neg h,DPath]; simp only [bounds01.1,zero_mul,zero_div,hopper,rot_0,one_mul]; change cap ((host k).choose (0,bound u))=_; rw [(host k).choose_spec.left _ (mid_bound _ )]; rfl
lemma edge_lower (p:u≤1/2) : dict k (1,u)= swivelC (orb k) (B_theme (α u)):=by
 by_cases h:k=0; · subst k; rw [stationary,orb, Mag.center_zero, inv_one,turn_one]
 rw [before k 1 h (by linarith)]; change cap ((host k).choose (1,bound u))=_; rw [(host k).choose_spec.right _ (mid_bound _ ), east_low k ((bet_f p).trans bet_m.le)]; rfl
lemma edge_middle (p:1/2≤u)(g:u≤1): dict k (1,u)=tap k (1-β u):=by
 by_cases h:k=0; · subst k; rw [stationary,alpha_final p, tap_idle,shape_cost.tail]
 rw [before k 1 h g]; change cap ((host k).choose (1,bound u))=_; rw [(host k).choose_spec.right _ (mid_bound _ ), east_high k ((bet_f p).trans' (le_of_eq bet_m.symm))]; rfl
lemma edge_upper (p:1≤u): dict k (1,u)=tap k (bound (u-1)):=by rw [pathII k H1 p,bounds01.2,one_mul]
end YM.CF.BPress.Lute.Kite
#print axioms YM.CF.BPress.Lute.Kite.dict_s
