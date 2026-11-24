import YM.CF.BPress.Dirichlet
import YM.CF.BPress.Grid.Line
/-!
Horizontal slices of a true Micro field. The same coordinates are used for sections, frame lookups and columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory Lattice Wilson RG SU Mag Cube Grid
open scoped Topology BigOperators Classical Matrix
abbrev SpatialDir:= Fin 3
abbrev FlatLink (s : Side):= Tri s × SpatialDir
abbrev Horiz (s : Side):= Grid.GaugeField group 3 s
abbrev HFrame (s : Side) := Tri s→ E
abbrev Mach (s : Side) := Site s→ E
variable {s : Side}
-- just at the given time slice. Use only faces with BOTH axes spatial later.
def fl (t : Per s) (p : FlatLink s) : Link s := (event t p.1,p.2.succ)
def vl (t : Per s) (p : Tri s) : Link s := (event t p,0)
def horizontal (t : Per s) (U : Micro s) : Horiz s:=fun i=> U (fl t i)
def normal (t : Per s) (U : Micro s) (p : Tri s) := U (vl t p)
@[fun_prop] lemma cont_horizontal (t : Per s) : Continuous (horizontal t):= continuous_pi fun i=> continuous_apply _
@[fun_prop] lemma cont_normal (t : Per s) : Continuous (normal t):= continuous_pi fun i=> continuous_apply _
@[simp] lemma vl_eq {u v:Per s}{i j:Tri s} : vl u i=vl v j ↔ u=v ∧ i=j:=by simp [vl]
@[simp] lemma fl_eq {u v:Per s}{i j:FlatLink s} : fl u i=fl v j ↔ u=v ∧ i=j:=by rcases i with ⟨i,p⟩; rcases j with ⟨j,q⟩; simp [fl,and_assoc]
@[simp] lemma fl_ne_vl (u v : Per s) (i : FlatLink s) (j : Tri s) : fl u i ≠ vl v j:= fun e=>Fin.succ_ne_zero i.2 (congrArg Prod.snd e)
lemma link_cases (e : Link s) : (∃ i : FlatLink s, e=fl (e.1 0) i) ∨ e=vl (e.1 0) (Fin.tail e.1):=by rcases e with ⟨x,i⟩; dsimp; refine Fin.cases ?_ ?_ i; right; simp [vl]; intro i; left; exact ⟨(Fin.tail x,i),by simp [fl]⟩
lemma Agrees.fl {S : Support s}{U V : Micro s}(h : Lattice.Agrees S U V) (t : Per s)(p : ∀ i,event t i∈S) : horizontal t U=horizontal t V:=funext fun i=> h _ (p _) (by simpa [BPress.fl] using p (glide i.2 i.1))
lemma gauge_trans (p q : Mach s) (U : Micro s) : Lattice.gauge p (Lattice.gauge q U)= Lattice.gauge (p*q) U:= by funext i; simp only [Lattice.gauge, Pi.mul_apply]; group
@[simp] lemma gauge_self (U : Micro s) : Lattice.gauge (1: Mach s) U=U:= by funext i; simp [Lattice.gauge]
@[fun_prop] lemma gauge_joint : Continuous fun x:Mach s × Micro s=> Lattice.gauge x.1 x.2:=by unfold Lattice.gauge; fun_prop

-- fields within slice. Use hop.
def adjust (h : HFrame s) (U : Horiz s) : Horiz s:=fun i=> h i.1 * U i * (h (hop i.1 i.2 1))⁻¹
def confine (t : Per s) (p : Mach s) : HFrame s:=fun x=> p (event t x)
@[fun_prop] lemma adj_cont : Continuous fun x:HFrame s × Horiz s=> adjust x.1 x.2:=by unfold adjust; fun_prop
lemma adj_gauge (t : Per s) (p : Mach s) (U : Micro s) : horizontal t (Lattice.gauge p U)= adjust (confine t p) (horizontal t U):= by
 funext i; simp [Lattice.gauge,adjust,confine,horizontal,fl,hop_glide]
lemma vl_gauge (t : Per s) (p : Mach s) (U : Micro s) (x : Tri s) : normal t (Lattice.gauge p U) x=confine t p x * normal t U x * (confine (t+1) p x)⁻¹ :=by simp [Lattice.gauge,confine,normal,vl]
lemma adjust_seq (p q : HFrame s) (U : Horiz s) : adjust p (adjust q U) = adjust (p*q) U:= by funext i; simp only [adjust,Pi.mul_apply]; group
@[simp] lemma adjust_one (U : Horiz s) : adjust 1 U=U:=by funext i; simp [adjust]
lemma adjust_center (r : Fin 5) (U : Horiz s) : adjust (fun _=>center r) U=U:=by funext i; unfold adjust; rw [center_comm,mul_inv_cancel_right]

def plaq (U : Horiz s)(x : Tri s)(i j : SpatialDir) := U (x,i)*U (hop x i 1,j)*(U (hop x j 1,i))⁻¹*(U (x,j))⁻¹
@[fun_prop] lemma plaq_cont (x : Tri s)(i j : SpatialDir) : Continuous fun U: Horiz s=> plaq U x i j:=by unfold plaq; fun_prop
lemma plaq_tension (U : Horiz s)(x : Tri s)(i j : SpatialDir): group.chord (plaq U x i j)=tension U 1 1 x i j:=by simp only [plaq,tension,line_one,chord]; rw [mul_inv_rev,←mul_assoc (U _ * _)]
lemma transform_plaq (h : HFrame s)(U : Horiz s)(x : Tri s)(i j : SpatialDir) : plaq (adjust h U) x i j=h x*plaq U x i j*(h x)⁻¹ := by simp only [plaq,adjust]; rw [hop_comm x i j]; group
-- use this for all squares
lemma Travel.price (x : Site s) (i j : Axis)(U : Micro s) : travel U x (square i j)= U (x,i)*U (x+step i,j)*(U (x+step j,i))⁻¹*(U (x,j))⁻¹:=by
 simp only [square, travel, Step.pos_read, Step.vec_pos, Step.neg_read, Step.vec_neg]; simp [show x+ step i+ step j=x+step j + step i by abel,mul_assoc]
lemma hq_eq (t : Per s)(U : Micro s)(x : Tri s)(i j : SpatialDir) : travel U (event t x) (square i.succ j.succ)= plaq (horizontal t U) x i j:=by rw [Travel.price]; simp [plaq,hop_glide,fl,horizontal]
lemma nq_eq (t : Per s) (U : Micro s)(x : Tri s)(i : SpatialDir) : travel U (event t x) (square 0 i.succ)= normal t U x * horizontal (t+1) U (x,i) * (normal t U (hop x i 1))⁻¹ * (horizontal t U (x,i))⁻¹:=by rw [Travel.price]; simp [normal,horizontal,hop_glide,fl,vl]
lemma nq_price (t : Per s)(U : Micro s)(x : Tri s)(i : SpatialDir): group.chord (travel U (event t x) (square 0 i.succ))=chord (normal t U x* horizontal (t+1) U (x,i)) (horizontal t U (x,i)*normal t U (hop x i 1)) := by rw [nq_eq,chord,mul_inv_rev,←mul_assoc (_ * _)]
lemma plaq_close (U V : Horiz s)(x : Tri s)(i j : SpatialDir){r:ℝ}(p : chord (U (x,i)) (V (x,i))≤r)(f : chord (U (x,j)) (V (x,j))≤r)(t: chord (U (hop x i 1,j)) (V (hop x i 1,j))≤r)(v: chord (U (hop x j 1,i)) (V (hop x j 1,i))≤r) : chord (plaq U x i j) (plaq V x i j) ≤ 4*r:=by
 apply (chord.product ..).trans; apply le_trans (add_le_add (chord.product ..) le_rfl); apply le_trans (add_le_add (add_le_add (chord.product ..) le_rfl) le_rfl); simp only [chord.inv]; linarith
lemma adj_repair (p : HFrame s)(U V : Horiz s)(x : FlatLink s) : chord (adjust p U x) (adjust p V x)=chord (U x) (V x):= by simp only [adjust,chord.right,chord.left]
lemma vl_repair (p q:HFrame s)(U V : Tri s → E)(x : Tri s) : chord (p x*U x*(q x)⁻¹) (p x*V x*(q x)⁻¹)=chord (U x) (V x):=by simp

def magnetH (y : ℝ)(i : SpatialDir) : E := group.lieExp (aA y • generator i)
def magnetHoriz (s : Side) (y : ℝ) : Horiz s:= fun i=> magnetH y i.2
@[simp] lemma horiz_background (t : Per s) (y : ℝ) : horizontal t (background y)=magnetHoriz s y:= by funext i; simp [horizontal, magnetHoriz,background,fl,backgroundDir,magnetH]
lemma plaq_bg (x : Tri s)(y : ℝ)(i j : SpatialDir): plaq (magnetHoriz s y) x i j=chord.panel (generator i) (generator j) (aA y):=rfl
end YM.CF.BPress
