import YM.CF.BProof.Angular.Broom
import YM.CF.BProof.Template

/-! Framing on each of the two sides of an N band. For writing the noncommutative test
before change of variables. Continuous in U for sweep with fixed input g. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge Mag CF.BProof.Face SU MeasureTheory Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (a x : Per s)(l:ℕ)(U:Config G s)

abbrev cut := l/2
abbrev Left := along a x≤cut l
/-- value false = left face -/
def flag : Bool := decide (¬ Left a x l)
abbrev basepoint (b:Bool) := if b then l else 0
def front (b:Bool) := atL a (basepoint l b)
@[simp] lemma front_left : front a l false=a:=by simp [front,atL,basepoint]
@[simp] lemma front_right : front a l true=atL a l:=rfl
abbrev Eyes (s : Side) := Bool → Frame s
lemma cut_lt (h:0<l) : cut l<l:=by unfold cut; omega
lemma onside (b:Bool)(hl:0<l)(hv:l<s.val) : flag a (front a l b) l=b:=by
 cases b
 · simp only [front_left,flag,Left,along_self,Nat.zero_le,not_true_eq_false,decide_false]
 rw [front_right]; simp only [flag,Left,along_add _ hv,not_le,cut_lt l hl,decide_true]
@[simp] lemma flag_false : flag a x l=false ↔ along a x≤cut l:=by simp [flag,Left]
@[simp] lemma flag_true : flag a x l=true ↔ cut l<along a x:=by simp [flag,Left]

/-- frames extended to band sites by the prescribed cut gauge. Nonband values are
irrelevant but a flag is assigned to make pointwise covariance hold globally. -/
def stage (g:Eyes s)(x:Site s) := let b:=flag a (time x) l; sweep a (time x) (space x) U (basepoint l b) (g b (space x))
def eye (g:Site s→E) : Eyes s := fun b p=>g (join (front a l b) p)
@[fun_prop] lemma stage_m : Continuous (Function.uncurry (stage (s:=s) a l)):=by
 apply continuous_pi; intro p; unfold stage Function.uncurry sweep; fun_prop
lemma stage_at (g:Eyes s)(x:Per s)(p:Space s): stage a l U g (join x p)=sweep a x p U (basepoint l (flag a x l)) (g (flag a x l) p):=by simp [stage]
lemma stage_set (g:Eyes s)(b:Bool)(p:Space s)(hl:0<l)(hv:l<s.val): stage a l U g (join (front a l b) p)=g b p:=by
 rw [stage_at,onside a l b hl hv]; apply sweep_base; apply along_add; cases b <;> simp [basepoint,hv,Nat.zero_lt_of_lt hv] -- tune
lemma stage_read (g:Eyes s)(hx:along a x≤l)(he:l+1<s.val)(V:Config G s)(h:Agrees (↑(strip a l)) U V)(p:Space s) : stage a l U g (join x p)= stage a l V g (join x p):=by
 rw [stage_at,stage_at]; apply local_sweep a _ _ l _ _ hx _ he _ h; cases flag a x l<;>simp [basepoint]
lemma stage_local (g:Eyes s)(he:l+1<s.val)(V:Config G s)(h:Agrees (↑(strip a l)) U V) : Set.EqOn (stage a l U g) (stage a l V g) ↑(strip a l):= fun x hx=> by simpa only [join_time_space] using stage_read a _ l U g (mem_strip.mp hx) he V h (space x)
lemma stage_normal (g:Eyes s)(he:along a x+1<s.val)(hx:along a x ≠ cut l)(p:Space s): Lattice.gauge (stage a l U g) U (vert x p)=1:=by
 unfold Lattice.gauge vert; dsimp only; rw [← join_step,stage_at,stage_at]
 have h : flag a (x+1) l=flag a x l:=by unfold flag Left; rw [along_succ he]; congr! 1; omega
 rw [h,sweep_next a _ _ U _ he]; exact mul_inv_cancel _
lemma stage_rot (g t) : stage a l (Lattice.gauge t U) (g*(eye a l t)⁻¹)=stage a l U g*t⁻¹ := by
 ext1 x; unfold stage; dsimp; simp only [eye,front,sweep_gate,join_time_space]
lemma stage_layers (g:Eyes s)(x:Site s): stage a l U g x=g (flag a (time x) l) (space x)*stage a l U 1 x := by unfold stage sweep; dsimp only; simp [mul_assoc]
lemma stage_move (g:Eyes s)(p:Space s): stage a l U g (join x p)= g (flag a x l) p*stage a l U 1 (join x p):=by rw [stage_layers]; simp only [space_join,time_join] -- rw expands RHS too?
lemma stage_identity (he:l<s.val) (hp:∀ x p,along a x<l→along a x≠cut l → U (vert x p)=1) : Set.EqOn (stage a l U 1) 1 ↑(strip a l):= by
 have e (x:Per s)(p:Space s)(b:Bool): sweep a x p (1:Config G s) (basepoint l b) 1=1 := by
   have h(d:ℕ):broom a p (1:Config G s) d=1:= by induction d with |zero=>rfl|succ i ih=>simp [broom,ih]
   simp [sweep,h]
 intro x hx; have hv:= mem_strip.mp (Finset.mem_coe.mp hx); unfold stage; dsimp only [Pi.one_apply]; cases g: flag a (time x) l
 · have hh:= (flag_false ..).1 g
   exact (sweep_reads_from0 a _ (space x) U (cut l) hh (1:Config G s) (fun v h=> hp v _ (lt_of_lt_of_le h (Nat.div_le_self ..)) h.ne) (lt_of_le_of_lt (Nat.div_le_self ..) he) 1).trans (e _ _ false)
 have hh:= (flag_true ..).1 g; exact (sweep_reads_fromL a _ (space x) l U (cut l+1) hv hh 1 (fun x h u=> hp x _ u (by omega)) he 1).trans (e _ _ true)
end YM.CF.BProof.Angular
