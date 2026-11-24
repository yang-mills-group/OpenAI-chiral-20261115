import YM.CF.BProof.Angular.Slice

/-! Local sweep in any one interval of time. Reads only normal links there. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge SU MeasureTheory Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {s : Side} (a x : Per s)(p : Space s)

/-- upper slice from the given lower face. -/
abbrev atL (d:ℕ) := a+(d:Per s)
lemma atL_succ (d:ℕ) : atL a (d+1)=atL a d+1:=by simp [atL,add_assoc]
variable (l:ℕ)(U:Config G s)

def broom (U:Config G s) : ℕ → E
 | 0 => 1
 | d+1 => broom U d * U (vert (atL a d) p) -- recursion arguments? syntax?
@[fun_prop] lemma broom_m (d:ℕ) : Continuous (fun U : Config G s=>broom a p U d):=by induction d with |zero=>unfold broom; fun_prop|succ d ih=>simp_rw [broom]; fun_prop

lemma broom_local (d:ℕ)(h:d≤l) (V:Config G s)(he:∀ d<l,U (vert (atL a d) p)=V (vert (atL a d) p)): broom a p U d=broom a p V d:=by
 induction d with|zero=>rfl|succ d ih=> exact congrArg₂ (·*·) (ih (by omega)) (he d (by omega)) -- maybe defeq?
lemma broom_gate (d:ℕ)(g:Site s → E) : broom a p (Lattice.gauge g U) d=g (join a p)*broom a p U d*(g (join (atL a d) p))⁻¹:=by
 induction d with | zero=>simp [atL,broom]|succ d ih=>
   rw [broom,ih,broom,atL_succ]; unfold Lattice.gauge vert; dsimp only; rw [← join_step]; group

/-- frame for axial coordinates. Conditional on normal links, put the given frame at
relative index `d`. For d=l this sweeps the normals towards the upper face. NB: though
computed with `broom` spanning from the left, intervals cancel so only the swept forest
links are needed. -/
def sweep (d:ℕ)(b:E) := b * (broom a p U d)⁻¹ * broom a p U (along a x)
@[fun_prop] lemma sweep_m (d:ℕ)(b:E) : Continuous (fun U : Config G s=>sweep a x p U d b):=by unfold sweep; fun_prop
lemma sweep_base {d:ℕ}(hd:along a x=d)(b:E) : sweep a x p U d b=b:=by simp [sweep,hd]
lemma sweep_next (d:ℕ)(he:along a x+1<s.val)(b:E) : sweep a (x+1) p U d b=sweep a x p U d b * U (vert x p):=by
 rw [sweep,sweep,along_succ he,broom]; simp [atL,mul_assoc]
lemma sweep_gate (d:ℕ) (b:E)(g:Site s→E): sweep a x p (Lattice.gauge g U) d (b*(g (join (atL a d) p))⁻¹)=sweep a x p U d b*(g (join x p))⁻¹ :=by unfold sweep; rw [broom_gate,broom_gate]; simp only [atL,add_along]; group
lemma sweep_reads (d:ℕ)(hx:along a x≤l)(hd:d≤l)(V:Config G s)(he:∀ d<l,U (vert (atL a d) p)=V (vert (atL a d) p))(b:E) : sweep a x p U d b=sweep a x p V d b := by unfold sweep; rw [broom_local a p l U _ hx V he,broom_local a p l U _ hd V he]
lemma local_sweep (d:ℕ)(hx:along a x≤l)(hd:d≤l)(he:l+1<s.val)(V:Config G s)(h:Agrees (↑(strip a l)) U V)(b:E) : sweep a x p U d b=sweep a x p V d b:=by
 apply sweep_reads a _ p l U d hx hd; intro d hv; specialize h (vert (atL a d) p); have e:= (wet_v (p:=p) (x:=atL a d) a _ he).mpr (by rw [along_add a (by omega)]; exact hv); exact h e.1 e.2

/-- Reads forward only (for forest proof). -/
lemma sweep_reads_from0 (l:ℕ)(hx:along a x≤l)(V:Config G s)(he:∀ x, along a x<l → U (vert x p)=V (vert x p))(hl:l<s.val)(b:E): sweep a x p U 0 b=sweep a x p V 0 b:= sweep_reads a _ p l U 0 hx (by omega) V (fun d hd=>he _ (by rw [along_add a (by omega)]; exact hd)) b
private lemma read_up (V:Config G s)(d:ℕ)(hl:l<s.val)(he:∀ x, l-d ≤ along a x → along a x<l → U (vert x p)=V (vert x p))(b:E) (hv:d≤l): sweep a (atL a (l-d)) p U l b=sweep a (atL a (l-d)) p V l b := by
 induction d with
 | zero=> rw [Nat.sub_zero,sweep_base _ _ _ _ (along_add a hl),sweep_base _ _ _ _ (along_add a hl)]
 | succ d ih=>
   set x := atL a (l-(d+1)); have hx:along a x=l-(d+1):=along_add a (by omega)
   have hg: l-d=l-(d+1)+1:=by omega
   specialize ih (fun x e h=> he x (by omega) h) (by omega); rw [hg,atL_succ] at ih
   have g: along a x+1<s.val:=by omega
   change sweep a (x+1) p U l b=sweep a (x+1) p V l b at ih; rw [sweep_next a x _ _ _ g,sweep_next a x _ _ _ g,he _ hx.ge (by omega)] at ih; exact mul_right_cancel ih
lemma sweep_reads_fromL (u:ℕ)(hx:along a x≤l)(hx':u≤along a x)(V:Config G s)(he:∀ x,u≤along a x→along a x<l→U (vert x p)=V (vert x p))(hl:l<s.val)(b:E): sweep a x p U l b=sweep a x p V l b:=by
 let d:=l-along a x; have hv:l-d=along a x:=by unfold d; omega
 have hu:= read_up a p l U V d hl (fun x' e h=> he x' (by omega) h) b (Nat.sub_le ..); rw [hv] at hu; simpa only [atL,add_along] using hu
end YM.CF.BProof.Angular
