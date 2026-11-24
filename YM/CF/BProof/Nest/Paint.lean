import YM.CF.BProof.Nest.Vote
import YM.CF.BProof.Stave.Pigment
import YM.CF.Skye.Can
-- travelling law. Clear any lattice lattice site. Positive link covariance extends reflected steps. Cost expressed at S*. Use finite orient keys.
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Wilson Lattice Function Finset Filter Nerve -- RG?
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators Classical
variable {n:Side}{s r C:ℕ}{δ u:ℝ}{G:Gauge}{b x:Site n}
def Wire (a:Site n)(p:Lattice.Order)(U:Config G n)(x:Site n):= travel U a (Cube.march a x p)
lemma bumpVH (s:ℕ):King*s=4*(Halo*s)+4*s:=by unfold King; ring
lemma duct (h:Law G u δ (King*s))(m:SmallN s n)(p:0<s)(U:Config G n) (d:Axis)(o o':Lattice.Order)(g:Clear u (King*s) U b)(a:separation x b≤ Halo*s)(N:separation (x+step d) b≤ Halo*s):cd G (Wire b o U x * U (x,d)) (Wire b o' U (x+step d)) ≤ δ:=by
 let X:=Cube.march b x o; let y:= x+step d; let Y:=Cube.march b y o'; let Z:= [posDir d]
 have he:travel U b (X++Z)=Wire b o U x* U (x,d):= by rw [travel_append, Cube.arrive]; simp only [Z, travel,Step.pos_read,mul_one]; rfl
 rw [←he]; refine h.gain b U g (X++Z) Y ?_ ?_ ?_
 · let k:=King*s; have hk:3≤n.val:=by unfold SmallN at m; omega
   rw [stop_append]; unfold X Y Cube.march Z y; rw [stop, stop,route_end,route_end,Step.vec_pos]; rw [rel_sum (x+step d) x b (by rw [separation_comm]; exact le_trans (nearV x (posDir d)) (show 1 ≤ King*s from by have h:= bumpVH s; omega)) (show separation x b≤ k from (by unfold k; have h:=bumpVH s; omega)) m]; rw [add_sub_cancel_left, Cube.lift_step hk d]; abel
 · have ht:= Cube.march_len b x o a; change X.length ≤_ at ht; rw [List.length_append]; change X.length+1≤ _; have h:=bumpVH s; omega
 have ht:= Cube.march_len b y o' N; exact ht.trans (by have h:=bumpVH s; omega)
lemma wire_cont (a:Site n)(p:Lattice.Order)(x:Site n): Continuous (fun U:Config G n=> Wire a p U x):= Cube.travel_cont _ _
lemma wire_cost (o:Lattice.Order)(u:separation x b ≤ C) : LocalOn (region n b (4*C)) (fun U:Config G n=> Wire b o U x):=by
 intro U V h; refine travel_local b _ U V (agrees_mono h ?_); intro y hy; exact (reg_in ..).2 ((plank (Cube.march b x o) b y hy).trans (Cube.march_len b x o u))

-- ℛ sym law general n and any translation, reversed by Sweep.PolarT.charge included.
def Opts (a:Signed)(b:Site n)(p:Bool)(U: Config SU.group n) : Config SU.group n:= Spire.polarT p ∘ pull a b U
-- facet keys
lemma facet_eq(a:Signed)(b:Site n): ⇑(facet a b)=affine a b:= funext fun x=>add_comm b _
lemma opt_read (d:Step)(a:Signed)(b:Site n)(p:Bool)(U:Config SU.group n)(x:Site n) : d.read (Opts a b p U) x=Spire.polarT p ((d.rotate a).read U (facet a b x)):=by
 rw [facet_eq, ← Step.pull_read]; simp only [Opts,Step.read]; split; exact (map_inv ..).symm; rfl
lemma opt_link(d:Axis)(a:Signed)(b:Site n)(p:Bool)(U:Config SU.group n)(x:Site n):(Opts a b p U) (x,d)=Spire.polarT p (((posDir d).rotate a).read U (facet a b x)):= opt_read (posDir d) .. -- tune
lemma opt_next(d:Step)(a:Signed)(b x:Site n): facet a b (x+d.vec)=facet a b x + (d.rotate a).vec:=by simp only [facet_apply,Step.vec_rotate,a.act_add,add_assoc]
lemma opt_travel(a:Signed)(b:Site n)(p:Bool)(U:Config SU.group n)(x:Site n)(W:Walk): travel (Opts a b p U) x W=Spire.polarT p (travel U (facet a b x) (W.map (·.rotate a))):=by
 induction W generalizing x with | nil=>exact (map_one _).symm| cons h W ih=>simp only [List.map_cons,travel, opt_read, ih,opt_next,map_mul]
lemma opt_mark (t:SmallN s n)(h: separation x b ≤ Halo*s) (a:Signed)(w:Site n)(p:Bool)(U:Config SU.group n)(o:Lattice.Order) : Wire b o (Opts a w p U) x=Spire.polarT p (Wire (facet a w b) (orderEquiv a o) U (facet a w x)):=by
 rw [Wire,Wire,opt_travel]; unfold Cube.march; congr 2; rw [send_route (b:=0),rel_turn _ _ _ _ (by have h:=bumpVH s; omega) t]; simp [affine]
lemma opt_p (a:Signed)(b:Site n)(p:Bool)(U:Config SU.group n)(x:Site n): Clear u r (Opts a b p U) x ↔ Clear u r U (facet a b x):=by
 unfold Opts Clear; rw [Skye.flagsQ]; rw [← Work.H03.flags_send a b u U, ← facet_eq]; set T:= facet a b; have he:region n (T x) r=(region n x r).image T:=by ext i; obtain ⟨i,rfl⟩:=T.surjective i; rw [mem_image]; simp only [T.injective.eq_iff, exists_eq_right, reg_in]; unfold T; rw [facet_keeps]
 rw [he,Finset.disjoint_image T.injective]
end YM.CF.BProof.Mesh.Nest
