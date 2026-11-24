import YM.CF.BPress.Grid.Skeleton
import YM.CF.BPress.Lute.Dance
import YM.CF.Cubes.Ferry
import YM.CF.BPress.Slice
/- Unit-vector layer interpolation budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Dial Grid Lute.Kite MeasureTheory RG
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
abbrev Sprout:= Ballot
abbrev pen(B:Vect)(p:‖B‖=1):Sprout:=⟨B,mem_sphere_zero_iff_norm.mpr p⟩
abbrev Seed : Sprout:=Dial.apex
lemma seed_value: Seed.val=Lute.Kite.embed:=rfl
lemma scaled_s(g k:E)(v:Sprout) : scaledV (g*k) v=scaledV g (scaledV k v):=Subtype.ext (turn_seq ..)
lemma scaled_one(v:Sprout):scaledV 1 v=v:=Subtype.ext (by change acts (fund 1) _=_; rw [fund_one,act_one])
lemma scaled_d(g:E)(x y:Sprout):dist (scaledV g x) (scaledV g y)=dist x y:= (spinV g).isometry.dist_eq x.val y.val
lemma scaled_chord (x y:E)(v:Sprout):dist (scaledV x v) (scaledV y v) ≤ sphereRate*chord x y:=by
 rw [Subtype.dist_eq,dist_eq_norm]; apply (turn_price x y v.val).trans; rw [vote_unit,mul_one]; exact sphereRate_cost.top .. -- tune no voter type scope
lemma scaled_meas : Measurable (fun x:E×Sprout=> scaledV x.1 x.2):= scaled_cont.measurable
lemma drive : ∃ D:Delivery group 4 Sprout, D.ship=fun s t=> scaledV t⁻¹ s:=by
 let k:ℝ≥0:=⟨sphereRate,sphereRate_cost.positive.le⟩; refine ⟨⟨_,scaled_one', fun g a b=>?_, fun g=> scaled_d g⁻¹,k,?_,?_ ,?_⟩,rfl⟩ -- use dot? edit
 · rw [mul_inv_rev, scaled_s] -- tune
 · intro v x y; have hp:=scaled_chord x⁻¹ y⁻¹ v; rwa [chord.inv] at hp
 · exact scaled_cont.comp (f:=fun x : Ballot × E=> (x.2⁻¹,x.1)) (continuous_snd.inv.prodMk continuous_fst)
 intro L; have he: dimH (rim 4) < ↑(9:ℕ):= lt_of_le_of_lt (rim_price 3) (by norm_num); obtain ⟨K,p⟩:= Smooth.sphere_extension Seed.val (vote_unit _) (table_compact 4) (rim_compact 4) Set.inter_subset_left dim_vect he L -- dimension p
 refine ⟨K,fun s h f w=>?_⟩; obtain ⟨g,p,T,v⟩:= p s h (fun i=> (f i).val) (LipschitzOnWith.of_dist_le_mul (fun i u j t=> w.dist_le_mul i u j t)) (fun x _=> vote_unit _)
 let H(x:Desk 4):Ballot:=if t:x∈table 4 then ⟨_, mem_sphere_zero_iff_norm.mpr (v x t)⟩ else Seed; have ht(x)(t:x∈table 4): (H x).val=g x:=by unfold H; rw [dif_pos t]
 exact ⟨H,LipschitzOnWith.of_dist_le_mul fun x u y a=>by rw [Subtype.dist_eq,ht _ u,ht _ a]; exact T.dist_le_mul x u y a,fun i t=> Subtype.ext ((p t).trans (ht _ ((h t).1)).symm)⟩
where scaled_one'(v:Sprout): scaledV (1:E)⁻¹ v=v:=by rw [inv_one,scaled_one]
variable {s:Side}
abbrev Zips:= drive.choose
lemma Z_ship (x :Sprout)(b:E) : Zips.ship x b=scaledV b⁻¹ x:=by rw [drive.choose_spec]
-- solid guards on local supports. Holder=weak Slow on this bond inclusive.
abbrev marks(s:Side):= Site s→ Sprout
def shuffle(M:Mach s)(H:marks s): marks s:= fun i=>scaledV (M i) (H i)
def urgent(U:Micro s)(x:Link s)(H:marks s):ℝ:=dist (scaledV (U x) (H (x.1+step x.2))) (H x.1)
lemma urgent_flip (U:Micro s)(x:Link s)(H:marks s): dist (Zips.ship (H x.1) (U x)) (H (x.1+step x.2))=urgent U x H:=by rw [Z_ship,dist_comm,← scaled_d (U x),←scaled_s, mul_inv_cancel,scaled_one]; rfl -- tune
lemma urgent_norm (U:Micro s)(x:Link s)(H:marks s): ‖turn (U x) (H (x.1+step x.2)).val-(H x.1).val‖=urgent U x H:=by rw [urgent,Subtype.dist_eq,dist_eq_norm]; rfl
lemma urgent_s (U:Micro s)(x:Link s)(H:marks s)(M:Mach s):urgent (gauge M U) x (shuffle M H)=urgent U x H:=by unfold urgent shuffle Lattice.gauge; rw [←scaled_s, mul_assoc, inv_mul_cancel, mul_one, scaled_s,scaled_d]
def Alert(U:Micro s)(R: Support s)(H:marks s)(K:ℝ):Prop:=∀ i∈ inside R, urgent U i H≤K
variable {U:Micro s}
def Rings(U:Micro s)(R:Support s)(K:ℝ):Prop:=∀ i:Face (Per s),touched i⊆R → group.chord (faceValue U i)≤K
-- `group.chord` local even when not guards. `k.r=1`
lemma ζ(U:Micro s)(x:Site s)(i j:Axis) : tension U 1 1 x i j=group.chord (travel U x (square i j)):=by
 let a:=U (x,i); let b:=U (x+step i,j); let c:=U (x,j); let d:=U (x+step j,i)
 have he: travel U x (square i j)=a*b*(c*d)⁻¹:=by
    simp only [square,travel,Step.pos_read, Step.vec_pos, Step.neg_read,Step.vec_neg,mul_one]; rw [show x+step i+step j-step i=x+step j by abel, show x+step i+step j+-step i-step j=x by abel]; rw [mul_inv_rev]; change _=a*b*(d⁻¹*c⁻¹); rw [mul_assoc]
 unfold tension; rw [line_one,line_one,line_one,line_one,hop_one,hop_one]; rw [he]; rfl
lemma rings_cost (d:ℝ)(S:Support s)(h:Guard U d): Rings U S (sphereRate*d):=by rintro ⟨x,⟨⟨i,j⟩,u⟩⟩ a; exact (sphereRate_cost.con _).trans (mul_le_mul_of_nonneg_left (h.1 x _ _ u.ne) sphereRate_cost.positive.le) -- binder tune
lemma rings_g {X:Support s}{a:ℝ}(h:Rings U X a)(M:Mach s):Rings (Lattice.gauge M U) X a:= fun i p=> by rw [face_gauge, group.chord_conj]; exact h i p
end YM.CF.BPress.Meadow
