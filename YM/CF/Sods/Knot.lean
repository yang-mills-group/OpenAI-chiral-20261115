import YM.CF.Sods.City
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset Kea Lat Lattice Laurent Fir Rush Tulip Cube SU
open scoped Topology BigOperators Matrix ContDiff Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{i:Slot}
abbrev zp(i:Slot)(x:Key):ℂ:=(SU.z^(charge i))^x.val
lemma sir_t(d:Candle)(N:Side)(a:Axis): (matter ((waveG (d a))^(More N).val)).val=Matrix.diagonal (fun i:Slot=>BallG N d i a):=by
 rw [map_pow]; change (↑(matter _):Op Slot)^_= _; rw [matD, Matrix.diagonal_pow]; congr 1; funext i; change (pw _ )^ (N.val*2)=pw (pulse d i a+pulse d i a)^_; rw [phase_a, mul_pow,Nat.mul_comm, pow_mul,sq,mul_pow]; rfl -- tune
lemma sim (N:Side)(d:Candle)(u:Hat)(i:Slot)(a:Axis): BallG N (sun d u (More N)) i a=zp i (u a)*BallG N d i a:=by
 have he:= congrArg (fun x=> (matter x).val) (dance d u (More N) a); change (matter _).val=(matter _).val at he; rw [map_mul] at he; rw [sir_t,show ↑((matter _)*(matter _):UNI Slot)= (matter (central^(u a).val)).val*(matter (waveG (d a)^(More N).val)).val from rfl,sir_t, map_pow] at he
 change _= (matter central).val^(u a).val* _ at he; rw [by_charge,Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal] at he
 have hv:= Matrix.ext_iff.mpr he i i; simpa only [Matrix.diagonal_apply_eq,Pi.pow_apply] using hv -- tune
lemma zp_j (i:Slot):Injective (zp i):=fun x y h=> Fin.ext ((z_prim.pow_of_coprime (charge i) (by cases hi:i.2<;> simp [charge,hi] <;> decide)).pow_inj x.isLt y.isLt h)
-- sphere of no collisions
lemma stripe: ∃ A:ℝ,0<A∧ A ≤2∧∀ i:Slot,∀ x y:Key,x≠y→2*A≤‖zp i x-zp i y‖:=by
 let X:Finset ℝ:= insert 4 (univ.image fun w:Slot× {x:Key×Key//x.1≠x.2}=> ‖zp w.1 w.2.val.1-zp w.1 w.2.val.2‖); let H:X.Nonempty:=insert_nonempty ..; let A:= X.min' H; have hp:0<A:= by
   have he:=X.min'_mem H; rcases mem_insert.mp he with p|p; · unfold A; rw [p]; norm_num
   obtain ⟨⟨i,⟨⟨x,y⟩,e⟩⟩,_,t⟩:=mem_image.mp p; unfold A; rw [← t]; exact norm_pos_iff.mpr (sub_ne_zero.mpr ((zp_j _).ne e))
 have he:A ≤4:= min'_le _ _ (mem_insert_self ..); refine ⟨A/2,by linarith, by linarith,fun i x y h=>?_⟩; rw [show 2*(A/2)=A by ring]; apply X.min'_le; exact mem_insert_of_mem (mem_image.mpr ⟨⟨i,⟨(x,y),h⟩⟩,mem_univ _,rfl⟩)
lemma clears :∃ A:ℝ,0<A∧A ≤2∧∀ (N:Side)(d:Candle),∃ u:Hat, Medal N (sun d u (More N)) A:=by
 obtain ⟨A,h,H,Z⟩:=stripe; refine ⟨A,h,H,fun N d=>?_⟩; by_contra! v
 have hp(u:Hat):∃ i:Slot,∀ a:Axis,‖BallG N (sun d u (More N)) i a+1‖ < A:=by simpa only [Medal, Classical.not_forall, not_exists, not_le] using v u
 choose f L using hp
 have hx:Injective f:=by
   intro i j p; funext a; by_contra k
   let Q:=BallG N d (f j) a; have hu:‖Q‖=1:=by unfold Q BallG; rw [norm_pow,pw_norm,one_pow]
   let V:=zp (f j); have he:=L i a; rw [p,sim] at he; have hv:=L j a; rw [sim] at hv; have hh:=norm_sub_le (V (i a)*Q+1) (V (j a)*Q+1); rw [add_sub_add_right_eq_sub,← sub_mul,norm_mul,hu,mul_one] at hh; exact not_lt.mpr (Z _ _ _ k) (hh.trans_lt ((add_lt_add he hv).trans_eq (by ring)))
 have he := Fintype.card_le_of_injective f hx; rw [slots] at he; exact absurd he (by simp [Hat,Axis,Key]) -- simp large
-- preserves plaquettes EXACT on all fields & ALL winding? No; center acts on PU adjoint path.
lemma step_cent (x:Site N)(p:Hat)(w:Step)(U:Bkg N): let V:=wob N (fun a=>central^(p a).val); w.read (welt U p) x=w.read V x*w.read U x:=by
 intro V; cases w with
 | mk d b=>
    cases b; rfl; unfold Step.read; simp only [ite_true]; rw [welt]; unfold V wob; split
    · rw [center_comm, mul_inv_rev]
    rw [one_mul,inv_one,one_mul] -- tune
lemma cent_v (x:Site N)(p:Hat)(w:Step)(u:E): let V:=wob N (fun a=>central^(p a).val); Commute u (w.read V x):=by
 intro V; unfold Step.read; split <;> unfold V wob <;> split
 · exact (Commute.symm (center_comm ..)).inv_right
 · rw [inv_one]; exact Commute.one_right _
 · exact Commute.symm (show Commute _ _ from center_comm ..)
 exact Commute.one_right _
lemma path_cent (x:Site N)(p:Hat)(w:Walk)(U:Bkg N): let V:=wob N (fun a=>central^(p a).val); travel (welt U p) x w= travel V x w* travel U x w:=by
 intro V; have hv(w:Walk)(x:Site N)(i:E):Commute i (travel V x w):=by induction w generalizing x with| nil=>exact Commute.one_right _| cons g w h=>exact (cent_v _ _ _ _).mul_right (h _)
 induction w generalizing x with
 | nil=>simp [travel]
 | cons d w ih=>rw [travel,travel,travel,step_cent,ih]; simp only [mul_assoc]; rw [← mul_assoc (Step.read d U x), (hv w (x+d.vec) (Step.read d U x)).eq, mul_assoc]
lemma square_c(x:Site N)(p:Hat)(U:Bkg N)(a b:Axis): travel (welt U p) x (square a b)=travel U x (square a b):=by
 rw [path_cent]; rw [show travel (wob N fun a=>central^(p a).val) x (square a b)=1 from ?_,one_mul]; let F:= emptyC; have hh: Kea.tax emptyC (N:=N)=1:=by funext i; apply group.mat_injective; change Matrix.diagonal (pw ∘ skyV.val)=(1:Op SU.F); ext a b; by_cases e:a=b <;> simp [e,Matrix.one_apply,pw,BZ.phase,skyV]
 let W:= sun emptyC p N; let Q:=wob N (fun a=>central^(p a).val); have ht:=overt N emptyC p; rw [hh,wok,mul_one] at ht; let v:=gKey N emptyC p; have hx:= travel_gauge v Q x (square a b); rw [show gauge v Q= _ from ht,square_stop,tax_flat] at hx; change travel Q x (square a b)=1; apply mul_left_cancel (a:=v x); exact mul_right_cancel (show v x*travel Q x (square a b)*(v x)⁻¹=v x*(1:E)*(v x)⁻¹ by rw [←hx,mul_one,mul_inv_cancel])
end YM.CF.Sods
