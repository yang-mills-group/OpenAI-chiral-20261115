import YM.CF.BProof.Shore.Stage
import YM.CF.BProof.Shore.Join
import YM.CF.Skye.Man
/-! Basic maps for every fixed field. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Nest Stave Gallery Function MeasureTheory Metric Filter Finset Wilson Lattice
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
abbrev Bones(n:Side) := Edge (Site n)
abbrev StampB(n:Side) := Bones n→ Bool×Bool
abbrev Heads (n:Side) := Config SU.group n
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
variable (s l u)(T:Tray (Floor q) ε)(F:Drum (rollup q T) (Floor q)) (A:Score n q) (R:StampB n)
local notation "X"=> opened s l u T F A
local notation "Y"=>caught s l u A
def make(U:Heads n): Heads n:= fun z=> if Y U z.1∧ Y U (z.1+step z.2) then U z else decideG (R z) (X U z.1) (X U (z.1+step z.2)) -- implicit bind reorder
local notation "LΨ"=> make s l u T F A R
private lemma pre_meas (i:Bones n): Measurable (fun U:Heads n=>decideG (R i) (X U i.1) (X U (i.1+step i.2))):=by
 let data : Measurable (fun U:Heads n => (X U i.1,X U (i.1+step i.2))) := (open_meas s l u T F A i.1).prodMk (open_meas s l u T F A (i.1+step i.2))
 have h : Measurable ((Function.uncurry (@decideG (Pad (Floor q)) _ (R i))) ∘ (fun U:Heads n => (X U i.1,X U (i.1+step i.2)))):= (decide_m (I:=Pad (Floor q)) (R i)).comp data
 exact h
lemma make_meas : Measurable (make s l u T F A R):= by
 unfold make; apply measurable_pi_lambda; intro i; refine Measurable.ite  (p:=fun U:Heads n=> Y U i.1 ∧ Y U (i.1+step i.2)) (f:=fun U:Heads n=> U i) (g:=fun U=>decideG (R i) (X U i.1) (X U (i.1+step i.2))) ?_ ?_ ?_
 · exact ((caught_meas s l u A i.1).inter (caught_meas s l u A (i.1+step i.2)))
 · exact measurable_pi_apply _
 exact pre_meas _ _ _ T F A R i
-- uniform.nK/
variable {s l u T F A R}{U V:Heads n}(W:Writ q T s l u a b δ d θ F) (B:Seal A s l b a)
include W B
theorem toll (k:Step)(x:Sκ): dist (roll (X U x) (k.read (LΨ U) x)) (X U (x+k.vec)) ≤3*d:=by
 have ht(i:Axis)(x:Sκ): dist (roll (X U x) ((LΨ U) (x,i))) (X U (x+step i)) ≤3*d:=by
    obtain ⟨g,h⟩:= worth U W B x i; unfold make; dsimp only; split; · rename_i hv; exact (worth_h U W B x i hv.1 hv.2).trans (by linarith only [W.cost_a,W.cost_b])
    exact (decide_p _ _ _ g).trans h
 rcases k with ⟨i,p|p⟩; exact ht i x; let y:= x-step i; change dist (roll _ (((negDir i).read (LΨ U) x))) _ ≤_; rw [Step.neg_read,backdist]; have hk:=ht i (x-step i); rw [sub_add_cancel] at hk; change dist (roll (X U (x+ -step i)) _) _ ≤_; rw [←sub_eq_add_neg]; exact hk
lemma truly(w:Walk)(x:Sκ):dist (roll (X U x) (travel (LΨ U) x w)) (X U (stop x w)) ≤ w.length*(3*d):=by
 induction w generalizing x with |nil=> simp [travel,stop] |cons i w ih=>
    let y:=x+i.vec; rw [travel,←roll_mul]; let g:=travel (LΨ U) y w; change dist (roll _ g) _ ≤_
    apply (dist_triangle _ (roll (X U y) g) _).trans ((add_le_add (show dist (roll (roll (X U x) (i.read (LΨ U) x)) g) (roll (X U y) g) ≤ 3*d from by rw [roll_dist]; exact toll W B i x) (ih y)).trans_eq ?_) -- tune
    rw [List.length_cons]; push_cast; ring
lemma turn_frame {d1:ℝ}(p:14*d ≤ d1*SU.group.colorScale)(U:Heads n):RG.flags d1 (LΨ U)=∅:=by
 have h(i:Lattice.Face (Per n)): SU.group.chord (faceValue (LΨ U) i) ≤d1:=by
    obtain ⟨q,hq,h⟩:=worthy U W B i.1; let x:= i.1; let g:=faceValue (LΨ U) i; have ht : dist (roll (X U x) g) (X U x) ≤ 4*(3*d):=by
       have hp:= truly (R:=R) (U:=U) W B (square i.2.val.1 i.2.val.2) x; rw [square_stop, show (square i.2.val.1 i.2.val.2).length=4 from rfl] at hp; exact_mod_cast hp -- tune
    have he:= dist_triangle4 (roll q g) (roll (X U x) g) (X U x) q; rw [roll_dist,dist_comm q] at he
    have hx: dist (roll q g) q= cd SU.group 1 g * SU.group.colorScale:=by
       nth_rw 2 [← roll_one q]; unfold roll; rw [dist_eq_norm,←Matrix.mul_sub,size_mul (show qᴴ*q=1 from hq),←mat_norm_dist,dist_eq_norm,norm_sub_rev]; rfl
    rw [hx] at he; change dist (X U x) q ≤d at h; rw [cd_one] at he; change SU.group.chord g≤ d1; apply le_of_mul_le_mul_right (_ : SU.group.chord g*_≤ d1*SU.group.colorScale) SU.group.colorScale_pos; linarith only [ht,h,p,he]
 apply Finset.eq_empty_iff_forall_notMem.mpr; intro i hi; obtain ⟨p,hp,g⟩:= RG.flags_spec ..|>.1 hi; exact g.not_ge (h p)
end Score
end YM.CF.BProof.Mesh.Shore
