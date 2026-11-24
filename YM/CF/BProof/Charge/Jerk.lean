import YM.CF.BProof.Charge.Form

/- Sum every magnetic linear charge cancels, including cross kept terms. We average in
momentum slice type at each channel physically. Computation on any bond array. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}(W:Argument s)(T:PathData SU.group)(M:ℕ)(σ:Signed)(x:Site s)(t:Per s)

-- Sum an argument leg around tangential translations. coset offsets drop in tangential sum entirely.
abbrev origin (p:Space s) : Site s:= (Micro.equiv σ).symm (join t p)
def line (o:Axis)(t:Per s) : Lie:= ∑ p:Space s,W (join t p,o)
lemma part_line (o:Axis) :
    ∑ p:Space s, part σ (origin σ t p+x,o) W=turn (σ.flip o) (line W (σ.perm o) (t+time (σ.act x+coset σ o))):=by
 simp_rw [part,LinearMap.comp_apply,part_key,spin,Signed.act_add,show ∀ p:Space s,σ.act (origin σ t p)=join t p from fun p=> (Micro.equiv σ).apply_symm_apply _,add_assoc]
 let v:=σ.act x+coset σ o; change (∑ p:Space s, turn _ (W (join t p+v,σ.perm o)))=_
 have hh(p): join t p+v=join (t+time v) (p+space v):=by conv_lhs=> rw [← join_time_space (join t p+v)]; simp
 simp_rw [hh, ← map_sum]; congr 1; exact Equiv.sum_comp (Equiv.addRight (space v)) (fun p:Space s=> W (join (t+time v) p,σ.perm o))
lemma slice_signed (e:Axis) : time (σ.act x)= if σ.flip (σ.perm.symm 0) then -(x (σ.perm.symm 0)) else x (σ.perm.symm 0):=rfl
lemma step_signed (i:Axis)(h:σ.perm i≠0): time (σ.act (step i:Site s))=0:=by
 unfold time Signed.act; have he:σ.perm.symm 0≠i:=mt (σ.perm.symm_apply_eq .. |>.mp) (Ne.symm h) -- tune
 rw [step_apply]; split <;> simp [he]
lemma curl_formula (a:PlaqAxes) : curlP σ (x,a) W=part σ (x,a₁ a) W+part σ (x+step (a₁ a),a₂ a) W-part σ (x+step (a₂ a),a₁ a) W-part σ (x,a₂ a) W:=rfl
def cross (p:PlaqAxes): Prop := σ.perm (a₁ p)≠0 ∧ σ.perm (a₂ p)≠0
lemma jersey0 (a:PlaqAxes)(h:cross σ a) : (∑ p:Space s,curlP σ (origin σ t p+x,a) W)=0:=by
 simp_rw [curl_formula,sum_sub_distrib,sum_add_distrib,add_assoc,part_line W]; simp only [Signed.act_add,time_add,step_signed σ (a₁ a) h.1,step_signed σ (a₂ a) h.2,add_zero]; abel

-- tangential flip inside the channel (right). e is channel/input axis.
def odd (e:Axis):= σ* Signed.mirror e
@[simp] lemma odd_perm (e:Axis): (odd σ e).perm=σ.perm:=by ext; rfl
lemma odd_touch (e:Axis):(odd σ e).flip e= !(σ.flip e):= by simp [odd,Signed.mirror]
lemma odd_fix {e i:Axis} (h:e≠i): (odd σ e).flip i=σ.flip i:=by simp [odd,Signed.mirror,h]
lemma odd_X (e:Axis): pointed (odd σ e) e= -pointed σ e:=by rw [pointed,odd_perm,odd_touch]; exact turn_v ..
lemma odd_X_other {e i:Axis}(h:e≠i): pointed (odd σ e) i=pointed σ i:=by simp only [pointed,odd_perm,odd_fix _ h]
lemma odd_time {e:Axis}(h:σ.perm e≠0): time ((odd σ e).act x)=time (σ.act x):=by
 have he:e≠σ.perm.symm 0:=by intro g; rw [g,Equiv.apply_symm_apply] at h; exact h rfl
 rw [slice_signed _ x e,slice_signed σ x e,odd_perm,odd_fix σ he]

def use (a:PlaqAxes)(e:Axis):Prop:= e=a₁ a ∨ e=a₂ a
lemma odd_rest {e:Axis}{a:PlaqAxes} (h:use a e): mark (odd σ e) a= -mark σ a := by
 have ht : a₁ a≠a₂ a:= a.property.ne; unfold mark; rcases h with h|h <;> subst e; simp only [odd_X,odd_X_other _ ht,map_neg,LinearMap.neg_apply]; simp only [odd_X,odd_X_other _ (Ne.symm ht),map_neg]
lemma odd_jersey {e:Axis}(h:σ.perm e≠0)(a:PlaqAxes)(p:¬use a e):
    ∑ q:Space s,curlP (odd σ e) (origin (odd σ e) t q+x,a) W=∑ q:Space s,curlP σ (origin σ t q+x,a) W := by
 have v (x:Site s)(o:Axis)(u:e≠o):∑ q:Space s, part (odd σ e) (origin (odd σ e) t q+x,o) W=∑ q:Space s,part σ (origin σ t q+x,o) W :=by
    rw [part_line W,part_line W]; simp only [coset,time_add,odd_perm,odd_fix σ u, odd_time σ x h]
 let u:=a₁ a; let v':=a₂ a
 simp_rw [curl_formula,sum_sub_distrib,sum_add_distrib,add_assoc]
 rw [v _ (a₁ a) (not_or.mp p).1,v _ (a₂ a) (not_or.mp p).2,v _ (a₁ a) (not_or.mp p).1,v _ (a₂ a) (not_or.mp p).2]
end YM.CF.BProof.Charge.Form
