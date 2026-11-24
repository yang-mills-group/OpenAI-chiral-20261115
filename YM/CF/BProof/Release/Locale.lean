import YM.CF.BProof.Release.Pints
import YM.CF.BProof.Law.Replay
import YM.CF.BProof.Charge.Drought

set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release.Locale
open Function MeasureTheory Filter Set Finset RG Wilson Lattice Precision Law Mag Angular Charge
open scoped BigOperators Topology Classical ENNReal Matrix.Norms.Frobenius
variable {s:Side}(Y:Yard s)
local notation "G" => SU.group
abbrev Place := Pub.Hall G Y.Apt
abbrev House := Y.Col → Place Y
def enters (U:Config G s):House Y := Function.curry (U ∘ Y.inter)
@[fun_prop] lemma enters_c : Measurable (enters Y) := by unfold enters Function.curry; fun_prop
abbrev lobby := Measure.pi fun _:Y.Col=> Pub.lobby G Y.Apt
lemma visits : MeasurePreserving (enters Y) (prior G s) (lobby Y) := by
 let e:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:Bond s=> SU.group.El) (· ∈ Y.field)
 let T:= Pub.lobby G (↑Y.field); let t:=Pub.lobby G {i//i∉Y.field}
 let d:=MeasurableEquiv.piCongrLeft (fun _=>SU.group.El) Y.enter
 let Q:=Pub.lobby G Y.Door
 have he: MeasurePreserving e (prior G s) (T.prod t):= by convert! measurePreserving_piEquivPiSubtypeProd (fun _:Bond s=>SU.group.probHaar) (· ∈ Y.field) using 2 <;> congr!
 have hd:MeasurePreserving d Q T:=measurePreserving_piCongrLeft (fun _=> SU.group.probHaar) _
 have hv:MeasurePreserving Prod.fst (T.prod t) T:=by unfold T t; exact measurePreserving_fst ..
 let f(U:Config G s):= d.symm (e U).1
 have hx:MeasurePreserving f (prior G s) Q:=(hd.symm _).comp (hv.comp he)
 have hg (U:Config G s)(p:Y.Door): f U p=U (Y.inter p):=by
   change d.symm _ p = (e U).1 (Y.enter p); calc
     _ = d (d.symm (e U).1) (Y.enter p):= (Equiv.piCongrLeft_apply_apply (P:=fun _=>SU.group.El) Y.enter (d.symm _) p).symm
     _ = _:= by rw [MeasurableEquiv.apply_symm_apply]
 let W:=MeasurableEquiv.curry Y.Col Y.Apt SU.group.El; have hh: (enters Y)=W ∘ f:=funext fun U=> funext fun i=> funext fun j=> (hg U (i,j)).symm; rw [hh]; exact (MP.scheme (fun (_:Y.Col)(_:Y.Apt)=> SU.group.probHaar)).comp hx

def issue (W:House Y) (p:Bond s):SU.group.El := if h:p∈ Y.field then uncurry W (Y.enter.symm ⟨p,h⟩) else 1
@[fun_prop] lemma issue_c : Measurable (issue Y):=by unfold issue; apply measurable_pi_lambda; intro p; split; unfold uncurry; fun_prop; exact measurable_const
@[simp] lemma issue_enter (U:Config G s): Set.EqOn (issue Y (enters Y U)) U ↑Y.field:=fun p hp => by unfold issue enters Function.curry uncurry; rw [dif_pos (mem_coe.mp hp)]; exact congrArg U (congrArg Subtype.val (Y.enter.apply_symm_apply ⟨p,mem_coe.mp hp⟩))
@[simp] lemma at_issue (W:House Y)(p:Y.Door) : issue Y W (Y.inter p)=W p.1 p.2 := by unfold issue; rw [dif_pos (Y.inter_mem p),show (⟨_,_⟩:↑Y.field)=Y.enter p from rfl,Equiv.symm_apply_apply]; exact rfl
lemma mix_enter (U V:Config G s) : Y.mix (issue Y (enters Y U)) V=Y.mix U V:=by
 unfold Angular.Yard.mix Angular.Yard.squash; ext1 p; unfold Law.patch; by_cases h:p∈ Y.trunks
 · rw [if_pos h,if_pos h]
 rw [if_neg h,if_neg h]; by_cases hi:p∈Y.rent; rw [if_pos hi,if_pos hi]; rw [if_neg hi,if_neg hi]; exact issue_enter Y U (Finset.mem_coe.mpr (Finset.mem_compl.mpr (fun hv=>not_or.mpr ⟨h,hi⟩ (Finset.mem_union.mp hv)))) -- tune
lemma play_enter (U V:Config G s)(S:Angular.Hall s)(p:Y.FaceS)(y:ℝ): Y.play y S (issue Y (enters Y U)) p V= Y.play y S U p V:=by unfold Angular.Yard.play Angular.Yard.view; rw [Y.centers_eq y S (issue Y (enters Y U)) p U (issue_enter Y U), mix_enter]

variable (κ y:ℝ)(Z:Finset Y.Col)(W:House Y)
-- exact severe sector
abbrev A (b:Y.Col): Place Y := fun i=> mag y (Y.inter (b,i))
abbrev dry (b:Y.Col) := Pub.den (Angular.Yard.scaleD κ y) (A Y y b)
def bed := Finset.univ.filter fun b=> W b∉ dry Y κ y b
lemma province : Y.severe κ y (issue Y W)=bed Y κ y W:=by
 ext b; simp only [Angular.Yard.severe,bed,mem_filter,Finset.mem_univ,true_and]; refine not_congr ⟨fun h i _=>?_,fun h i=>?_⟩; specialize h i; rw [at_issue] at h; exact h; rw [at_issue]; exact h i (Set.mem_univ _)
lemma berth : MeasurableSet {W|bed Y κ y W=Z}:=by
 let T(b:Y.Col):= if b∈ Z then (dry Y κ y b)ᶜ else dry Y κ y b; have hx(b:Y.Col):MeasurableSet (T b):= by unfold T; split; exact (Pub.den_m ..).compl; exact Pub.den_m ..
 rw [show {W|bed Y κ y W=Z}=Set.univ.pi T from ?_]; exact MeasurableSet.univ_pi hx
 ext W; change bed Y κ y W=Z ↔ _; rw [Finset.ext_iff]; simp only [bed,mem_filter,Finset.mem_univ,true_and,Set.mem_pi,Set.mem_univ,true_implies]; refine forall_congr' (fun b=>?_); by_cases h:b∈Z <;> simp [T,h]
lemma dry_s (h:bed Y κ y W=Z){b:Y.Col}(u:b∉ Z): W b∈ dry Y κ y b:=by subst Z; simpa [bed] using u
end YM.CF.BProof.Release.Locale
