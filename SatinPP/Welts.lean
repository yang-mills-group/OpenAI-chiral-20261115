import SatinPP.Sashes
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

open Function Filter Set MeasureTheory
open OS OS.Semigroup Spectral Boundary Probe Hierarchy.Seld
open YM.Quays YM.SatinJets
open scoped Topology Matrix BigOperators InnerProductSpace NNReal ContDiff
variable {H:Hilbert}{j:Axis}{S:OS.Semigroup H j}
local notation "R"=>saucer S
local notation "K"=>Cache S


namespace Role
variable {B:H.Op}{A:Stamp H}{d:ℕ}(w:Role S d A B)

lemma encrypted
    (z r:ℂ)(a:z∈inside)(p:r∈inside):
    HasDerivAt (fun t=> R * S.F (z+t) * B * S.F (r-t) * R)
       (S.F z * (R*B-B*R) * S.F r) 0:=by
 have b:HasDerivAt (fun t=>S.F (z+t)) (slug S z) 0:=by
   have q:HasDerivAt S.F (slug S z) (z+0):=by
     rw [add_zero];exact (S.localHeat z a).differentiableAt.hasDerivAt
   simpa [Function.comp_def] using q.scomp (0:ℂ) ((hasDerivAt_id' _).const_add z)
 have c:HasDerivAt (fun t=>S.F (r-t)) (-slug S r) 0:=by
   have q:HasDerivAt S.F (slug S r) (r-0):=by
     rw [sub_zero];exact (S.localHeat r p).differentiableAt.hasDerivAt
   simpa [Function.comp_def] using q.scomp (0:ℂ) ((hasDerivAt_id' _).const_sub r)
 convert ((((b.const_mul (R)).mul_const B).mul c).mul_const (R)) using 1
 · rfl

 all_goals try rfl
 have d:R * slug S z=R * S.F z - S.F z:=by
    have h:=dorsal S z a
    unfold looper at h;rw [mul_sub] at h; exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp h).symm
 have e:slug S r *R=S.F r*R-S.F r:=by
    have h:=jalousie S r p
    unfold looper at h;rw [sub_mul] at h
    exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp h).symm
 rw [d,add_zero,sub_zero,mul_neg,add_mul,neg_mul,mul_assoc (R*S.F z*B),e]
 rw [sub_mul,sub_mul,sub_mul,mul_sub]
 rw [mul_sub,(cupF S z a).eq,(cupF S r p).symm.eq]
 simp only [sub_mul,mul_assoc]; rw [(cupF S r p).symm.eq]
 abel

include w
lemma cuts {m:ℕ}{c:ℝ}(p:Paid S m c A):
    Role S (d+1) (flicks S A) (R*B-B*R):=by
 have price (z r:ℂ)(h:z∈inside)(t:r∈inside):
    K (d+1) * paint S A z r * K (d+1)=R * S.F z * B * S.F r * R:=by
      rw [w.suited p z r h t]
      nth_rw 1 [show K (d+1)=R*K d from pow_succ' ..]
      rw [show K (d+1)=K d*R from pow_succ ..]
      have o:=recover S d z h
      have a:=change_m S d r t
      rw [←o,←a]
      simp only [mul_assoc]
 constructor;intro u v a b
 have T:(u:ℂ)∈inside:=a
 have V:(v:ℂ)∈inside:=b
 have h:=encrypted (S:=S) (B:=B) _ _ T V
 have t:= ((hasFlick p T V).const_mul (K (d+1))).mul_const (K (d+1))


 rw [F_heat S a,F_heat S b] at h
 refine t.unique (h.congr_of_eventuallyEq ?_)
 have e:((u:ℂ)+0:ℂ)∈inside:=by rw [add_zero];exact T
 have q:((v:ℂ)-0:ℂ)∈inside:=by rw [sub_zero];exact V
 filter_upwards [(continuous_const.add continuous_id').continuousAt.eventually (open_inside.mem_nhds e),
    (continuous_const.sub continuous_id').continuousAt.eventually (open_inside.mem_nhds q)] with r y z
 exact price _ _ y z

end Role

lemma sous (g:Test4)(B:H.Op):valise S (R*B-B*R) g=R*valise S B (-εpref j g)*R:=by
 have v(Y:H.Op):valise S (-Y) g=-(valise S Y g):=by
    rw [←neg_one_smul ℂ Y,vscale,neg_one_smul]
 have y:valise S (B*R) g=valise S B g*R:=by
    simpa [Cache] using shingle S g B 0 1
 have z:valise S (R*B) g=R*valise S B g:=by
    simpa [Cache] using shingle S g B 1 0
 have f:valise S B (-εpref j g)=-(valise S B (εpref j g)):=map_neg (barren S B) _
 rw [sub_eq_add_neg,vadd,v,z,y,f,mul_neg,neg_mul,orion]
 abel

variable {A:Stamp H}
lemma feature_flick(p:Sold S A)(g:Test4):
  feature S (flicks S A) g=feature S A (-εpref j g):=by
 obtain ⟨_,_,h⟩:=p
 rw [feature_eq (Role.cuts (serve S ⟨_,_,h⟩) h)]
 exact anoint S g _ (sous ..)
#print axioms feature_flick

def beadlet(j:Axis)(g:Test4):Test4:=-εpref j g
def stringlet(j:Axis)(n:ℕ)(g:Test4):Test4:=((beadlet j)^[n]) g
lemma feature_scratches(p:Sold S A)(n:ℕ)(g:Test4):
  feature S (scratches S n A) g=feature S A (stringlet j n g):=by
 induction n generalizing g with
 |zero=>rfl
 |succ i ih=>
   rw [succ_flick,feature_flick (p.scratched _),ih,stringlet,stringlet,Function.iterate_succ_apply]
   rfl
def sectionals (j:Axis)(q:Prism)(c:ℂ)(g:Test4):Test4:=
    ∑ i∈q.support,q i • (c • stringlet j (i+1) g)
lemma feature_surfaces(p:Sold S A)(q:Prism)(c:ℂ)(g:Test4):
   feature S (surfaces S q (c • A)) g=feature S A (sectionals j q c g):=by
 unfold surfaces sectionals
 rw [feature_sum _ _ (fun i=>((p.smul c).scratched _).smul _),map_sum]
 refine Finset.sum_congr rfl (fun i _=>?_ )
 rw [feature_smul ((p.smul c).scratched _),
    feature_scratches (p.smul c),feature_smul p,map_smul,map_smul]

def nextFacing (j:Axis)(q:Prism)(c:ℂ)(g:Test4):Test4:=
    bar (sectionals j q c (bar g))
lemma feature_earlier(p:Sold S A)(q:Prism)(c:ℂ)(g:Test4):
   feature S (Turn (surfaces S q (c • A))) g=
   feature S (Turn A) (nextFacing j q c g):=by
 have e:bar (bar g)=g:=by
   ext x; change star (star (g x))=_
   exact star_star _
 ext1 y
 apply ext_inner_left ℂ; intro x
 let B:=surfaces S q (c • A)
 have h:Sold S B:=(p.smul c).surfaced q
 have u:=feature_turn h (bar g) x y
 unfold B at u
 rw [feature_surfaces p,e,feature_turn p] at u
 exact u.symm

#print axioms feature_earlier

lemma curtains_sub {f g:Test4}
    (h:∀x, x∉tsupport g→ f x=0):
 tsupport f⊆tsupport g:=closure_minimal
   (fun x z=>by_contra fun y=>z (h x y))
   (isClosed_tsupport _)

lemma beadlet_tsupp (g:Test4)(j:Axis):
    tsupport (beadlet j g) ⊆ tsupport g:=by
 have k:tsupport (Silk.slip j g) ⊆ tsupport g:=
   SchwartzMap.tsupport_lineDerivOp_subset (basis j) g
 refine curtains_sub fun x h=>?_
 have e : slip j g x=0:=by
    by_contra t; exact h (k (subset_tsupport _ t))
 change -(Complex.I * slip j g x)=0
 rw [e,mul_zero,neg_zero]
#check @subset_tsupport
#check SchwartzMap.sum_apply


lemma stringlet_tsupp(g:Test4)(j:Axis)(i:ℕ):
   tsupport (stringlet j i g) ⊆ tsupport g:=by
 induction i generalizing g with
 |zero=>exact Subset.rfl
 |succ i h=>exact Subset.trans (h (beadlet j g)) (beadlet_tsupp ..)

lemma bar_tsupp(g:Test4):tsupport (bar g)⊆tsupport g:=by
 refine closure_mono fun x e k=>?_
 change g x=0 at k
 exact e (show star (g x)=0 by rw [k,star_zero])

lemma sectional_tsupp(g:Test4)(q:Prism)(c:ℂ):
  tsupport (sectionals j q c g)⊆tsupport g:=by
 refine curtains_sub fun x h=>?_
 have e(i:ℕ):stringlet j i g x =0:= by
    by_contra t;exact h (stringlet_tsupp g j i (subset_tsupport _ t))
 unfold sectionals;rw [sum_apply]
 refine Finset.sum_eq_zero ?_
 intro i _
 change q i * (c * stringlet j _ g x)=0
 rw [e,mul_zero,mul_zero]
lemma facing_tsupp(g:Test4)(q:Prism)(c:ℂ):
  tsupport (nextFacing j q c g)⊆tsupport g:=
   (bar_tsupp _).trans ((sectional_tsupp _ _ _).trans (bar_tsupp ..))

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

