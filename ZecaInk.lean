import ZecaArcs
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
local notation "R" => saucer S

open Poin
variable {n:ℕ}(Ω:H)
  (D:Fin n→Moment H)(x:Points n)(k:ℕ)

/-- guard non-increasing indices -/
def spacer(i j:Fin n):H.Op :=
 if i<j then leap0 S D (cord k) i j else 1
lemma spacerU (y:E4)(i j:Fin n): Commute (M S y) (spacer S D k i j):=by
 unfold spacer; split_ifs with h
 · exact (mslot S y _ (show (↑(cord k j-cord k i):ℂ) ∈inside by
       simpa only [inside,Set.mem_setOf_eq,ofReal_re] using sub_pos.mpr (cordMono k h)) _).symm
 exact Commute.one_right _
abbrev hands (a:Axis)(x:Points n):=fun i:Fin n=> x i a • basis a

lemma spacer_arc (i j:Fin n)(h:i<j):
   spacer S D k i j * M S (hands a x j-hands a x i)=arcOp S D k x I i j:=by
 rw [spacer,if_pos h]
 unfold hands; rw [←sub_smul,timeslot]
 let z:ℂ:=↑(cord k j-cord k i)
 let t:=x j a-x i a
 have e:z∈inside:=by simpa only [z,inside,Set.mem_setOf_eq,ofReal_re] using sub_pos.mpr (cordMono k h)
 have f:z+sideways t=litGap a k x I i j:=by unfold litGap z sideways t; ring
 unfold arcOp leap0; rw [←f]
 let v:=(D i).n+(D j).n
 ext1 b; apply cache_I S v

 have r: Cache S v * (parabola S v z * S.edge t)= Cache S v * parabola S v (z+sideways t):=by
     rw [←mul_assoc,recover S v z e,recover S v _ ((allow z t).2 e)]
     exact S.either e t
 exact DFunLike.congr_fun r b

lemma spacer_arc_all (o:∀x,M S x Ω=Ω):
 inner ℂ Ω (pitch S (fun i=>(D i).op) (spacer S D k) x Ω)= arc S Ω D k x I:=by
 let sp:= bodySp a x
 let T:= hands a x
 let J:= spacer S D k
 let C:=lodgedOp S D sp
 let Y i:= optx S (C i) (T i)
 have e:dress S (fun i=>(D i).op) x=Y:=by
    funext i; unfold Y C lodgedOp
    rw [opt_act,show T i+(sp i).val=x i by
       change x i a • basis a + (x i- x i a • basis a)=_
       exact add_sub_cancel ..] -- add_sub_cancel or add_sub_cancel?
 change inner ℂ Ω (Rail (dress S (fun i=>(D i).op) x) J Ω)=
    inner ℂ Ω (Rail C (arcOp S D k x I) Ω)
 rw [e]
 exact (baroque S Ω C T o J (spacerU S D k) (Each n)).trans
     (congrArg (fun U:H.Op=>inner ℂ Ω (U Ω))
      (FilmRel _ _ _ (·<·) (spacer_arc S D x k) _ (ord n)))

abbrev charge (D:Fin n→Moment H):=fun i=> (D i).n

lemma spacer_paid:Solution S (charge D) (spacer S D):=by
 have d(i j:Fin n)(t:ℕ)(p:i<j):
    (↑(cord t j-cord t i):ℂ)∈inside:=by
        simpa only [inside,Set.mem_setOf_eq,ofReal_re] using sub_pos.mpr (cordMono t p)
 refine ⟨fun t=>⟨fun i j p=>?_⟩,?_⟩
 · rw [spacer,if_pos p]; exact (gear S _ (d _ _ t p) _).symm
 intro i j p
 let s (r:ℕ):ℝ≥0:= ⟨_,(sub_pos.mpr (cordMono r p)).le⟩
 have u:Tendsto s atTop (𝓝 0):=by
    apply tendsto_subtype_rng.mpr; change Tendsto (fun t=>cord t j-cord t i) _ (𝓝 (0:ℝ)); simpa using (cordGo j).sub (cordGo i)
 unfold Gesture Xpay
 have c(t:ℕ): spacer S D t i j * Cache S (charge D i + charge D j)=S.E (s t):=by
   rw [spacer,if_pos p]
   exact parabolaE S _ (s t) (sub_pos.mpr (cordMono t p))
 simp_rw [c]
 refine ⟨1,fun t=>S.shrinks _, fun z=>?_⟩
 simpa [Function.comp_def,S.eZero] using ((S.continuousE z).tendsto 0).comp u

open Boundary Probe

abbrev Wproduct (S:OS.Semigroup H a)(Ω:Bench S)
 (D:Fin n→Moment H)(g:Fin n→Test4):ℂ:=
 inner ℂ Ω.val (Rail (fun i=> (D i).field S (g i)) (Omit S) Ω).val

lemma wick (Ω:Bench S)(o:∀x,M S x Ω.val=Ω.val)(g:Fin n→Test4){V}
  (p:Marks S Ω.val D V):
    (∀ i:ℕ, Integrable (fun x=>Joint.materialize n g x * V i x I)) ∧
    Tendsto (fun i:ℕ=>∫ x, Joint.materialize n g x * V i x I)
       atTop (𝓝 (Wproduct S Ω D g)):=by
 let J:=spacer S D
 let G:=fun i=> (D i).op
 have e(k x): V k x I=inner ℂ Ω.val (pitch S G (J k) x Ω.val):=
     (ink_uniq S Ω.val D x k p).trans (spacer_arc_all S Ω.val D x k o).symm
 simp_rw [e]
 exact ⟨fun i=>billI .., traverse S G (charge D) Ω g J (spacer_paid S D) (rlock S Ω.val o)⟩
#print axioms wick
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
