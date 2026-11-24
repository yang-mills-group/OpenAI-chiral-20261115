import YM.SU5.FiniteGaugeData.Tower.Baggage
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra

open Afterglow Tower Lifted Journey

open SlabMark
variable {K:Calibration} {F G:ℕ→Buffered.Family K}{f g:Buffered.Family K}
 {S T:Finset Cover}
/-- A BQueue in `observ`. -/
structure Elite (S:Finset Cover)(F:ℕ→Buffered.Family K) (f:Buffered.Family K):Prop extends
    BQueue S F f where
 guard(i):CovCover K (F i)
 obs:CovCover K f

lemma Elite.zero(S:Finset Cover) :
 Elite S (fun _=> (0:Buffered.Family K)) 0 :=
  ⟨BQueue.stay InTest.zero zero_lt_one (fun _ _=> norm_zero.trans_le zero_le_one),
    fun _=>covariant_zero K,covariant_zero K⟩
lemma Elite.add (a:Elite S F f)(b:Elite S G g):
 Elite S (fun i=>F i+G i) (f+g):=by
 refine ⟨⟨fun _=>(a.whereTo _).add (b.whereTo _),a.landing.add b.landing,?_,?_⟩,
   fun _=>(covariant_parts K (a.guard _) (b.guard _)).1, (covariant_parts K a.obs b.obs).1⟩
 · obtain ⟨C,c,u,v⟩:=a.bdd
   obtain ⟨D,d,x,y⟩:=b.bdd
   exact ⟨C+D,add_pos c d,pay_add u x,(v.and y).mono fun _ ⟨u₁,x₁⟩=>pay_add u₁ x₁⟩
 intro ε p
 filter_upwards [a.saved _ (half_pos p),b.saved _ (half_pos p)] with i u v

 rw [show F i+G i - (f+g) =F i-f+(G i-g) by abel]
 exact (add_halves ε) ▸ pay_add u v -- check

lemma Elite.smul (a:Elite S F f)(w:ℂ): Elite S (fun i=>w • F i) (w • f):=by
 refine ⟨⟨fun i=> (a.whereTo i).smul _,a.landing.smul _,?_,?_⟩,
    fun i=>covariant_scale K (a.guard i) w, covariant_scale K a.obs w⟩
 · obtain ⟨C,c,u,v⟩:=a.bdd
   exact ⟨‖w‖*C+1,by positivity, fun i x=> (pay_scale u w i x).trans (le_add_of_nonneg_right zero_le_one),
      v.mono fun i hi m x=>(pay_scale hi w m x).trans (le_add_of_nonneg_right zero_le_one)⟩
 intro ε p
 let d:=ε/(‖w‖+1);have e:0<d:=by unfold d;positivity
 have k:‖w‖*d≤ε:=by
    have t:d*(‖w‖+1)=ε:=div_mul_cancel₀ _ (by positivity)
    linarith
 filter_upwards [a.saved _ e] with i u;rw [←smul_sub];exact fun m x=>(pay_scale u w m x).trans k

lemma Elite.neg (a:Elite S F f) :Elite S (fun i=>-F i) (-f):=by
 simpa only [neg_one_smul] using a.smul (-1)
lemma Elite.sub (a:Elite S F f)(b:Elite S G g):Elite S (fun i=>F i-G i) (f-g):=by
 simpa only [sub_eq_add_neg] using a.add b.neg


lemma Elite.mono (a:Elite S F f) (g:S⊆T):Elite T F f:=
  ⟨⟨fun i=>(a.whereTo i).mono g,a.landing.mono g,a.bdd,a.saved⟩,a.guard,a.obs⟩
lemma Elite.goes (a:Elite S F f)(j:Axis)(x:ℤ):
    Elite (Tower.address j x S) (fun i=>Tower.chime K j x (F i)) (Tower.chime K j x f):=by
 have t:= ((a.toBQueue.revolve j 0).revolve j x)
 rw [Tower.support_translation,sub_zero] at t -- params?
 exact ⟨t,fun _=>chime_cov K _ _ (a.whereTo _) (a.guard _),chime_cov K _ _ a.landing a.obs⟩
lemma Elite.sum {ι:Type*}(s:Finset ι) {f:ι→Buffered.Family K}
 {F:ℕ→ι→Buffered.Family K}(p:∀i,Elite S (fun n=>F n i) (f i)):
 Elite S (fun n=>∑ i∈s,F n i) (∑i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty => simp;exact Elite.zero _
 | insert x s h ih=> simp only [sum_insert h];exact (p x).add ih

end YM.CF.Merino.Tiara
