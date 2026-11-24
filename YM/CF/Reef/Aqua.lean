import YM.CF.Reef.Pole
import YM.CF.Thera.Jolt
import YM.CF.Pec.Breath
import YM.PCalc.Chart
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reef
open Function Filter NormedSpace SU Spire Lattice Wilson RG Finset Precision
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {k:ℕ}{σ A B:ℝ}
private def eI:= EuclideanSpace.basisFun SU.group.ColorIndex ℝ
private def invertR (F:Atom SU.group k):Atom SU.group k where
 leg:=F.leg
 coeff i:=F.poly fun j=> frolic (eI (i j))
lemma rotP(F:Atom SU.group k)(x:Fin k→Ox):(invertR F).poly x=F.poly (fun i=>frolic (x i)):=by
 let A:=SU.group.ColorIndex; let f(j:Fin k)(i l:A):ℝ:= (x j) i* (frolic (eI i)) l
 have he (i j): (frolic (x i)) j=∑ s:A,f i s j:=by
    let W:=∑ t:A,(x i) t • eI t; have hp: W=x i:= eI.sum_repr _
    let X: Ox→ₗ[ℝ]ℝ := LinearMap.comp (LinearMap.proj (R:=ℝ) j) (WithLp.linearEquiv 2 ℝ _).toLinearMap
    unfold f; change X (frolic (x i))=_; rw [← hp,map_sum]; simp_rw [map_smul]; rw [map_sum]; simp_rw [map_smul,smul_eq_mul]; simp_rw [hp]; rfl -- tune X
 have hx (z:Fin k→A): (∏ i, (frolic (x i)) (z i))=∑ y:Fin k→A,(∏ i,(x i) (y i))* ∏ i, frolic (eI (y i)) (z i):=by
   simp_rw [he]; rw [Fintype.prod_sum]; simp_rw [f, prod_mul_distrib]; -- tune
 unfold Atom.poly invertR; dsimp only; simp only [Atom.poly, Finset.sum_mul]; simp_rw [hx, Finset.mul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; ring
private lemma norm_p(x: Ox)(i): |x i| ≤ ‖x‖ := by
 have he:=abs_real_inner_le_norm (eI i) x; rw [show inner ℝ (eI i) x=x i from EuclideanSpace.basisFun_inner ..,OrthonormalBasis.norm_eq_one,one_mul] at he; exact he
private lemma cost_r (F:Atom SU.group k)(i): |(invertR F).coeff i|≤ F.magnitude:=by
 unfold invertR Atom.poly; dsimp only; refine (abs_sum_le_sum_abs ..).trans (sum_le_sum (s:=(univ:Finset (Fin k→SU.group.ColorIndex))) fun j _=>?_) -- tune name
 rw [abs_mul, Finset.abs_prod]; apply mul_le_of_le_one_right (by positivity); apply prod_le_one (fun _ _=> by positivity); intro l _; rw [← show ‖frolic (eI (i l))‖=1 from by simp]; exact norm_p ..
private def market(F:Atom SU.group k):Atom SU.group k:= {F with coeff:=fun i=> (F.coeff i+(invertR F).coeff i)/2}
lemma aqua_e(F:Atom SU.group k)(x:Fin k→Ox):(market F).poly x=(F.poly x+F.poly (frolic ∘ x))/2:=by
 unfold Function.comp; rw [←rotP]; unfold Atom.poly market; dsimp only; rw [←sum_add_distrib,sum_div]; apply sum_congr rfl; intro i h; ring
def Prist(F:Atom SU.group k): Prop:= ∀ x:Fin k→Ox,F.poly (frolic ∘x)= F.poly x
private lemma market_s(F:Atom SU.group k)(h:F.Invariant):(market F).Invariant∧Prist (market F):=by
 refine ⟨fun i x=>?_,fun x=>?_⟩
 · rw [aqua_e,aqua_e,h]; unfold Function.comp; simp_rw [dip]; rw [h];
 rw [aqua_e,aqua_e]; unfold Function.comp; simp_rw [fiz2]; rw [add_comm]
abbrev girk(k:ℕ):ℝ:= (1:ℝ)+ Fintype.card (Fin k→SU.group.ColorIndex)
private lemma market_h(F:Atom SU.group k)(s:ℝ): (market F).budget s ≤girk k*F.budget s:=by
 have hm:F.magnitude≥0:=sum_nonneg fun _ _=>abs_nonneg _
 have he:(market F).magnitude≤girk k*F.magnitude:=by
    let I:=Fin k→SU.group.ColorIndex
    have hp(i:I): |(market F).coeff i|≤ |F.coeff i|+ F.magnitude:=by
       unfold market; dsimp only; rw [abs_div, abs_of_pos (by norm_num:0<(2:ℝ))]; linarith [cost_r F i, abs_add_le (F.coeff i) ((invertR F).coeff i), abs_nonneg (F.coeff i)]
    apply (sum_le_sum (s:=(univ:Finset I)) (fun i _=>hp i)).trans_eq; simp [girk,sum_add_distrib, Atom.magnitude, add_mul,I]
 unfold Atom.budget; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right he (by positivity)
lemma market_b (F:ℕ→Atom SU.group k)(p:SumBudget (fun i=>(F i).budget σ) A)(h:girk k*A ≤ B): SumBudget (fun i=>(market (F i)).budget σ) B:=by
 let f(i):= girk k*(F i).budget σ; let u(i):=(market (F i)).budget σ
 have he:Summable f:= p.2.1.mul_left _; have ht(i):0≤u i:=by unfold u Atom.budget Atom.magnitude; positivity
 have hp(i):u i ≤f i:=market_h ..
 have hh:=he.of_nonneg_of_le ht hp
 refine ⟨ht,hh,(Summable.tsum_le_tsum hp hh he).trans (_root_.tsum_mul_left.trans_le ?_)⟩; exact (mul_le_mul_of_nonneg_left p.2.2 (by unfold girk; positivity)).trans h
end YM.CF.Reef
namespace YM.CF.Reef
open Function Filter NormedSpace SU Spire Lattice Wilson RG Finset Precision Thera
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {n:Side}{p q:Clip}{R:PathData SU.group}{k:ℕ}{σ A B C:ℝ}
lemma twoK (F:Atom SU.group 2)(h:F.Invariant): Prist F:=by
 haveI : Nontrivial Ox:=yet_one.nontrivial_color
 let f(x y:Ox):ℂ:=F.poly ![x,y]
 let P : Ox→ₗ[ℝ]Ox→ₗ[ℝ]ℂ :=
  { toFun x:= {
     toFun:=f x
     map_add':=by intro x y; simp only [f,Atom.poly,Fin.prod_univ_two]; simp [mul_add,sum_add_distrib] -- tune
     map_smul':=by intro i y; simp only [f,Atom.poly,Fin.prod_univ_two]; simp [PiLp.smul_apply,mul_left_comm,mul_comm,mul_assoc,Finset.mul_sum,Complex.real_smul, Complex.ofReal_sum,Complex.ofReal_mul] -- tune
    }
    map_add':=by intro a b; ext1 y; change f (a+b) y = _; change _= f a y+ f b y; simp only [f,Atom.poly,Fin.prod_univ_two]; simp [add_mul,mul_add,sum_add_distrib]
    map_smul':=by intro i x; ext1 y; change f (i • x) y= i • f x y; simp only [f,Atom.poly,Fin.prod_univ_two]; simp [PiLp.smul_apply,mul_comm,mul_assoc, Finset.mul_sum,Complex.real_smul, Complex.ofReal_sum,Complex.ofReal_mul]
   }
 obtain ⟨e,hp⟩:=exists_norm_eq Ox zero_le_one
 have he(g:SU.group.El)(x y:Ox): P (SU.group.adjoint g x) (SU.group.adjoint g y)=P x y:=by
    change (↑(F.poly _):ℂ)=↑(F.poly _)
    rw [show ![SU.group.adjoint g x,SU.group.adjoint g y]= (fun i=>SU.group.adjoint g (![x,y] i)) from funext fun i=>by fin_cases i<;>rfl, h g] -- tune
 have hy(r s:Ox):P r s=inner ℝ r s • P e e:= StressFlux.bilinear_invariant yet_one P he hp r s
 intro x; apply Complex.ofReal_injective; have hv(r: Fin 2→Ox): (↑(F.poly r):ℂ)=P (r 0) (r 1):=by change _=(↑(F.poly ![r 0,r 1]):ℂ); congr; funext i; fin_cases i<;>rfl
 rw [hv,hv,hy, hy (x 0) (x 1), Function.comp_apply, Function.comp_apply,frolic.inner_map_map]
lemma tollSlot (p:RG.Slot)(U:Config SU.group n)(x:Site n): p.atSite (echo U) x=frolic (p.atSite U x):=by
 unfold RG.Slot.atSite; rw [show expandAt x (echo U)=echo (expandAt x U) from rfl]; simp_rw [RG.Slot.eval, faceValue,echo_t,dip, swing]
private lemma merchant(F:Atom SU.group k)(U:Config SU.group n)(x:Site n): (market F).unmasked U x=(F.unmasked U x+F.unmasked (echo U) x)/2:=by
 unfold Atom.unmasked; rw [aqua_e]; simp_rw [tollSlot]; rfl
private lemma burden(T:ℕ→Atom SU.group k)(h:SumBudget (fun i=>(T i).budget σ) A)(g:0<σ)(U:Config SU.group n)(x:Site n): Summable fun i=>(T i).unmasked U x:=by apply Summable.of_norm; exact (h.2.1.mul_right ((2:ℝ)^k)).of_nonneg_of_le (fun _=>norm_nonneg _) fun i=> ((T i).unmasked_bound U x).trans (mul_le_mul_of_nonneg_right ((T i).lower_budget _ g) (by positivity)) -- tune
private lemma uncP(T:ℕ→Atom SU.group k)(h:SumBudget (fun i=>(T i).budget σ) A)(g:0<σ)(U:Config SU.group n):uncut (market ∘ T) U= (uncut T U+uncut T (echo U))/2:=by
 unfold uncut; rw [← sum_add_distrib,sum_div]; apply sum_congr rfl; intro i h'; unfold Function.comp
 simp_rw [merchant,div_eq_mul_inv]; rw [tsum_mul_right, (burden T h g U _).tsum_add (burden T h g (echo U) _)]
def pocket(k:ℕ):= market (k:=k)
def solvent (T:PathData SU.group): PathData SU.group:={T with cubic:=pocket _ ∘ T.cubic, quartic:=pocket _ ∘ T.quartic}
def Rare(T:PathData SU.group):Prop:=∀ i,Prist (T.loop i)∧Prist (T.cubic i)∧Prist (T.quartic i)
lemma gem_b(h:R.Bounds p σ A B)(he:A≤ C)(hp:girk 3*A≤ C)(hx:girk 4*A≤ C): (solvent R).Bounds p σ C B ∧ Rare (solvent R):=by
 refine ⟨⟨h.width,fun i=> ⟨(h.rows i).1,(h.rows i).2.1,(h.rows i).2.2.trans he⟩,h.two, market_b R.cubic h.three hp,market_b R.quartic h.four hx,fun i=> ⟨(h.invariant i).1,(market_s _ (h.invariant i).2.1).1,(market_s _ (h.invariant i).2.2).1⟩,h.symTerms,h.metric,h.loopTerms,h.loop_normal⟩,fun i=> ?_⟩
 exact ⟨twoK _ (h.invariant i).1,(market_s _ (h.invariant i).2.1).2,(market_s _ (h.invariant i).2.2).2⟩
lemma quadratic_c (h:R.Bounds q σ A B) (U:Config SU.group n):quadratic p R (echo U) = quadratic p R U:=by
 unfold quadratic; refine sum_congr rfl fun i _=>?_ ; rw [faceValue,echo_t,cold]; congr 3
 unfold RG.PathData.ell; have ht(j):R.ellTerms i j (echo U) = frolic (R.ellTerms i j U):=by unfold RG.PathData.ellTerms; rw [tollSlot,map_smul]
 simp_rw [ht]; change ‖∑' j,frolic.toContinuousLinearMap _‖= _; rw [← frolic.toContinuousLinearMap.map_tsum]; exact frolic.norm_map _; exact ((R.ell_dominated h i).summable U) -- tune
lemma echo_uncut (F:ℕ→Atom SU.group k)(h:∀ i,Prist (F i)) (U:Config SU.group n):uncut F (echo U) = uncut F U:=by unfold uncut Atom.unmasked; simp_rw [tollSlot]; apply sum_congr rfl; intro i _; exact tsum_congr fun k=> h k _
lemma lore(r:Rare R)(h:R.Bounds q σ A B)(U:Config SU.group n): mainTerm p R (echo U)=mainTerm p R U:=by unfold mainTerm; simp_rw [echo_p, quadratic_c h,echo_uncut R.cubic (fun i=>(r i).2.1),echo_uncut R.quartic (fun i=>(r i).2.2)]
lemma engross(r:Rare R)(U:Config SU.group n): Precision.loop R (echo U)=Precision.loop R U:=by unfold Precision.loop; simp_rw [echo_p, echo_uncut R.loop (fun i=>(r i).1)]
lemma splits(h:R.Bounds q σ A B)(U:Config SU.group n): mainTerm p (solvent R) U= (mainTerm p R U+mainTerm p R (echo U))/2:=by
 let m(i:Signed):= quadratic p R (pull i 0 U)
 have he(i:Signed): (quadratic p (solvent R) (pull i 0 U)+uncut (solvent R).cubic (pull i 0 U)+uncut (solvent R).quartic (pull i 0 U))=((m i+uncut R.cubic (pull i 0 U)+uncut R.quartic (pull i 0 U))+(m i+uncut R.cubic (echo (pull i 0 U))+uncut R.quartic (echo (pull i 0 U))))/2:=by
    change m i+uncut (market∘R.cubic) _+uncut (market∘R.quartic) _=_; rw [uncP R.cubic h.three h.width,uncP R.quartic h.four h.width]; ring
 unfold mainTerm RG.Patch.average; simp_rw [he,echo_p,quadratic_c h]; unfold m; rw [←sum_div,sum_add_distrib]; ring
end YM.CF.Reef
