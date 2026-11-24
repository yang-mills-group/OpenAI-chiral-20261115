import YM.SU5.FiniteGaugeData.Trigonal.Panel
import Mathlib.MeasureTheory.SpecificCodomains.Pi
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option linter.unusedSimpArgs false
namespace YM.CF.Window.Trigo
open Function Filter Finset Metric
open Laurent Lattice Next.Free Bloch Fir Lat ArchiveK Largo WithLp MeasureTheory Complex
open scoped Topology BigOperators Set Pointwise InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra μFin
set_option quotPrecheck false
-- universal meromorphic extinction lemma. One output component whose kernel is linear of melody/slurp. proof takes multiplicities grouped by polynomial Site into L'.
section
variable (S T:Finset Cover)
local notation "Ω"=> Momentum →ₗ[ℂ] ℂ
variable (F:Cover→ Momentum→ₗ[ℂ]ℂ)
noncomputable def preQ (S:Finset Cover) (F:Cover→ Momentum→ₗ[ℂ]ℂ) (p:Momentum)(t:Momentum) :ℂ:= ∑ x∈S,mode p (-x) * F x t
-- support bill.L
abbrev Limb(S:Finset Cover)(F:Cover→ Momentum→ₗ[ℂ]ℂ) := fun x:E4=> preQ S F (brushQ x) (slurp x)
abbrev Tang(B:Cover→ℂ)(T:Finset Cover)(p:Momentum):ℂ:= ∑ x∈T, mode p (-x)*B x
lemma Loan(a:Ω):Integrable (a ∘ slurp) μF:= (a.toContinuousLinearMap.restrictScalars ℝ).integrable_comp (integrable_pi_iff.mpr (fun i=> slurp_I i)) -- tune
lemma scout_v(x:Cover): scout (Limb S F) x=∑ y∈S, scout (F y∘ slurp) (x-y) :=by
 let f(a:Cover):=fun y:E4=> pulseFT (-a) y • (F a) (slurp y); change scout (fun p:E4=>∑ a∈S,f a p) x=_; rw [scout_sum _ f (fun i _=> sing_in (Loan (F i)) (-i))]; exact sum_congr rfl fun a _=>by dsimp only [f,pulseFT]; rw [sub_eq_add_neg]; exact scout_more (F a ∘ slurp) (-a) x
lemma feasible(t:E4)(h:brushQ t∈doorP)(k:t≠0): ContinuousAt slurp t:=by
 let M(x:E4):=brushQ x; let Z:= M t; have hv:pass Z≠0:= (by rw [show pass Z=_ from spendQ t]; exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr k))); have he: ContinuousAt M t:= brush_safe.continuousAt; let L(x:E4):= (pass (M x))⁻¹ • (AcornT (M x)); apply ContinuousAt.congr (f:=L) ?_ (EventuallyEq.symm ?_)
 · exact (((differPass.continuous.continuousAt.comp he).inv₀ hv).smul ((AcornT.cont.continuousAt (isOpen_ball.mem_nhds h)).comp he))
 filter_upwards [(differPass.continuous.continuousAt.comp he).eventually_ne hv,he.eventually (isOpen_ball.mem_nhds h)] with y t v; unfold L; rw [AcornT.billing v t,inv_smul_smul₀ (show pass (M y)≠0 from t)] -- tune Eq symm
lemma atlas (h:∀ x∉T,scout (Limb S F) x=0):∀ᶠ x:E4 in 𝓝 0, preQ S F (brushQ x) (AcornT (brushQ x)) = pass (brushQ x)* Tang (scout (Limb S F)) T (brushQ x):=by -- rm p
 let b:= Limb S F; let c:= scout b; let A:= Tang c T; let f(a:Cover):=fun y:E4=> pulseFT (-a) y • (F a) (slurp y); have hb: Integrable b μF:=integrable_finsetSum S (f:=f) (fun i _=> sing_in (Loan (F i)) _)
 let g(a:Cover):=fun y:E4=> pulseFT (-a) y • c a; have hv(a):Integrable (g a) μF:= sing_in (integrable_const _) (-a)
 have hm(x:Cover): scout (A ∘ brushQ) x= scout b x:=by
    change scout (fun p:E4=>∑ a∈T,g a p) x=_; rw [scout_sum _ g (fun i _=> hv i)]; simp_rw [g,pulseFT,scout_more,pact]; by_cases p:x∈T
    · rw [sum_eq_single x]
      · rw [add_neg_cancel,if_pos rfl]
      · intro i l t; rw [if_neg (fun u=>t (add_neg_eq_zero.mp (show x + -i=0 from u)).symm)]
      exact fun v=>(v p).elim
    rw [h x p,sum_eq_zero]; intro i l; rw [if_neg (fun t=>p ((add_neg_eq_zero.mp (show x + -i=0 from t)).symm ▸ l))] -- tune indentation
 let X:= A ∘ brushQ; let B:= b-X; have hX:Continuous X:=by unfold X A Tang; apply continuous_finsetSum; intro; intro; exact (song_in _).mul continuous_const
 have hB:Integrable B μF:= hb.sub (integrable_finsetSum T (f:=g) (fun i _=>hv _)); have ht(x:Cover): scout B x=0:= by
    rw [show B=b + -X from sub_eq_add_neg ..]; change scout (fun x=>b x + (-X) x) x=_; have hU:Integrable X μF:= integrable_finsetSum T (f:=g) (fun i _=>hv _); rw [scout_add hb hU.neg]; change _+scout (fun p=> -X p) x=_; unfold scout; simp_rw [ smul_neg,integral_neg,smul_neg]; change scout b x + -scout X x= _; rw [show scout X x=scout b x from hm x, add_neg_cancel]
 have he(i:Cover): Continuous fun z=> mode (brushQ z) (-i):=song_in _
 have hu: (0:E4)∈realIn:=fun i=> by change |(0:ℝ)|< _; simpa using Real.pi_pos;
 have hh: brushQ 0∈ doorP:= by rw [show brushQ 0=0 from (by ext; simp [brushQ,tmap,PiLp.zero_apply])]; exact mem_ball_self zero_lt_one
 filter_upwards [realIn_g.mem_nhds hu,brush_safe.continuousAt.eventually (isOpen_ball.mem_nhds hh)] with u v k; by_cases U:u=0
 · rw [U, show brushQ 0=0 from (by ext; simp [brushQ,tmap,PiLp.zero_apply])]; have hv:pass 0=0:=(by simp [pass]); unfold preQ; simp_rw [hv, AcornT.null hv]; simp
 have hy:= feasible u k U; have hpZ:ContinuousAt b u:= tendsto_finsetSum _ (fun i _=> (he i).continuousAt.tendsto.mul ((F i).toContinuousLinearMap.continuous.continuousAt.comp hy)) -- tune binder expression hidden preQ.
 have hz:= Fabre B hB ht v (hpZ.sub hX.continuousAt); let z:= brushQ u; have hi: b u=A z:= sub_eq_zero.mp hz; rw [AcornT.billing k ?_]; swap; · rw [spendQ]; exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr U))
 change preQ S F z (pass z • slurp u)= pass z*A z; rw [←hi]; unfold b Limb preQ; simp_rw [map_smul, mul_sum,smul_eq_mul]; exact sum_congr rfl fun i _=>mul_left_comm _ _ _
-- pin on a complex null line
lemma hookR {a b:E4}(c:‖a‖=‖b‖)(d:inner ℝ a b=0)(p:Injective (fun x:Cover=> inner ℝ (emitX x) a))(h:∀ x∉T, scout (Limb S F) x=0): ∀ i∈S,F i (needleQ a b)=0:=by
 let Z:= needleQ a b; let W:= Tang (scout (Limb S F)) T; let X(u:Momentum):= preQ S F u (AcornT u)-pass u*W u
 have hp:Hose X:=by
    intro B U y p t; have he:= AcornT.film U t p; have hf (x:Cover): DifferentiableOn ℂ (fun z=>mode (y z) (-x)) B:=by unfold mode; fun_prop -- many
    have hg: Differentiable ℂ W:=by unfold W Tang mode; fun_prop
    refine DifferentiableOn.sub (DifferentiableOn.fun_sum (u:=S) ?_) ((differPass.comp_differentiableOn p).mul (hg.comp_differentiableOn p)); intro i _; exact (hf i).mul ((F i).toContinuousLinearMap.differentiable.comp_differentiableOn he)
 have he:= (tube a b hp (show ∀ᶠ i:E4 in 𝓝 0, X (brushQ i)=0 from (atlas S T F h).mono (fun i p=>sub_eq_zero.mpr p))).filter_mono (nhdsWithin_le_nhds (s:=Set.Ioi 0))
 apply flashN (u:=S) _ _ (PriceSep a b p) -- expected ext? output F;implicit metavars
 have hv:∀ᶠ x:ℝ in 𝓝 (0:ℝ), leer ((x:ℂ) • Z)≠0:= by
    apply (show Continuous fun x:ℝ=> leer ((x:ℂ) • Z) by fun_prop).continuousAt.eventually_ne; simp [leer,hzero]
 filter_upwards [he,hv.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r w u v; change ∑ i∈S,F i Z * Complex.exp (_*DotX Z (-i))=_
 let z:=(r:ℂ) • Z; have k : pass z=0:= needle_i _ (needleI _ _ c d); change X z=0 at w; unfold X preQ at w; rw [k,zero_mul,sub_zero, AcornT.null k] at w
 let y:=(leer z ^ 8*2:ℂ)*(r:ℂ); have hy:y≠0:=mul_ne_zero (mul_ne_zero (pow_ne_zero _ u) (by norm_num)) (Complex.ofReal_ne_zero.mpr (show r>0 from v).ne'); rw [←mul_right_inj' hy]; rw [mul_sum,mul_zero]; refine Eq.trans ((?_): _=_) w; refine sum_congr rfl fun i j=> ?_; simp only [map_smul,z, smul_eq_mul, scaleDot]; unfold y z; ring
lemma royalty (h:∀ x∉T, scout (Limb S F) x=0){a:E4}(p:Injective (fun x:Cover=> inner ℝ (emitX x) a)): ∀ i ∈ S,F i (brushQ (a+a))=0:=by
 let B:= eSwing a; obtain ⟨d,v⟩:= ePartner a; have he: ‖a‖=‖-B‖:= (by rw [norm_neg]; exact d); have hp:inner ℝ a (-B)=0:=by rw [inner_neg_right]; exact v.symm ▸ neg_zero; -- tune
 intro i u; rw [← needlesum a B,map_add,hookR S T F (b:=B) d v p h i u,hookR S T F (b:=-B) he hp p h i u,add_zero]
#print axioms royalty
end
end YM.CF.Window.Trigo
