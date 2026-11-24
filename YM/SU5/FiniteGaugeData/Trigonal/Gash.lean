import YM.SU5.FiniteGaugeData.Trigonal.Fabre
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
abbrev Hose(f:Momentum→ℂ): Prop:= ∀ (S:Set ℂ),IsOpen S→∀ Z:ℂ→Momentum, DifferentiableOn ℂ Z S→ Set.MapsTo Z S doorP → DifferentiableOn ℂ (f∘ Z) S
-- transfer along complex line from arbitrary real feet
abbrev pliance(a b:E4)(t:ℂ):Momentum:=brushQ a + t • brushQ b
def needleQ(a b:E4):Momentum:=pliance a b Complex.I
variable {a b:E4}{p:Momentum}{x:ℂ}{f:Momentum→ℂ}
lemma brite(a b:E4)(p:ℝ): pliance a b (p:ℂ)=brushQ (a+p • b):=by funext i; simp [pliance,brushQ,tmap,PiLp.add_apply]
private lemma bless(Z:Set ℂ){f:ℂ→ℂ}(p:IsOpen Z)(v:IsPreconnected Z)(e:0∈Z)(t:∀ᶠ x:ℝ in 𝓝[>] (0:ℝ), f x=0)(w:DifferentiableOn ℂ f Z): ∀ x∈ Z,f x=0:=by
 refine fun x h=>(w.analyticOnNhd p).eqOn_of_preconnected_of_frequently_eq (g:=fun _=>0) analyticOnNhd_const v e ?_ h; intro q
 have hp:Tendsto ((↑):ℝ→ℂ) (𝓝[>] (0:ℝ)) (𝓝[≠] 0):= by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; · exact continuous_ofReal.continuousAt.continuousWithinAt
    filter_upwards [self_mem_nhdsWithin] with i u; exact fun e=> (Set.mem_Ioi.mp u).ne' (by exact_mod_cast (show (i:ℂ)=0 from e))
 obtain ⟨i,l,z⟩:= (t.and (hp.eventually q)).exists; exact z l
lemma tube(a b:E4)(h:Hose f)(t:∀ᶠ x:E4 in 𝓝 (0:E4), f (brushQ x)=0):∀ᶠ u:ℝ in 𝓝 (0:ℝ), f ((u:ℂ) • needleQ a b)=0:=by
 let V:=ball (0:ℂ) 2; let F(t:ℝ × ℂ): Momentum:=(t.1:ℂ) • pliance a b t.2; have he: Continuous F:= by unfold F pliance; fun_prop
 -- compact bounded u via norms
 have ht:∀ᶠ u:ℝ in 𝓝 (0:ℝ),∀ y∈ V,F (u,y)∈doorP:=by
    let C:= ‖brushQ a‖ + 2* ‖brushQ b‖; have hv:∀ y∈V,‖pliance a b y‖≤ C:= fun y h=> (norm_add_le ..).trans (add_le_add_right (by rw [norm_smul]; exact mul_le_mul_of_nonneg_right ((mem_ball_zero_iff.mp h).le) (norm_nonneg _)) _)
    have hm: ‖(0:ℝ)‖*C < 1:=by simp; -- parser
    filter_upwards [((show Continuous fun u:ℝ=> ‖u‖*C from continuous_norm.mul continuous_const).continuousAt.eventually (gt_mem_nhds hm))] with u p y Y; rw [mem_ball_zero_iff]; unfold F; apply lt_of_le_of_lt _ p; rw [norm_smul,Complex.norm_real]; refine mul_le_mul_of_nonneg_left (hv _ Y) (norm_nonneg u)
 obtain ⟨S',s₀,S,g⟩:= _root_.mem_nhds_iff.mp t
 filter_upwards [ (show Continuous fun u:ℝ=> u • a from by fun_prop).continuousAt (x:=0)|>.eventually (S.mem_nhds (show (0:ℝ) • a∈S' from (zero_smul ℝ a).symm ▸ g)), ht] with x W y
 let P(z:ℂ):= F (x,z); have hp:= h V isOpen_ball P (by unfold P F pliance; dsimp only; fun_prop) y; apply bless V isOpen_ball (convex_ball ..).isPreconnected (mem_ball_self (by norm_num)) (f:=f ∘ P) _ hp Complex.I (show Complex.I∈V by unfold V; norm_num)
 have he: ∀ᶠ z:ℝ in 𝓝[>] (0:ℝ), x • (a+z • b)∈ S':= Filter.Eventually.filter_mono nhdsWithin_le_nhds (((show Continuous fun z:ℝ=> x • (a+z • b) from by fun_prop).continuousAt (x:= (0:ℝ))).eventually (S.mem_nhds (by simpa only [zero_smul,add_zero])))
 filter_upwards [he] with k v; unfold Function.comp P F; rw [brite,show (x:ℂ) • brushQ (a+k • b)=brushQ (x • (a+k • b)) from ?_]; · exact s₀ v
 funext i; simp [brushQ,tmap]; ring -- tune
lemma needlesum(a b:E4): needleQ a b + needleQ a (-b)= brushQ (a+a):=by funext i; simp [needleQ,pliance,tmap,brushQ]; ring
lemma needleI(a b:E4)(p:‖a‖=‖b‖)(g:inner ℝ a b=0): pass (needleQ a b)=0:=by
 let x:= brushQ a; let y:=brushQ b; have he(i:Axis): (needleQ a b i)^2=x i^2 - y i ^2 + 2*Complex.I*(x i*y i):=by change (x i + Complex.I * y i)^2 =_; ring_nf; simp; ring -- tune
 unfold pass; simp_rw [he, sum_add_distrib,sum_sub_distrib, ←mul_sum]; rw [show ∑ i:Axis,(x i)^2= (((‖a‖^2):ℝ):ℂ) from spendQ a,show ∑ i:Axis,(y i)^2= (((‖b‖^2):ℝ):ℂ) from spendQ b, p,sub_self]
 rw [show ∑ i:Axis,x i*y i=(inner ℝ a b:ℂ) from ?_,g]; simp; rw [pis]; push_cast; rfl
lemma needle_i(t:ℂ)(p:pass (needleQ a b)=0): pass (t • needleQ a b)=0:=by unfold pass; simp only [Pi.smul_apply,smul_eq_mul,mul_pow,←mul_sum]; exact mul_eq_zero.mpr (Or.inr p)
#print axioms tube
#print axioms needleI
lemma brush_sep : ∃ a:E4,a≠0∧ Injective (fun x:Cover=> inner ℝ (emitX x) a):=by
 let μ: Measure E4:= volume; have he(t:E4)(g:t≠0): ∀ᵐ y∂μ,inner ℝ t y≠0:=by
    let H:= LinearMap.ker (innerSL ℝ t).toLinearMap; have h:∀ᵐ y ∂ μ, y∉H:=by
       rw [ae_iff]; simp only [not_not]; apply Measure.addHaar_submodule μ H; intro h; have z:t∈H:=by rw [h]; trivial; -- tune
       exact g (inner_self_eq_zero.mp z)
    exact h
 have ht: ∀ᵐ y∂μ, ∀ a b:Cover,a≠b→ inner ℝ (emitX a) y≠ inner ℝ (emitX b) y:= by
    refine ae_all_iff.mpr fun a=>ae_all_iff.mpr fun b=> ae_all_iff.mpr fun p => ?_; simpa only [inner_sub_left,ne_eq,sub_eq_zero] using he _ (sub_ne_zero.mpr (emit_in.ne p))
 obtain ⟨x,z,h⟩:= ((zero_free (MeasureTheory.volume (α:=E4))).and ht).exists; exact ⟨x,z, fun i j p=> not_not.mp fun k=> h i j k p⟩
def eSwing(x:E4):E4:=toLp 2 ![x 1,-x 0,x 3,-x 2]
lemma ePartner(x:E4): ‖x‖=‖eSwing x‖ ∧ inner ℝ x (eSwing x)=0:=by
 constructor; · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]; simp [eSwing, Fin.sum_univ_succ,Axis]; ring
 rw [pis]; simp [eSwing,Axis,Fin.sum_univ_succ]; ring
#print axioms brush_sep
end YM.CF.Window.Trigo
