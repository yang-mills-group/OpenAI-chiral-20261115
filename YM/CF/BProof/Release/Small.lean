import YM.CF.BProof.Law.Move
import YM.CF.BProof.Chart
import YM.LocalH.Haar

/- exponential one Apt. Open domain (no boundary Jacob on shell); dry uses weak ≤.
Scale choices enforce shell in that domain and local chart log equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release
open Function MeasureTheory Filter RG Wilson Lattice Precision Law Set Metric
open scoped BigOperators Topology Classical ENNReal Matrix.Norms.Frobenius
variable {G:Gauge}
structure Pub (G:Gauge) where
 Q : ChartRatio G
 actual : LocalRatio Q
 radius : ℝ
 C : ℝ
 positive : 0<radius
 holds : radius < Q.radius
 cost : 0≤C
 log_tariff x : ‖x‖≤ radius → |Real.log (Q.J x)| ≤ C*‖x‖
lemma stock (Q:ChartRatio G)(h:LocalRatio Q) : ∃ S: Pub G,S.Q=Q := by
 have ht: ContDiffAt ℝ ⊤ (fun x=> Real.log (Q.J x)) 0:= ((h.germ 0 (mem_ball_self h.patch)).log (by rw [h.anchored]; norm_num)).of_le (by simp)
 obtain ⟨C,d,hC,hd,H⟩:= chargedLip ht -- tune regularity
 let r:=min (Q.radius/2) d; have hv:0<Q.radius:=h.patch
 refine ⟨⟨Q,h,r,C,lt_min (half_pos hv) hd, (min_le_left ..).trans_lt (by linarith),?_,?_⟩,rfl⟩; exact hC.le
 intro x hx; have hx:=H 0 (mem_closedBall_self hd.le) x (mem_closedBall_zero_iff.mpr (hx.trans (min_le_right ..))) -- tune
 simpa [h.anchored,Real.norm_eq_abs] using hx
variable (T:Pub G) (K:Chart G) (R g:ℝ)
namespace Pub
abbrev near (A:G.El) : Set G.El := {x| cd G A x≤R}
variable (A:G.El)
lemma near_m : MeasurableSet (near R A):= measurableSet_le (by unfold cd; fun_prop) measurable_const

def atom (G:Gauge) := G.ColorIndex → ℝ -- abbrev?
-- keep real vectors unc
abbrev Atom (G:Gauge) := G.ColorIndex → ℝ
def grant (a : Atom G) : G.Color := g • (WithLp.toLp 2 a)
def unlock (a : Atom G) := A*G.lieExp (grant g a)
@[fun_prop] lemma grant_c : Continuous (grant (G:=G) g) := by unfold grant; fun_prop
@[fun_prop] lemma unlock_c : Continuous (unlock g A):=by unfold unlock; fun_prop
abbrev input : Set (Atom G) := grant g ⁻¹' (Metric.ball 0 T.Q.radius)
def soft := unlock g A ⁻¹' near R A ∩ T.input g
lemma soft_m : MeasurableSet (T.soft R g A):=((unlock_c g A).measurable (near_m R A)).inter ((grant_c g).measurable isOpen_ball.measurableSet) -- tune
-- dimension exact
abbrev many (G:Gauge):=G.lieDim
lemma volume_pres (hg:0<g): MeasurePreserving (grant (G:=G) g) (ENNReal.ofReal (g^(many G)) • volume) volume:=by
 let u : Atom G→ₗ[ℝ] Atom G:= g • LinearMap.id; have hp:LinearMap.det u=g^many G:=by unfold u many; rw [LinearMap.det_smul, Module.finrank_pi,LinearMap.det_id,mul_one]; exact congrArg (g^·) (by simp)
 have hx:0<LinearMap.det u:=by rw [hp]; positivity
 rw [←hp]; exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp G.ColorIndex).symm).comp (Law.MP.linear u hx) -- tune G implicit omitted variable
-- near in translated image iff. use chart log from K; must ensure <T.radius.
def phase (A:G.El) := (MeasurableEquiv.mulLeft A) '' G.lieExp '' ball 0 T.Q.radius
lemma commute {x:G.El} (h:x∈ near R A)(u:R≤ K.radius) (p:K.C*R ≤ T.radius) : let q:= logG G (A⁻¹*x); q∈ball 0 T.Q.radius ∧ x=A*G.lieExp q∧ ‖q‖≤K.C*R:=by
 intro q; have he:= K.C_one; have hx:G.chord (A⁻¹*x)≤K.radius:= (show G.chord (A⁻¹*x)≤R from h).trans u
 have hh : ‖q‖≤K.C*R:= (K.width _ hx).trans (mul_le_mul_of_nonneg_left h (by linarith)) -- tune h expected coercion
 refine ⟨mem_ball_zero_iff.mpr ((hh.trans p).trans_lt T.holds),?_,hh⟩; unfold q; rw [(K.exposes _ hx).2]; group
lemma phase_near (u:R≤K.radius)(p:K.C*R ≤T.radius): near R A ⊆ T.phase A := fun x hx=> by
 obtain ⟨a,b,c⟩:= commute T K R A hx u p; exact ⟨_,⟨_,a,rfl⟩,b.symm⟩
lemma phase_m : MeasurableSet (T.phase A) := (MeasurableEquiv.mulLeft A).measurableEmbedding.measurableSet_image.mpr (T.actual.isOpen.measurableSet) -- tune
lemma identify {a : Atom G}(h:a∈ T.soft R g A) (u:R≤ K.radius)(p: K.C*R ≤ T.radius): ‖grant g a‖≤K.C*R:=by
 obtain ⟨u,v,w⟩:= T.commute K R A h.1 u p; exact (congrArg (fun (x:G.Color)=>‖x‖) (T.actual.inject h.2 u (mul_left_cancel v))).trans_le w
abbrev bare (a:Atom G) := T.Q.scale*T.Q.J (grant g a)
def fee (a:Atom G) := if a∈ T.soft R g A then g^many G*T.bare g a else 0
def time := volume.withDensity (fun a=> ENNReal.ofReal (T.fee R g A a))
lemma fee_holds {a:Atom G}(h:a∈T.soft R g A)(p:0<g) : 0<T.fee R g A a:=by unfold fee; rw [if_pos h]; exact mul_pos (pow_pos p _) (mul_pos T.actual.scale (T.actual.pos _ h.2))
lemma fee_nn (p:0<g)(a:Atom G):0≤T.fee R g A a:=by by_cases h:a∈ T.soft R g A; exact (T.fee_holds R g A h p).le; unfold fee; rw [if_neg h]
@[fun_prop] lemma fee_c : Measurable (T.fee R g A):=Measurable.ite (soft_m T R g A) (measurable_const.mul (measurable_const.mul (T.actual.borel.comp (grant_c g).measurable))) measurable_const
lemma install (p:0<g)(u:R ≤ K.radius)(v: K.C*R≤ T.radius) : MeasurePreserving (unlock g A) (T.time R g A) (G.probHaar.restrict (near R A)):=by
 let X:=T.Q; let μ : Measure (Atom G):=ENNReal.ofReal (g^many G) • volume; let H : G.Color→ ℝ≥0∞ := fun a=>ENNReal.ofReal (X.scale*X.J a)
 let S:=ball (0:G.Color) X.radius; let W := (volume.restrict S).withDensity H
 have hg:Measurable H:=(measurable_const.mul T.actual.borel).ennreal_ofReal
 have hk: MeasurePreserving (grant g) ((μ.restrict (T.input g)).withDensity (H ∘ grant g)) W:= MP.fund (MP.cut (volume_pres (G:=G) g p) isOpen_ball.measurableSet) H hg
 let Q:=MeasurableEquiv.mulLeft A; let d:=G.lieExp '' S
 have hd:MeasurePreserving Q (G.probHaar.restrict d) (G.probHaar.restrict (T.phase A)):=by
   have hx: Q ⁻¹' T.phase A=d:= Q.injective.preimage_image d; rw [←hx]; exact MP.cut (measurePreserving_mul_left ..) (T.phase_m A)
 have he : MeasurePreserving (unlock g A) ((μ.restrict (T.input g)).withDensity (H ∘ grant g)) (G.probHaar.restrict (T.phase A)):=hd.comp ((show MeasurePreserving G.lieExp W (G.probHaar.restrict d) from ⟨G.lieExp_cont.measurable,T.actual.actual⟩).comp hk)
 have hv:=MP.cut he (near_m R A); rw [restrict_withDensity ((unlock_c g A).measurable (near_m R A)),Measure.restrict_restrict ((unlock_c g A).measurable (near_m R A)), Measure.restrict_restrict (near_m R A), inter_eq_left.mpr (phase_near T K R A u v)] at hv
 convert! hv using 1 <;> try rfl
 unfold time; change _=(μ.restrict (T.soft R g A)).withDensity (H ∘ grant g); unfold μ; rw [← withDensity_indicator (soft_m T R g A), withDensity_smul_measure, ←withDensity_smul' _ _ ENNReal.ofReal_ne_top]; congr 1; ext a; unfold fee; by_cases h:a∈ T.soft R g A
 · rw [if_pos h, ENNReal.ofReal_mul (by positivity)]; simp only [Pi.smul_apply,indicator_of_mem h,smul_eq_mul]; rfl
 rw [if_neg h,Pi.smul_apply,indicator_of_notMem h,smul_zero,ENNReal.ofReal_zero]
end Pub
end YM.CF.BProof.Release
