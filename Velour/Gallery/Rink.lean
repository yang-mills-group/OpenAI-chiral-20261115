import YM.SU5.FiniteGaugeData.Celeritas.Sledge
/-! Adaptation of Celeritas.Sledge for arbitrary direction set. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas.Division
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a b: Axis}(S:OS.Semigroup H a)(D:Set (Cross a))(v: OS.Cross a)(x:E4)(t:ℝ)(u s:ℝ≥0)
local notation "Π" x:max=> Probe.plane x
local notation "Λ" x:max=> metal a x

def Delimit (D:Set (Cross a)):= {x:E4| ∀ v∈D,|ped x v|≤x a}
lemma pitch (x:E4): x∈Delimit D ↔ ∀ v∈D,|ped x v| ≤ x a:= Iff.rfl
lemma shuts : IsClosed (Delimit D):=by
 unfold Delimit; simp_rw [setOf_forall]; refine isClosed_iInter (fun i=> isClosed_iInter fun _=>isClosed_le ?_ ?_)
 · unfold ped; fun_prop
 · fun_prop
lemma flipPay (v:OS.Cross a){x:E4}(t: x∈ Delimit D) (h:v∈D): rateX a ((s:ℝ) • v.val) (u+s) x ≤ rateT a (u+s) u x:=by
 have hn:= (pitch D x).1 t v h; let D:= metal a (u+s) x; let E:= metal a u x; let V:= Real.exp ((s:ℝ)*x a:ℝ); have hp:=hn; have he:E=D*V:=by unfold D E V; unfold metal; rw [←Real.exp_add]; push_cast; ring_nf
 have hg:‖Probe.plane x ((s:ℝ) • v.val)-1‖ ≤ V-1:= by rw [plane_rate]; apply (whiff ..).trans; rw [abs_of_nonneg s.coe_nonneg]; nlinarith only [mul_le_mul_of_nonneg_left hp s.coe_nonneg, (show (s:ℝ)*x a+1 ≤ V from Real.add_one_le_exp _)]
 let ε:=‖Probe.plane x ((s:ℝ) • v.val)-1‖; have hD:0≤D:=metal_0 ..; unfold rateX; rw [metal_add,←pow_two]; change D^2*ε^2 ≤ (E -D)^2; rw [←mul_pow,he]; apply pow_le_pow_left₀ (mul_nonneg hD (norm_nonneg _)); nlinarith only [mul_le_mul_of_nonneg_left hg hD]
variable (x:H)(P: PVM H E4)
local notation "U" v:max=> S.U v
local notation "F" t:max=> S.E t
abbrev Velocity (u:ℝ≥0)(k:ℝ)(x:H): Prop := ∀ (v:Cross a), v∈D → ∀ (s:ℝ≥0), (s:ℝ)≤ k→ dist ((U ((s:ℝ) • v)) ((F (u+s)) x)) ((F (u+s)) x) ≤ dist ((F (u+s)) x) ((F u) x)
local notation "T"=>Delimit D
local notation "Pm"=> S.ℚmeasure
local notation "Po" x:max=> S.ℚmeasure.diagonal x
abbrev Cinema := S.ℚmeasure.region (Delimit D)ᶜ=0
@[fun_prop] lemma ratex(z:E4) : Continuous (rateX a z s):= (mint _).mul (((Probe.plane_cont.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow _)
@[fun_prop] lemma ratet : Continuous (rateT a u s):= ((mint _).sub (mint _)).pow _
lemma veer (k:ℝ) : Velocity S D u k x ↔ ∀ (v:Cross a), v∈D → ∀ (s:ℝ≥0), (s:ℝ)≤ k→ (∫ p, rateX a ((s:ℝ) • v.val) (u+s) p ∂ (Po x)) ≤ (∫ p, rateT a (u+s) u p ∂ (Po x)):=by
 unfold Velocity; apply forall_congr'; intro v; apply forall_congr'; intro e; apply forall_congr'; intro s; apply forall_congr'; intro q
 rw [ (paid_P ..).2,(paid_T ..).2]; refine Iff.trans ?_ (sq_le_sq₀ (by positivity) (by positivity)).symm
 rw [←vacancy]; rfl
lemma chinaK (p:Cinema S D)(w:H) : ∀ᵐ u∂Po w, u∈ T:= by rw [ae_iff]; exact ((Pm).null_pair (shuts D).isOpen_compl.measurableSet w).2 (by rw [p]; rfl) -- tune arg
variable {k:ℝ}
lemma vell (p:Cinema S D):Velocity S D u k x :=(veer S D u x k).2 (fun v e s _=> integral_mono_ae (paid_P ..).1 (paid_T ..).1 (Eventually.mono (chinaK S D p x) (fun i p=> flipPay D u s v p e))) -- tune
-- enough on dense via closed condition
lemma closed_v {K:ℝ}: IsClosed {x:H| Velocity S D u K x}:=by
 simp_rw [Velocity,setOf_forall]; refine isClosed_iInter (fun i=> isClosed_iInter (fun _=> isClosed_iInter fun s=> isClosed_iInter (fun e=> isClosed_le ?_ ?_))); all_goals fun_prop
lemma sure_support {Q:PVM H E4}(s:Set E4)(h:IsOpen s)(p:IsClosed sᶜ) (x:H)(t:Q.diagonal x s≠0): let y:=Q.region s x; (∀ᵐ z ∂ Q.diagonal y,z∈ s) ∧ NeZero (Q.diagonal y):=by
 intro y; have hv:y≠0:= fun e=> t ((Q.null_pair h.measurableSet x).2 e); constructor
 · rw [ae_iff]; apply (Q.null_pair p.measurableSet y).2; change Q.region sᶜ y=0; unfold y; rw [← ContinuousLinearMap.comp_apply,Q.joins p.measurableSet h.measurableSet,compl_inter_self,Q.none]; rfl
 exact ⟨fun z=> hv (let t:= (Q.null_pair (s:=univ) MeasurableSet.univ y).1 (by rw [z]; rfl); by rwa [Q.all] at t) ⟩
lemma free_run (u0:0<k)(h:∀ x:H,Velocity S D u k x) : Cinema S D:=by
 have he(x:H) : (Po x).support ⊆ Delimit D:=by
    intro y p; rw [pitch]; intro v t; by_contra! e
    obtain ⟨s,g,p',l⟩:= slotPay u v e (S.nonneg x p) k u0; let f:=rateX a ((s:ℝ) • v.val) (u+s); let g:=rateT a (u+s) u; let V:= {x| g x<f x}; have hz:IsOpen V:= isOpen_lt (ratet _ _) (ratex ..); have H0:(Po x) V≠0:= ne_of_gt ((Measure.mem_support_iff_forall y).1 p V (hz.mem_nhds l)) -- extra V arg
    obtain ⟨Ax,l⟩:= sure_support V hz hz.isClosed_compl x H0; let X:= (Pm).region V x; haveI hp:NeZero (Po X):=l
    have hL:g ≤ᵐ[Po X] f:= Ax.mono (fun i t=> (show g i<f i from t).le); have hf:Integrable f (Po X):=(paid_P ..).1; have hk:Integrable g (Po X):=(paid_T ..).1
    have hv:∫ z,g z ∂ (Po X)=∫ z,f z ∂(Po X):=le_antisymm (integral_mono_ae hk hf hL) ((veer S D u X k).1 (h X) v t s p')
    obtain ⟨z,e,hz⟩:= (Ax.and ((integral_eq_iff_of_ae_le hk hf hL).1 hv)).exists; exact (show g z<f z from e).ne hz

 unfold Cinema; ext1 x; exact ((Pm).null_pair (shuts D).isOpen_compl.measurableSet x).1 (measure_mono_null (compl_subset_compl.mpr (he x)) (measure_compl_support))
theorem correct (u0:0<k)(V:Set H) (p:Dense V): Cinema S D ↔ ∀ x∈V,Velocity S D u k x:= ⟨fun p x _=> vell S D u x p,fun e=> free_run S D u u0 fun x=> closure_minimal (t:={x| Velocity S D u k x}) e (closed_v S D u) (p x)⟩
#print axioms correct
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas.Division

