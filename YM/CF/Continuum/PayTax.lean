/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Graph.Easel
import YM.CF.Girt.Zero
import YM.Next.RANK.Determinant

/-! # Use base contribution also for FiniteGaugeData at a whole period

From `Next.RANK.{Axial,Determinant}` --- use the strategy of the base theorem
but for the actual terms of the FiniteGaugeData complex/vFock rate. It is **not** a roll
of pure YM pressure or an application with complex weights replaced by absolute
ones. Give the two budgets separately for the clear-cube part and all flags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial
open Graph Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova YM.Next.Rank
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {N : Side}{a b c v g C L μ : ℝ}

lemma variance_beta (t:0<g) (e:b*g^2=1) : 0<b := by rw [show b=1/g^2 from (eq_div_iff (pow_ne_zero _ t.ne')).mpr e]; positivity

lemma basal_cost {G:Gauge}(V: Config G N) {F:PathData G}{C:RG.Clip}{q:BudgetPoint}(t:0<g) (e:b*g^2=1) (r:g≤q.threshold) (p:Face (Per N)) :
   G.chord (faceValue V p)/(g/strength C)-1 ≤ b* F.baseTerm C q V p := by
  -- comparison as for determinant.Numerator
  let f:=G.chord (faceValue V p); let s:=strength C
  have hp:0<b:=variance_beta t e; have hv:0≤f:= G.chord_nonneg _; have hX: 0<s:=strength_pos C; have ht:s≤C.linear:=min_le_right ..; have he:s≤C.direct:=by have h:=C.kink; linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (show PathData.clipped C q.threshold f ≤ _ from ?_) hp.le)
  · change f/(g/s)-_ ≤_; rw [show f/(g/s)=s*(f/g) by field_simp]; unfold PathData.clipped; split_ifs
    · calc
       s*(f/g)-1 ≤ s*((f/g)^2)/2:= by have h₁:s≤1:=strength_le_one _; nlinarith only [h₁, show 0 ≤ s *((f/g)-1)^2 from mul_nonneg hX.le (sq_nonneg _)]
       _ = b *(s*f^2/2) := by rw [show b=1/g^2 from (eq_div_iff (pow_ne_zero _ t.ne')).2 e]; ring
       _ ≤ _ := by gcongr
    calc
      s*(f/g)-1 ≤ s*(f/g):=by linarith only
      _ ≤ C.linear*(f/g):= mul_le_mul_of_nonneg_right ht (by positivity)
      _ = b*(C.linear*g*f):=by rw [show b=1/g^2 from (eq_div_iff (pow_ne_zero _ t.ne')).2 e]; field_simp
      _ ≤ _:=by gcongr; exact C.tail_pos.le
  unfold PathData.baseTerm; apply le_add_of_nonneg_right; split_ifs <;> positivity

section sugar
variable {G:Gauge}{F:PathData G}{C':RG.Clip}{q:BudgetPoint}(b':F.Bounds C' a C L)(t:0<g)(e:b*g^2=1)(h:g≤q.threshold)
include b' t e h
lemma per_channel (V:Config G N):
   (∑ p:Face (Per N), G.chord (faceValue V p) /(g/strength C')) - Fintype.card (Face (Per N))-taxY N b q.threshold C L ≤ F.inChannels C' q b V:=by
  let Q:=Fintype.card (Face (Per N)); let r:=g/strength C'; let D(U:Config G N):=∑ p:Face (Per N), G.chord (faceValue U p) / r
  have s (k:Signed): D (Lattice.pull k 0 V)=D V:=by
    unfold D; simp_rw [Face.send_price V _ k 0 G.chord G.chord_inv (fun _ u => G.chord_conj u _)]
    let e : Equiv.Perm (Face (Per N)) := Equiv.ofBijective (Face.send k 0) ⟨Face.injective_send k 0, Finite.injective_iff_surjective.mp (Face.injective_send k 0)⟩
    exact Equiv.sum_comp e (fun x => G.chord (faceValue V x)/r)
  let T:= taxY N b q.threshold C L; let X:=D V-Q-T
  have he(j:Signed): X ≤ F.principal C' q b (Lattice.pull j 0 V) := by
    let U:=Lattice.pull j 0 V; let A:= b*(N.val:ℝ)^4*(C*q.threshold^3+C*q.threshold^4); let z:ℝ:= N.val^4*(L*q.threshold^2)
    obtain ⟨hr,hB⟩:= oath b' q U; let Y(i:Face (Per N)):= F.baseTerm C' q U i; have hF := sum_le_sum (s:=univ) fun i _=>basal_cost U (F:=F) (C:=C') t e h i
    rw [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,←mul_sum] at hF -- edit
    have ht:D V - Q ≤ b * ∑ i:Face (Per N),Y i:=by
       rw [←s j]; exact hF
    unfold PathData.principal; rw [mul_add]; apply le_trans ?_ (add_le_add (add_le_add ht (mul_le_mul_of_nonneg_left (neg_le_of_abs_le hr) (variance_beta t e).le)) (neg_le_of_abs_le hB)); apply le_of_eq; unfold X T taxY; ring
  exact le_trans (show X≤(Fintype.card Signed:ℝ)⁻¹*∑ j:Signed,X from le_of_eq (by simp)) ((mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> he i)) (by positivity)))
end sugar

def priorWeight (V:GramM N)(x:Pane N):ℝ:= (Calm group (More N) V.p.threshold).indicator (Graph.past V) x
lemma weight_nonneg (V:GramM N)(x:Pane N): 0 ≤ priorWeight V x:=Set.indicator_nonneg (fun _ _=>(Real.exp_pos _).le) x
lemma weight_gauge (V:GramM N)(p:V.path.Bounds V.funds μ C L) : GaugeInvariant (priorWeight V) := by
  intro j k; unfold priorWeight; have ht:= Girt.thumb V p k j; by_cases e:k ∈ Calm group (More N) V.p.threshold
  · rw [Set.indicator_of_mem e]; have he: flags V.p.threshold (Lattice.gauge j k)=∅:=by rw [RG.gauge_flags]; exact e
    rw [Set.indicator_of_mem (show _∈ Calm _ _ _ from he)]; unfold past; rw [ht]
  rw [Set.indicator_of_notMem e,Set.indicator_of_notMem]; intro h; change flags V.p.threshold (Lattice.gauge j k)=∅ at h; rw [RG.gauge_flags] at h; exact e h
lemma weight_is (V:GramM N)(x: Orbit N) : Graph.dim V x=priorWeight V x.1 := by
  by_cases e:x∈ Lace V; rw [Graph.dim,Set.indicator_of_mem e,priorWeight,Set.indicator_of_mem (show x.1∈ Calm _ _ _ from e)]
  rw [Graph.dim,Set.indicator_of_notMem e,priorWeight,Set.indicator_of_notMem (show x.1∉ Calm _ _ _ from e)]
lemma env_priorWeight(V:GramM N)(p:V.path.Bounds V.funds μ C L):Envelope (priorWeight V):=by
 let H:= pole_w (ι:=Pane N) (V.path.inChannels V.funds V.p V.beta) (fun x=> Real.exp (-x)) (by fun_prop) (V.path.channels_env p _ _)
 obtain ⟨v,h⟩:=H.cost; refine ⟨H.meas.indicator (calm_m ..),max v 0,fun i=>?_⟩; unfold priorWeight Set.indicator; split
 · exact (h i).trans (le_max_left ..)
 simp
lemma usesPrior {T:Type*}[NormedAddCommGroup T][NormedSpace ℝ T](f:Pane N→T)(t:Integrable f (prior group (More N))): (∫ i:Orbit N,f i.1∂city _) = ∫ i,f i ∂prior group (More N) :=by
   have he: MeasurePreserving (fun i:Orbit N=>i.1) (city N) (prior group (More N)):=measurePreserving_fst (μ:=prior group (More N)) (ν:=depot N)
   exact ((integral_map (μ:=city N) he.measurable.aemeasurable (f:=f) (he.map_eq.symm ▸ t.aestronglyMeasurable)).symm).trans (by rw [he.map_eq])
lemma weight_angle(V:GramM N)(p:V.path.Bounds V.funds μ C L) : Graph.angle V=∫ i,priorWeight V i ∂prior group (More N):=by unfold Graph.angle; simp_rw [weight_is]; exact usesPrior _ ((env_priorWeight V p).integrable _)

def clearRate (O:HaarBudget group)(V:GramM N) (C L γ g:ℝ) := Real.exp (-stoutY (More N) V.beta g γ V.p.threshold C L) * (O.small*g^group.lieDim)^(3*Fintype.card (Site (More N))+1)
theorem clearPaid (O:HaarBudget group)(V:GramM N)(p:V.path.Bounds V.funds μ C L)(ht:V.funds.direct≤a)(t:0<g)(h:g≤V.p.threshold)(e:0 ≤ V.beta)(K:0 ≤ C) : clearRate O V C L a g ≤ Graph.angle V:=by
  let n:=More N; let A:= Next.Rank.Axial.axle n; let S:=Set.univ.pi fun _ : A.Free => group.shell (g/4)
  have hs:MeasurableSet S:= MeasurableSet.univ_pi fun _=> group.shell_meas _
  let X:=stoutY n V.beta g a V.p.threshold C L
  have he(u)(w:u∈S): Real.exp (-X) ≤ priorWeight V (A.drape u):=by
     have hv:A.drape u ∈ stone group n (g/4):=by
        intro i _; change group.chord _ ≤_; by_cases e:i∈A.trunks
        · rw [show A.drape u i=1 from A.on_tree u ⟨i,e⟩,group.chord_one]; positivity
        rw [show A.drape u i=u ⟨i,e⟩ from A.off_tree u ⟨i,e⟩]; exact w ⟨i,e⟩ (Set.mem_univ _)
     have h0:4*(g/4)=g:=by ring
     have hf:= h0.trans_le h; rw [priorWeight,Set.indicator_of_mem (show _ ∈ Calm _ _ _ from rife V.p _ hv hf)]; apply Real.exp_monotone (neg_le_neg _); unfold X; rw [←h0]; exact money p _ _ hv ht hf (by positivity) e K
  have ho:= env_priorWeight V p; obtain ⟨hc,hV⟩:= ho.cost; have hI : Integrable (fun u=>priorWeight V (A.drape u)) (A.order group) := by
    exact Integrable.of_bound (ho.meas.comp A.continuous_drape.measurable).aestronglyMeasurable hc (Eventually.of_forall fun i=>hV _)
  rw [weight_angle V p,A.pack (priorWeight V) (ho.integrable _) (fun k _=> weight_gauge V p k)]
  unfold clearRate; apply le_trans ?_ (integral_mono ((integrable_const _).indicator hs) hI (show ∀ u, S.indicator (fun _=>Real.exp (-X)) u ≤ priorWeight V (A.drape u) from ?_)); swap
  · intro u; by_cases w:u∈S
    · rw [Set.indicator_of_mem w]; exact he u w
    rw [Set.indicator_of_notMem w]; exact weight_nonneg ..
  rw [integral_indicator hs,setIntegral_const,smul_eq_mul,mul_comm _ (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; unfold S Tree.Forest.order; rw [measureReal_def,Measure.pi_pi,Finset.prod_const,Finset.card_univ,show Fintype.card A.Free= _ from Next.Rank.Axial.free_count n,ENNReal.toReal_pow]; exact pow_le_pow_left₀ (mul_nonneg O.positive.le (by positivity)) (O.low _ t (h.trans V.p.threshold_le)) _
end YM.CF.Window
