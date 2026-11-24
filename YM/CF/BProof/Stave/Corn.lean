import YM.CF.BProof.Stave.Horn
/-! Table rates – only the tolerances d are bought uniform before the palettes; later
also use u-paid Palette dependence to buy λ in lattice mesh. (not the RG λ) -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Metric Filter Topology Sim Extension Gallery
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal -- Classical
variable {I J:Type*}[Fintype I][Fintype J]
structure Fuse (S:Finset I)(x:Pool I) : Prop where
  pos (i:I) : 0≤ x i
  ht : supp x⊆ S
  h1 : ∑ i,x i≤ 1
def Corner (S:Finset I):Set (Pool I) := {x|Fuse S x}
def tome(x:Pool I):=∑ i,x i
variable {x y:Pool I}{S:Finset I}
lemma Fuse.weight(h:Fuse S x) : 0≤tome x:= Finset.sum_nonneg (fun i _=>h.pos i)
lemma tome_c: Continuous (@tome I _) := by unfold tome; fun_prop
private lemma treasury {g:Gallery I J}(x:Pool I): tome (g.tilt x)=tome x:= Equiv.sum_comp g.μ.symm x
def lane(x:Pool I): Pool I:= (tome x)⁻¹ • x
lemma Fuse.rail(h:Fuse S x)(p:tome x≠0): Sim S (lane x) := by
 have hz:=h.weight
 refine ⟨fun i=>mul_nonneg (by positivity : 0 ≤ (tome x)⁻¹) (h.pos i),fun i hi=>h.ht (mem_supp.mpr (right_ne_zero_of_mul (show (tome x)⁻¹*x i ≠ 0 from (show lane x i≠0 from mem_supp.mp hi)))),?_⟩
 simp only [lane,Pi.smul_apply,smul_eq_mul]; rw [←Finset.mul_sum]; exact inv_mul_cancel₀ p
private lemma lane_μ {g:Gallery I J}(x:Pool I): lane (g.tilt x)=g.tilt (lane x):=by unfold lane; rw [treasury]; rfl
lemma corner_compact(S:Finset I) : IsCompact (Corner S):=by
 classical
 refine (isCompact_closedBall 0 1).of_isClosed_subset ?_ (fun x hx=> ?_)
 · have he: Corner S={x|∀ i,0≤x i} ∩ {x|∀ i,i∉S→x i=0} ∩ {x|tome x≤1}:= by
       ext x; change Fuse S x↔(_ ∧ _) ∧ _; constructor; exact fun u=> ⟨⟨u.pos,fun i hi=> of_not_not (fun q=> hi (u.ht (mem_supp.mpr q)))⟩,u.h1⟩; rintro ⟨⟨p,g⟩,U⟩; exact ⟨p,fun j hj=> of_not_not (fun q=> mem_supp.mp hj (g j q)),U⟩
   rw [he]; simp_rw [Set.setOf_forall]; exact ((isClosed_iInter (fun i=> isClosed_le continuous_const (continuous_apply i))).inter (isClosed_iInter fun i=> isClosed_iInter fun _=>isClosed_eq (continuous_apply i) continuous_const)).inter (isClosed_le tome_c continuous_const)
 rw [mem_closedBall,dist_zero_right]; let H: Fuse S x:=hx; exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> by rw [Real.norm_of_nonneg (H.pos i)]; exact (Finset.single_le_sum (fun j _=>H.pos j) (Finset.mem_univ i)).trans H.h1

namespace Gallery
def dummy (F:Drum I J)(x:Pool I): plate (Pad J):= taperL (F (lane x)) (tome x)
variable {g:Gallery I J} {F:Drum I J}{d u:ℝ}{k:ℕ}{S:Finset I}
omit [Fintype J] in
lemma marker (p:tome x=1): dummy F x=lower (F x):=by simp only [dummy,taperL,lane,p,inv_one,one_smul]; simp [firmant,lower]
def Dummy {I:Type*}[Fintype I](d:ℝ)(A:plate I) :=∃ B∈King I, dist A B≤d
lemma is_dummy (h: 0≤ d)(p:g.Small d S F)(x)(g':Fuse S x): Dummy d (dummy F x):=by
 by_cases w:tome x=0
 · exact ⟨Matrix.fromRows 0 1,king_back J,by simpa [dummy,taperL,w,firmant] using h⟩
 obtain ⟨i,hi⟩:=(g'.rail w).nonempty; obtain ⟨j,z⟩:=(p.fee (g'.rail w) i hi).symm; rw [← roll_dist _ _ j⁻¹,roll_mul,mul_inv_cancel,roll_one] at z
 refine ⟨taperL (roll (g.car i) j⁻¹) _,king_taper (king_roll (g.portrait i) _) g'.weight g'.h1,?_⟩
 unfold dummy taperL; rw [row_price,dist_eq_norm,←smul_sub,norm_smul, Real.norm_of_nonneg g'.weight,← dist_eq_norm]; exact (mul_le_of_le_one_left dist_nonneg g'.h1).trans z
lemma transitY (p:g.Coat d k u F) (x:Pool I) : dummy F (g.tilt x)=blink (dummy F x):=by unfold dummy; rw [lane_μ,treasury,p.note,blink_prev]
lemma paragraph (p:g.Small d S F): ContinuousOn (dummy F) (Corner S):=by
 let V(y:Pool I):=tome y • F (lane y); let Q(y:Pool I):= ((firmant (tome y)) • (1:plate (Fin 5)))
 suffices H:ContinuousOn V (Corner S) from by
    exact plat_c.continuousOn.comp (H.prodMk (g:=Q) (((firm_c.comp tome_c).smul continuous_const).continuousOn)) (Set.mapsTo_univ ..)
 intro x hx; let h:Fuse S x:=hx; by_cases e:tome x=0
 · unfold ContinuousWithinAt; rw [show V x=0 from by unfold V; simp [e]]
   apply tendsto_zero_iff_norm_tendsto_zero.mpr
   let s:=Corner S; apply squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) (_ : ∀ᶠ x in 𝓝[s] x,‖V x‖≤tome x*(3+d)) -- tune
   · simpa [e] using! ((show Continuous (fun x:Pool I=> tome x*(3+d)) from tome_c.mul continuous_const).continuousAt (x:=x)).tendsto.mono_left nhdsWithin_le_nhds
   filter_upwards [self_mem_nhdsWithin] with y hy; unfold V; by_cases g0:tome y=0; simp [g0]; let H:Fuse S y:= hy; obtain ⟨i,s⟩:=(H.rail g0).nonempty; rw [norm_smul,Real.norm_of_nonneg H.weight]; exact mul_le_mul_of_nonneg_left (size_like (p.fee (H.rail g0) i s) (g.portrait i)) H.weight
 apply tome_c.continuousAt.continuousWithinAt.smul; refine (p.spot.li.continuousOn _ (h.rail e)).comp_of_preimage_mem_nhdsWithin (f:=lane) ?_ ?_
 · exact ((tome_c.continuousAt.inv₀ e).smul continuousAt_id).continuousWithinAt
 -- need local map only ↔ change comp_of_eq
 filter_upwards [(tome_c.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (eventually_ne_nhds e), self_mem_nhdsWithin] with y hy hz; exact (show Fuse S y from hz).rail hy
lemma console (d':ℝ)(h:0<d')(c:g.Coat d k u F): ∃ η:ℝ,0<η∧∀ S:Finset I,g.tonic u S→S.card≤k→∀ x y:Pool I, Fuse S x→ Fuse S y→ dist x y < η→dist (dummy F x) (dummy F y)<d':=by
 classical
 let A(S:Finset I)(η:ℝ):= g.tonic u S→S.card≤k→∀ x y:Pool I, Fuse S x→ Fuse S y→ dist x y < η→dist (dummy F x) (dummy F y)<d'
 have H(S:Finset I):∃ η,0<η∧ A S η:=by
    by_cases t:g.tonic u S∧ S.card≤k
    · obtain ⟨r,p,e⟩:= Metric.uniformContinuousOn_iff.mp ((corner_compact S).uniformContinuousOn_of_continuous (paragraph (c.kit S t.1 t.2))) _ h; exact ⟨r,p,fun _ _ _ _ u' v=> e _ u' _ v⟩ -- tune
    exact ⟨1,one_pos,fun p q=> (t ⟨p,q⟩).elim⟩
 choose r p hr using H; refine ⟨Finset.univ.inf' Finset.univ_nonempty r, (Finset.lt_inf'_iff ..).mpr (fun i _=> p i), fun S t v x y hx hy e=> hr S t v x y hx hy (e.trans_le (Finset.inf'_le _ (Finset.mem_univ S)))⟩
end Gallery
end YM.CF.BProof.Mesh.Stave
