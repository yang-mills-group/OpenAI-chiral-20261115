import YM.SU5.Selected.Airy.Frequency
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
def joinBin(x:Facet3×ℝ):Bin:= Ε x.1 x.2
def foyer : Set (Facet3 × ℝ):= grounds ×ˢ Set.Icc (-π) π
lemma groundsCompact : IsCompact grounds:= isCompact_univ_pi fun i=>isCompact_Icc
lemma foyerCompact : IsCompact foyer:= groundsCompact.prod (isCompact_Icc)
@[fun_prop] lemma join_cont : Continuous joinBin:= by
 apply continuous_pi; intro i; cases i using Fin.lastCases
 · simp only [joinBin,Ε,Fin.snoc_last]; fun_prop
 · simp only [joinBin,Ε,Fin.snoc_castSucc]; fun_prop
private lemma root {x:Facet3 × ℝ}(hx:x∈foyer)(i:Cover) : joinBin x+stem i≠0:= norm_pos_iff.mp <| (norm_pos_iff.mpr (pureV hx.1 _)).trans_le (peaks (banded hx.1 _ hx.2) (show peers (joinBin x) _ from ⟨i,rfl⟩)) -- type
lemma thermal (a:Axis) : ContinuousOn (fun x=> tough (joinBin x) a) foyer:=by
 obtain ⟨C,hC,p⟩:=boundC a
 have h (v: Cover): ContinuousOn (fun x=> slat (joinBin x) v a) foyer:=by
    intro x hx
    have hv:(↑(radius (joinBin x+stem v):ℝ):ℂ)≠0:= by exact_mod_cast (radius_pos _ (root hx v)).ne'
    apply ContinuousAt.continuousWithinAt; unfold slat; apply ContinuousAt.mul; · unfold weave skirt; fun_prop
    refine ContinuousAt.div ?_ ?_ ?_; rotate_left 2; · exact hv
    · fun_prop
    unfold radius; fun_prop
 obtain ⟨o,k⟩:= foyerCompact.bddAbove_image (h 0).norm
 apply continuousOn_tsum h (u:= fun i:Cover=> C*income i+(Pi.single (0:Cover) o:Cover→ℝ) i) ((wallet.mul_left C).add (hasSum_pi_single ..).summable)
 intro v x u; by_cases e:v=0; · subst v; exact (k (Set.mem_image_of_mem _ u)).trans (by rw [Pi.single_eq_same]; apply le_add_of_nonneg_left; exact (mul_pos hC (income_2 _)).le)
 rw [Pi.single_eq_of_ne e,add_zero]; exact p _ (banded u.1 _ u.2) (pureV u.1 _) _ e
lemma thermalV : ContinuousOn (tough ∘ joinBin) foyer:= continuousOn_pi.mpr thermal -- name
lemma climbs {ι:Type*}{l:Filter ι}{M:ι→Side}(p:Tendsto M l atTop)(v:∀ᶠ i in l,Odd (M i).val) : TendstoUniformlyOn (fun k:ι=> mixL 4 (M k) ∘ tmap ∘ joinBin) (tough ∘ joinBin) l foyer:=by
 rw [←tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact foyerCompact,tendstoLocallyUniformlyOn_iff_forall_tendsto]
 intro x u; let P:=𝓝[foyer] x; let l':= l ×ˢ P
 have e : ∀ t, Tendsto (fun i:ι× (Facet3 ×ℝ)=> mixL 4 (M i.1) (tmap (joinBin i.2)) t) l' (𝓝 (tough (joinBin x) t)):= by
    intro t; have h: Continuous tmap:= by unfold tmap; fun_prop
    refine gulch (M':=M ∘ Prod.fst) (p.comp tendsto_fst) (((h.comp join_cont).continuousOn (s:=foyer) x u).tendsto.comp tendsto_snd) (tendsto_fst.eventually v) (banded u.1 _ u.2) (pureV u.1 _) t ?_
    filter_upwards [(show Tendsto Prod.snd l' (𝓝[foyer] x) from tendsto_snd).eventually eventually_mem_nhdsWithin] with y i; exact b_base (banded i.1 _ i.2) -- signature
 exact (((thermalV x u).tendsto.comp (show Tendsto Prod.snd l' P from tendsto_snd)).prodMk_nhds (tendsto_pi_nhds.mpr e)).mono_right (nhds_le_uniformity _) -- tune
lemma regime (x:Bin)(w: Cover) : tough (x+stem w)=tough x:=by
 funext i; unfold tough; rw [← Equiv.tsum_eq (Equiv.addLeft w) (fun t=> slat x t i)] -- tune
 congr 1; ext1 t; have ht: x+stem w+stem t=x+stem (w+t):=by unfold stem; ext; simp; ring
 unfold slat; rw [ht]; rfl

lemma warmth : ContinuousOn (arc ∘ joinBin) foyer:=by
 unfold comp; simp_rw [arc_lo]; exact (thermal 2).add (continuousOn_const.mul (thermal 3))
private lemma keep {X:Type*}[PseudoMetricSpace X]{K:Set X}(p:IsCompact K){V: X×ℝ→ℂ}(h:ContinuousOn V (K ×ˢ Set.Icc (-π) π)) : ContinuousOn (fun (x:X)=> ∫ s in deck,V (x,s)) K:=by
 intro x hx; obtain ⟨u,k⟩:= (p.prod (isCompact_Icc)).bddAbove_image h.norm; let μ:= volume.restrict deck; haveI:IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioc (-π) π))); apply tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun i=>u) ?_ ?_ (integrable_const _) ((ae_restrict_mem measurableSet_Ioc).mono (fun i w => ?_))
 · filter_upwards [eventually_mem_nhdsWithin] with x l; exact ((h.comp (by fun_prop) (show Set.MapsTo (fun i:ℝ=>(x,i)) deck (K ×ˢ _) from fun _ e=>⟨l, e.1.le,e.2⟩))).aestronglyMeasurable measurableSet_Ioc -- use metric separable
 · filter_upwards [eventually_mem_nhdsWithin] with x l; filter_upwards [ae_restrict_mem measurableSet_Ioc] with y i; exact k ⟨(x,y),⟨l,i.1.le,i.2⟩,rfl⟩
 exact (h.comp (by fun_prop) (show Set.MapsTo (fun x:X=>(x,i)) K _ from fun _ e=>⟨e,w.1.le,w.2⟩) _ hx) -- tune
lemma gait (w:ℤ) : ContinuousOn (fun x=>thru x w) grounds:= keep groundsCompact (V:=fun x=> surge w x.2*arc (joinBin x)) (((surge_cont.comp (continuous_const.prodMk continuous_snd)).continuousOn).mul warmth)
lemma legs (u:Bool) (w:ℕ): ContinuousOn (fun x=>knee x u w) grounds:=by cases u; exact (gait _).neg; exact gait _
lemma peerspace (x:Facet3)(w:FaceL)(t:ℝ)(i:ℤ) : tough (Ε (tempoL x w) (turn t i))=tough (Ε x t):= by rw [←ridges,regime]
lemma regimeT (x:Facet3)(t:ℝ)(i:ℤ) : tough (Ε x (turn t i))=tough (Ε x t):=by
 have e:tempoL x 0=x:=funext (fun a=>by simp [tempoL,turn]); simpa only [e] using peerspace x 0 t i
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms climbs
#print axioms regimeT
#print axioms gait
