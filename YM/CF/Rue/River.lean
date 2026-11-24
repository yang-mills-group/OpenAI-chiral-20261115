import YM.CF.Scree.Tune
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{n:Side}{t:ℝ}
abbrev FleetS(t:ℝ)(V:Config G n):Prop:=∀ i:Face (Per n),G.chord (faceValue V i) ≠ t
lemma shoreK(t:ℝ)(V:Config G n)(p:FleetS t V)(X:Support n) : Healthy t X V↔ pingS t X V:=by
 refine ⟨?_,ping_le⟩; intro u i s; obtain ⟨j,k,w⟩:=Finset.not_disjoint_iff.mp s; exact lt_of_le_of_ne (le_of_not_gt fun v=> Finset.disjoint_left.mp u k ((flags_spec t V j).2 ⟨i,w,v⟩)) (p i)
abbrev IsleB(G:Gauge)(t:ℝ):Prop:=∀ n:Side,∀ᵐ V:Config G n∂ prior G n,FleetS t V
lemma island(G:Gauge): Set.Countable {t:ℝ|¬ IsleB G t}:=by
 let F(n:Side)(i:Face (Per n))(V:Config G n):= G.chord (faceValue V i); let L(n:Side)(i:Face (Per n)):= {t:ℝ|0 < prior G n {v|F n i v=t}}
 have ht(n:Side)(i:Face (Per n)):Set.Countable (L n i):= Measure.countable_meas_level_set_pos ((show Continuous (F n i) from by unfold F faceValue; fun_prop).measurable)
 haveI:Countable Side:=Function.Injective.countable (f:=fun i:Side=>i.val) (fun i j p=>Subtype.ext p) -- tune
 refine ((Set.countable_iUnion fun i:Side=> Set.countable_iUnion (ht i))).mono ?_; intro t p; by_contra g; refine p (fun i => ae_all_iff.mpr fun j:Face (Per i) => ?_)
 have hx:= le_antisymm (le_of_not_gt fun (l:0<prior G i {v|F i j v=t})=>g (Set.mem_iUnion₂.mpr ⟨i,j,l⟩)) (show 0 ≤ prior G i _ from bot_le); rw [ae_iff]; simpa only [not_not] using hx
lemma arrests : ∃ z:ℝ,StrictAntiOn temp (Set.Ioi z):=by
 let R(u:ℝ):ℝ:= -(u/2)+(Real.log u)^2; have hp : ∀ᶠ u in atTop, deriv R u<0:=by
    filter_upwards [(Real.isLittleO_log_id_atTop.def (show (0:ℝ)<1/8 by norm_num)), eventually_gt_atTop (1:ℝ)] with u h v
    have hu:0<u:=zero_lt_one.trans v; simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_pos v).le,id, abs_of_nonneg hu.le] at h
    have hg:=(( (hasDerivAt_id' u).div_const 2).neg.add ((Real.hasDerivAt_log hu.ne').pow 2)); change deriv ((-fun x:ℝ=> x/2)+Real.log^2) u<0; rw [hg.deriv]; -- tune simplification
    push_cast; simp only [pow_one]; field_simp; nlinarith
 obtain ⟨y,l⟩:= eventually_atTop.mp hp; let z:=max 1 y; have he:= strictAntiOn_of_deriv_neg (convex_Ioi z) (f:=R) (continuousOn_of_forall_continuousAt (fun (i:ℝ) (v:i∈Set.Ioi z)=> (by have hf:0 < i:=zero_lt_one.trans ((le_max_left _ y).trans_lt v); unfold R; fun_prop (disch:= grind)))) (fun i u=>l _ ((le_max_right ..).trans (Set.mem_Ioi.mp (interior_subset u)).le)) -- tune
 have hz(i:ℝ)(p:Real.exp z < i): temp i=Real.exp (R (Real.log i)):=by have hv:0 < i:=(Real.exp_pos z).trans p; unfold temp R; rw [Real.exp_add,Real.exp_neg]; congr 2; rw [← Real.log_sqrt hv.le,Real.exp_log (Real.sqrt_pos.mpr hv)] -- tune
 refine ⟨Real.exp z,fun i (hi:Real.exp z < i) j (hj:Real.exp z<j) t=>?_⟩; rw [hz _ hi,hz _ hj]; have hv:0 < i:=(Real.exp_pos z).trans hi
 exact Real.exp_strictMono (he ((Real.lt_log_iff_exp_lt hv).2 hi) ((Real.lt_log_iff_exp_lt (hv.trans t)).2 hj) (Real.log_lt_log hv t))
lemma inherits(G:Gauge)(z D:ℝ)(h:0≤D):∃ s:ℝ,z<s∧ ∀ i:ℕ, IsleB G (temp (s+i*D)):=by
 obtain ⟨v,p⟩:= arrests; let x:=max z v; let A:= Set.Ioi x; let X(i:ℕ):={u:ℝ|u∈ A∧¬IsleB G (temp (u+i*D))}; have hv(i) : Set.Countable (X i):=by
    let f(u:ℝ):=temp (u+i*D); refine Set.countable_of_injective_of_countable_image (s:=X i) (f:=f) ?_ ?_
    · intro j uj k uk v'; have hx (u)(k:u∈ X i):v < u + (i:ℝ)*D :=lt_of_lt_of_le (lt_of_le_of_lt (le_max_right ..) (show x < u from k.1)) (le_add_of_nonneg_right (by positivity)); exact add_right_cancel (p.injOn (hx _ uj) (hx _ uk) v')
    exact (island G).mono (fun q v=> by obtain ⟨u,k,g⟩:=v; exact g ▸ k.2)
 have hg := (Set.countable_iUnion hv).dense_compl ℝ; obtain ⟨i,w,u⟩:=hg.inter_open_nonempty A isOpen_Ioi Set.nonempty_Ioi
 refine ⟨i,(le_max_left ..).trans_lt (show x < i from ?_),fun j=>by by_contra hp; exact u (Set.mem_iUnion.mpr ⟨j,(show _ ∈X j from ⟨w,hp⟩)⟩)⟩ -- order tune
 exact w
end YM.CF.Rue
