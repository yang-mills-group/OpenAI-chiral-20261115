import YM.CF.BPress.Lily.Rose
/-! § VolumeB-phase eq:B-Jrep. Letters of species one. Explicit row convention and site localization, not diagonal approximation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Lily
open Function MeasureTheory Filter NormedSpace Finset Fock Lattice Cube Lat Spin Spin.Paint SU SU.Pair Chalk Pf Pressure Branch Bias Dial Nacre Tulip
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{C: Op I}
open Course
variable {N:Side} (x:Site N) (A:Op Slot)
abbrev μ (x:Site N)(A:Op Slot):= Yore x A
abbrev bloom := summitOp x A
abbrev trunk := acts (bloom x A) (vacuum (Single N))
abbrev Bot (x:Site N):= stem (den x)
abbrev team (x:Site N):= (univ : Finset (Bot x)).filter fun x=> x.val.card % 2=0
abbrev pollen := glyph (μ x A)
abbrev word (s:Bot x):=star (filament (pollen x A) (string s))
abbrev calyx(s:Bot x):=seaH (L:=pollen x A) (trunk x A) s
abbrev ascent (x: Site N)(P:Op Slot)(v:Bool):FC (Single N):=(if v then proud x else 1)* summitOp x P
variable (P:Op Slot)(u:Bool)
abbrev heading := ascent x P u
abbrev quote (s: Bot x):=star (weights (trunk x A) (acts (heading x P u) (vacuum _)) (pollen x A) s) -- tune reserved syntax
lemma coherence (H:Paint (More N))(p:A=H (node x))(s:Bot x) : word x A s=((string s).reverse.map (glyph (coupling H))).prod:=by
 unfold word; rw [←oddity]; have ht: (string s).reverse.map (glyph (coupling H))=(string s).reverse.map (pollen x A):= List.map_congr_left fun i t=> by rw [p]; refine axial_glyph x i ?_; exact mem_powerset.mp s.property (by simpa [string] using t)
 rw [ht] -- tune word syntax
lemma pollen_crew : ∀ i∈den x,Sector (den x) true (pollen x A i):=fun i=> axial_petal x A i
lemma seed_sector(s:Bot x)(h:s∈team x):Sector (den x) false (word x A s):=by
 have ht:sacred (pollen x A) s=false:= by unfold sacred; have hp:=(mem_filter.mp h).2; rw [show decide (_%2=1)=false from decide_eq_false (by rw [hp]; omega)]
 exact ht ▸ (sector_κ _ s (pollen_crew x A)).contr
lemma uCrew : Sector (den x) false (heading x P u):= Sector.mul (b:=false) (a:=false) (by split; exact helm.property x; exact Sector.one) (neatC (snug ..)) -- apply field names a b? x binder implicit?
lemma trunk_large : 1 ≤ ‖trunk x A‖ :=by
 unfold trunk bloom summitOp; rw [stored]; have he:=PiLp.norm_apply_le (pairWave (Yore x A)) ∅; simpa only [paired_vac,norm_one] using he -- tune
lemma seed_p (s:Bot x)(t:s∉team x): sacred (pollen x A) s=true:= by unfold sacred; simp only [team,mem_filter,mem_univ,true_and] at t; exact decide_eq_true (by omega)
variable {A}
lemma pollen_law (p:Spin.Sym A): Course (den x) (pollen x A) (trunk x A):=by
 let C:=Paint.coupling (N:=N) (fun _=>A); let t: Paint (More N):=fun _=>A; have ht:Cᵀ= -C:= Paint.skew t (fun _=>p); refine ⟨fun i _=>?_,?_,?_⟩; · unfold trunk bloom summitOp; rw [stored]; exact glyph_s (axial_skew x A p) i -- tune syntax
 · intro i u j t; exact glyph_duo (axial_skew x A p) i j
 intro i v j q; have he(k)(t':k∈ den x):glyph C k=pollen x A k:=axial_glyph (H:=t) x k t'; rw [←he i v, ←he j q]; exact glyph_pair ht (Paint.unit _ fun _=>p) i j
lemma debt (t:Spin.Sym P): ‖acts (heading x P u) (vacuum (Single N))‖ ≤ Real.exp (Chalk.ν^2) :=by
 let c:=bloom x P; let k:= summitOp x P; unfold heading ascent; split; next h=> rw [markHere x t, point_norm]; exact Real.one_le_exp (sq_nonneg _)
 next h=> rw [one_mul]; refine (Eye.norm_act k _).trans ?_; rw [show ‖vacuum (Single N)‖=1 by simp [vacuum,basisKet],mul_one]; exact bear_cost x P t -- tune
lemma tollT(V:Bot x)(h:Spin.Sym P) (e:Spin.Sym A): ‖quote x A P u V‖≤Real.exp (Chalk.ν^2):=by
 unfold quote; rw [norm_star]; let E:=trunk_large x A; exact (pollen_law x e).price_e (norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le E))) _ E (debt x P u h) _ -- tune
-- readability: $v ↦ trunk$ continuous; μ and word. quote denominator nonzero all. uniform. used off authorised domains too.
lemma μ_cont : Continuous (μ x):=continuous_matrix fun i j=>by
  simp_rw [μ,yore_at]; split; swap; · exact continuous_const
                                                                                                                                               -- tune
  unfold nodeC; exact continuous_const.mul ((continuous_id (X:=Op Slot)).matrix_elem ..) -- tune
lemma word_cont (s:Bot x) : Continuous (fun A:Op Slot=>word x A s):=by simp_rw [word,←oddity]; suffices u:∀ t:List (Single N),Continuous fun A:Op Slot=>(t.map (pollen x A)).prod from u _; intro t; induction t with| nil=> exact continuous_const|cons i t ih=> exact ((glyph_cont i).comp (μ_cont x)).mul ih
lemma bloom_c : Continuous (fun A:Op Slot=> bloom x A):=by
 letI : NormedAlgebra ℚ (FC (Single N)):= NormedAlgebra.restrictScalars ℚ ℂ _; exact exp_continuous.comp (f:=fun A=>coupl (μ x A)) (coupl_cont.comp (μ_cont x))
lemma act_c {X:Type*}[TopologicalSpace X]{f:X→FC I}{g:X→Wave I}(p:Continuous f)(t:Continuous g): Continuous fun x=> acts (f x) (g x):= (acts_cont.comp p).clm_apply t -- check
lemma trunk_c : Continuous (trunk x):= act_c (bloom_c x) continuous_const
lemma quote_cont (s:Bot x) : Continuous (fun v:Op Slot×Op Slot=> quote x v.1 v.2 u s):=by
 have he:Continuous fun A:Op Slot=> seaH (L:=pollen x A) (trunk x A) s:=by simp_rw [seaH,winged,show ∀A:Op Slot, filament (pollen x A) (string s)=star (word x A s) from fun A=> Eq.symm (star_star (_:FC (Single N)))]; exact act_c (word_cont x s).star (trunk_c x) -- tune
                                                                                --
 let f:= trunk x; let g:=fun A:Op Slot=> acts (heading x A u) (vacuum _); let F:= Continuous.inner (𝕜:=ℂ) (trunk_c x) (trunk_c x); have hF:Continuous g:= act_c (continuous_const.mul (bloom_c x)) continuous_const; exact ((Continuous.inner (𝕜:=ℂ) (he.comp continuous_fst) (hF.comp continuous_snd)).div (F.comp continuous_fst) (fun v=>inner_self_ne_zero.mpr (norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le (trunk_large x _)))))).star -- tune

variable (A)
def joker : FC (Single N):= ∑ s∈team x, quote x A P u s • word x A s
lemma joker_c : Continuous (fun v:Op Slot× Op Slot=> joker x v.1 v.2 u):= continuous_finsetSum _ fun s _=> (quote_cont x u s).smul ((word_cont x s).comp continuous_fst) -- arg order
lemma joker_even :Sector (den x) false (joker x A P u) := Sector.sumS _ _ fun i t=> (seed_sector x A _ t).scale _
lemma restoration (v:Spin.Sym A) : acts (star (joker x A P u) * bloom x A) (vacuum _)=acts (heading x P u) (vacuum _):=by
 let X:=trunk x A; let Y:=acts (heading x P u) (vacuum _); let C:=pollen x A; let V:=pollen_law x v; have e:trunk x A≠0:=by rw [← norm_ne_zero_iff]; exact (zero_lt_one.trans_le (trunk_large x A)).ne'
 have hx:∀ s:Bot x,s∉team x→ quote x A P u s=0:= fun s h=>by unfold quote; rw [V.odd_weight e (bloom x A) _ (neatC (snug ..)) (uCrew x P u) rfl rfl (pollen_crew x A) s (seed_p x A s h),star_zero] -- tune
 have ht:joker x A P u= ∑ s: Bot x,quote x A P u s • word x A s:=by unfold joker; apply (sum_subset (subset_univ _) (fun i _ e=> by rw [hx _ e,zero_smul])).symm.symm -- tune order
 rw [ht,star_sum,act_mul,act_sum]; simp_rw [word, star_smul,quote,star_star,act_smul]; exact V.reset e _ (V.ownedB e (bloom x A) (neatC (snug ..)) _ rfl (uCrew x P u) rfl (pollen_crew x A)) -- tune
end YM.CF.BPress.Lily
#print axioms YM.CF.BPress.Lily.restoration
