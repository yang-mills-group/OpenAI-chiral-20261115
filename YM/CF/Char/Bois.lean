import YM.CF.Char.Calls2
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open Push Push.Uniform
local notation "Y₀"=> bareStores S
local notation "uΠ"=> pageX (G:=G) F x
local notation "Z₀"=> clipped T x F k
variable {u:Mast G c}{a:Fish (Key F G)}
lemma iter_affine {ι τ:Type}[NormedAddCommGroup ι][NormedSpace ℝ ι][NormedAddCommGroup τ][NormedSpace ℝ τ](f:ι→ℝ)(p:ι)(L:τ→L[ℝ]ι)(h:ContDiffAt ℝ ω f p)(n:ℕ)(hp:n≠0):
 iteratedFDeriv ℝ n (fun y=> f (p+L y)-f p) 0=(iteratedFDeriv ℝ n f p).compContinuousLinearMap (fun _=> L):=by
 let H :ι→ℝ:=fun y=> f (p+y)
 have ht:ContDiffAt ℝ ω H (L 0):=by
    rw [map_zero]; exact (show ContDiffAt ℝ ω f (p+0) from (add_zero p).symm ▸ h).comp (f:=fun y=>p+y) _ (contDiffAt_const.add contDiffAt_id)
 let Q := H ∘ L
 have hQ:ContDiffAt ℝ ω Q 0:=ht.comp _ L.contDiff.contDiffAt
 change iteratedFDeriv ℝ n (Q-fun _=>f p) 0=_; rw [iteratedFDeriv_sub_apply (hQ.of_le le_top) contDiffAt_const, iteratedFDeriv_const_of_ne hp, Pi.zero_apply, sub_zero]; unfold Q; rw [Uniform.iter_lin_at (ht.of_le le_top),map_zero]; unfold H; rw [iteratedFDeriv_comp_add_left, add_zero]
lemma heart (i j:Key F G)(h: ContDiffAt ℝ ω Z₀ (meetVar u a))(he:uΠ j∈panels Y₀ F (uΠ i)) :
 headed T x (facadeX G u) k Y₀ F (leaveX F x a) (uΠ i) (uΠ j)=Uniform.block Z₀ (meetVar u a) i j:=by
 let L: G.Color × G.Color →L[ℝ] Fish (Joint F G) := lowerCol.comp ((agentX i).comp (ContinuousLinearMap.fst ..)+(agentX j).comp (ContinuousLinearMap.snd ..))
 let p:=meetVar u a; have ht : curveX T x (facadeX G u) k (trays S x F a) i.1.val j.1.val=(fun y=> Z₀ (p+L y)-Z₀ p):=by
    funext y; unfold curveX; rw [← trays_A, ← trays_A, ← trays_add,← trays_add,clip_actual,clip_actual,cumu]; rfl
 unfold headed; rw [Matrix.of_apply,if_pos he]
 change iteratedFDeriv ℝ 2 (curveX T x (facadeX G u) k (trays S x F a) i.1.val j.1.val) 0 ![(epsI G i.2,0),(0,epsI G j.2)]= _
 rw [ht,iter_affine Z₀ p L h 2 (by decide), (isHermitian_iff_isSymm.mp (Uniform.block_hermitian h)).apply j i]
 simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,Uniform.block, Matrix.of_apply,Uniform.entry, iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
 change fderiv ℝ (fderiv ℝ Z₀) p (lowerCol (agentX i (epsI G i.2) + agentX j 0)) (lowerCol (agentX i 0+agentX j (epsI G j.2)))=_
 simp only [agent_b,map_zero,add_zero,zero_add,lower_bolt]; rfl
lemma not_here {A:Stores S}{i j: Rows.In x A F (G:=G)}(p:span S.patch x≤radiusB x/50)(hp:1000 ≤ radiusB x)(h:j∉panels A F i): 2*span S.patch x<separation (front A F i) (front A F j):=by
 by_contra! H; apply h; intro y hy z hz
 let u:=front A F i; let v:=front A F j
 have hu:separation u y ≤ 1:= meetings _ hy; have hv:separation v z ≤ 1:= meetings _ hz
 refine (separation_triangle y v z).trans ((Nat.add_le_add (separation_triangle y u v) hv).trans ?_)
 rw [separation_comm]; change _+_ ≤ _; change _≤_ at hp; change separation u v ≤ _ at H; omega
private lemma far_drive (i j:Key F G)(hr:Ready T x)(hp:2*span S.patch x < separation (front Y₀ F (uΠ i)) (front Y₀ F (uΠ j))) (t:ℝ) :
 drive T x (facadeX G u) k (trays S x F (a+t•bolt j)) i.1.val=drive T x (facadeX G u) k (trays S x F a) i.1.val:=by
 let o:=S.ratio.parent i.1.val.1; let r:=2*span S.patch x
 change r < separation o (S.ratio.parent j.1.val.1) at hp
 ext1 w
 apply echos hr.rules (x:=x) (o:=o) (r:=r) (selfX (facadeX G u) k F Y₀)
 · intro l hl
   rw [trays_add,← agent_b j,trays_smul,trays_A]; simp only [Pi.add_apply,Pi.smul_apply]; rw [Pi.single_eq_of_ne (show l≠j.1.val from fun h=> hp.not_ge (h ▸ hl)),smul_zero,add_zero]
 intro l hl; by_cases hx:l=i.1.val
 · subst l; unfold o r at hl; rw [separation_self, zero_add] at hl; omega
 exact Pi.single_eq_of_ne hx _
lemma heart_zero (i j:Key F G)(h: ContDiffAt ℝ ω Z₀ (meetVar u a)) (hr:Ready T x)(hp:2*span S.patch x < separation (front Y₀ F (uΠ i)) (front Y₀ F (uΠ j))): Uniform.block Z₀ (meetVar u a) i j=0:=by
 let m(t:ℝ):=a+t • bolt j; let M:= Uniform.block Z₀ (meetVar u a); have hm:m 0=a:=by simp [m]
 let X:= Slope Z₀ ∘ meetVar u; let L:Fish (Key F G)→L[ℝ] ℝ:= ContinuousLinearMap.proj (φ:=fun _=>ℝ) i
 let K(t:ℝ):=L (X (m t)); have hh : HasDerivAt m (bolt j) 0:= by simpa [m] using (HasDerivAt.const_add a ((hasDerivAt_id' (x:= (0:ℝ))).smul_const (bolt j)))
 obtain ⟨hv,hh'⟩:=slope_block h
 have he:DifferentiableAt ℝ X (m 0):=by rw [hm]; exact (hv.differentiableAt (by simp)).comp _ (meet_derivative u a).differentiableAt
 have hl :HasDerivAt (fun t=>X (m t)) (M *ᵥ bolt j) 0:=by
    rw [← show fderiv ℝ X (m 0) (bolt j)=M *ᵥ bolt j from hm.symm ▸ hh' (bolt j)]
    exact (he.hasFDerivAt.comp_hasDerivAt (0:ℝ) hh)
 have hK : HasDerivAt K (M i j) 0 :=by
    have hL: L (M *ᵥ bolt j)=M i j:= by rw [show bolt j=Pi.single j 1 from funext fun k=>by by_cases k=j <;> simp [bolt, *],Matrix.mulVec_single_one]; rfl
    exact hL ▸ (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) hl)
 apply hK.unique; apply (hasDerivAt_const (0:ℝ) (K 0)).congr_of_eventuallyEq
 have hx:ContinuousAt (meetVar u ∘ m) 0:= (meet_derivative u (m 0)).continuousAt.comp hh.continuousAt
 have ht:∀ᶠ t:ℝ in 𝓝 0,ContDiffAt ℝ ω Z₀ (meetVar u (m t)):= hx.eventually (show ∀ᶠ y in 𝓝 ((meetVar u ∘ m) 0),ContDiffAt ℝ ω Z₀ y by rw [Function.comp_apply,hm]; exact h.eventually (by simp))
 filter_upwards [ht] with t ht
 change Slope _ _ i=Slope _ _ i -- tune explicit
 rw [hm,← driveB i ht, ← driveB i h]
 exact congr_arg (fun g:G.Color→ℝ=> fderiv ℝ g 0 (epsI G i.2)) (far_drive (u:=u) (k:=k) (a:=a) i j hr hp t)
lemma heart_all(hr:Ready T x)(h: ContDiffAt ℝ ω Z₀ (meetVar u a))(HP:1000 ≤ radiusB x):
 (headed T x (facadeX G u) k Y₀ F (leaveX F x a)).submatrix uΠ uΠ=Uniform.block Z₀ (meetVar u a):=by
 ext i j; by_cases he:uΠ j∈panels Y₀ F (uΠ i)
 · exact heart i j h he
 rw [Matrix.submatrix_apply,headed,Matrix.of_apply,if_neg he,heart_zero i j h hr (not_here hr.inputs HP he)]
end YM.CF.Char
