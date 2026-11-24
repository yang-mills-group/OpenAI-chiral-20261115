import YM.SU5.Regis.Spindle
import YM.SU5.Gleam.Danube
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
open ProbabilityTheory Regis
section isometric
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {ι:Type}[Fintype ι][DecidableEq ι]{S:Sheet ι}(T:Vec ι→ₗ[ℝ] E)(h:S.PosDef)(p:∀ x, ‖T x‖^2 = qpay S x)
include h p
open WithLp
lemma pew : MeasurePreserving (fun x:Vec ι=> T.rangeRestrict x) (cloud S⁻¹) (stdGaussian T.range):=by
 let M:=cloud S⁻¹
 let R:= CFC.sqrt (S⁻¹); have hR: R*R=S⁻¹:=CFC.sqrt_mul_sqrt_self _ h.inv.posSemidef.nonneg
 have hRw:R.transpose=R:= isHermitian_iff_isSymm.mp (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S⁻¹)).isHermitian -- namespace
 have hr:R.det^2=S⁻¹.det:=by rw [sq,←det_mul,hR]
 have he : IsUnit R.det:= IsUnit.mk0 _ fun t=> (h.inv.det_pos.ne') (by rw [←hr,t]; norm_num)
 let Z:=EuclideanSpace ℝ ι; let W:= T.rangeRestrict.comp ((Matrix.toLin' R).comp (WithLp.linearEquiv 2 ℝ (ι→ℝ)).toLinearMap)
 have hp(x:EuclideanSpace ℝ ι): W x=T.rangeRestrict (R*ᵥ ofLp x):=rfl
 have hf : Function.Surjective W:=by
    intro b; obtain ⟨t,ht⟩:= b.property; refine ⟨toLp 2 (R⁻¹ *ᵥ t),?_⟩; rw [hp,ofLp_toLp,mulVec_mulVec,R.mul_nonsing_inv he,one_mulVec]; exact Subtype.ext ht
 have hd(x:EuclideanSpace ℝ ι): ‖W x‖^2= ‖x‖^2:= by
    rw [hp]; change ‖T (R *ᵥ ofLp x)‖^2=_; rw [p]; let H:=ofLp x; have he' : R*S*R=1:=by
        have hs: S = (S⁻¹)⁻¹:= (Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit)).symm; nth_rw 1 [hs]; rw [←hR,Matrix.mul_inv_rev,←mul_assoc,R.mul_nonsing_inv he,one_mul, R.nonsing_inv_mul he]; -- assoc
    unfold qpay
    calc
     _ = H ⬝ᵥ H :=by
        change (R *ᵥ H) ⬝ᵥ _ = _
        conv_lhs=>arg 1; rw [←vecMul_transpose,hRw] -- formula vecMul_transpose v B: v ᵥ* Bᵀ = B *ᵥ v ; careful
        rw [← dotProduct_mulVec, mulVec_mulVec,mulVec_mulVec, he',one_mulVec]
     _ = _ := by rw [EuclideanSpace.real_norm_sq_eq]; simp [sq,H,dotProduct]
 have hm(x): ‖W x‖=‖x‖:= by have hx:=hd x; nlinarith [norm_nonneg (W x), norm_nonneg x]
 let V:EuclideanSpace ℝ ι≃ₗᵢ[ℝ] T.range:= ⟨LinearEquiv.ofBijective W ⟨(show EuclideanSpace ℝ ι→ₗᵢ[ℝ] T.range from ⟨W,hm⟩).injective,hf⟩,hm⟩
 refine ⟨T.rangeRestrict.continuous_of_finiteDimensional.measurable,?_⟩; rw [← paid S⁻¹,Measure.map_map]; all_goals first | exact T.rangeRestrict.continuous_of_finiteDimensional.measurable | exact acts_meas _ | skip
 let U:=toLp 2 (V:=ι→ℝ); have hi : Measure.map U (coins ι) = stdGaussian (EuclideanSpace ℝ ι):= map_pi_eq_stdGaussian
 refine Eq.trans ?_ (stdGaussian_map V)
 rw [← hi,Measure.map_map]; all_goals first | exact V.continuous.measurable | exact (MeasurableEquiv.toLp ..).measurable | rfl
end isometric
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S)(P:Attached H Z)(L:Floor H q n δ w)
abbrev estate (B:Z.Bounds q η C S)(P:Attached H Z) (T:Forest r)(F:Finset T.Free) := ((tiler B P).comp (stockLine T F)).comp (colors (G:=G) (ι:=↥F)).toLinearMap
abbrev stamen (B:Z.Bounds q η C S)(P:Attached H Z) (n:Side):= LinearMap.range (tiler (n:=n) B P)
abbrev starCost (B:Z.Bounds q η C S)(P:Attached H Z)(r:Ratio c n)(A:Support c)(m:ℕ)(Y:fieldDir G n 1)(β:ℝ)(X:fieldDir G n 1):= (coupling β)⁻¹ • (tiler B P X + accession B P r A m Y)
def climbSource (B:Z.Bounds q η C S)(P:Attached H Z)(T:Forest r)(F:Finset T.Free)(A:Support c)(m:ℕ)(Y:fieldDir G n 1)(β:ℝ)(W:Altar G n→ℝ)(t:ℝ) (x:LogArray G F):= yieldY Z q T F A m Y β x * Real.exp (t* W (starCost B P r A m Y β (stock T F x)))
open Module
abbrev plumeCost (B:Z.Bounds q η C S)(P:Attached H Z)(W:Altar G n→ℝ)(t:ℝ):= t* ∫ x, W ((stamen B P n).starProjection x)∂stdGaussian (Altar G n)
include B P L
set_option maxHeartbeats 220000 in -- adaptation Rounds
lemma at_source (Y:fieldDir G n 1)(h:(cellM T F H).PosDef)(p:0<β)(W:Altar G n→ℝ)(a: ContDiff ℝ 1 W){b₁ b₂:ℝ}(h1:∀ x, |W x|≤ b₁)(h2:∀ x, ‖fderiv ℝ W x‖≤ b₂)(t:ℝ): let f:=climbSource B P T F A m Y β W t; let K:= chartCost (prism T F H G)⁻¹ (coupling β); let E:= plumeCost B P W t + trend*b₂^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2; Integrable f volume ∧ (∫ x,f x) ≤ K* Real.exp E:=by
 let Ψ:= (prism T F H G); let σ:= coupling β; have hf: Ψ.PosDef:= h.kronecker PosDef.one; let Φ:= tiler (n:=n) B P; let D:= accession B P r A m Y; let V:= estate B P T F; let X:= LinearMap.range V; let g:= coupling_pos p; obtain ⟨a',ha,b,hb,he⟩:= X.exists_add_mem_mem_orthogonal D; obtain ⟨x,hx⟩:= ha; let c':= - x; have hE: D=a'+b:=he
 intro f K Q
 obtain ⟨hq,ht⟩:= at_price Ψ⁻¹ hf.inv g c' f
 let μ:=cloud Ψ⁻¹; let d:= σ⁻¹ • b; let L':= Real.exp (-β* (‖b‖^2/2)); let ξ: X→ℝ:= fun i=> Real.exp (t * W (i.val+d)); let T'(x:Prices G F):=Real.exp (force Ψ⁻¹ x/2) • f (displaced c' σ x)
 have he' : T'=fun x=> L'* ξ (V.rangeRestrict x):=by
    funext y; unfold T' f climbSource yieldY; rw [tiler_occupy B P]; let t':= displaced c' σ y
    have h : Φ (stock T F t')+D= σ • V y+b:=by
       rw [hE,←hx]; change V (-x+σ • y)+(V x+b)=_; rw [map_add,map_neg,map_smul]; abel
    rw [starCost,show (tiler B P) _ + _=_ from h,norm_add_sq_real (σ • V y) b,show inner ℝ (σ • V y) b=0 from ?_,mul_zero,add_zero]
    · rw [norm_smul,Real.norm_of_nonneg g.le,mul_pow]; let Y:=qpay Ψ y; have hv : ‖V y‖^2=Y:=Tape_price B P L y; rw [hv,show force Ψ⁻¹ y=Y from ?_, smul_eq_mul, ← mul_assoc, ← Real.exp_add]; swap; · unfold force; rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hf.isUnit)]; rfl
      congr 1
      · have hw:β*σ^2=1:=coupling_inter _ p; unfold L'; congr 1; linarith only [show β*σ^2 * Y =Y by rw [hw,one_mul]]
      unfold ξ; rw [smul_add, inv_smul_smul₀ g.ne']; rfl
    exact (Submodule.mem_orthogonal _ b).1 hb _ (X.smul_mem _ ⟨y,rfl⟩)
 let U:=stamen B P n; have hx:X≤U:=by intro x h; exact (LinearMap.range_comp_le_range ..).trans (LinearMap.range_comp_le_range ..) h -- tune
 have hw(X'): ‖V X'‖^2=qpay Ψ X':= Tape_price B P L _
 let κ:= stdGaussian X; let S:=V.rangeRestrict; have hs:MeasurePreserving S μ κ:= pew V hf hw
 have hi: Integrable ξ κ:= puff κ (fun y:X=> W (y.val+d)) t (a.continuous.comp (continuous_subtype_val.add continuous_const)|>.measurable) (fun i=> h1 _)
 have hp : ‖d‖^2= β*‖b‖^2:= by
    have hw:β*σ^2=1:=coupling_inter _ p; unfold d; rw [norm_smul,mul_pow,Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr g).le,inv_pow, inv_eq_of_mul_eq_one_left hw] -- tune
 have hy: (∫ x,T' x ∂μ) ≤ Real.exp Q:=by
    rw [he', integral_const_mul]; change L' * (∫ x, ξ (S x)∂μ)≤ Real.exp Q
    rw [← integral_map hs.aemeasurable (f:=ξ) (by unfold ξ; fun_prop (disch:=exact a.continuous)),hs.map_eq]
    refine (mul_le_mul_of_nonneg_left (swerve W t X U h1 a h2 hx d) (Real.exp_pos _|>.le)).trans_eq ?_; rw [←Real.exp_add,hp]; unfold Q U X plumeCost; congr 1; ring
 refine ⟨hq.mpr ?_,ht.trans_le ?_⟩; · change Integrable T' μ; rw [he']; exact (hs.integrable_comp_of_integrable hi).const_mul _
 exact mul_le_mul_of_nonneg_left hy (chartCost_pos _ hf.inv g|>.le)
lemma at_rank(h:(cellM T F H).PosDef): Module.finrank ℝ (LinearMap.range (estate B P T F)) = F.card*Fintype.card G.ColorIndex:=by
 let X:= estate B P T F; have he: Function.Injective X:= by
    intro x y t; by_contra h'; have ht:x-y≠0:=sub_ne_zero.mpr h'; have hs:0< ‖X (x-y)‖^2:= Tape_price B P L _ ▸ q_at (prism T F H G) (h.kronecker PosDef.one) ht; rw [map_sub,t,sub_self] at hs; simp at hs
 have hx:= LinearMap.finrank_range_of_inj he; rw [show finrank ℝ ↥(LinearMap.range (estate B P T F))=finrank ℝ (Prices G F) from hx]; unfold Prices; simp -- tune
lemma garden_equiv (h:Buttress T F): LinearMap.range (estate B P T F) = stamen B P n:=by
 let W:= estate B P T F; refine le_antisymm ((LinearMap.range_comp_le_range ..).trans (LinearMap.range_comp_le_range ..)) ?_
 intro a p; obtain ⟨x,rfl⟩:= p
 -- choose coord solution mod null directions
 choose Y H' using fun i:G.ColorIndex=>h.2 (parts G 1 x i); let V : Prices G F := fun j=> (Y j.2 (Sum.inr j.1))
 let y:= stock T F (tape V); have ht (i:G.ColorIndex) :d 1 n*ᵥ parts G 1 x i=d 1 n *ᵥ parts G 1 y i:=by
    rw [← H' i]; dsimp only; rw [fromCols_mulVec,mulVec_add,mulVec_mulVec,arena_comm,Matrix.zero_mulVec,zero_add] -- tune
    -- access Rounds.stockV private; repeat
    have hx: parts G 1 (stock T F (tape V)) i = seatsF T F *ᵥ fun x=> V (x,i):=by
       funext j; unfold parts stock; change (∑ k:↥F, seatsF T F j k • tape V k) i = _; change (EuclideanSpace.proj i) (∑ k:↥F, seatsF T F j k • tape V k)=_; rw [map_sum]; rfl
    unfold y; rw [hx]; rfl
 refine ⟨V,?_⟩; change tiler B P y=_; ext ⟨w,b,i⟩; cases b
 · exact congrArg (Real.sqrt q.direct * ·) (congrFun (ht i).symm (w.1,plaquette w.2))
 change ellLine Z w y i=_; rw [ellLine_mulVec H B P]; change _=ellLine Z w x i; rw [ellLine_mulVec H B P, ht]
end YM.Gleam
#print axioms YM.Gleam.at_source
#print axioms YM.Gleam.garden_equiv
