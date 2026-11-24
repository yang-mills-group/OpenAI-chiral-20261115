import GaugeFieldConstruction.BackingLimeL
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary.Ferry
open YM.Boundary Work Work.C15
open Function MeasureTheory Filter Set Distribution Probe
open scoped Topology InnerProductSpace Classical ContDiff
variable {G:Gauge}{L:Register G}{S T:Table L}{n:ℕ}
private theorem mirrorTrans (j:ℕ)(R:Points n→ℂ)(C:ℝ)(a:Continuous R)(b:∀ p,‖R p‖ ≤ C)(f:Test4)(g:Joint n):
 (∫ p,(∫ y,R (p+skirt j y)*hat f y)*hat g p) = ∫ p, R p * hat (pliss j f g) p:=by
 let X(p:Points n)(y:E4):=R (p+skirt j y)*hat f y*hat g p
 let Y(y:E4)(p:Points n):=R p*(hat g (p-skirt j y)*hat f y)
 have hx: Integrable (uncurry X) (volume.prod volume):=by
    have hl:Continuous (uncurry X):=by unfold X uncurry; fun_prop
    refine (((hat g).integrable.norm).mul_prod ((hat f).integrable.norm.const_mul C)).mono' hl.aestronglyMeasurable (ae_of_all _ fun p=>?_)
    dsimp only [uncurry,X]; rw [norm_mul,norm_mul,mul_comm ((‖_‖)*(‖_‖))]; gcongr; apply b
 have hy: Integrable (uncurry Y) (volume.prod volume):=by
    have hl:Continuous (uncurry Y):=by unfold Y uncurry; fun_prop
    let Z(p:E4 × Points n):=(p.1,p.2-skirt (n:=n) j p.1)
    have hZ: MeasurePreserving Z (volume.prod volume) (volume.prod volume):=by
       refine (MeasurePreserving.id _).skew_product (g:=fun x p=>p-skirt j x) ?_ (Eventually.of_forall (fun x=>?_)) -- tune
       · exact (show Continuous (fun p:E4 × Points n=>p.2-skirt j p.1) from by fun_prop).measurable
       exact (measurePreserving_sub_right (volume : Measure (Points n)) (skirt j x)).map_eq -- tune map_eq
    refine (hZ.integrable_comp_of_integrable ((((hat f).integrable.norm).mul_prod ((hat g).integrable.norm.const_mul C)))).mono' hl.aestronglyMeasurable (ae_of_all _ fun p=>?_)
    dsimp only[uncurry,comp_apply,Y,Z]; rw[norm_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_right (b _) (by positivity)).trans_eq (by ring)
 calc
    _ = ∫ p, ∫ y,X p y :=by simp_rw [X, integral_mul_const]
    _ = ∫ y,∫ p,X p y:= integral_integral_swap hx
    _ = ∫ y,∫ p,Y y p:=by
       refine integral_congr_ae (ae_of_all _ fun y=>?_); dsimp only; rw [←integral_add_right_eq_self (Y y) (skirt j y)]
       simp [X,Y]; congr! 2; ring
    _ = ∫ p,∫ y,Y y p:= integral_integral_swap hy
    _ = _:=by simp_rw [Y,integral_const_mul,pliss_conn]
-- Distribution support to Schwartz transform slice at single real point.
lemma ferry_free {W:Surface S}{F:Waves S}(d:F.during W)(h:Bid.cones W)(r:F.Region T)(p:F.Breathes)(J:F.Bounds)(k:Fin n→S.Union)(y:Heights n)(hy:y∈east n)(j:ℕ)(f:Test4)(hf:tsupport f ⊆ Mink.coneᶜ)(x:Points n):
  (∫ b:E4,F.restricted k y (x+skirt j b)*hat f b)=0:=by
 obtain ⟨C,hC⟩:= restricted_bounded p k hy; obtain ⟨w,w'⟩:= psi_tempered p J k hy
 let R:= F.restricted k y
 have cr:Continuous R:= restricted_continuous r k hy
 have he:dsupport (Distn.fourier w)⊆ coneM n:=by
    apply (Distn.due _ _ (closedM _)).2
    rw[Distn.from_compact]
    intro g h₁ h₂
    let z:Joint n:=lifts (-(dawn y)) g h₂
    have hc:HasCompactSupport ⇑z:=remains ..
    have hu: tsupport z⊆tsupport g:=by
       apply closure_mono; intro i i'; rw [mem_support] at i' ⊢; intro hi; apply i'; dsimp only [z]; simp [hi]
       -- directly
    rw[Distn.fourier_at,w', ←lifts_cancel (dawn y) g h₂] -- tune occurrence
    exact (d n k y hy z hc).symm.trans ((Distn.due _ _ (closedM _)).1 (h n k) z (hu.trans h₁)) -- proof irrel
 let Y(v:Points n):= ∫ b,R (v+skirt j b)*hat f b
 have hx: Continuous Y:=by
    apply continuous_iff_continuousAt.2; intro v
    refine tendsto_integral_filter_of_dominated_convergence (F:=fun (v:Points n) b=>R (v+skirt j b)*hat f b) (bound:=fun b=> C*‖hat f b‖) ?_ ?_ ((hat f).integrable.norm.const_mul _) (ae_of_all _ fun b=>?_) -- tune
    · exact Eventually.of_forall fun k=> (show Continuous (fun b:E4=>R (k+skirt j b)*hat f b) by fun_prop).aestronglyMeasurable
    · exact Eventually.of_forall fun k=>ae_of_all _ fun b=> by rw[norm_mul]; exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    exact (show Continuous (fun k:Points n=>R (k+skirt j b)*hat f b) from by fun_prop).tendsto v
 suffices Y=fun _=>0 from congr_fun this x
 refine eq_of_tests _ _ hx continuous_const fun g=>?_
 suffices ∀ G:Joint n, (∫ p,Y p*hat G p)=0 by simpa using this (port g)
 intro G
 have hz:tsupport (pliss j f G)⊆ (coneM n)ᶜ:=by
    have hi: tsupport (pliss j f G)⊆ (vane j)⁻¹' tsupport f:=by
       apply closure_minimal _ ((isClosed_tsupport f).preimage (ContinuousLinearMap.continuous _))
       intro v hv; refine subset_tsupport _ ?_; rw[mem_support] at hv ⊢; intro e; apply hv; simp only [pliss_at,e]; simp
    intro x h₁ h₂; exact hf (hi h₁) (sees h₂ _)
 unfold Y; rw[mirrorTrans j R C cr hC f G] -- let rw tune
 exact (w' _).symm.trans ((Distn.due _ _ (closedM _)).1 he _ hz)
#print axioms ferry_free
end YM.NSF.Boundary.Ferry
end
