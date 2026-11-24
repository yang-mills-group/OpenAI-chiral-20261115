import YM.SU5.Relativistic.Afield
/-!
# credentials pre-purchase (non winding & forecast).
Do before s not after coming to character; no small geometry assumptions
on μ (external forecast). all k firms.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable (K:Calibration){n:Side}{k:ℕ}
private lemma rightful_less (g f:ℝ)(l:g≤f)(A:Cliplet n k){V:Pane n}(C D:Finset (Seat n))(h:C⊆D) (p:Rightful D V 1 g): Rightful C V 1 f:=by apply (riotPort ..).2; intro j t; exact ((riotPort ..).1 p j (mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp t).2.1,h (mem_filter.mp t).2.2⟩)).trans l
abbrev super (d A m w l:ℕ)(F:Waxy)(r:Fin 3)(z:Side): Cliplet (K.c z) (m^3):=AWork K F (baseX m d A) r A (archH A) z (loftH m d A (w+l+1) F)
lemma forecast (d A m w l μ D:ℕ)(F:Waxy)(V Z R:ℝ)(γ γ':ℝ)(s:Finset ℤ) (u:∀ i∈plusHalf,∀ j:ℤ,j∉s→F i j=0) (v:s⊆ TwistT A)(p:0<γ)(t:0<γ')(e:0<d)(g:l≤2*d)(a:0≤Z)(hR:V+Z ≤ R)(c:∀ n:Side,∀ s:SU.Slot,∀ i:XGr m, ‖strum n (baseX m d A i) A F s‖≤ V)(c':∀ C:Finset WalkA, ∑ x∈C, ‖F 2 0 ((d:ℤ) • x)-(if x=0 then 1 else 0)‖^2 ≤ Z^2) (j:ℕ)(u₀:∀ᶠ N:ℕ in atTop,∀ (M:Jill.Male),N≤ M.val.val→∀ n:Side,∀ i:XGr m,∀ s:SU.Slot, let X:=strum n (baseX m d A i) A F s; ‖acts (spar j M (1:Pane n)) X-X‖≤Z) :
    ∃ τ₀> (0:ℝ),∃ T:ℕ,D+μ ≤ T ∧ ∃ N:ℕ,∀ z:Side,N ≤ (K.c z).val→∀ (M:Jill.Male),N≤M.val.val→IsStarProjection (spar j M (1:Pane (K.c z)))→∀ τ:ℝ,0≤τ→τ≤τ₀→∀ c, Column j M w l μ T γ γ' τ (3*Z) R (super K d A m w l F c z):=by
 let U:=baseX m d A; let H:= loftH m d A (w+l+1) F; let G:=archH A; have hx:G∈ H:=mem_union_left _ (mem_union_left _ (mem_insert_self ..))
 obtain ⟨Y,tP⟩:= long_cost H G; let I:=Y+μ; let T:= max (D+μ) (I+1)
 let J:=min γ γ'; obtain ⟨τ0,hτ,k₀⟩:=stampG_price I J (lt_min p t)
 obtain ⟨B₁,p₁⟩:= lodges_cost d A e l g m (w+l+1) F; obtain ⟨B₂,hp⟩:=u₀.exists
 refine ⟨τ0,hτ,T,le_max_left .., 2*(I+1)+1+(B₁+B₂),fun z k M hM ξ τ hz z' r=>?_⟩
 let n:= K.c z; have hf:2*(I+1)<(More n).val:=by change _<n.val*2; change _ ≤ n.val at k; omega
 obtain ⟨y,u1,u2,u3⟩:= p₁ n (by change _≤ n.val at k; omega)
 let E:= stains m d A F
 have hQ(a)(z:Cover)(x:z∈district (TwistT A) (baseX m d A a) F):z∈ E:= mem_union_right _ (slit_pass m d A F _ x)
 let P0:=(super K d A m w l F r z); let G':= wrap (More n) G
 apply warrant K F U r A G z E H u2 s u (base_stay m d A (w+l+1) F) (fun i z p=> ⟨hQ i z p,span_soil m d A F z (hQ i z p), u3 _ (hQ i z p)⟩) (fun i=> subset_trans (via_pass m d A F _ i) (via_fur m d A _ F s v)) l d (fun i=>spike_grid m d A i) V Z R a hR c' j M ξ (fun i x=> c n x i) (hp M (by omega) n) w μ T γ γ' τ y u1 (extras ..) -- hp doesn't expect swap
 intro v p; have ht: ∀ x∈ hot P0 μ,separation G' x ≤ I:=by
    intro x t; obtain ⟨y,w₀,e⟩:= halo_spec.mp t; obtain ⟨j,f,rfl⟩:= mem_image.mp w₀; exact (separation_triangle ..).trans (Nat.add_le_add (tP _ j f) e)
 let B₀:=BlockP I G'
 have hq: hot P0 μ ⊆ B₀:=fun x t=> blocks_test.mpr (ht _ t)
 have he: Disjoint (BlockP T G') (flags τ v):= p.mono_left (Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_image_of_mem (wrap (More n)) hx)))
 let hw:=k₀ τ hz z' hf (le_max_right (D+μ) _) _ _ he
 exact ⟨rightful_less J γ (min_le_left ..) P0 P0.broad B₀ ((halo_subset μ _).trans hq) hw,rightful_less J γ' (min_le_right ..) P0 (hot P0 μ) B₀ hq hw⟩
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.forecast
