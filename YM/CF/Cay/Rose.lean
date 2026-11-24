import YM.CF.Cay.Gora
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open Matrix Far AnalyticBridge.RelativeLogdet
section
abbrev about(L:Side)(r:ℕ):ℕ:= ((L.val^4)*Fintype.card PlaqAxes+ Fintype.card Axis + Fintype.card PlaqAxes+ Fintype.card Gain+(L.val^4)+1)*(r+r+1)^4
def peakM(S:StepData c f)(s:Signed)(p:Site c)(r:ℕ):= Finset.univ.filter fun i=>separation (herald S s i) p ≤ r
lemma num_peak (s: Signed)(p: Site c): (peakM S s p r).card ≤ about S.patch.L r:=by
 let Q:= (s⁻¹).act p; let M:=halo r {Q}; let Z:=(r+r+1)^4; have hZ:M.card ≤ Z:= (Corona.halo_size ({Q}:Support c) r).trans_eq (by simp [Z]); let Y(i:Site c):Prop:= separation (s.act i) p ≤ r; have hh {i : Site c}(hp:Y i):i∈ M:= by
    refine halo_spec.mpr ⟨Q,mem_singleton_self Q,?_⟩; rw [separation_comm,← separation_signed i Q s, show s.act Q=p from s.act_inv p]; exact hp
 let L(ι:Type)[Fintype ι](f:ι→ Site c):ℕ:= ∑ i:ι,(if separation (s.act (f i)) p ≤ r then 1 else 0)
 have ht{ι:Type}[Fintype ι](f:ι→ Site c): L ι f=(univ.filter (fun i=> separation (s.act (f i)) p ≤ r)).card:= by unfold L; rw [← sum_filter]; simp
 have hF{ι:Type}[Fintype ι]: L (Site f×ι) (S.ratio.parent ∘ Prod.fst) ≤ Fintype.card ι*S.patch.L.val^4*Z:=by
    rw [ht]; exact le_trans (fine_count _ M fun i v=> hh ((mem_filter.mp v).2)) (by gcongr)
 have hC{ι:Type}[Fintype ι]: L (Site c ×ι) Prod.fst ≤ Z*Fintype.card ι:=by rw [ht]; exact le_trans (coarse_count _ M (fun i v=> hh ((mem_filter.mp v).2))) (by gcongr)
 have hX:L (Site f) S.ratio.parent≤ S.patch.L.val^4*Z:=by
    have hp : L (Site f) S.ratio.parent = L (Site f × Unit) (S.ratio.parent∘Prod.fst):=by unfold L; simp [Fintype.sum_prod_type]; exact (ht S.ratio.parent).symm
    rw [hp]; simpa using (hF (ι:=Unit)) -- implicit metavars binder not function named? tune
 have hV:L (Site c) id≤ Z:=by rw [ht]; exact (card_le_card (show _ ⊆ M from fun i u=> hh ((mem_filter.mp u).2))).trans hZ
 have he:(peakM S s p r).card=L (Site f × PlaqAxes) (S.ratio.parent ∘ Prod.fst)+(L (Site c×Axis) Prod.fst+(L (Site c×PlaqAxes) Prod.fst+ L (Site c × Gain) Prod.fst))+(L (Site f) S.ratio.parent+ L (Site c) id):=by
    unfold peakM; rw [show ∀ t:Finset (Along S),t.card=∑ i∈t,(1:ℕ) from fun i=>by simp, sum_filter]; simp only [Fintype.sum_sum_type]; rfl
 rw [he]; apply le_trans (add_le_add (add_le_add hF (add_le_add hC (add_le_add hC hC))) (add_le_add hX hV)); exact le_of_eq (by unfold about Z; ring)
lemma speaks (e:Bond f)(j:ℕ){M: Monk G S} {C D:ℝ}(h:∀ t:Signed,∀ i∈rush x M.key t j, Allows n (fun v=>spring (dense T x q d l β t i) e (M.atop v x)) 0 C)(u: Allows n (fun v=>spring (adjust T x q d l β) e (M.atop v x)) 0 D)(hR: Ready T x)(hp:1000 ≤ radiusB x)(ht:0 ≤ C): Allows n (fun v=> opus T x q d l β j e (M.atop v x)) 0 (|β| * (about S.patch.L (horn x l)*C)+D):=by
 let r:=horn x l; let P(s):=rush x M.key s j; let Z(s):=peakM S s (S.ratio.parent e.1) r; let W(s):= P s ∩ Z s; let U(s:Signed)(i:Along S)(v):=spring (dense T x q d l β s i) e (M.atop v x); let X:= about S.patch.L r; let F(s:Signed)(v):=∑ i∈ P s,U s i v
 have hx(s:Signed): Allows n (F s) 0 (X*C):=by
    refine ((summed (W s) (U s) (p:=fun i hp=>h s i ((mem_inter.mp hp).1))).mono (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((Finset.card_le_card inter_subset_right).trans (num_peak (S:=S) s _))) ht)).germ ?_
    filter_upwards with v; unfold F; refine Finset.sum_subset inter_subset_left ?_; intro i he hu; have hx: ¬separation (herald S s i) (S.ratio.parent e.1) ≤ r:=fun p=> hu (mem_inter.mpr ⟨he,mem_filter.mpr ⟨mem_univ _,p⟩⟩); let B:= halo r {herald S s i}; exact off (calm (q:=q) (l:=l) (β:=β) (d:=d) s i hR hp (show Beat.shadows (o:=herald S s i) B r from Subset.refl _)) e (points_p e _ (lt_of_not_ge hx)) _
 let H:ℝ:= Fintype.card Signed; have hH:0<H:=by unfold H; positivity
 have hv:Allows n (fun v=> averaged fun s=> F s v) 0 (X*C):=by refine (((summed Finset.univ F fun i _=> hx i).smul H⁻¹).mono (le_of_eq ?_)); rw [card_univ]; change |H⁻¹| * (H*_)=_; rw [abs_of_nonneg (inv_nonneg.mpr hH.le),←mul_assoc,inv_mul_cancel₀ hH.ne',one_mul] -- S list
 refine (((hv.smul (-β)).mono (le_of_eq (by rw [abs_neg]))).add u)
end
end YM.CF.Cay
