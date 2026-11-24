import GaugeFieldConstruction.Pimper
import YM.CF.Rue.Coin
/- average on point gauges in this volume. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive
local notation "GS"=>SU.group
abbrev HaarG(n:Side) : Measure (Agora n):= Measure.pi fun _=> SU.group.probHaar
section ringouts
lemma rank_HE {I:Type}[MeasurableSpace I](X:I→Lit n)(R:Hubber n)(h:Envelope (uncurry X))(P:BudgetPoint)(u:ℝ)(p:∀ i, Micro P R (X i) u)(q:0≤u)(μ:Measure I)[IsProbabilityMeasure μ]: Micro P R (fun U=> ∫ i,X i U∂μ) u:=by
 let V(U:Pane n):=∫ i,X i U∂μ; refine ⟨q,Env.marginal (g:=uncurry X) h μ, fun i j v=> integral_congr_ae (Eventually.of_forall fun z=> (p z).2.2.1 i j v),fun i v=>?_⟩; let t:=P.threshold; let G(z):=X z ∘ increment i; let T:=V ∘ increment i; let L:= univ (α:=WilsonStartup.Bond (More n)); let d:=univ.sup (fun a:Seat n=> separation (0: Seat n) a)
 have he: R⊆ halo d ({0}:Hubber n):=fun x _=>halo_spec.mpr ⟨0,mem_singleton_self _,le_sup (s:=univ) (f:=fun i:Seat n=>separation 0 i) (mem_univ _)⟩; let C:=u*((1+(d:ℝ))^P.power)^P.order
 let U:= {x:Pane n | pingS P.threshold R x}; have hD(W : Pane n): Forge.gyrate L W = increment W:=funext (fun i=> congrArg (RG.increment W) (funext (fun e=>by rw [Forge.steadyB]; simp [L])))
 have hh(x:Pane n)(v:x∈U)(i:I): Signs P (0:Seat n) (X i ∘ Forge.gyrate L x) C:=by rw [hD]; exact halo_price 0 x ((p i).2.2.1) ((p i).2.2.2 _ v) he
 obtain ⟨hx,hk⟩:= Rue.rank_pi ping_o hh (fun x _=> ((h.meas.comp (measurable_id.prodMk measurable_const) : Measurable (fun i=> X i x))).stronglyMeasurable) (show 0≤ C from mul_nonneg q (by positivity)) μ i v; simp_rw [hD] at hx hk
 let N:tangD n→L[ℝ]tangD n:= t • ContinuousLinearMap.id ℝ _; change Allows P.order (T ∘ N) _ _; refine ⟨(show ContDiffAt ℝ P.order T (N 0) from (map_zero N).symm ▸ hx).comp _ N.contDiff.contDiffAt,fun j x=> ContinuousMultilinearMap.opNorm_le_bound q (fun y=>?_)⟩; obtain ⟨M,J⟩:= hk j x
 let b(z):=iteratedFDeriv ℝ j (G z) 0; let A:=ContinuousMultilinearMap.apply ℝ (fun _:Fin j=>tangD n) ℂ (fun i=>N (y i))
 rw [Next.Foundations.jets_linear N (f:=T) (show ContDiffAt ℝ ((j:ℕ∞ω)) T 0 from ContDiffAt.of_le hx (Nat.cast_le.mpr x)), ContinuousMultilinearMap.compContinuousLinearMap_apply]; change ‖A (iteratedFDeriv ℝ j T 0)‖ ≤ _; rw [show iteratedFDeriv ℝ j T 0=∫ z,b z ∂μ from J, ←A.integral_comp_comm (φ:=b) M]; refine (norm_integral_le_of_norm_le_const (Eventually.of_forall fun z=>?_)).trans (show (u* ∏ x:Fin j,‖y x‖)*(μ.real Set.univ) ≤ _ from by simp)
 have hr:=p z; let D:= X z ∘ Shield.solo P.threshold i; have hv : Allows P.order D 0 u:=(hr.2.2.2 _ v); change ‖iteratedFDeriv ℝ j (G z) 0 (fun i=>N (y i))‖ ≤ _; have hc : ContDiffAt ℝ (j:ℕ∞ω) (G z) 0:=by
    have hf:= hh i v z; rw [hD] at hf; exact hf.paid.of_le (Nat.cast_le.mpr x)
 rw [show iteratedFDeriv ℝ j (G z) 0 (fun i=> N (y i))=_ from (show iteratedFDeriv ℝ j (G z) 0 (fun i=> N (y i))=iteratedFDeriv ℝ j (G z∘ N) 0 y from ?_)]; swap; · rw [Next.Foundations.jets_linear _ hc]; rfl
 exact ((iteratedFDeriv ℝ j D 0).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hv.norm_le j x) (by positivity))
end ringouts
lemma basis_CU (x:Bool)(i j:Single n) : Continuous fun g: Agora n=> moko (tradew n g) false x i j:=by
 have he : Continuous fun g:Agora n=> (tradew n g).val:=by
    apply continuous_pi; intro i; apply continuous_pi; intro j; unfold tradew; simp only [jump_apply]; split
    · exact (SU.matter_cont.comp (show Continuous (fun t:Agora n=> t (node i.1.1)) from continuous_apply _)).matrix_elem _ _
    exact continuous_const
 cases x
 · change Continuous fun g:Agora n=>star ((tradew n g).val _ _); exact (he.matrix_elem _ _).star
 exact he.matrix_elem _ _
lemma ray_CU (i j:Wa n) : Continuous fun g:Agora n=> boostX (tradew n g) false i j:=by
 cases i <;> cases j <;> try exact continuous_const
 rename_i i j; rcases i with ⟨b,a,B⟩; rcases j with ⟨t,k,l⟩; simp_rw [boostX]; split; exact (basis_CU ..).mul (basis_CU ..); exact continuous_const
lemma volumeDeck{S:Hubber n}(F: Paper n)(P:BudgetPoint)(h c:ℝ)(p:TrackD P S h F c)(j:Wa n):Envelope (fun g: Agora n× Pane n=> censusF g.1 F j g.2):=by
 let Q(i:Wa n)(x:Agora n × Pane n):ℂ:=boostX (tradew n x.1) false i j * F i (GA x.1⁻¹ x.2)
 let L(x:Agora n×Pane n):= GA x.1⁻¹ x.2
 have hp(x:Agora n × Pane n):censusF x.1 F j x.2=∑ i,Q i x:=stripeQ ..
 simp_rw [hp]; apply Env.total; obtain ⟨A,U,u⟩:= p; intro i; have hK:Continuous L:=by unfold L GA Lattice.gauge; refine continuous_pi fun i=>?_; dsimp only [Pi.inv_apply]; fun_prop
 exact env_mult (Env.along (g:=Prod.fst) (Env.compact (ray_CU i j)) measurable_fst) (Env.along (g:=L) (U i).1.2.1 hK.measurable)
def civilM(F:Paper n):Paper n:=fun j x=>∫ g:Agora n,censusF g F j x ∂ HaarG n
lemma civil_H{S:Hubber n}(F:Paper n)(P:BudgetPoint)(h c:ℝ)(p:TrackD P S h F c): TrackD P S h (civilM F) (CaseL*c):=by
 let X:= Equiv.refl (Seat n); let d:=volumeDeck F P h c p; obtain ⟨V,Q,q⟩:=p; let C:= Listing X false V; have he(i:Agora n)(j): Micro P S (censusF i F j) (C j) ∧ (¬DomainP S j→ censusF i F j=0):=by
    let f:= tradew _ i; let R:= MustCap X S
    rw [← show R=S from map_refl]; -- rewrite also DomainP indices? F. listing. tune
    exact trade_G f false false P X _ (massTransitG i P) V Q j
 refine ⟨C,fun i =>⟨rank_HE (n:=n) _ _ (d i) P (C i) (fun x=> (he x i).1) (he 1 i).1.1 _,fun v=>?_⟩,(wardPay false X V (fun i=>(Q i).1.1) h).trans (mul_le_mul_of_nonneg_left q (Nat.cast_nonneg _))⟩
 funext U; change (∫ g:Agora n,censusF g F i U∂ HaarG n)=_; simp_rw [show ∀ g:Agora n,censusF g F i=0 from fun g=>(he g i).2 v]; simp
lemma civil_V {S:Hubber n}(F:Paper n)(P:BudgetPoint)(h c:ℝ)(p:TrackD P S h F c): portable (civilM F):=by
 intro i g; let μ:= HaarG n; let Q(u:Agora n):= censusF u F; let H(u:Agora n)(j:Wa n):= Q u j i; funext j; rw [stripeQ]; let A(u:Agora n):=censusF u F j (GA g i)
 change (∫ u,A u ∂μ)=∑ k:Wa n,boostX (tradew n g) false k j * ∫ u,H u k∂μ
 have he:MeasurePreserving ((g*·):Agora n→Agora n) μ μ:=by
    letI:(HaarG n).IsMulLeftInvariant:=by unfold HaarG; infer_instance
    exact measurePreserving_mul_left (HaarG n) g
 rw [← he.integral_comp (show MeasurableEmbedding ((g*·): Agora n→ Agora n) from (Homeomorph.mulLeft g).measurableEmbedding) A]
 have hp(u:Agora n):A (g*u)=∑ k:Wa n,boostX (tradew n g) false k j * H u k:=by change αLines (censusF _ F) (GA g i) _=_; rw [← census_L, censusK]; apply stripeQ
 simp_rw [hp]; rw [integral_finsetSum];
 · apply sum_congr rfl; intro i _; rw [integral_const_mul]
 intro j _; exact (Env.integrableX (Env.along (volumeDeck F P h c p j) (g:=fun u: Agora n=> (u,i)) (measurable_id.prodMk measurable_const)) μ).const_mul _ -- tune
end MastTin
end YM.CF.XGarden
end
