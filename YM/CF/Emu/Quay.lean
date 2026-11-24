import YM.CF.Emu.Never
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory
variable {α:Type*}{N:Side}{o:Site N}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r τ w u:ℝ}{P:Grasp Y B e}{H:Pearl P}{m:Side}{f:ℕ→Side}{R T W:ℕ→ℝ}
-- gauge invariant (covariant exterior operator with coefficient gauge field). no anchor polarization average among gauge fields in previous estimates needed.
def muni(o:Site N)(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α):= ∫ z:E, zoneA o U z R a J ∂group.probHaar
def valA(o:Site N)(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α)(p:Wave (Single N)):= inner ℂ (mateK N) (acts (muni o U R a J) p)
lemma payI(o:Site N)(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α):Integrable (fun z:E=>zoneA o U z R a J) group.probHaar:= ((cityH o R a J).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma teen(o:Site N)(g:Cart (More N))(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α): muni o (gauge g U) R a J= twist (quantU (tradew N g)) (muni o U R a J):=by
 let W:=quantU (tradew N g); let L:FC (Single N)→L[ℝ] FC (Single N):= (twist W).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap; let V(z:E):=zoneA o (gauge g U) z R a J
 unfold muni; change (∫ z:E,V z ∂group.probHaar)= L _; rw [← L.integral_comp_comm (payI o U R a J), ← integral_mul_left_eq_self (μ:=group.probHaar) V (g (node o))]; apply integral_congr_ae; exact Eventually.of_forall fun i=> must o U g i _ _ _
lemma teg(o:Site N)(R:ℝ)(a:α→TagT)(J:List α): Continuous fun U=>muni o U R a J:=by
 let F(x:Bkg (More N) × E):= zoneA o x.1 x.2 R a J; have ht:=cityH o R a J
 obtain ⟨C,h⟩:= (isCompact_range (f:=fun x : Bkg (More N) × E => ‖F x‖) ht.norm).bddAbove
 let f(x:Bkg (More N)):=(fun z:E=> F (x,z)); unfold muni; refine continuous_iff_continuousAt.mpr fun x=>?_ ; refine (continuousAt_of_dominated (F:=f) (μ:=group.probHaar) (bound:= fun _=>C) ?_ ?_ (integrable_const C) ?_) -- tune
 · exact Eventually.of_forall fun U=> (payI o U R a J).aestronglyMeasurable
 · exact Eventually.of_forall fun U=>Eventually.of_forall fun i=> h ⟨(U,i),rfl⟩
 exact Eventually.of_forall fun t=> (ht.comp (continuous_id.prodMk continuous_const)).continuousAt
lemma tank(o:Site N)(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α)(p:Wave (Single N))(x:ℂ): valA o U R a J p-inner ℂ (mateK N) p*x=∫ z:E,wall o U z R a J p x∂ group.probHaar:=by
 let g:Fock.FC (Single N)→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap {toFun:=fun A=>inner ℂ (mateK N) (acts A p), map_add':=fun X Y=> by rw [act_add,inner_add_right],map_smul':=fun c X=>by rw [act_smul,inner_smul_right]; rfl }
 let G(z:E):=zoneA o U z R a J; have ht:=payI o U R a J; unfold valA wall matchF muni; change g (∫ z,G z ∂group.probHaar)-_ = ∫ z,g (G z)- _ ∂_
 rw [← g.integral_comp_comm ht, integral_sub (show Integrable (fun i:E=>g (G i)) _ from (g.restrictScalars ℝ).integrable_comp ht) (integrable_const _), integral_const,probReal_univ, one_smul] -- tune names
lemma vigor(o:Site N)(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α)(p:Wave (Single N))(x:ℂ)(e:∀ z:E,‖wall o U z R a J p x‖ ≤ b): ‖valA o U R a J p-inner ℂ (mateK N) p*x‖ ≤ b:=by rw [tank]; exact (norm_integral_le_of_norm_le_const (ae_of_all group.probHaar e)).trans_eq (by simp)
-- uniform observation estimate on abstract Tab. need existence stock backgrounds with positive support often for uniform.
open Classical in
lemma choose_q{I:ℕ→Type*}[∀ i,Nonempty (I i)](P Q:∀ i,I i→Prop)(h:∀ᶠ i in atTop,∃ a,P i a)(t:∀ a:∀ i,I i,(∀ᶠ i in atTop,P i (a i))→ ∀ᶠ i in atTop,Q i (a i)):∀ᶠ i in atTop,∀ a,P i a→ Q i a:=by
 obtain ⟨v,he⟩:=budgetO _ h
 let Zv(i):=if hx:∃ a,P i a∧ ¬Q i a then hx.choose else v i
 have hp :∀ᶠ i in atTop,P i (Zv i):= he.mono fun i e=>by
    unfold Zv; split
    next hx=>exact hx.choose_spec.1
    next _=> exact e
 filter_upwards [t Zv hp] with i hx; by_contra hk; push Not at hk; obtain ⟨a,h,l⟩:=hk; let he:∃ a,P i a∧ ¬Q i a:=⟨a,h,l⟩; unfold Zv at hx; rw [dif_pos he] at hx; exact he.choose_spec.2 hx
variable (D:Span H K b v c l r n) {I:ℕ→Type*} [∀ i,MeasurableSpace (I i)] [∀ i,Nonempty (I i)]
include D
lemma valQ(Q: Plot α R)(J:List α)(y:Yard (aj B f) R)(t:BeamG D f T W (3*J.length))(o:∀ i,Site (aj B f i))(M:ℕ→Jill.Male)(U:∀ i,I i→ Bkg (Sep B f i))(G:∀ i,I i→wit (f i) B)(μ:∀ i,Measure (I i))(A:∀ i,I i→ℝ)(p:∀ᶠ i in atTop, Tab H (U i) (μ i) (A i) (G i) (M i) (K*Greek (aj B f i)) (T i) (W i) a)(w:∀ᶠ i in atTop,∃ t,0<A i t)(l:ℝ)(z:0<l): ∀ᶠ i in atTop,∀ x:I i,0<A i x →∀ h:E,‖wall (o i) (U i x) h (R i) (Q.pal i) J (G i x) (runes Q.rho J)‖≤ l*Kea.angel (f i) P (M i):=by
 let g(i)(x:I i)(h:E):=wall (o i) (U i x) h (R i) (Q.pal i) J (G i x) (runes Q.rho J); let Y(i):=Kea.angel (f i) P (M i)
 suffices H:∀ᶠ i in atTop,∀ (x:I i × E),0<A i x.1 → ‖g i x.1 x.2‖ ≤ l*Y i by exact H.mono fun i u x v h=> u (x,h) v
 apply choose_q (h:=w.mono fun i e=>by obtain ⟨u,h⟩:=e; exact ⟨(u,(1:E)),h⟩)
 intro a ha; have ht:Tendsto (fun i=>g i (a i).1 (a i).2 / Y i) atTop (𝓝 0):=reshot D Q J y t o M _ _ _ (by
    filter_upwards [p,ha] with i hp hx; exact ⟨hp.stock (a i).1 hx,hp.inner (a i).1 hx⟩)
 filter_upwards [ht.norm.eventually (gt_mem_nhds (norm_zero (E:=ℂ) |>.trans_lt z)),t.ok] with i hx hv; have hp:0<Y i:=angel_p H D.stmt (D.plan _ hv.1).1 D.p D.eP _ (D.plan _ hv.1).2; apply (div_le_iff₀ hp).1; change ‖g i _ _/(Y i:ℂ)‖<_ at hx; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hp.le] at hx; exact le_of_lt hx
end YM.CF.Emu
