import GaugeFieldConstruction.GreatJournalVU
import GaugeFieldConstruction.CrystalBowlVU
import GaugeFieldConstruction.CrystalVaneVU
/-!
 Combined M receipts, continuous width payouts exp all t≥0, on mean.Radon convention.Collision polynomial extension tests as restricted panel bills only.
 Don't apply on arbitrarily projected χ by itself. Includes ANY Weight in this alphabet. Damped integral even at p=0 homogeneous.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} (V:∀ i, Chamber S i)
-- #119 at all real bandwidth times exp(Log(R))
noncomputable abbrev PaneRentRC (i:Axis)(Q:Finset Axis)(f : Grouping) (x:E4→ℝ):= fun p:E4=> x p * crop (Q.erase i) f p
abbrev WalkExpenseRC (e:Axis→Bool) (A:Weight L)(Q:Finset Axis)(i:Axis):Prop:=i∈Q→Mixed Q e→(∀ i∈Q,Pressed i A)→(∀ i∈Q,Own A i (e i))→∀ (w:Axis→ℝ), (∀ i∈Q,w i≤0)→∀ (δ:ℝ),0<δ→ ∃ a : ℝ, 0 < a ∧ ∀ (d : ℝ), 0 ≤ d → d ≤ a → ∀ (s : ℝ), 1≤s → ∀ (f : Grouping), Colors Q f →
      (∀ᶠ n in atTop, Room (mailsAllRC w f n i) (s*fuelAllRC d n)) → ∀ᶠ m:ℕ in atTop,
          (∀ n:ℝ≥0,Integrable (PaneRentRC i Q (mailsAllRC w f n) (Reel i (lampsAllRC m (w i) d s (f i) n))) (ν (V i) A)) ∧ BudgetAllRC δ (fun n => pay (ν (V i) A) i Q (lampsAllRC m (w i) d s (f i) n) (mailsAllRC w f n))
abbrev PressCostRC (P:DiffPlan S)(H:S.Hierarchy)(J:Stress S)(R:Series)(D:ℕ):Prop:=LedgerTwoVU P H J D R ∧ ∀ (a b c d i:Axis)(f:Panels)(w:Axis→ℝ)(δ:ℝ), δ>0 → w i=0→ (∀ i,w i≤0)→ (∀ i,HasCompactSupport ⇑(f i))→ (⇑(f i)=ᶠ[𝓝 0] fun _=>0)→ BudgetAllRC δ (fun n=>R a b c d (GroupsJetAllRC f w n))
abbrev MixCostRC (H:S.Hierarchy) (B₁ A₁:S.Tag)(e e':Axis→Bool):Prop:= Mixed Finset.univ e → Mixed Finset.univ e' → Enters H e B₁.2→ Enters H e' A₁.2→ ∀ᶠ D:ℕ in atTop,LedgerFourVU B₁ A₁ H D ∧∀ T:Paper,(∀ (f:Panels) i,flat D (f i)→ T f =∫ x,pair A₁ ⟨B₁.1,S.conj H.spin _ B₁.2⟩ x*tensor f x)→∀(δ:ℝ),0<δ→∀ w:Axis→ℝ,(∀ i,w i≤0)→∀ f:Panels,(∀ j,HasCompactSupport ⇑(f j))→ BudgetAllRC δ (fun n=>T (GroupsJetAllRC f w n))
structure FullBudgetRC (P:DiffPlan S)(H:S.Hierarchy)(J:Stress S):Prop extends ScrapsVU V P H J where
 gravity i (A: Weight L) (x:ℝ): (∀ t:ℝ≥0,Lowered i A t→Integrable (MomShiftRC i (t+t) x) (ν (V i) A))∧ (Pressed i A→ ∀ᶠ D in atTop,Integrable (DecMomRC i D x) (ν (V i) A))
 walkAt : ∀ e A Q i,WalkExpenseRC V e A Q i
 quant:∃ D R,0<D∧ PressCostRC P H J R D
 mixes (A B: S.Tag)(e e'):MixCostRC H B A e e'
lemma coversRC (P:DiffPlan S)(H:S.Hierarchy)(J: Stress S)(hp:P.Derivatives S)(ho:P.Orientation H.spin)(C:Conserved P H.spin J)(z:RawTensor H.spin J):FullBudgetRC V P H J where
 toScrapsVU:= recordsVU V P H J hp ho C z
 gravity i A x:=⟨softMomRC i (V i) H A x,fun h=>hardMomRC i (V i) H A h x⟩
 walkAt e A Q i hh ht hi ha w hw δ hz:=by
    obtain ⟨D,hD,hP⟩:=walkAllRC V H Q e i hh ht _ hi ha w hw δ hz
    refine ⟨D,hD,?_⟩
    intro d h y s hs f hf e; obtain ⟨N,hN⟩:=hP _ h y _ hs _ hf e
    obtain ⟨K,g⟩:=runs_order (V i) H A (hi i hh)
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop K] with m v q
    refine ⟨fun n=>crop_int (reel_int _ (g m q _ ?_ _ ?_ ?_)) _ _, hN _ v⟩
    · exact mul_pos (by linarith) (fuel_posAllRC d n)
    · exact (hf i hh).1.width _
    exact (hf i hh).2.2.tall _
 quant:=by
    obtain ⟨D,R,ht,he⟩:=(recordsVU V P H J hp ho C z).fixed
    exact ⟨D,R,ht,he,fun a b c d i f w δ hy hk ht hB q=> MainFixedAllRC V H P hp ho J C z he.hearts a b c d i _ (he.hearts.agrees a b c d) f hB q w hk ht δ hy⟩
 mixes A B e e' b c d u:=by
    -- compute tangible.M.Scale and ded polynomial powers
    obtain ⟨T,H₁,H₂,H₃⟩:=enters_weights H e B.2 d
    obtain ⟨U,h₁,h₂,h₃⟩:=enters_weights H e' A.2 u
    let f:= pair A ⟨B.1,S.conj H.spin _ B.2⟩; have hf:Measurable f:=pair_meas H ..
    obtain ⟨M,w⟩:=pair_bound H A ⟨B.1,S.conj H.spin _ B.2⟩
    have hA x (y:x≠0): readsCluster S T U x=f x:=pair_reply H U T _ _ h₁ H₁ x y
    filter_upwards [(recordsVU V P H J hp ho C z).mixed B A e e' b c d u,eventually_ge_atTop M] with D h hh
    have hy:ScaleCap D f:=w.loosen hh
    exact ⟨h,fun Q h=> PureSavingsAllRC V H T U e e' b c H₂ h₂ H₃ h₃ D f hf (fun i v=>(hA i v).symm) hy _ h⟩
#print axioms coversRC
end YM.NSF.Outer
end
