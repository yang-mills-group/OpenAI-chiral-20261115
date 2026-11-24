import GaugeFieldConstruction.EisJournalVU
import GaugeFieldConstruction.StyxJournalVU
/-!
 Standard receipts for a physical **mean** kernel system on U4 plus derivative tags. All these expenses can be pulled on
 ACT data (Unselected mean). 119,122 expenditures along R=exp(n) suffice for the motion estimates
 in this route. #110 through even order per transverse coordinate. #118 & 123 full budgets.
 Help-book kept specialized later. -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} (V:∀ i, Chamber S i)
structure LedgerOneVU (Q: Finset Axis)(i:Axis)(A:Weight L)(w:Axis→ℝ)(δ : ℝ) : Prop where
 walk_Paid:∃ a : ℝ, 0 < a ∧ ∀ (d : ℝ), 0 ≤ d → d ≤ a → ∀ (s : ℝ), 1≤s → ∀ (f : Grouping), Colors Q f →
      (∀ᶠ n in atTop, Room (mails w f n i) (s*fuel d n)) → ∃ M : ℕ, ∀ m≥M,
          (∀ n:ℕ,Runs (ν (V i) A) i 1 (stamp (lamps m (w i) d s (f i) n))) ∧ Budget δ (fun n => pay (ν (V i) A) i Q (lamps m (w i) d s (f i) n) (mails w f n))
 soft_Paid:∀ f:Grouping, (∀ j∈Q, Ends (f j))→ (∀ t:ℝ,Integrable (cost i Q (FuelVU (w i) t) (TonalVU f w t)) (ν (V i) A)) ∧
    RealBudgetVU δ (fun t=>∫ p,cost i Q (FuelVU (w i) t) (TonalVU f w t) p ∂ν (V i) A)
structure LedgerTwoVU (P:DiffPlan S)(H:S.Hierarchy)(J: Stress S)(D:ℕ)(R: Series): Prop where
 hearts : Portrait J D R
 bound: Strong J P D
 fixed_band a b c d i (f:Panels) : (∀ j,HasCompactSupport ⇑(f j))→ (⇑(f i)=ᶠ[𝓝 0] fun _ => 0)→ ∀ w:Axis→ℝ,w i=0→ (∀ i,w i≤0)→∀ δ:ℝ,0<δ→ Budget δ (fun n=> R a b c d (GroupsJetVU f w n))
 locks i: BL R i=Pmul 2 i (SelfB R i)+FiniteGaugeData R i ∧ CL R i=Pmul 2 i (BL R i)+DC R i ∧ Disappears i (D+1+1) (FiniteGaugeData R i) ∧ Disappears i (D+1+1+1+1) (DC R i)
 supports (i) (a : ℝ) : a≤0→∀ w : Axis→ℝ,(∀ j,w j≤a)→ Ach w (a*4) (FiniteGaugeData R i) ∧ Ach w (a*6) (DC R i)
structure LedgerFourVU (B₁ A₁:S.Tag) (H:S.Hierarchy)(D:ℕ):Prop where
 paperExists : ∃ Z:Paper, ∀ f:Panels,∀ i, flat D (f i) → Integrable (fun p:E4=>pair A₁ ⟨B₁.1,S.conj H.spin _ B₁.2⟩ p * tensor f p) ∧ Z f=∫ x,pair A₁ ⟨B₁.1,S.conj H.spin _ B₁.2⟩ x*tensor f x
 payment (T:Paper): (∀ f:Panels,∀ i,flat D (f i)→ T f =∫ x,pair A₁ ⟨B₁.1,S.conj H.spin _ B₁.2⟩ x*tensor f x)→
    ∀ δ:ℝ,0<δ→∀ w:Axis→ℝ,(∀ i,w i≤0)→∀ f:Panels,(∀ j,HasCompactSupport ⇑(f j))→ Budget δ (fun n=>T (GroupsJetVU f w n))
-- Main ledger requiring actual payments. quantification all orders. Provides measures decompositions of Read w sign, q rates & hierarchy. Authority sign of J. Includes nonvacuous masks across axes.
structure ScrapsVU (P:DiffPlan S)(H:S.Hierarchy)(J: Stress S): Prop where
 photographic (i:Axis)(A B:Weight L) (e): Own A i e→∀ (u:ℝ≥0),Lowered i A u→Lowered i B u→∀ s:ℝ, u+(u:ℝ)≤ s→∀ x:Cross i, fits (V i) A B (propagator i s x.val) ∧ signValue e * readsCluster S A B (s • basis i+x.val) = cross (V i) A B (propagator i s x.val)
 normalized (i:Axis)(A:Weight L):∀ t:ℝ≥0,Lowered i A t→ ν (V i) A=weighted (V i) A t
 costs (i:Axis)(A:Weight L)(j:Axis): j≠i→∀ k:ℕ,(∀ u:ℝ≥0,Lowered i A u→ Integrable (mom i j k (u+u:ℝ≥0)) (ν (V i) A)) ∧ (Pressed i A→ ∃ D:ℕ,Integrable (fun p : E4=> ((1+p i)⁻¹)^D * ‖p j‖^(2*k)) (ν (V i) A))
 scene (Q:Finset Axis) (e) (i) (A:Weight L): i∈Q→Mixed Q e→(∀ i∈Q, Pressed i A)→(∀ i∈Q,Own A i (e i))→∀ w:Axis→ℝ,(∀ i∈Q,w i ≤ 0)→∀ δ:ℝ,0<δ→LedgerOneVU V Q i A w δ
 trail (l i e A): Mixed (other l) e →(∀ i∈other l, Pressed i A)→(∀ i, Own A i (e i))→∀ δ:ℝ,0<δ→∀ w: Axis→ℝ,(∀ i,w i ≤ 0)→∀ f:Grouping,(∀ j, Ends (f j))→
    (∀ t:ℝ,Integrable (cost i Finset.univ (FuelVU (w i) t) (TonalVU f w t)) (ν (V i) A)) ∧ RealBudgetVU (if i=l then δ else -w l+δ) (fun t=>∫ p,cost i Finset.univ (FuelVU (w i) t) (TonalVU f w t) p ∂ν (V i) A)
 -- stress-stress Fourier profiles
 fixed : ∃ D R,0<D∧ LedgerTwoVU P H J D R
 mixed (B₁ A₁ : S.Tag) (e e'):Mixed Finset.univ e→Mixed Finset.univ e'→ Enters H e B₁.2→ Enters H e' A₁.2→ ∀ᶠ D:ℕ in atTop,LedgerFourVU B₁ A₁ H D
 cone (i: Axis): (∃ A, equalRead S A (pick (J i i)) ∧ Own A i false ∧ Pressed i A) ∧ ∀ A:Weight L,equalRead S A (pick (J i i))→Own A i false→Pressed i A→∀ (w:Axis→ℝ) (a:ℝ),a≤0→(∀ j,j≠i → w j≤ a)→ ∀ f:Grouping,(∀ j, Ends (f j))→∀ (δ:ℝ),0<δ→
    (∀ t:ℝ,0≤t→Integrable (coneWeight i (FuelVU a t) (TonalVU f w t)) (ν (V i) A)) ∧ RealBudgetVU (δ+a*4) (fun t=>∫ p,coneWeight i (FuelVU a t) (TonalVU f w t) p ∂ν (V i) A)
lemma recordsVU (P:DiffPlan S)(H:S.Hierarchy)(J: Stress S)(hp:P.Derivatives S)(ho:P.Orientation H.spin)(C:Conserved P H.spin J)(z:RawTensor H.spin J):ScrapsVU V P H J where
 photographic i A B e h := axis_rep (V i) H.translations A B e h
 normalized i A:= issued (V i) A
 costs i A j e k:= ⟨placed_moment (V i) H A j e k,fun h=>pay_moment (V i) H A h j e k⟩
 scene Q e i A h p q s w u x r:=by
    obtain ⟨a,hA,hW⟩:=walk V H Q e i h p A q s w u _ r
    refine ⟨⟨a,hA,?_⟩, fun f g=> EarnPressVU V H Q i A e h p q s x r w u f g⟩
    intro d ht ha G hg f hf hR; obtain ⟨M,P⟩:=hW _ ht ha G hg f hf hR
    obtain ⟨B,h⟩:=runs_order (V i) H A (q i h)
    -- name h_shadow
    refine ⟨max M B,fun m p=>⟨fun n=>?_, P m (by omega)⟩⟩
    refine h m (by omega) _ (mul_pos (by linarith) (fuel_pos d n)) _ ?_ ?_
    · exact Ends.width (hf i (by assumption)).1 _
    exact Reflects.tall (hf i (by assumption)).2.2 _
 trail l i e A hr p v δ hd w hw f h:= EarnTrailVU V H l i A _ hr p v δ hd w hw f h
 fixed:=by
    obtain ⟨D,d,t⟩ := stronger H J P
    obtain ⟨R,h⟩:=portrays H J z (C.symmetric) D t.bound
    have he:=joined h d
    refine ⟨D,joint R,d,he,t,?_ ,fun i=>⟨BL_law he i,CL_law he i,accounts_sink he P hp H C t i⟩,fun i a y w e=>accounts_cost h d P hp H C t a y w e i⟩
    exact fun a b c d i f hv g w e he' δ y=> MainFixedVU V H P hp ho J C z he a b c d i _ (he.agrees a b c d) f hv g w e he' δ y
 mixed B A e e' hi hj h r:=by
    obtain ⟨T,H₁,H₂,H₃⟩:=enters_weights H e B.2 h
    obtain ⟨U,h₁,h₂,h₃⟩:=enters_weights H e' A.2 r
    let f:= pair A ⟨B.1,S.conj H.spin _ B.2⟩; have hf:Measurable f:=pair_meas H ..
    obtain ⟨M,w⟩:=pair_bound H A ⟨B.1,S.conj H.spin _ B.2⟩
    have hA x (y:x≠0): readsCluster S T U x=f x:=pair_reply H U T _ _ h₁ H₁ x y
    filter_upwards [eventually_ge_atTop M] with t e
    have hs:ScaleCap t f:=w.loosen e
    refine ⟨⟨article f t hs hf, fun g i h=> ⟨radical g t i h f hs hf,article_test g i h⟩⟩, ?_⟩
    intro T' HT; exact PureSavingsVU V H T U _ _ hi hj H₂ h₂ H₃ h₃ t f hf (fun x y=>(hA x y).symm) hs T' HT
 cone i:=by
    obtain ⟨A,x,y,v⟩:=enters_weights H (spar i i) (J i i) (shines J H z i i)
    exact ⟨⟨A,x, by simpa [spar] using y i,v i⟩,fun a p l h=> ConeLineVU V H J P hp ho z C i a p l h⟩
#print axioms recordsVU
end YM.NSF.Outer
end
