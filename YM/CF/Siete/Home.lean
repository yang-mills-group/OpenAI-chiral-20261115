import YM.CF.Siete.Lull
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Skye Scree Cube Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n j l:ℕ}{K M' H C Q b v a ε r u R x t:ℝ}{c f:Side}{L:Side}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{P B:BudgetPoint}{X X':Support (More f)}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]
local notation "G"=>SU.group
structure Major(P B: BudgetPoint)(V:Pane c)(o:Seat f)(u: Seat c)(X:Support (More f))(U:Pane c→ Pane f)(n:ℕ)(C:ℝ):Prop where
 expZ : ∃ Z:tangD c→ tangD f, ContDiffAt ℝ (n:ℕ∞ω) Z 0 ∧ Z 0=0 ∧ (∀ᶠ w in 𝓝 (0:tangD c),Agrees X (U (increment V w)) (increment (U V) (Z w))) ∧ ∀ j≤n,∀ x: Fin j→ tangD c,(∀ i,P.dirBound u (x i))→Sized C (iteratedFDeriv ℝ j Z 0 x) B o
lemma contains (o:Seat f)(t:Seat c)(V:Pane c)(U:Pane c→Pane f)(ψ:Seat f→Seat c)(h:0≤C)(p:∀ i : Bond (More f), Mom.needed X i → ∃ a : tangD c→SU.group.Color,Mails V U (ψ i.1) t i a P n (C*Lyre.width B o i)) : Major P B V o t X U n C:=by
 choose! a hb using p; let Z(u:tangD c): tangD f:= fun i=> if Mom.needed X i then a i u else 0
 have hg:ContDiffAt ℝ (n:ℕ∞ω) Z 0:= contDiffAt_pi.mpr fun i=> by unfold Z; split; exact (hb i ‹_›).ch; exact contDiffAt_const
 refine ⟨Z,hg,?_,?_,fun j b x u=>⟨h,fun i=>?_⟩⟩
 · funext i; unfold Z; split; exact (hb i ‹_›).grade; rfl
 · apply eventually_all.mpr; intro i; by_cases g:Mom.needed X i
   · exact (hb i g).pre.mono fun x u j z=> by change _=SU.group.lieExp (Z x i) *_; rw [show Z x i=a i x from if_pos g]; exact u
   exact Eventually.of_forall fun x v u=> False.elim (g ⟨v,u⟩)
 let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond (More f)=> SU.group.Color) i
 rw [show iteratedFDeriv ℝ j Z 0 x i=iteratedFDeriv ℝ j (L ∘ Z) 0 x from congrArg (fun p : tangD c [×j]→L[ℝ] SU.group.Color=> p x) (L.iteratedFDeriv_comp_left hg (Nat.cast_le.mpr b)).symm]; by_cases y:Mom.needed X i
 · rw [show L∘ Z=a i from funext fun _=> if_pos y]; exact (hb i y).holds j b x u
 rw [show L ∘ Z= fun _=>0 from funext fun _=> if_neg y, iteratedFDeriv_fun_zero]; exact (norm_zero (E:=SU.group.Color)).le.trans (mul_nonneg h (Lyre.width_pos ..).le) -- tune
lemma file (K:Teller G)(n s:ℕ)(p:2 ≤ n)(hs:2 ≤ s) : ∃ C a:ℝ,1 ≤ C∧1 ≤ a∧∀ P:Patch, P.Branches K.bind G → ∀ W: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1),∀ q:Chi,∀ R:ℝ,0 < R → ∀ l:ℕ,l ≤ 18 → ∃ t:ℝ,0<t∧∀ᶠ x in atTop,∀ B Y:BudgetPoint,Find B Y n s x P.L→ 0 < gateX G P.L l (s*n+s*n) x t ∧∀ {c f:Side}(S:StepData (More c) (More f))(F:Forest S.ratio)(T:Tube G S)(V: Pane c)(k:S.Choices)(A:Stores S)(X:Support (More f))(U:Support (More c))(o:Seat f),Cert P K S T x→ A.flags=flags (temp x) V →sizedP G P K S T F → o∈X → Healthy B.threshold U V →∀ (I:Type)[Fintype I][DecidableEq I](M:Museum F x A X U I), ∀ (β:ℝ), y G P.L x/2 ≤ β →∀ N:Pane f,∀ Z: LogArray G (Active A x F),(∀ i∈coZ M,‖Z i‖ ≤ gateX G P.L l (s*n+s*n) x t) → Major B Y V o (S.ratio.parent o) X (recent T β k q (R*fiery G x P.L) l N Z) n (fleece n l X Y C a):=by
 obtain ⟨Z⟩:= Foliage.collarSupply G n; let a:= Foliage.Cube.fee Z; have hA:1≤ a:= Foliage.Cube.fee_one _; obtain ⟨r,b,hb,ha,H⟩:= title n a hA; have high:=hA.trans ha
 obtain ⟨C,hC,T'⟩:= coaches K s b hs (by positivity); refine ⟨C,b,hC,high,fun P ht W q R h l hl=>?_⟩
 obtain ⟨u,Q,hu,hQ,Hq⟩:= Heir.recital G P K ht n p
 obtain ⟨t,hp,L⟩:= portrait_zoom n l R h K P ht p hl W q (1/2) (by norm_num) s
 obtain ⟨W'⟩:= webExists G; have hF:=W'.cost
 obtain ℓ:= towns W' (B₀:=Z) (M:=1) (ε:=0) b ha hQ (L:=P.L) hu hb zero_lt_one (by simp) (by norm_num) (by positivity) s
 refine ⟨t,hp,?_⟩
 filter_upwards [ℓ,L,Hq,Folio.subscribe K P,fee_looms (C+clinicFee n Q) b G P.L n l s,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, Rebuild.geometry (SU.group.slopeConstant * Real.log P.L.val)] with x ℓ L fT FF LL hr hz -- tune Heir path
 intro B Y v; obtain ⟨v1,v2,v3,v4,v5,v6,v7⟩:=v; obtain hP:= ℓ B Y v1 v2 v5 v3 v4
 have he:=hP.tension
 let s':= loom B (Heir.reach x) b
 have hw:B.threshold ≤ s':= le_trans (le_mul_of_one_le_left B.threshold_pos.le high) (le_mul_of_one_le_right (by have hx:=B.threshold_pos; positivity) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
 have hs':s' ≤1:=le_trans (le_mul_of_one_le_left (B.threshold_pos.le.trans hw) hQ) (hP.tension.small.trans (min_le_right ..))
 refine ⟨L.1,fun {c f} S F T V k A X U o hx hX hU hg hs I _ _ M β hβ N Z' ht => contains o _ _ _ S.ratio.parent (zero_le_one.trans (pac hC high)) ?_⟩
 intro i y; have hy : i.1∈ inspected X:= mem_union_left _ y.1; have hn:i.1∈ twoZ i:= mem_insert_self ..; have hh: twoZ i ⊆ X:= Finset.insert_subset y.1 (Finset.singleton_subset_iff.mpr y.2); let A':= fringe M hh; obtain ⟨g,hg'⟩:=M.canvas _ hy hs hx.size Z (by omega) hP.lit; have hN:= H _ B V _ g hg' hP.caps
 let z:= 1/2*Y.threshold / feeI x l (s*n); have hv:Matins T F Y.power b C:= (v4).symm ▸ T' S T hx.funds.1 F
 have hz' := L.2 S T hx A F V hU hX k β hβ (PlaceZ F (twoZ i) A x) A' B v3 v1 (S.ratio.parent i.1) (cappoint Y i.1 v5 hn (short_z S i) A'.away A'.asks) N Z' (fun i p=> ht i (fry M hh p)) g
 have hα : z ≤ s':=by
    have ha := hz.2.1; have hh:Y.threshold ≤ 2*B.threshold:=by rw [v1,v2]; exact ha
    have hs:1≤feeI x l (s*n):=one_le_pow₀ (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x),mul_nonneg (Nat.cast_nonneg (α:=ℝ) l) (Nat.cast_nonneg (α:=ℝ) (radiusB x))]); unfold z; have hu:=B.threshold_pos; rw [div_le_iff₀ (one_pos.trans_le hs)]; nlinarith only [hh,hw,mul_le_mul_of_nonneg_left hs (hu.le.trans hw)]
 refine ⟨_,ships A' T V β k q (R*fiery G x P.L) l N Z' g i o ⟨hn,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ hg hy (α:=z) (by unfold z; rw [v2]; exact hz') hN (FF S T hx.funds.1 hx.got) (fT S T hx.got hx.funds hx.size F k) hv (v3.trans v4.symm) hQ hC hα he.allows hs' (v1.symm ▸ he.coarse) v1 p v5 hr ?_⟩
 unfold z; rw [v3]; have hh := LL B v3 v1; have hz:=Y.threshold_pos; rw [←v2] at hh
 apply le_trans (add_le_add (show C*_+clinicFee n Q *_≤Y.threshold/feeI x l (s*n) from (le_div_iff₀ (by unfold feeI; positivity)).mpr (by rw [←add_mul]; exact hh)) (show 1/2*Y.threshold/feeI x l (s*n)≤Y.threshold/feeI x l (s*n) by gcongr; nlinarith)) (le_of_eq (by ring))
end YM.CF.Siete
