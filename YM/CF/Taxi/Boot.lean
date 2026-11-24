/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Vow.Cause
import YM.Next.FOUNDATIONS.TestBounds
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Comparison
/-! Adaption of FND:TestBounds from project. Only use diagonal; never identify wrong ordered field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes

open Rush Scroll Paige Vault Phase Acorn Spire

open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations
section Detect

/-- Any probes that separate (on a fixed finite-dimensional real stage)
suffice here, with *probe-dependent* costs permitted. -/
private theorem budget_probes {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : ι → V →L[ℝ] W) (h : ∀ x : V, (∀ i, p i x = 0) → x = 0) (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) : ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      ∀ x : V, (∀ i, ‖p i x‖ ≤ b i*c) → ‖x‖ ≤ C*c := by
  by_contra! hu
  let B (n : ℕ) := (n : ℝ)+1
  have he (n) : 0 < B n := by unfold B; positivity
  choose c hc x hp hN using fun n : ℕ => hu (B n) (he n)
  have hx (n) : 0 < ‖x n‖ := lt_of_le_of_lt (mul_nonneg (he n).le (hc n)) (hN n)
  let y (n : ℕ) := ‖x n‖⁻¹ • x n
  have hy (n) : y n ∈ Metric.sphere (0:V) 1 := by simp [y,norm_smul,(hx n).ne']
  haveI : ProperSpace V := FiniteDimensional.proper ℝ _
  obtain ⟨z,hz,m,hm,ha⟩ := (isCompact_sphere (0:V) 1).isSeqCompact hy
  suffices z = 0 by simp [this] at hz
  apply h
  intro i
  have ht (n) : ‖p i (y n)‖ ≤ b i/B n := by
    unfold y
    rw [map_smul,norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hx n)).le]
    calc
      _ ≤ ‖x n‖⁻¹ * (b i*c n) := by
        apply mul_le_mul_of_nonneg_left (hp ..) (inv_pos.mpr (hx n)).le
      _ ≤ ‖x n‖⁻¹ * (b i*(‖x n‖/B n)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hb i))
          (inv_pos.mpr (hx n)).le
        rw [le_div_iff₀ (he n), mul_comm]; exact (hN n).le
      _ = _ := by field_simp [(hx n).ne', (he n).ne']
  have hs : Tendsto (fun n => ‖p i (y n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) ht
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  exact norm_eq_zero.mp (tendsto_nhds_unique (((p i).continuous.continuousAt.tendsto.comp ha).norm)
    (hs.comp hm.tendsto_atTop))

end Detect

private def tensorSpace (k : ℕ) : Submodule ℝ (Tensor.T (Fin k → ℝ) ℝ k) where
  carrier := {A | Tensor.Sym A}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {A B} (ha : Tensor.Sym A) (hb : Tensor.Sym B) x s => by
    simp only [add_apply, ha x s, hb x s]
  smul_mem' r A ha x s := by
    change Tensor.Sym A at ha
    simp only [smul_apply, ha x s]

private lemma tensor_budget (k : ℕ) (q : Fin k → (Fin k → ℝ)) (b : (Fin k → ℝ) → ℝ)
    (hb : ∀ x, 0 ≤ b x) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Tensor.T (Fin k → ℝ) ℝ k,
      Tensor.Sym T → ∀ c : ℝ, 0 ≤ c → (∀ x, ‖Tensor.diagonal T x‖ ≤ b x*c) → ‖T q‖ ≤ C*c := by
  let u (x : Fin k → ℝ) : tensorSpace k →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ fun _ => x) ∘L (tensorSpace k).subtypeL
  have hd (T : tensorSpace k) (ht : ∀ i, u i T = 0) : T = 0 := by
    apply Subtype.ext
    show T.val = 0
    apply Tensor.ext_diag T.val 0 T.property (fun _ _ => rfl)
    exact funext fun i => ht i
  obtain ⟨C,hC,hh⟩ := budget_probes (V:=tensorSpace k) (W:=ℝ) u hd b hb
  let K := ∏ j, ‖q j‖
  have hK : 0 ≤ K := Finset.prod_nonneg fun i _ => norm_nonneg _
  refine ⟨C*K, mul_nonneg hC.le hK, fun A hA c hc hx => ?_⟩
  have hi : ‖A‖ ≤ C*c := hh c hc ⟨A,hA⟩ hx
  calc
    ‖A q‖ ≤ ‖A‖*K := A.le_opNorm _
    _ ≤ C*c*K := mul_le_mul_of_nonneg_right hi hK
    _ = C*K*c := by ring

private theorem mixed_budget (G : Gauge) (k : ℕ) (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : BudgetPoint) (n : Side)  (o : Site n)
      (f : Config G n → ℝ) (V:Config G n)(c : ℝ), 0 ≤ c → ContDiffAt ℝ k (f ∘ increment V) 0 →
        (∀ A, B.dirBound o A → ‖leftDerivs f (List.replicate k A) V‖ ≤ c) →
        ∀ w : Fin k → Directions G n,
          (∀ i l, ‖w i l‖ ≤ a i*B.threshold*(1+(separation l.1 o : ℝ))^B.power) →
          ‖iteratedFDeriv ℝ k (f ∘ increment V) 0 w‖ ≤ C*c := by
  classical
  let r (x : Fin k → ℝ) := 1 + ∑ i, ‖x i‖*a i
  have hr (x) : 0 < r x := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ =>
    mul_nonneg (norm_nonneg _) (ha _))
  obtain ⟨C,hC,h⟩ := tensor_budget k (fun i => Pi.single i 1) (fun x => r x^k) (fun x => pow_nonneg (hr x).le _)
  refine ⟨C,hC,fun B n o f V c hk hf hc w hw => ?_⟩
  let L : (Fin k → ℝ) →L[ℝ] Directions G n := ∑ i : Fin k,
    (ContinuousLinearMap.proj (R:=ℝ) i).smulRight (w i)
  have ht (x : Fin k → ℝ) : L x = ∑ i, x i • w i := by simp [L]
  let A := iteratedFDeriv ℝ k (f ∘ increment V) 0
  let T := A.compContinuousLinearMap (fun _ => L)
  have hf' :=hf
  have hp : Tensor.Sym T := by
    intro u e
    exact Analysis.sym_Jet (F:=ℝ) hf' (L ∘ u) e
  have he (x : Fin k → ℝ) : ‖Tensor.diagonal T x‖ ≤ r x ^ k * c := by
    let p := (r x)⁻¹ • L x
    have hb : B.dirBound o p := by
      intro l
      let u := B.threshold * (1+(separation l.1 o : ℝ))^B.power
      have hU : 0 ≤ u := mul_nonneg B.threshold_pos.le (pow_nonneg (by positivity) _)
      have H : ‖L x l‖ ≤ r x*u := calc
        ‖L x l‖ = ‖∑ i, x i • w i l‖ := by rw [ht]; simp [Finset.sum_apply]
        _ ≤ ∑ i, ‖x i • w i l‖ := norm_sum_le ..
        _ ≤ ∑ i, (‖x i‖*a i)*u := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_of_le_of_eq (hw i l) (mul_assoc ..)) (norm_nonneg _)
        _ ≤ r x*u := by
          unfold r; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left zero_le_one) hU
      change ‖(r x)⁻¹ • L x l‖ ≤ u
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hr x)).le]
      exact le_trans (mul_le_mul_of_nonneg_left H (inv_pos.mpr (hr x)).le) (by simp [(hr x).ne'])
    have hi : ‖Tensor.diagonal A p‖ ≤ c := by
      rw [show Tensor.diagonal A p = iteratedDeriv k (fun t : ℝ => f (increment V (t • p))) 0 from
        (iteratedDeriv_on_line hf' p).symm, ← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]
      exact hc _ hb
    change ‖Tensor.diagonal A (L x)‖ ≤ _
    calc
      ‖Tensor.diagonal A (L x)‖ = ‖Tensor.diagonal A (r x • p)‖ := by
        congr 2; unfold p; rw [smul_smul, mul_inv_cancel₀ (hr x).ne',one_smul]
      _ = r x ^ k * ‖Tensor.diagonal A p‖ := by
        rw [Tensor.homogeneous, norm_smul, Real.norm_of_nonneg (pow_nonneg (hr x).le _)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (pow_nonneg (hr x).le _)
  have hT : T (fun i => Pi.single i 1) = A w := by
    unfold T; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply congr_arg A
    funext i
    simp [ht, Pi.single_apply, ite_smul]
  change ‖A w‖ ≤ _
  rw [← hT]; exact h T hp c hk he
open AnalyticBridge.VerifiedReset Push.Local
-- pole meter.D Any p including path.B law read stamp support Z no PPP global
lemma takeF (m:ℕ) : ∃ Q:ℝ,0  ≤  Q ∧ ∀ k : ℕ,k ≤ m → ∀ (n:Side)(p:BudgetPoint)(V:Pane n)(U: Config SU.group (More n) → ℝ)(A:ℝ)(o:Skye.Seat n),0  ≤  A  →  Chart p.order U V  →  (∀ i,p.dirBound o i → ‖leftDerivs U (List.replicate k i) V‖ ≤ A) →  k  ≤  p.order  → ∀ x:Fin k →  tangD n, (∀ i,p.dirBound o (x i))  →  ‖iteratedFDeriv ℝ k (U ∘ increment V) 0 x‖ ≤  Q*A:=by
 choose C v h using fun k=> mixed_budget SU.group k (fun i=>1) (fun i=> (by norm_num)); refine ⟨∑ k∈ range (m+1),C k,sum_nonneg (fun i _=>v i),fun k l n p V U A w f s g Q x r=>?_⟩
 apply ((h k p _ w U V A f (s.of_le (Nat.cast_le.mpr Q)) g x fun i j=>?_)).trans; swap; · rw [one_mul]; exact r i j
 exact mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> v i) (mem_range.mpr (Nat.lt_add_one_of_le l))) f
lemma psalmB (m:ℕ):∃ Q:ℝ,0 ≤ Q∧∀ (n:Side)(P:BudgetPoint)(Z:Config SU.group (More n) → Prop)(z:Skye.Seat n)(A:ℝ)(F:Config SU.group (More n) → ℝ),Bill P z Z A F  →  P.order=m → ∀ i, Z i  →  Signs P z (F ∘ RG.increment i) (Q*A):=by
 obtain ⟨Q,v,h⟩:=takeF m; refine ⟨Q,v,fun n P Z z A F H p i l=>?_⟩; have ht:0≤A:= H.nonneg; have hp: Chart P.order F i:= (((H.smooth [] (by simp) i).of_le (by exact_mod_cast (le_top : (P.order:ℕ∞) ≤ ⊤))).contDiffAt) -- tune name
 refine ⟨mul_nonneg v ht,hp,fun k f=>h k (p ▸ f) _ _ _ _ _ _ ht hp (fun j m=>?_ ) f⟩; exact Bill.norm H (show (List.replicate k j).length ≤ _ from by simpa) (fun i w=> ((List.mem_replicate.mp w).2.symm ▸ m)) l
end YM.CF.Taxi
