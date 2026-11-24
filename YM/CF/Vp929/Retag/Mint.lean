import YM.CF.Vp929.Retag.Registrars
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.SplitFlag
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade
open scoped Mew
open Jet SU Taxi Rue
open WilsonStartup
/-! Factor the gas sum. -/
variable {n:Side} (c:Clip)(b p:BudgetPoint)(z:ℂ)(A:ℂ→L[ℝ]ℝ) (V:Orbit n)
/-! All connected mark sets and anchors. Use forest estimate instead of path-count. -/
variable {σ γ : ℝ}
def wideBox (B : ℕ):ℕ:= (4*B+4*B+1)^4
structure TagRoom : Prop where
  bids : (wideBox b.B:ℝ)*Real.exp ((b.supportExponent+1)*9^4-σ) ≤ γ
  room : ((b.B+b.B+1:ℕ):ℝ)^4*γ ≤ 1
lemma TagRoom.gamma (H: TagRoom b (σ:=σ) (γ:=γ)) : 0 ≤ γ:= le_trans (by positivity) H.bids
lemma TagRoom.hit (H: TagRoom b (σ:=σ) (γ:=γ)) : Ac.Hit (pad (n:=More n) (widen b)) b.B (fun _=>Real.exp (-σ)) (b.supportExponent+1) γ:=by
  intro x; let t:=widen b; let D:=pad t x
  let f(y:Site (More n)):= if x ∈ pad t y then Real.exp (-σ) * Real.exp ((b.supportExponent+1)*coverNumber b.B (pad t y)) else 0
  have hf (i) : 0 ≤ f i := by unfold f; split <;> first | exact le_rfl | positivity
  refine ⟨hf,(hasSum_fintype f).summable,((hasSum_fintype f).tsum_eq).trans_le (le_trans ?_ H.bids)⟩
  have he(y : Site (More n)) : pad t y=Lattice.halo (4*b.B) {y}:=by simp [WilsonStartup.pad,t,widen, ←mul_assoc,show 2*2=4 from rfl]
  have hb : D.card ≤ wideBox b.B := by simp [D,he,wideBox]; simpa using Corona.halo_size ({x}:Support (More n)) (4*b.B)
  calc
    ∑ y, f y = ∑ y ∈ D, Real.exp ((b.supportExponent+1)* coverNumber b.B (pad t y) - σ) := by
      unfold f; simp_rw [mem_pad,separation_comm _ x, ← Real.exp_add, neg_add_eq_sub]
      rw [← Finset.sum_filter]; congr 1; ext y; simp [D,mem_pad]
    _ ≤ ∑ _∈D,Real.exp ((b.supportExponent+1)*9^4-σ) := by
      apply Finset.sum_le_sum; have ha := b.exponent_pos
      intro y _; rw [he]; gcongr; exact_mod_cast Corona.tile y 4 _ b.B_pos
    _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul]; gcongr
lemma TagRoom.earns (H: TagRoom b (σ:=σ) (γ:=γ)) (x: Seat n) :
    (∑ i:Force n,if x∈patch i then b.mass (patch i) (quote b i σ) else 0) ≤ Real.exp γ-1:= by
  let L:= pad (n:=More n) (widen b); let S:= b.supportExponent; let W:=Ac.roots L b.B (fun _=>Real.exp (-σ)) S x
  have hw:= Ac.forest L b.B b.exponent_pos.le (fun _=> (Real.exp_pos _).le) (TagRoom.hit b H) H.room (TagRoom.gamma b H) x
  let F(i:Force n):= if x∈patch i then b.mass (patch i) (quote b i σ) else 0
  let T:=univ.filter (Used (n:=n) b)
  calc
    ∑ i, F i = ∑ i∈T,F i:= (sum_subset (Finset.subset_univ _) fun i _ hi=>by
      have hh : ¬ Used b i := fun h=> hi (mem_filter.mpr ⟨mem_univ _,h⟩)
      simp [F,quote,hh,BudgetPoint.mass]).symm
    _ = ∑ X:Support (More n), W X:= by
      rw [← sum_fiberwise T marks]; refine sum_congr rfl fun X _=>?_ ; rw [sum_subtype _ (p:= fun i=>Used b i ∧ marks i=X) (by simp [T])]; change (∑ i:Chart b X, F i.val)=_
      by_cases h: Ac.Spark L X
      · let D:=tiles b X
        have he(f:Chart b X) : F f.val= if x∈ D then (#D:ℝ)⁻¹*b.mass D (offer σ X) else 0:= by
          simp only [F,quote,BudgetPoint.mass,if_pos f.property.1,f.property.1.2,f.property.2]; split_ifs; ring; rfl
        have hu:(0:ℝ)<D.card:= by exact_mod_cast card_pos.mpr (h.1.mono (subset_region ..))
        simp_rw [he,sum_const,card_univ,Fintype.card_congr (chart_equiv b X h).some,Fintype.card_coe,nsmul_eq_mul]; unfold W Ac.roots; simp only [h,true_and]
        change (#D:ℝ)*_ = if x∈D then _ else 0; split_ifs; rw [← mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]; unfold BudgetPoint.mass offer; rw [Finset.prod_const,← Real.exp_nat_mul,mul_comm (-σ)]; try rfl
        ring
      haveI : IsEmpty (Chart b X):= ⟨fun x=> h (by rw [← (show marks x.val=X from x.property.2)]; exact x.property.1.1)⟩
      rw [Fintype.sum_empty]; simp [W,Ac.roots,h]
    _ ≤ _ := (hw.2.1.sum_le_tsum _ fun i _=> hw.1 i).trans hw.2.2
lemma earns_entry (H0: Decent c b) (hr:12 ≤ b.B) (H: TagRoom b (σ:=σ) (γ:=γ)) (w:ℝ)
    (hh : ∀ (D:Support (More n)) U, |minted c b p z A U D| ≤ offer σ D) : Dark Utrue (entry (n:=n) c b p z A) b w (Real.exp γ-1) :=
  ⟨⟨fun i=> quote b i σ,fun i=> shape c b p z A i σ H0 hr w (hh _), fun x=> TagRoom.earns b H x⟩, fun s _ M hs i V τ _ => shape_turn c b p z A i s M hs V τ⟩
end YM.CF.SplitFlag
