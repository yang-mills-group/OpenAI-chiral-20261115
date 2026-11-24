import YM.CF.Siete.Rip
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads Skye Scree
open Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}
section sectionT
variable {V:BudgetPoint}{P:Teller G}{S: StepData c f}{F:Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support f}{T:Tube G S}{Y:Support c}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}{t Q r:ℝ}
-- exact rechart
abbrev sonic (T:Tube G S)(M: Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z: LogArray G (Active A x F))(g: Site c→ G.El)(o: Site f)(V: Config G c)(y:Directions G c): Heir.Deck G c f:=
 (crop (S.ratio.parent o) (Heir.reach x) g (increment V y), atoms T M β k q d l B Z g (increment V y))
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z:LogArray G (Active A x F)) (g:Site c→ G.El)(o:Site f)(V:Config G c) -- shadow
local notation "δ"=>sonic T M β k q d l B Z g o V
local notation "D"=>display T F x k true ∘ δ
lemma own (b:Folio.Bulletin x P T)(B':BudgetPoint)(hx:o∈X)(h:Heir.Short S B' X)(hp:B'.B≤2*radiusB x)(ξ: BudgetPoint)(η:ℝ)(p:Canvas ξ (S.ratio.parent o) (Heir.reach x) V g n η)(E:Heir.Act T F x k n t Q)(he:ContinuousAt δ 0)(ha:‖δ 0‖<t) : ∀ᶠ v in 𝓝 (0:Directions G c),
 Agrees (inspected X) (increment 1 (D v)) (Lattice.gauge (fun i=> G.lieExp (φ T F true (δ v).1 i)) (gauge (g∘ S.ratio.parent) (recent T β k q d l B Z (increment V v)))):=by
 let A':=increment V; have hk:Tendsto A' (𝓝 0) (𝓝 V):=by
    have he : Continuous A':=by unfold A' increment; fun_prop
    simpa [A'] using he.tendsto 0
 filter_upwards [he.norm.eventually (gt_mem_nhds ha), hk.eventually p.seen] with v hv hab
 intro i hi hj; simp only [Function.comp_apply]; rw [E.represents true _ hv.le]
 exact obtain_s T M β k q d l B Z g b (M.asks_origin hx) _ (δ v).1 hab i hi hj ((separation_comm ..).trans_le ((short_patch h hp hx hi).trans (by omega))) true
end sectionT
section proof
variable {P:Teller SU.group}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support (More f)}{T:Tube SU.group S}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}{t r C Q ε η a b:ℝ}{B' p:BudgetPoint}
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Pane f)(Z:LogArray SU.group (Active A x F)) (g:Seat c→ SU.E)(o:Seat f)(V:Pane c) (E:Heir.Act T F x k n t C)
local notation "δ"=>sonic T M β k q d l B Z g o V
local notation "Y'"=>display T F x k true ∘ δ
variable (h: Nut p V (S.ratio.parent o) (Heir.reach x) n a b r g)(v: Matins T F B'.power (2*b) Q)(hp:p.threshold=temp x)(hs:p.power=B'.power)(ht:p.threshold ≤ 2*B'.threshold)
variable (N:Proofs B' X o Y' 0 (p.dirBound (S.ratio.parent o)) n (Q+2) ((S.patch.L.val:ℝ)⁻¹))
include h E v hp hs ht
lemma endeav {u w:ℝ}(y:o∈X)(e: Heir.Short S B' X) (pB:B'.B≤2*radiusB x)(hv:Folio.Bulletin x P T)(hz:Healthy (B'.threshold/4) X (recent T β k q d l B Z V))(W:Heir.Web SU.group) (hn: 2≤n)(hC:1≤C)
    (g':Guide _ (p.dirBound (S.ratio.parent o)) 0 (atoms T M β k q d l B Z g ∘ increment V) n w)(hW:w≤u)(hu: u ≤ 1) (hP: loom p (Heir.reach x) b ≤ u)(hq:u<t)(he:clinicFee n C*u^2+w≤2*(S.patch.L.val:ℝ)⁻¹^3*B'.threshold) (hX:∀ i, Mom.needed X i → Lyre.width B' o i ≤ 1) (hc:C*u ≤ min 1 W.radius)(hd: W.scale*(C*u)^2 ≤ B'.threshold/32): Proofs B' X o Y' 0 (p.dirBound (S.ratio.parent o)) n (Q+2) ((S.patch.L.val:ℝ)⁻¹) ∧
      ∀ᶠ jx in 𝓝 (0:tangD c),∃ g' : Seat f → SU.E, Agrees (inspected X) (increment 1 (Y' jx)) (Lattice.gauge g' (recent T β k q d l B Z (increment V jx))):=by
 let o':= S.ratio.parent o; have hQ:1≤ b:=h.hC.trans h.hQ
 let z:=sphereQ V o' (Heir.reach x) g; have heg: Guide _ (p.dirBound o') 0 z n u:= (step_guide h).rise hP
 have hu':0< u:=by have ht:= p.threshold_pos; unfold loom at hP; exact lt_of_lt_of_le (by positivity) hP
 have hx: temp x ≤ u :=by rw [←hp]; exact (le_trans (le_mul_of_one_le_left p.threshold_pos.le hQ) (le_trans (le_mul_of_one_le_right (by have ht:=p.threshold_pos; positivity) (one_le_pow₀ (by simp; positivity))) hP))
 have hv':0 ≤ 2*b:=(by linarith only [hQ]); obtain ⟨hf,hξ⟩:=baton Q _ heg g' E.toTour hx hu hq.le (zero_le_one.trans hC) v hv' hW hn 2 zero_le_two he X o (fun i hi v hp j=> (limb_cost h v hp hi j).trans (by rw [← hs]; apply mul_le_mul_of_nonneg_right _ (spine_pos ..).le; nlinarith only [hQ, mul_le_mul_of_nonneg_left ht (zero_le_one.trans hQ)]))
 have hG: Guide _ (p.dirBound o') 0 δ n u:= heg.duo (g'.rise hW)
 let hA:= hG.1.continuousAt; let H:= own T M β k q d l B Z g o V hv B' y e pB p a h.toCanvas E hA (hG.size.trans_lt hq)
 have hx : ‖Y' 0‖ ≤ C * u:=display_price E (by omega) hG.size hq.le hC
 refine ⟨⟨hξ,hf,fun i hi=> ⟨(norm_le_pi_norm ..).trans (hx.trans (hc.trans (min_le_left ..))),hX i hi⟩, fun i hi=>?_⟩,?_⟩
 · apply voyage W (Y' 0) (C*u) (by positivity) _ hx (hc.trans (min_le_right ..)) hd i hi
   have hu := RG.flags_agree (B'.threshold/4) _ _ _ H.self_of_nhds
   rw [RG.gauge_flags,RG.gauge_flags,Work.G07.at_zero_increment] at hu; apply Finset.disjoint_iff_inter_eq_empty.mpr; exact hu.trans (Finset.disjoint_iff_inter_eq_empty.mp hz)
 apply H.mono; intro x k; simp_rw [gauge_sq] at k; exact ⟨_,k⟩
end proof
end YM.CF.Siete
