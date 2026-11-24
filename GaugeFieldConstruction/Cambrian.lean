import GaugeFieldConstruction.Jasper
import GaugeFieldConstruction.Joppa
import YM.CF.Prism.Pop
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q R v ε d r η t x:ℝ}{c f: Side}{L:Side}
local notation "G"=> SU.group
open Cube (More)
open Tree
variable {S: StepData (More c) (More f)}{F:Forest S.ratio}{T:Tube G S}{V:Pane c}{k:S.Choices}

structure Courant (B P:BudgetPoint)(T:Tube G S)(M ε:ℝ)(n:ℕ)(X:Hub f)(Y:Support (More c))(V:Pane c)(U:Pane c→Pane f)(L:Side)(r:ℕ)(a C γ:ℝ):Prop where -- keep Canvas same axial
 cap:mirth X P ((L.val:ℝ)⁻¹) M
 card:Healthy (P.threshold/4) X.val.2 (U V)
 bill:∃ g:Seat c→SU.E, Heir.Canvas B (S.ratio.parent X.val.1) r V g n a∧∃ (Z':tangD c→tangD f) (Θ:tangD c→Seat f→SU.group.Color), Proofs P X.val.2 X.val.1 Z' 0 (B.dirBound (S.ratio.parent X.val.1)) n M ((L.val:ℝ)⁻¹) ∧ Guide _ (B.dirBound (S.ratio.parent X.val.1)) 0 Θ n ε∧ (V=1→ g=1) ∧ (∀ᶠ v in 𝓝 (0:tangD c), Agrees (inspected X.val.2) (increment 1 (Z' v)) (Lattice.gauge (fun i=> SU.group.lieExp (Θ v i)) (Lattice.gauge (g∘ S.ratio.parent) (U (increment V v))))) ∧ (∀ i≤n,∀ v:Fin i→tangD c,(∀ j,B.dirBound (S.ratio.parent X.val.1) (v j))→ FlightFlux.StrongE P X (C*Next.Free.HarmP.SpanL L) ((L.val:ℝ)⁻¹) (iteratedFDeriv ℝ i Z' 0 v) ∧ ‖iteratedFDeriv ℝ i Z' 0 v-Heir.route T (iteratedFDeriv ℝ i (sphereQ V (S.ratio.parent X.val.1) r g) 0 v)‖≤γ *P.threshold)
theorem gala_pin (K:Teller G)(n s:ℕ)(p:2 ≤ n)(hs:2 ≤ s)(ps:s=3) (η J:ℝ)(h:0<η)(hJ:0  ≤  J):∃ C a0 FC:ℝ,1 ≤ a0 ∧1  ≤  C∧1≤FC∧∀ P:Patch, P.Branches K.bind G → licensed η J P.L → ∀ W: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1),∀ q:Chi,∀ R:ℝ,0 < R → ∀ l:ℕ,l ≤ 18 → ∀ ε ξ:ℝ,0<ε→0<ξ→∃ t:ℝ,0<t∧∀ᶠ x in atTop,∀ B Y:BudgetPoint,Find B Y n s x P.L→ 0 < gateX G P.L l (s*n) x t ∧∀ {c f:Side}(S:StepData (More c) (More f))(F:Forest S.ratio)(T:Tube G S)(V: Pane c)(k:S.Choices)(A:Stores S)(X:Support (More f))(U:Support (More c))(o:Seat f),Cert P K S T x→ Seam T η J → A.flags=flags (temp x) V →sizedP G P K S T F → ∀ hX : o∈X, Short S Y X → Healthy B.threshold U V →∀ (I:Type)[Fintype I][DecidableEq I](M:Museum F x A X U I), (∀ i:I,separation (S.ratio.parent o) (incF M i)  ≤  7*(1+radiusB x)) →∀ (β:ℝ), y G P.L x/2  ≤ β →∀ N:Pane f,∀ Z: LogArray G (Active A x F),(∀ i∈coZ M,‖Z i‖ ≤ gateX G P.L l (s*n) x t) → (∀ Ξ:Next.Free.Flight 4 4, Ξ.L=S.ratio.count→HEq (Planned.PrimaryIntegral295.Carrier.linesOf Ξ K.bind.penalty) T.R.A0 → Courant B Y T C ε n (⟨(o,X),hX⟩) U V (recent T β k q (R*fiery G x P.L) l N Z) P.L (Heir.reach x) a0 FC ξ):=by
 obtain ⟨Z⟩:= Foliage.collarSupply G n; let a:= Foliage.Cube.fee Z; have hA:1≤ a:= Foliage.Cube.fee_one _; obtain ⟨r,b,hb,ha,H⟩:= title n a hA
 have hp:0<b:= one_pos.trans_le (hA.trans ha)
 obtain ⟨C,hC,T'⟩:= coaches K s (2*b) hs (by positivity); obtain ⟨W'⟩:= webExists G
 obtain ⟨Rℓ,hR,RH⟩:= FlightFlux.StrongCurve K.bind.penalty K.bind.penalty_pos
 refine ⟨C+2,a,Rℓ*(2*b)+1,hA,hC.trans (le_add_of_nonneg_right (by norm_num)),(by nlinarith),fun P ht hL W q R hr l hm ε ξ hε hξ=> ?_⟩
 obtain ⟨u,Q,hu,hQ,Hq⟩:= Heir.recital G P K ht n p
 let Lₚ:=((P.L.val:ℝ)⁻¹^3); let wₚ:=(P.L.val:ℝ)⁻¹; let e₀:=min Lₚ ((128*W'.scale)⁻¹); let v:=min (ξ/2) (wₚ^4/2); let e:=min e₀ v; have hF:=W'.cost; have he':0<128*W'.scale:=by linarith
 have hE:e ≤ _:= (min_le_left ..).trans (min_le_right Lₚ ((128*W'.scale)⁻¹)); have he:W'.scale*e ≤1/128:= (mul_le_mul_of_nonneg_left hE (zero_le_one.trans hF)).trans_eq (by field_simp)
 have hb':e ≤ 1/2:=(hE.trans (by rw [←one_div (128*W'.scale)]; gcongr; linarith)) -- tune
 have h':0< e:=lt_min (lt_min (pow_pos (by positivity) _) (inv_pos.mpr he')) (lt_min (by positivity) (by unfold wₚ; positivity))
 obtain ⟨z,hz,L⟩:=portraitZ n l R hr K P ht p hm W q e h' s
 refine ⟨z,hz,?_⟩
 filter_upwards [Hq,L,towns W' (B₀:=Z) (M:=J) b ha hQ hu hb h he hb' (le_trans (min_le_left ..) (show e₀ ≤ (P.L.val:ℝ)⁻¹^3 from min_le_left ..)) s,Folio.subscribe K P,reachPays (K:=C*b) (a:=0) hε s,happy s P.L ((P.L.val:ℝ)⁻¹) (C+2) (by linarith) (by positivity),reachPays (K:=clinicFee n Q*b^2*2) (a:=0) h' (s*2)] with x Hq L H' HF Hh Hg hxGap
 intro B Y v; obtain ⟨v1,v2,v3,v4,v5,v6,v7⟩:= v
 refine ⟨L.1,fun {cval fval'} S F T V k A X U o hx hs' hp' hU hX ht' hz I _ _ M hP β hβ N Z' hZ Ξ uℓ uΞ=>?_⟩
 let d:= R*fiery G x P.L; let α:=e*Y.threshold; let z':=loom B (Heir.reach x) b; have hc:= H' B Y v1 v2 v5 v3 v4; have heq:S.patch.L=P.L:= congr_arg RG.Patch.L hx.got
 have hx' := Hq S T hx.got hx.funds hx.size F k
 have hz'(g:Seat _→SU.E) : Guide _ (B.dirBound (S.ratio.parent o)) 0 (atoms T M β k q d l N Z' g ∘ increment V) n α := by unfold α; rw [v2]; exact L.2 S T hx A F V hU hp' k β hβ I M B v3 v1 (S.ratio.parent o) hP N Z' hZ g -- tune implicit match B
 have hf := HF S T hx.funds.1 hx.got
 let K':=recent T β k q d l N Z'; have ht1:o∈ inspected X:= Finset.mem_union_left _ hX
 have hcan(p: Site (More fval'))(g:p∈inspected X): ∃ g:Site _→SU.E,Nut B V (S.ratio.parent p) (Heir.reach x) n a b r g:=by -- tune type
    obtain ⟨h,hg⟩:= M.canvas p g hz hx.size Z (by omega) hc.lit; exact ⟨h,H _ B V _ h hg hc.caps⟩
 have hL: licensed η J S.patch.L := heq.symm ▸ hL
 have he:Healthy (Y.threshold/4) X (K' V):=by
    apply proofHere T M β k q _ l N Z' hf hs' W' h hJ hL hx' hQ p hc.tension Y.threshold_pos V (v1 ▸ hz); intro i p; obtain ⟨g,hg⟩:= hcan _ (p.retain (Work.E01.base_touched i)); exact ⟨_,g, ((hg.toCanvas.paid hA).trans (by unfold loom; have hp:=B.threshold_pos; gcongr)), hg.toCanvas.seen.self_of_nhds, (by simpa using (hz' g).size)⟩ -- tune
 obtain ⟨g,hg,hpinned⟩ : ∃ g:Seat _→SU.E,Nut B V (S.ratio.parent o) (Heir.reach x) n a b r g∧ (V=1→ g=1):=by
    by_cases hp':V=1
    · refine ⟨1,H _ B V _ _ ?_ hc.caps,fun _=> rfl⟩; rw [hp']; apply canvas_price_station Z (by omega) hc.lit; intro i hi; change SU.group.chord (((1:SU.E)*1)*(1:SU.E)⁻¹) ≤_; rw [inv_one,mul_one,mul_one,SU.group.chord_one]; have h:=B.threshold_pos; positivity
    obtain ⟨g,hg⟩:=hcan _ ht1; exact ⟨g,hg,fun h=>(hp' h).elim⟩
 have hT:= T' S T hx.funds.1 F
 have hy: C=C:=rfl
 have hK: Q*z' ≤ min W'.radius 1:=hc.tension.small
 have hα:0≤z':=by unfold z' loom; have hτ:=B.threshold_pos; positivity
 have ho: Proofs Y X o (display T F x k true ∘ sonic T M β k q d l N Z' g o V) 0 (B.dirBound (S.ratio.parent o)) n (C+2) _ ∧ _:= endeav T M β k q d l N Z' g o V hx' hg (show Matins T F Y.power (2*b) C from v4.symm ▸ hT) v1 (v3.trans v4.symm) (v1.symm ▸ hc.tension.coarse) hX ht' v5 hf he W' p hQ (hz' g) hc.tension.noise ((le_mul_of_one_le_left hα hQ).trans (hK.trans (min_le_right ..))) le_rfl hc.tension.allows (by rw [heq,add_comm]; exact hc.people) (hc.narrow _ _ _ heq hX ht') (by rw [min_comm]; exact hK) hc.lamp 
 let δ:=sonic T M β k q d l N Z' g o V; let Q':= δ; let χ:= φ T F true
 refine ⟨Hg S heq Y v5 v4 v2 (⟨(o,X),hX⟩) ht',he,g,hg.toCanvas,display T F x k true ∘ δ,(fun x=>χ (δ x).1),heq ▸ ho.1,?_,hpinned,?_,?_⟩
 · let H:=step_guide hg; have ht: ‖χ‖ ≤ C:=hT.norm_phi; rw [add_zero,← v1,← v3] at Hh; change Guide _ _ _ (χ ∘ sphereQ V _ (Heir.reach x) g) _ _; refine ⟨χ.contDiff.contDiffAt.comp 0 H.1,fun i p v w=>?_⟩; rw [χ.iteratedFDeriv_comp_left H.1 (Nat.cast_le.mpr p)]; refine (χ.le_opNorm _).trans ((mul_le_mul ht (H.2 i p v w) (norm_nonneg _) (zero_le_one.trans hC)).trans ?_); unfold loom; linarith only [Hh]
 · have he: Guide _ (B.dirBound _) 0 δ n z':= (step_guide hg).duo ((hz' g).rise hc.tension.noise)
   exact own T M β k q d l N Z' g o V hf Y hX ht' v5 B a hg.toCanvas hx' he.1.continuousAt (he.size.trans_lt hc.tension.allows) -- tune
 intro i hi v h
 let o':= S.ratio.parent o
 have hcB:B.threshold ≤2*Y.threshold:= v1.symm ▸ hc.tension.coarse
 have hgy:Heir.Limb 3 o' (iteratedFDeriv ℝ i (sphereQ V o' (Heir.reach x) g) 0 v) ((2*b)*Y.threshold):= fun j=> (limb_cost hg v h hi j).trans (by rw [v3,ps]; apply mul_le_mul_of_nonneg_right _ (spine_pos ..).le; nlinarith only [hp, mul_le_mul_of_nonneg_left hcB hp.le]) -- tune rw v3 inside
 have hbB : temp x≤ z':=by rw [←v1]; exact le_trans (le_mul_of_one_le_left B.threshold_pos.le (hA.trans ha)) (le_trans (le_mul_of_one_le_right (by have ht:=B.threshold_pos; positivity) (one_le_pow₀ (by simp; positivity))) le_rfl)
 let x':=iteratedFDeriv ℝ i (display T F x k true ∘ δ) 0 v; let y':= Heir.route T (iteratedFDeriv ℝ i (sphereQ V o' (Heir.reach x) g) 0 v)
 have hΔ: ‖x'-y'‖ ≤ clinicFee n Q*z'^2+ α := (baton_gap (step_guide hg) (hz' g) hx'.toTour hbB ((le_mul_of_one_le_left hα hQ).trans (hK.trans (min_le_right ..))) hc.tension.allows.le (zero_le_one.trans hQ) hc.tension.noise p).2 i hi v h
 have hgap : clinicFee n Q*z'^2≤ e*Y.threshold:=by simp only [add_zero,←v1, pow_mul] at hxGap; unfold z' loom; rw [v3]; nlinarith only [mul_le_mul_of_nonneg_right hxGap.le B.threshold_pos.le,mul_le_mul_of_nonneg_left hcB h'.le]
 have ht:e*Y.threshold+α= (2*e)*Y.threshold:=by unfold α; ring
 have he:=hΔ.trans ((add_le_add_left hgap _).trans_eq ht) -- left tune
 change FlightFlux.StrongE Y _ _ _ x'∧ _; refine ⟨?_,he.trans (mul_le_mul_of_nonneg_right ?_ Y.threshold_pos.le)⟩; swap; · linarith only [show e ≤ ξ/2 from le_trans (min_le_right ..) (min_le_left ..)]
 have hp' : wₚ=(Ξ.L.val:ℝ)⁻¹:=by unfold wₚ; rw [←heq,uℓ]; rfl
 have hr:(P.L)=Ξ.L:=by rw [←heq,uℓ]; rfl
 have hm := RH _ _ S Y T Ξ uℓ uΞ (⟨(o,X),hX⟩) _ (2*b) (by positivity) (v4.trans ps) hgy; rw [←hr] at hm -- caution dependent rewrite
 refine StrongE_mon _ _ (by positivity) (StrongE_sack _ x' y' (by positivity) hm (he.trans (mul_le_mul_of_nonneg_right (by linarith only [show e ≤ ((P.L.val:ℝ)⁻¹)^4/2 from le_trans (min_le_right ..) (min_le_right ..)]) Y.threshold_pos.le))) ?_
 change Rℓ*_ * _ +1 ≤ (Rℓ*(2*b)+1)* Next.Free.HarmP.SpanL P.L; linarith only [Next.Free.HarmP.span_one P.L]
end YM.CF.Prism
end

