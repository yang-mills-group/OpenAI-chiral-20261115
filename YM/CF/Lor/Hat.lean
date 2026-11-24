import YM.CF.Lor.Thaw
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable (q:Chi)(n l j:ℕ)
def scar(t v K C K' C':ℝ):ℝ:= ((K*t^3*C+K*t^4*C) +(K'*v^3*C'+K'*v^4*C'))
def scarf(t v K B K' B' H z:ℝ):ℝ:= (H*z +(K*t^2*B + K'*v^2*B'))
lemma sr (A R K K':ℝ)(L:Side): sizeK L 1 fun x:ℝ=>2*Scales.y G₅ L x * scar (fiery G₅ x L) (temp x) A R K K':=by
 let h:=sizeK.fierce L; have t:=sizeK.tempo L
 let S(x:ℝ):= scar (fiery G₅ x L) (temp x) A R K K'
 have hp(C v:ℝ)(f:ℝ→ℝ)(u:sizeK L 1 f):sizeK L 3 (fun x=> C*f x^3*v + C*f x^4*v):= sizeK.accrue (((u.square 3).scale C).tint (sizeK.mild L v)) ((((u.square 4).scale C).tint (sizeK.mild L v)).low (show 3 ≤ _ by omega))
 have he:sizeK L 3 S:=(hp _ _ _ h).accrue (hp _ _ _ t)
 exact ((sizeK.yearsK (n:=1) L he).scale 2).cost_d (Eventually.of_forall fun i=>Eq.le (congrArg abs (mul_assoc ..))) -- tune
lemma sf(B B' K K':ℝ)(L:Side):sizeK L 1 fun x=> K*fiery G₅ x L^2*B + K'*temp x^2*B':=by
 let h:= sizeK.fierce L; let p:=sizeK.tempo L; exact ((((h.square 2).scale K).tint (sizeK.mild L B)).accrue (((p.square 2).scale K').tint (sizeK.mild L B'))).low (by decide)
lemma shore (R:Patch)(F:Teller G₅)(ρ aτ a b C D H h' L:ℝ)(hv:0<ρ)(ht:0<aτ)(hH:0≤H)(h:0<h')(p:0<L)(hl:l ≤ 18)(v:ℝ)(hx:0<v)(Z:ChartRatio G₅)(hZ:LocalRatio Z)(hY:4*v<Z.radius) (w:Clip) : ∃ W:ℝ,0 ≤ W∧∀ᶠ x:ℝ in atTop,∀ {N P B:Side}{G:Ratio (mid N B) (mid P B)}{e:ℝ}(S:StepData (Domain N B) (Domain P B))(T:Tube G₅ S), Cert R F S T x → T.up.Bounds T.high ρ a b → T.down.Bounds T.low aτ C D→ T.low=w →∀ U:Muster G S x e T,U.beta∈ Set.Icc (y G₅ R.L x/2) (2*y G₅ R.L x) → |U.ang+U.fee|≤H →U.trot=q→U.vita=Z→U.rota=v→U.loft=j→ U.post=l → U.phaseUp.threshold=fiery G₅ x R.L →U.phaseLow.threshold=temp x→ 0<U.room → 2*U.room<firstRadius G₅→∀ (M: Monk G₅ S),M.key.flags=RG.flags (temp x) M.V→ MossX n l x M.key M.park T M.V M.k h' U.room (fiery G₅ x R.L) q→‖M.z‖ ≤ L*Scales.p G₅ R.L x → ∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](i:E→L[ℝ] Directions G₅ (Domain N B)), (∀ y,axl M.key.flags (temp x•i y)=temp x•i y)→ ‖i‖≤1→∀ O:Stores S,Allows n (fun y=>soreG U (M.atop (i y) x) O) 0 (W*Esti.latticeFieldEstimates O j x) :=by
 obtain ⟨u,u',hu,hu',hz⟩:= bloomP n l q R ρ aτ h' L h p hv ht; obtain ⟨W,hW,Hb⟩:=inc n w C aτ ht; obtain ⟨C',hv',hp'⟩:=rub q n Z v hZ hx hY
 let G(h):= Jet.composeCost n h 1; let Y:=about R.L 0; let Z':= H*W +1; let V:= (Y:ℝ)+(Y:ℝ)*Z'+ G C'; refine ⟨V,by unfold V Z' G Jet.composeCost; positivity,?_⟩
 filter_upwards [(year G₅ R.L).eventually_gt_atTop 0,(sr u a u' C R.L).spine.eventually (ge_mem_nhds zero_lt_one), (sf b D u u' R.L).spine.eventually (ge_mem_nhds zero_lt_one), Hb, tamper n l R h' L h p,hz,Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x P hP kk hZ hp hz eB N P' B J e S T H₁ vB tB zB U β Ω u_ v_ g_ X y κ τ w' p0 M p1 p2 p3 E _ _ _ i Ht Hu O
 let Q(u:E):=M.atop (i u) x; let X₁(s:Signed):=lyn x s O U.loft; let T'(s:Signed):=strum x s O U.loft; let V'(s:Signed)(y:E):=pull s 0 (Q y|>.V); let Vo(y:E):=(Q y).sent x T U.trot U.room U.post U.beta; let W'(s:Signed):=pull s 0∘Vo
 let f:= scar U.phaseUp.threshold U.phaseLow.threshold u a u' C; let f':=scarf U.phaseUp.threshold U.phaseLow.threshold u b u' D H W; have hb:0<U.beta:= (half_pos P).trans_le β.1
 have hh: Inherits n q R ρ aτ h' L u u' (fiery G₅ x R.L) (L*Scales.p G₅ R.L x) M T l U.beta x U.room:=hz S T H₁.got M p1 p3 _ _ p2 β; have hi:=hp U.beta β S T M H₁.got p3 _ _ p2; rw [←y,←u_] at p2 hh -- tape uses q
 have hk:∀ j:Bond _,ContDiffAt ℝ (↑n) (fun y=> SU.group.mat (Vo y j)) 0:= fun j=> Err.sentE (U:=(0:E)) (β:=fun _=> U.beta) (R:=i) (Z:= fun _=> M.bush x) (z:=fun _=> M.bell x) p2 H₁.funds.1 (y ▸ hl) w' p0 i.contDiff.contDiffAt (map_zero _) contDiffAt_const hb (fun i=>contDiffAt_const) contDiffAt_const j
 let g(s):= deliver_s (a:=h') (c:=L) (Z:=L*Scales.p G₅ R.L x) U M R i Ht Hu hh κ τ (by linarith) (by linarith) hk s; let T0:ℝ:=(about S.patch.L 0*Esti.latticeFieldEstimates O U.loft x:ℕ); have hy : T0= Y*(Esti.latticeFieldEstimates O j x:ℝ):=by unfold T0 Y; rw [X,Nat.cast_mul,H₁.got]
 have he(s): Allows n (fun y:E=> ∑ j∈ X₁ s, folkK T x (Q y) s U.trot U.room U.post U.beta U.phaseUp U.phaseLow j) 0 (T0*f):=Lor.scope_p M.key O s _ (g s).1 (g s).2.1 vB tB (g s).2.2 fun _=>rfl
 have hf(s):Allows n (fun y:E=>∑ j∈ T' s, heatR T (Vo y) (Q y).V s M.key U.trot U.phaseUp U.phaseLow x (U.ang+U.fee) j) 0 (T0*f'):=by
    refine sauce M.key O s _ (g s).1 (g s).2.1 vB tB (g s).2.2 hW Ω fun j=>?_ ; rw [zB,τ]; exact hZ S T M i Ht Hu _ (zB ▸ tB) s j
 have hg:Allows n (fun y:E=> gemG U (Q y) O) 0 (Esti.latticeFieldEstimates O j x * G C'):=by
    unfold gemG; let I:= M.zoo x; let u:= locals M.key O x M.park ((U.loft+104)*radiusB x); have ht:u.card ≤ Esti.latticeFieldEstimates O j x:=by unfold u; rw [X]; exact (tune (F:=M.park) (A:=M.key) (O:=O) j eB).2.2.2
    have hv(z:I):Allows n (fun y:E=>Corne.flare T x U.trot U.room U.post U.beta U.vita U.rota (Q y) (show M.zoo x from z)) 0 (G C'):=by
       have hp1:=hp' _ _ (hi z)
       unfold Corne.flare; rw [y,u_,v_,g_]; exact Allows.comp (f:=i) ((map_zero i).symm ▸ hp1) (allows_linear Hu (by rw [map_zero,norm_zero]; norm_num))
    exact (summed u _ fun i _=> hv i).mono (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (by unfold G Jet.composeCost; positivity))
 have hs:|U.beta| *(T0*f) ≤ T0 :=by
    apply le_trans (mul_le_mul_of_nonneg_right ((abs_of_pos hb).le.trans β.2) (he (1:Signed)).nonneg); rw [mul_left_comm]; apply mul_le_of_le_one_right (by unfold T0; positivity); unfold f; rw [κ,τ]; exact hP
 have hf' := (allowedAv _ _ hf).mono (mul_le_mul_of_nonneg_left (show f'≤Z' by unfold f' Z' scarf; rw [κ,τ]; exact add_le_add_right kk _) (by unfold T0; positivity))
 let Q₀(y:E):=oak T x (Q y) U.trot U.room U.post U.beta U.phaseUp U.phaseLow U.loft O; have ht' : Allows n Q₀ 0 T0:= (((allowedAv _ _ he).smul (-U.beta)).mono (by rwa [abs_neg]))
 exact (subtract_p (subtract_p ht' hf') hg).mono (Eq.le (by unfold V; rw [hy]; ring))
end YM.CF.Lor
