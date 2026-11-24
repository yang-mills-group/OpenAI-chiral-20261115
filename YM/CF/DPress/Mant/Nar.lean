import YM.CF.DPress.Loch.Indian
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
namespace LinearT
open DPress Fees.Moral Larch Bake
variable {n:Side}{P:BudgetPoint}{a θ u h:ℝ}(p:1≤h){X Y:RegBudget n}{B E:Pax n}{K F:Cusp n}{f g:Aura n → ℝ}
lemma writ0 : writ_E (0:RegBudget n)=0:=by have he:= Ione.writ_k (0:RegBudget n) (0:RegBudget n); rw [zero_add] at he; exact add_right_cancel (b:=writ_E (0:RegBudget n)) (by rw [←he,zero_add])
lemma write : writ_E (X-Y)=writ_E X-writ_E Y:=by apply eq_sub_of_add_eq; rw [←writ_k,sub_add_cancel]
lemma forcedK(s:Sweep n) : force_V s (K-F)=force_V s K-force_V s F:=funext fun _=>funext fun _=>funext fun _=>map_sub ..
lemma writes :writ_K (K-F)=writ_K K-writ_K F:=by unfold writ_K; simp_rw [forcedK,sum_sub_distrib,smul_sub]
lemma stepUp(i:Ids n): cast_E (B-E) i=cast_E B i-cast_E E i:=by funext j U; simp only [cast_E,Pi.sub_apply, Pi.smul_apply, smul_sub]
lemma fuel_p : nextE (f-g)=nextE f-nextE g:=by funext i j v; change -((f i-g i) • (1:Cipher n))=_ ; change _= -(f i • (1:Cipher n))- -(g i • (1:Cipher n)); rw [sub_smul]; abel
lemma TurfB (u:Turf B)(v:Turf E):Turf (B-E):=fun i p j=>congrArg₂ (·-·) (u i p j) (v i p j) -- order i V p
lemma Bsym (u:Sym_a B)(v:Sym_a E): Sym_a (B-E):=fun i p j=>(congrArg₂ (·-·) (u i p j) (v i p j)).trans (map_sub ..).symm
lemma wageSub(k:ℕ)(x y:Cipher n): wage_Q k (x-y)= wage_Q k x-wage_Q k y:=by apply eq_sub_of_add_eq; rw [←plus_Y,sub_add_cancel]
lemma ksym (t:Mono_W K)(q:Mono_W F): Mono_W (K-F):=fun i v p z x=> (wageSub _ _ _).trans (congrArg₂ (·-·) (t i v p z x) (q i v p z x))
lemma SYp (t:Sym_P (numbD X))(q:Sym_P (numbD Y)): Sym_P (numbD (X-Y)):=by
 rw [show numbD (X-Y)=numbD X-numbD Y from ?_]; swap
 · funext i j; change deadP (X i j-Y i j)=deadP (X i j)-deadP (Y i j); unfold deadP; rw [wageSub]; abel
 intro s; rw [show base_Q s _=base_Q s (numbD X)-base_Q s (numbD Y) from funext fun _=>funext fun _=>map_sub ..,t s,q s]
include p
lemma νForce (t:Mono_W K)(v:ZL P h θ K u): ZL P h θ (writ_K K) (pack_Q P.order *u):=by
 obtain ⟨V,w,t'⟩:= mantle P h θ p _|>.1 v; exact (mantle P h θ p _).2 ⟨pony_R P.order V,memo_P K _ P w t (zero_le_one.trans p),family_Q V t' P.order⟩ -- arg tune
lemma νFuel (t:∀ i:Skye.Seat n,tallB (fun j=>|f j|) P.B θ i≤u): ZL P h θ (nextE f) u:=by
 refine (mantle P _ _ p _).2 ⟨(fun j=>|f j|),⟨(fun j=>abs_nonneg _),fun i j _ _=>?_⟩,t⟩; change Medal P i.val j (- ((f i) • 1:Copy n)) _ _; exact (Medal.oneT.rum (f i) |>.negT |>.big (mul_one ‖f i‖|>.le)) -- tune abs
lemma receiptR (τ:Ids n) (s:Sym_a E)(t:Turf E)(q:PactF P (P.supportExponent+1+1) h E u):IncX Utrue (cast_E E τ) P h (reserveT P.power P.order P.B 1 * u):=by obtain ⟨v,q,w⟩:=q; exact worth_R P E τ s t (zero_le_one.trans p) q w
end LinearT
end YM.CF.Py.Kay
