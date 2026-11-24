import YM.CF.Vow.Grow
import YM.CF.Salt.Mica
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- Spin off Δ reimbursement. natural translations kernel even. arbitrary AlgHom linear
open Salt Trees Ursell
variable (T:Sweep n) (X Y:Aura n)
abbrev FrameR(f:Sweep n)(UnitA:UNI SpinIdx):Cipher n→ₐ[ℝ]Cipher n:=Scree.paintR f.charge (detX f.s) (prepU (castX f) UnitA (xtra f.charge) n)
abbrev moldA (T:Sweep n):Equiv.Perm (Aura n):= Equiv.ofBijective (fun i=>⟨actY T i.val,Finset.map_nonempty.mpr i.property⟩) ⟨fun i j l=>Subtype.ext (map_injective _ (show actY T i.val= _ from congrArg Subtype.val l)),Finite.surjective_of_injective fun i j l=>Subtype.ext (map_injective _ (show actY T i.val= _ from congrArg Subtype.val l))⟩
local notation "Yc"=> moldA T
local notation "Λ"=> Salt.quill (boxA T)
local notation "Υ"=> actY T
lemma moldT:Disjoint X.val Y.val ↔ Disjoint (Yc X).val (Yc Y).val:= (Finset.disjoint_map _).symm
variable {F:Pax n}{K W:Cusp n} (C:Cipher n→ₐ[ℝ]Cipher n) (V:Orbit n)
abbrev yellA(s:Sweep n)(V:Orbit n):Orbit n:=(flashA s V.1,bun s V.2)
variable (p:∀ i, F (moldA T i) (yellA T V) = C (F i V))
lemma yarnV (i: Aura n)(z:ℝ) : visible P i.val ∅ V.1 ↔ visible P (Yc i).val ∅ (yellA T V).1:=by
 have he (X:Support (More n)): Rue.litres P.threshold X ∅={U:Pane n|pingS P.threshold (X\∅) U}:=by ext; simp [Rue.litres]; -- tune
 have hy:= Salt.lights_V P.threshold i.val ∅ T V.1; rw [he,show actY T ∅=∅ from map_empty _,he] at hy; exact hy.symm
abbrev curlV(T:Sweep n) (m:ℕ) : Equiv.Perm (Tuple (Aura n) m):= Equiv.arrowCongr (Equiv.refl _) (moldA T) -- ext
lemma patV (i:Tuple (Aura n) k) : coefficient Palot.gRule (curlV T k i)=coefficient Palot.gRule i:=by
 unfold coefficient; congr 1; ext j; rw [potential_mem,potential_mem]; apply and_congr_right; intro h; constructor
 · exact fun v x t j' p d=> (moldT T (i x) (i j')).mp.mt (v x t _ p d) -- .? moldT goes Or.S. need .mpr.mt
 exact fun v x t j' p d=> (moldT T (i x) (i j')).mpr.mt (v x t _ p d)
lemma tideI (i:Tuple (Aura n) k): tideU ⟨k,curlV T k i⟩= Yc (tideU ⟨k,i⟩):=Subtype.ext (by
    let L:= tideU ⟨k,curlV T k i⟩; ext x ; change x∈ unionOf Palot.stern (curlV T k i) ↔x∈Υ (tideU ⟨k,i⟩).val; unfold actY; rw [Finset.mem_map_equiv]; constructor
    · intro p; obtain ⟨j,w,h⟩:=mem_biUnion.mp p; change _∈ _ at h; refine mem_biUnion.mpr ⟨j,w,?_⟩; exact mem_map_equiv.mp (show x∈Υ _ from h) -- tune
    intro h; obtain ⟨j,u,w⟩:= mem_biUnion.mp h; refine mem_biUnion.mpr ⟨j,u,?_⟩; change x∈Υ _; exact mem_map_equiv.mpr w)
include p
lemma voyage (i:Tuple (Aura n) k):sta F (Yc X) m (⟨k,curlV T k i⟩) (yellA T V) = C (sta F X m ⟨k,i⟩ V):=by
 unfold sta; simp only [tideI,(moldA T).injective.eq_iff]; split; swap; · exact (map_zero _).symm
 unfold guava; simp only [Pi.smul_apply, Finset.prod_apply]; rw [patV,map_smul,map_prod]; refine congrArg _ ?_; apply prod_congr rfl; exact fun j _=> p _
variable {Q:Aura n→ℝ} {d1 d2 d3:ℝ}{M:ℕ}(Pv:Ready Palot.stern M Q c d1 d2 d3)(t:1≤h)(P_:∀ i,Medal P i.val ∅ (F i) h (Q i))(k_:0≤c)
include Pv t P_ k_
lemma spinsE(m:ℕ):spinD P (Yc X) F m (yellA T V)= C (spinD P X F m V):=by
 by_cases x: visible P X.val (∅:Support _) V.1; swap; · exact (if_neg (mt (yarnV T V X 0).2 x)).trans (by rw [show spinD P X F m V=0 from if_neg x, map_zero]) -- tune
 let J(i k:ℕ):= V; rw [spiritD (Yc X) _ _ _ Pv k_ ((yarnV T V X 0).1 x) m,spiritD X V _ _ Pv k_ x]; all_goals first| exact P_| exact t|skip -- params
 let L:= C.toLinearMap.toContinuousLinearMap
 let A:=fun (s: Clusters (Aura n))=> sta F X m s V; obtain ⟨i,g,h⟩:=x; have hp:Summable A:=Summable.of_norm_bounded (glomM X Pv k_) (fun j=>by
    let K:=ponder X j t P_ m; unfold A; rw [K.same _ (i,V.2) h (fun _ _=>rfl)]; exact K.capF t _ g)
 let Y:= Equiv.sigmaCongrRight (fun m=> curlV T m)
 change _ = L (∑' (i:Clusters (Aura n)), A i); rw [←(L.hasSum hp.hasSum).tsum_eq] -- tune
 rw [← Y.tsum_eq]; exact tsum_congr fun s=> voyage T X C V p s.2
end YM.CF.Vow
