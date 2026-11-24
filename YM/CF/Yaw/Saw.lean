import YM.CF.Yaw.Oar
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(z:Odd G.count.val)(e:ℝ)(g:0<e)(X: Meter TailB G e)(V: Meter Grave G e)
local notation "bay"=> Stilo.bay
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "A'"=> Single (mid P B)
local notation "B'"=> Single (mid N B)
variable (K:E→Rill.Arch G e) (k:ℕ)
local notation "α'"=> Scion.tinOre (switchG G).symm
local notation "H'"=> Eire.Ride S
local notation "L'"=> Domain P B
local notation "W'"=> LeanV B'
variable (d:ℕ) {δ:ℝ}
-- mantle artisanal
abbrev starsC : ℂ →L[ℝ] ℂ:= (starL ℝ).toContinuousLinearMap
abbrev Wax:= max ‖starsC‖ 1
abbrev lip := (d+1:ℝ)*Wax
lemma wax_m:1≤ Wax:=le_max_right ..
lemma richP :0≤ lip d:=mul_nonneg (by positivity) (zero_le_one.trans wax_m)
lemma sign_c(b:Bool)(F:E→ℂ)(t:E)(u:ℝ)(h:Allows d F t u): Pence d (fun i=> cSignX b (F i)) t (lip d*u):=by
 unfold lip; rw [mul_assoc]; apply Rue.bare_p; cases b; exact h.mono (le_mul_of_one_le_left h.nonneg wax_m); exact h.linear starsC (le_max_left ..)
abbrev BeamV (T:Support L')(A:ℝ)(p:E):Prop:= (∀ i:Bond L',Skye.ends i⊆ T → Tender (fun y=>(K y).val.1.1 i) p A d∧ Tender (fun y=>(K y).val.2 i) p A d) ∧∀ i:Bond (Domain N B),Skye.ends i⊆ cloudG G T → Tender (fun y=>(K y).val.1.2 i) p A d
-- due & full. co parity false still overpay per-half*2
variable (HX:TailB→Support (Domain P B)→Toll (Iota G))(HY:Grave→Support (Domain P B)→Toll (Iota G))
local notation "τ"=> Twig (Single (mid P B))
local notation "S_"=> Support L'
abbrev payK(Y:S_)(i:τ)(j:W'):= let h:=α' i; lip d*HX (tallC h,(twigS h).1) Y (twigS h).2 (patchQ G j.2)
abbrev payZ(Y:S_)(i j:τ) := let h:=α' i; let s:= α' j; lip d*HY (tallC h,tallC s,(twigS h).1,(twigS s).1) Y (twigS h).2 (twigS s).2
abbrev SureV (F:S_→ (W'→ℝ))(i:S_):Raid W':=∑ j: W',Pi.single ({j}:Finset W') (F i j)
def sign_l(i:τ):Track H' (Raid (LeanV B')) := ∑ T:Support L',Pi.single (mark_l S k T) (SureV (N:=N) (B:=B) (fun Y=> payK G d HX Y i) T)
def sign_z(i j:τ):Track H' (Raid W'):= (∑ T:Support L',Pi.single (mark_l S k T) (Pi.single ∅ (payZ G d HY T i j)))+ Pi.single ⊥ (Pi.single ∅ ‖due_z G i j‖)
variable (E)
abbrev SpiritX(Pcap ℕ':ℝ)(k:ℕ):Prop:=∀{N P:Side}(X:Ratio N P)(F:cro X ℕ'→ Op (Iota X)){S:Support (More P)}(t n:Bool)(W:Toll (Iota X)), Suite (badge _) (pinH X ℕ' t) (pinH X ℕ' n) S W F → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](u:E→ cro X ℕ')(x:E)(V:E→ Nom N P)(T:E→ Pane P), (∀ i,(u i).val=(unionP (V i),Tulip.profile (T i))) → JointB X (V x) ℕ' → Guard (T x) ℕ' → (∀ i:Bond (More P),Skye.ends i⊆ S → Tender (fun y=> (V y).1 i) x Pcap k ∧ Tender (fun y=>T y i) x Pcap k) → (∀ i:Bond (More N), Skye.ends i⊆ cloudG X S → Tender (fun y=> (V y).2 i) x Pcap k) →∀ i j, Allows k (fun p=> F (u p) i j) x (W i j)
variable {E}
variable (x:∀ i Y, Suite (badge _) (pinH G e true) (pinH G e false) Y (HX i Y) (X i Y))
variable (u:∀ i Y, Suite (badge _) (pinH G e true) (pinH G e true) Y (HY i Y) (heal G e V i Y)) (h:SpiritX δ e d)
include g x h
lemma baneV(Y:Support L')(R:E)(p:BeamV G e K d Y δ R)(i:τ): Woody d (fun v=>balm G e g X K i Y v) R (SureV (N:=N) (B:=B) (fun Y=> payK G d HX Y i) Y):=by
 let Q(j:W')(a:E):= gash G e g X (K a) i j Y • put j
 refine Woody.germ (Woody.sumV (S:=univ) (G:=Q) (fun j _=>?_ )) (Eventually.of_forall fun z=>by unfold Q; simp only [Finset.sum_apply])
 simp_rw [Q,show ∀ j:LeanV B',put j=poke {j} from fun j=> (Poly.tag_once (cane (LeanV B')) j).symm]; apply Woody.chit
 let j':=α' i; let T:TailB:=(tallC j',(twigS j').1); have ht:= h G (X T Y) _ _ _ (x T Y) E _ R (fun y=>(K y).val.1) (fun y=>(K y).val.2) (fun i=> (show (bring g (K i)).val=(unionP (K i).val.1,Tulip.profile (K i).val.2) from rfl)) (K R).property.1 (K R).property.2 p.1 p.2 (twigS j').2 (patchQ G j.2); unfold gash Urn.mount; dsimp only; split; · exact sign_c _ _ _ _ _ ht
 refine ⟨contDiffAt_const,?_ ⟩; rw [pot_const,norm_zero]; exact mul_nonneg (richP d) ht.nonneg
omit x
include u
lemma boonV(Y:Support L')(R:E)(p:BeamV G e K d Y δ R)(i j:τ): Woody d (bowZ G e g V K i j Y) R (Pi.single ∅ (payZ G d HY Y i j)):=by
 unfold bowZ; simp_rw [show (1:FC (LeanV B'))=poke ∅ from (Poly.tag_void ..).symm]; apply Woody.chit
 let i':=α' i; let j':=α' j; let T:Grave:=(tallC i', tallC j',(twigS i').1,(twigS j').1); have ht:= h G (heal G e V T Y) _ _ _ (u T Y) E (bring g ∘ K) R (fun y=>(K y).val.1) (fun y=>(K y).val.2) (fun i=>rfl) (K R).property.1 (K R).property.2 p.1 p.2 (twigS i').2 (twigS j').2; unfold pairZ Urn.soar; dsimp only; split; swap; · exact sign_c _ _ _ _ _ ht
 refine ⟨contDiffAt_const,?_ ⟩; rw [pot_const,norm_zero]; exact mul_nonneg (richP d) ht.nonneg
include x
lemma launch_v (F:H')(R:E)(p:∀ Y,mark_l S k Y ≤ F→BeamV G e K d Y δ R): TramS (fun E s=>cala G S z e g X V (K E) k s) R d F (sign_l G S k d HX) (sign_z G S k d HY) :=by
 refine ⟨fleetT G S e g X K k, fleetZ G S e g V K k, ⟨fun s _ i=>Eventually.of_forall (fun x=>grants_m G S z e g X V K k s x i),fun s _ i j=> Eventually.of_forall (fun x=>grants_z G S z e g X V K k s x i j)⟩, fun i j v=>?_,fun i j t v=>?_⟩
 · unfold fleetT sign_l; simp only [Finset.sum_apply]; apply Woody.sumV; intro s _; simp_rw [Pi.single_apply]; split_ifs with f; exact baneV G e _ X K d _ x h s R (p _ (f ▸ v)) i; exact Woody.empty _
 unfold fleetZ sign_z; rw [Pi.add_apply,Pi.add_apply]; apply Woody.addP; swap
 · rw [Pi.single_apply ⊥,Pi.single_apply ⊥]; split_ifs;  · simp_rw [show (1:FC (LeanV B'))=poke ∅ from (Poly.tag_void ..).symm]; exact Woody.chit ∅ (Pence.const _ _) 
   exact Woody.empty _
 simp only [Finset.sum_apply]; apply Woody.sumV; intro s _; simp_rw [Pi.single_apply]; split_ifs with f; exact boonV G e g V K d HY u h s R (p _ (f ▸ v)) i j; exact Woody.empty _
end YM.CF.Yaw
