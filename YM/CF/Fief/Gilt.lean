import YM.CF.Fief.Boon
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Jet Push.AbsoluteSums
local notation "G₅"=> SU.group
variable {c f n N X B:Side}{S:StepData (Domain N B) (Domain X B)}{G:Ratio (mid N B) (mid X B)}{a b e C H D:ℝ}{k l j:ℕ}
local notation "m"=> mid N B
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{x:E}
lemma manager (v:Nom c f)(G:Ratio c f)(p:JointB G v e)(h:e < b):∀ᶠ i in 𝓝 v,JointB G i b:=by
 have hx(w:Guy (N:=c)):∀ᶠ i in 𝓝 v, ‖brand (i.2 w)-brand (travel i.1 ((ratio G).embed w.1) (pathL G w.2))‖ ≤ b:=by
    let P(i:Nom c f):=‖brand (i.2 w)-brand (travel i.1 ((ratio G).embed w.1) (pathL G w.2))‖; exact (show ContinuousAt P v from (((Dial.spinD.comp ((continuous_apply w).comp continuous_snd)).sub (Dial.spinD.comp (show Continuous fun i:Nom c f=> travel i.1 ((ratio G).embed w.1) (pathL G w.2) by fun_prop))).norm).continuousAt).eventually (ge_mem_nhds ((p.follow w).trans_lt h)) -- tune Dial.spinD
 filter_upwards [eventually_all.mpr hx, continuousAt_fst.tendsto.eventually (walkL _ v.1 p.fg h),continuousAt_snd.tendsto.eventually (walkL _ v.2 p.cg h)] with i hp v w using ⟨v,w,hp⟩
variable (k)(u:E→ Rent0 G e){S₀:Support (Domain X B)}
private lemma meetZ(k:ℕ){p:ℝ}{U:E→ Pane c}(h:TransK k U x 1)(g:1<p) :∀ᶠ t in 𝓝 x,TransK k U t p:=by -- p undecl
 have ht(i:Bond (More c)):∀ᶠ v in 𝓝 x, Allows k (fun y=>SU.fund (U y i)) v p:=by
    let f:=fun y=> SU.fund (U y i); have hp:=h i; have hs (j: Fin (k+1)):∀ᶠ t in 𝓝 x,‖iteratedFDeriv ℝ (j:ℕ) f t‖≤p:=(((hp.smooth.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt))).norm).eventually (gt_mem_nhds ((hp.norm_le j (Nat.le_of_lt_succ j.isLt)).trans_lt g))).mono fun i v=> LE.le.trans (LT.lt.le v) le_rfl
    filter_upwards [eventually_all.mpr hs,hp.smooth.eventually (by simp)] with i hs g; exact ⟨g,fun j v=>hs ⟨j,Nat.lt_succ_of_le v⟩⟩
 exact eventually_all.mpr ht
lemma riseP(W:Rent0 G e→ℂ)(p: OrderD (LineE k G C e) k W H)(h:∀ x y,(dressL G e).rel S₀ x y→ W x=W y)(g:b<e)(hc:1<C)(hy:JointB G (u x).val b)(hv:∀ j:Bond (Domain X B),Skye.ends j⊆ S₀ → Allows k (fun v=>SU.fund ((u v).val.1 j)) x 1)(he:∀ j:Bond (Domain N B),Skye.ends j ⊆ cloudG G S₀ → Allows k (fun v=> SU.fund ((u v).val.2 j)) x 1): Allows k (W∘ u) x H:=by
 let V(t:E):Nom (CSide N B) (CSide X B):=((fun j=>if Skye.ends j⊆ S₀ then (u t).val.1 j else (u x).val.1 j),fun j=> if Skye.ends j⊆cloudG G S₀ then (u t).val.2 j else (u x).val.2 j); let P(t:E):Prop:= JointB G (V t) e; let f(t:E):Rent0 G e:=if h:P t then ⟨V t,h⟩ else u x
 obtain ⟨hp,hx⟩:= post_u k (U:=fun v=>(u v).val.1) hv; obtain ⟨hL,hK⟩:= post_u k (U:=fun v=>(u v).val.2) he
 have ht':∀ᶠ i in 𝓝 x,P i:=(show ContinuousAt V x from hx.prodMk hK).eventually (p:=fun i=>JointB G i e) (manager _ _ (show JointB G (V x) b from ?_) g); swap
 · rw [show V x=(u x).val from ?_]; exact hy; apply Prod.ext <;> ext1 <;> simp [V]
 have hh:∀ᶠ i in 𝓝 x,TransK k (fun v=>(f v).val.1) i C∧ TransK k (fun v=>(f v).val.2) i C:=by
    filter_upwards [meetZ k hp hc, meetZ k hL hc,eventually_eventually_nhds.mpr ht'] with i u v p; refine ⟨fun j=> (u j).germ (p.mono fun y r=> ?_), fun j=>(v j).germ (p.mono fun y r=> ?_)⟩ <;> dsimp only [f] <;> rw [dif_pos r] -- tune
 obtain ⟨Y,hY,hF,hV⟩:= _root_.mem_nhds_iff.mp hh; apply Allows.germ (p E Y hF f (fun x hx=>hY hx) x hV)
 filter_upwards [ht'] with i xi; apply h (f i) _; refine ⟨fun u a b=>?_,fun u a b=>?_⟩ <;> unfold f <;> rw [dif_pos xi] <;> exact if_pos (insert_subset a (singleton_subset_iff.mpr b))
end YM.CF.Fief
