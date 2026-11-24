import YM.CF.Corne.Pink
import YM.CF.Corne.Falls
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.L2Operator InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G₅"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G₅}{P': Tab S}
open Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec Facet Peaks
variable {n' B Mx X: Side}{T: Roam Mx X B}(G: Ratio (CSide Mx B) (CSide X B))(F:Tube G₅ T)
variable {C V R Z η e:ℝ}(Q: Msca Mx X B G e){Φ:nomA Mx X B→ ℂ}
local notation "pG"=> CSide Mx B
local notation "pF"=> CSide X B
local notation "D₀"=> More pG
local notation "D₁"=> More pF
variable (x d u:ℝ)(q:Chi)(l:ℕ)(S: Monk G₅ T)(A:Rent0 G e)(β:ℝ)(t:0 < e)
section
local notation "Y"=> mSeal X B
open Rill Fock Lat Skye Hest Acorn Tulip
attribute [local instance] opCStarAlgebra
open scoped Matrix.Norms.L2Operator
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma tickH (x:Rent0 G e)(s: JointB G x.val a)(h:a≤b): x.val∈ Rent0 G b:= ampleB s h
lemma drift_v {A:Nom (CSide Mx B) (CSide X B)}(s: JointB G A a)(h:a<e):∀ᶠ V in 𝓝 A,V∈Rent0 G e:=by
 let Q:= {U:Nom pG pF|JointB G U e}; have hx(i: Guy (N:=pG)):∀ᶠ V in 𝓝 A, ‖brand (V.2 i)-brand (travel V.1 ((ratio G).embed i.1) (pathL G i.2))‖ ≤ e:=by
    let Tt(V:Nom pG pF):=‖brand (V.2 i)-brand (travel V.1 ((ratio G).embed i.1) (pathL G i.2))‖
    have hY:Continuous Tt:=by unfold Tt; apply Continuous.norm; apply (Dial.spinD.comp _).sub (Dial.spinD.comp _) <;> fun_prop
    exact hY.continuousAt.eventually (ge_mem_nhds ((s.follow i).trans_lt h)) -- tune
 filter_upwards [continuous_fst.continuousAt.eventually (walkL _ _ s.fg h),continuous_snd.continuousAt.eventually (walkL _ _ s.cg h),eventually_all.mpr hx] with v e' v' i; exact ⟨e',v',i⟩
private lemma vogue(k:ℕ){U:E→ Pane c}(x:E)(h:TransK k U x 1)(g:1<C):∀ᶠ t in 𝓝 x,TransK k U t C:=by
 have ht(i:Bond (More c)):∀ᶠ v in 𝓝 x, Allows k (fun y=>SU.fund (U y i)) v C:=by
    let f:=fun y=> SU.fund (U y i); have hp:=h i; have hs (j: Fin (k+1)):∀ᶠ t in 𝓝 x,‖iteratedFDeriv ℝ (j:ℕ) f t‖≤C:=(((hp.smooth.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt))).norm).eventually (gt_mem_nhds ((hp.norm_le j (Nat.le_of_lt_succ j.isLt)).trans_lt g))).mono fun i v=> LE.le.trans (LT.lt.le v) le_rfl
    filter_upwards [eventually_all.mpr hs,hp.smooth.eventually (by simp)] with i hs g; exact ⟨g,fun j v=>hs ⟨j,Nat.lt_succ_of_le v⟩⟩
 exact eventually_all.mpr ht
variable (i:Seal (Site (More (CSide X B))))(Z:Rent0 G e→ℂ) -- reuse Z:ℝ conflict implicit
lemma mereP [FiniteDimensional ℝ E] (U:E→Rent0 G e)(x:E) (hZ:OrderD (LineE n G C e) n Z b)(v:∀ x y, (dressL G e).rel i x y→ Z x=Z y)(g:a<e)(hx:1<C)(hv:JointB G (U x).val a)(h:∀ j:Bond D₁,Skye.ends j⊆i→ Allows n (fun y=>SU.fund ((U y).val.1 j)) x 1)(u:∀ j:Bond D₀,Skye.ends j⊆cloudG G i→ Allows n (fun y=>SU.fund ((U y).val.2 j)) x 1): Allows n (Z ∘ U) x b:=by
 let W(y:E): Pane (CSide X B):=fun j=> if Skye.ends j⊆i then (U y).val.1 j else (U x).val.1 j; let V(y:E): Pane pG:=fun j=> if Skye.ends j⊆cloudG G i then (U y).val.2 j else (U x).val.2 j
 let f(y:E): Nom pG pF:= (W y,V y); let Ω:=fun y=> f y∈Rent0 G e; let H(y):Rent0 G e:= if h:Ω y then ⟨f y,h⟩ else U y
 have he:f x=(U x).val:=Prod.ext (funext fun j=>by simp only [f,W,ite_self]) (funext fun j=>by simp only [f,V,ite_self])
 have hW:TransK n W x 1∧ContinuousAt W x:=post_u n h -- tune cannot infer function
 have hV:TransK n V x 1∧ContinuousAt V x:=post_u n u
 have hr: ∀ᶠ y in 𝓝 x, Ω y:= (hW.2.prodMk hV.2).eventually (he.symm ▸ drift_v G hv g : ∀ᶠ y in 𝓝 (f x),y∈Rent0 G e)
 have hm:∀ᶠ y in 𝓝 x,TransK n (fun i=>(H i).val.1) y C ∧TransK n (fun i=>(H i).val.2) y C:=by
    filter_upwards [vogue n x hW.1 hx, vogue n x hV.1 hx,eventually_eventually_nhds.mpr hr] with y hw hV' h
    refine ⟨fun j=>(hw j).germ ?_,fun j=>(hV' j).germ ?_⟩<;> (filter_upwards [h] with i v; unfold H; rw [dif_pos v])
 obtain ⟨D,t,w,hQ⟩:=_root_.mem_nhds_iff.mp hm; apply (hZ E D w H t x hQ).germ -- tune test not t
 filter_upwards [hr] with z k; apply v; constructor <;> intro v h t <;> unfold H <;> rw [dif_pos k]; exact if_pos (insert_subset h (singleton_subset_iff.mpr t)); exact if_pos (insert_subset h (singleton_subset_iff.mpr t))
end
end YM.CF.Corne
