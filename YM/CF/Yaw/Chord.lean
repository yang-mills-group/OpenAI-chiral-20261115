import YM.CF.Yaw.Seal
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
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Eire Jet Scroll Push.AbsoluteSums.Trees Rill Atala
local notation "G_"=> SU.group
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B))(φ:S.ratio=Rush.ratio G)
local notation "c₁"=> Domain N B
local notation "c₂"=> Domain P B
variable {r l n k k' m:ℕ}(x d e s s' K τ B₀:ℝ)(q h:Chi)
variable{S} (U:Loom (mid N B))(V:Loom (mid P B))(T:Tube SU.group S)
variable {e s s' d x K τ B₀} {t v b b' a β e0 v':ℝ}
local notation "B'"=> radiusB x
local notation "k_"=> ((l+90)*radiusB x)
local notation "bay"=> Stilo.bay
variable (M:Monk SU.group S)(J: List (Kite S r))(p:M.key=cook S J.toFinset)(A:Ride S) 
local notation "F"=> erosion ((l+70)*radiusB x) (bay A)
local notation "Y"=> (((M.V,M.U,β,M.z):HomeL (Domain N B) (Domain P B)))
local notation "D"=> cusp M.key x M.V
variable {J':Teller SU.group}
variable (hp:30*radiusB x ≤ r)(hx:1000≤radiusB x)(vK:∀ i∈ J.toFinset,Lattice.halo ((l+90)*radiusB x) (Eire.frameP S i)⊆Stilo.bay A)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (I:E→L[ℝ] Directions SU.group (Domain N B))
local notation "Z_"=> (fun i=>Rill.TasteZ.hover M.V I i x Y)
local notation "K_"=> (monkD M ∘ Z_)
local notation "Nc"=> ({M with key:=cusp M.key x M.V}:Monk SU.group S)
variable {Jc:ChartRatio SU.group}
local notation "U_"=> legL M T x q d l
include p vK
set_option maxHeartbeats 900000 in
-- recover cooldown even at strictly surviving supports(and closure). crucial O.READ authority.
lemma monitor {L t w:ℝ}{Bz:Type}[Zero Bz](V:E→Bz)(g:0∈tsupport V)(u:pureK S J.toFinset)(c:(m+110)*radiusB x+14 ≤ r)(y:0<fiery G_ x S.patch.L)(z:Rill.MarkP M F x s s' Y l n T q d)(p':∀ i, V i ≠ 0 → (∏ j∈ liftK S J.toFinset, Reine.treat T x (K_ i) q d l β Jc w t L r m j) ≠0): looseV x M r m (M.sent x T q d l β):=by
 let U(x':E):= U_ (Z_ x'); have hx: (Z_ 0)=Y:=by simp [TasteZ.hover,Vmove]
 have hu:Continuous Z_:=by unfold TasteZ.hover Vmove increment; fun_prop
 have hp(v:E)(lo:V v≠0): looseV x M r m (U v):=by
    apply shave (q:=q) (β:=β) (d:=d) (l:=l) (w:=w) (t:=t) (K_ v) Jc y; apply Finset.prod_ne_zero_iff.mpr; intro i h; change i∈ blip S M.key r at h; rw [p,cooked S _ u] at h
    exact left_ne_zero_of_mul (left_ne_zero_of_mul ((Finset.prod_ne_zero_iff.mp (p' v lo)) i h))
 have ht(O:Hos S r)(b: O∈ blip S M.key r)(j:Cell c₂)(x':j∈ nearFace S (obv x m 110 O.val)) : ContinuousAt (fun i=> Pressure.toll (U i) j) 0 :=by
    rw [p,cooked S _ u] at b; obtain ⟨i,lx,v⟩:= mem_image.mp b; have hk:= Reine.reachP (r:=(m+110)*B'+10) j x' (Nat.le_refl _) -- tune names
    have hc(s:Site c₂)(k:s∈touched j): S.ratio.parent s ∈ stem S O:= dome_u hk (r:=r) (by have ht:= Work.E01.sep_touched j s k; have hp:= Work.E04.parent_separation S.ratio j.1 s; omega)
    let W:= touched j
    let Z(i:E):Pane (mid P B):= fun k=> if k.1∈ W then U i k else 1
    have hp: ContinuousAt Z 0:=by
       apply continuousAt_pi.mpr; intro v'; unfold Z; split; next p =>
          have hZ:=z.tea v' ((halo_subset 13 _) (((frame_s S i).trans ((halo_subset ..).trans ((skyC (x:=x) (l:=l) (r:=r) S A).ports _ (vK i lx)))) ((congrArg (stem S) v).symm ▸ (hc _ p))))
          apply ContinuousAt.comp (f:=Z_) (g:=fun i=> U_ i v') _ hu.continuousAt; change ContinuousAt (fun i=> U_ i v') (Z_ 0); rw [hx]; exact (SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (wet _ hZ)
       exact continuousAt_const
    have he(i:E): Pressure.toll (U i) j=Pressure.toll (Z i) j:= congrArg SU.group.chord (travel_local _ _ _ _ (fun i p _=> (if_pos (List.mem_toFinset.mpr p)).symm)) -- Lean likely inference
    rw [funext he]; exact (((SU.group.continuous_chord.comp (show Continuous (fun U:Pane (mid P B)=>faceValue U j) from by unfold faceValue; fun_prop))).continuousAt.comp hp)
 rw [show M.sent x T q d l β=U 0 from ?_]; swap; · unfold U; rw [hx]; rfl
 intro O u j x' a; by_contra! t; obtain ⟨i,l,q⟩:=mem_closure_iff_nhds.mp g _ ((ht O u j x').eventually (lt_mem_nhds t)); exact (hp i q O u j x' a).not_gt l
end YM.CF.Yaw
