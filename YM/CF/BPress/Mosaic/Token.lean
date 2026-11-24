import YM.CF.BPress.Mosaic.Drive
import YM.CF.BPress.Honey.Restore
/- supplies weak field pieces w/ true sign. The no-reads rule for zero fees. Warm frame Authorization.Sc.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mosaic.Pulse
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Peel.Spine Ledger Push.AbsoluteSums
variable (R: Hangar (More N)) (H:Crew A){I:Type}[Fintype I]{V:GramM N} (F: Recipe (A:=A) V) (C ζ k D a C' τ t:ℝ)
def payL := d0 1 R.L.val 1 |leftCost H F C'|
def payE := d0 2 R.L.val (counted F.M B.D) (errorCost H F ζ D)
def payJ := expense 4 t (R.L.val^3) (estate 2)* (Recipe.jac H) -- tune parsing
variable {R H F C ζ k D a C' τ t} {X: Sugar.Stage N}
variable (p: Budgeting H F τ k D ζ a C') (Q:Mangrove R H F.M) (v: RightsC X R H t)(g:Fast H.y)
local notation "U°"=> Visit A R H
local notation "β"=> party A R H
include g in
lemma atm (f:H.castP→ℝ)(h:Measurable f) : Measurable (fun x:Visit A R H=> (f (party A R H x):ℂ)):= Complex.continuous_ofReal.measurable.comp (h.comp (party_meas g)) -- argument order g isn't include
include p Q g
theorem shelf : Lift (payL R H F C') (fun x: Visit A R H=> (∑ i:A.Hcols,(leftY H F (β x).val i:ℂ))):=by
 let w:=fun (i:A.Hcols)(v:U°)=> (leftY H F (β v).val i:ℂ); let V':= |leftCost H F C'|; refine localSupply 1 (fun _=>True) id 1 (fun i=>?_) (abs_nonneg (leftCost H F C')) w (fun i=>?_) (fun i x=>?_) fun i x y f=> congrArg (fun a:ℝ=>(a:ℂ)) (Q.sailsL p f i le_rfl); · simp [-Function.id_def,id, filter_eq']
 · exact atm g _ ((p.grain_m i).comp measurable_subtype_coe)
 unfold w; rw [Complex.norm_real, if_true,Real.norm_eq_abs]; exact (p.left ..).trans (le_abs_self _)
theorem traveler : Lift (payE R H F ζ D) (fun x: U° => (∑ i:Root (More N), - (tinW H F (β x).val i:ℂ))):=by
 let w:= fun i (v:U°)=> -(tinW H F (β v).val i:ℂ); let r:= retained A F.M; refine localSupply 2 r (block A F.M) (counted F.M B.D) (fun x=>?_) (abs_nonneg _) w (fun i=>?_) (fun i x=>?_) (fun i x y f=> congrArg (fun v:ℝ=> -(v:ℂ)) (Q.tinRead p f i le_rfl)) -- tune r defined nonexp
 · apply le_trans (card_le_card ?_) (ticket_copies p.high x); intro i v; obtain ⟨q,w⟩:= (mem_filter.mp v).2; rw [←w]; exact mem_filter.mpr ⟨mem_univ _,q,column_self ..⟩
 · exact (atm g _ ((p.wheat_m i).comp measurable_subtype_coe)).neg
 unfold w; rw [norm_neg,Complex.norm_real, Real.norm_eq_abs]; split; exact p.billT ..; next h=> simp only [tinW, Θ, mem_filter, mem_univ,true_and,show ¬retained A F.M i from h,false_and, ↓reduceIte,abs_zero,le_refl] -- tune false orientation
-- Jac mapping $courant$.
include v
theorem coastal (v₀:t≤ ΩJ H) : Lift (payJ R H t) (fun x: Visit A R H => ∑ T:Seal A.Hcols,(tailY H F (β x).val T:ℂ)) :=by
 let w:=columnCost H F; obtain ⟨l,G⟩:= turfReceipt A R 0 (fun T=>T) w p.Jac_turf; let k:=Recipe.jac H; let T:=p.Jac; have he: estate 0*estate 2 ≤ Fac H X:=by
    unfold Fac overhead pacer magicC baser; unfold estate; generalize fundP X H=n; generalize creep H.n H.L H.y=z; let h:(0:ℕ)< (n+n+1)^4:=by positivity
    calc
     _ ≤ (4 * 40 + 1)^4 * (((4 * 1 + 1) ^ 4 * (4 * 2 + 1)^4 + 2 * (4*2+1)^4*(0+1)) * 1):= by norm_num
     _ ≤ _:= by gcongr <;> first| exact h| exact Nat.zero_le _ 
 have hp: Cash l w 4 (payJ R H t):=by
    have hu:= G.height.purse (T.chill v₀) (by norm_num : (0:ℝ)≤ 4) T.zero v.c (he.trans v.boss.1) ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he) (by norm_num : (0:ℝ)≤4)).trans v.boss.2); unfold payJ; rw [show estate 0*estate 2=estate 2 from by norm_num [estate]] at hu; exact hu
 refine (show Act0 l w (payJ R H t) (fun T x=> (tailY H F (β x).val T:ℂ)) from ⟨fun T x y f=> congrArg (fun v:ℝ=>(v:ℂ)) (Q.tailRead p (peeking _ _ _ f) T (?_ )), hp, (?_), G.height.trunk, fun T=> atm g _ ((p.tail_m T).comp measurable_subtype_coe)⟩).wallet
 · rw [G.pack]; exact b_blank ..
 intro i x; rw [Complex.norm_real, Real.norm_eq_abs]; exact p.tail ..
include v
lemma back_g (C:Host R H)(t':t≤τ): Lift (MicCost R X B t * k) (fun x:U°=> ∑ i:Support (More N), -(weak H F (β x).val i:ℂ)):=by
 let w:= weakBill (A:=A) F; refine mirror v (p.world.cash.chill t') ?_ (?_ ) (?_ )
 · intro i h; have he := (not_not.mp (fun t=> h (p.world.zero i t))); have hp:= (show Grove (Grid.field 4 _) i from he); have hm: Locale.meets A X.W.M i:=by
       obtain ⟨i,h⟩:= near_weak A i he (show weakFar A i from Classical.byContradiction fun t=> h (if_neg t)) -- tune ``weakFar=∀..`
       obtain ⟨x,f,V⟩:= Finset.not_disjoint_iff.mp h; exact ⟨x,f,i,(zone_of_halo ..).mp (halo_subset X.W.M _ V)⟩ -- tune args
   refine ⟨hm,FeeT.general v C hp hm (fun t p' x y h=>?_ )⟩; apply congrArg (fun r:ℝ=> -(r:ℂ)); exact (p.world.unit i).loc _ _ (agrees_mono (p'.raw _ _ (peeking _ _ _ h)) (Finset.coe_subset.mpr (halo_subset ..))) -- tune hp budget. patch
 · intro i x; simp only [norm_neg,Complex.norm_real,Real.norm_eq_abs]; exact p.lucid (β x) i
 intro i; exact (atm g _ ((p.weak_m i).comp measurable_subtype_coe)).neg
end YM.CF.BPress.Mosaic.Pulse
