import SatinFixedContrastNovember4
import SatinThinFusionStitch
/-! # Sales of mixed centric fields (before the prescribed finite time derivatives)

Note the error tolerance at the *raw seam*, much stronger than at a fixed ε>0.
Chosen purchase works for all strict positive times. Width limit here means a real
series of stencils with strictly increasing physical cost resolutions.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets
variable (P:Spine)(Z:Lead.Clan)(x:P.Spectrum0 3)
local notation "K" => P.calibration
local notation "T" => timeMesh P.par
local notation "ξ"=> P.advocate 3 x 3
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ξ"=> P.wealth 3 ξ
local notation "R"=> P.seasons 3 ξ
local notation "ζ" i:max=> (purePrice i:ℂ)
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "E"=> (S).E
local notation "L"=> Lead.Clan
local notation "V!"=> (∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (c r:ℕ→ℕ)(Y:ℕ→ P.Apron) (n:ℕ→ℕ)
local notation "Q" k:max j:max=> P.stitchApron k (Y j) (c (n j)) (r (n j))
local notation "w" i:max=> (Y i).realWidth P 3
local notation "e" i:max=> (Y i).engine P 3 ξ
structure HandleWith : Prop where
 fast: StrictMono n
 already: ∀ i, (Y i).s ≤ c (n i)
 distinct: ∀ i, P.calibration.ℓ < r (n i)
 price: ∀ i,∀ k:Lead.Clan, ‖((Y i).engine P 3 (P.advocate 3 x 3)) ((P.physicalEnergy 3 (P.advocate 3 x 3)).E ((w i).toNNReal) (P.shard x k (c (n i)) (r (n i)))) - ζ k • (Y i).engine P 3 (P.advocate 3 x 3) (P.colorZero 3 (P.advocate 3 x 3))‖ ≤ P.macroStep i
private lemma choose_handle {W:ℕ→ℕ→Prop} (p:∀ i,∀ᶠ j:ℕ in atTop,W i j):∃ n:ℕ→ℕ,StrictMono n ∧ ∀ i,W i (n i):=by
 choose h u using fun i=> eventually_atTop.1 (p i)
 let g:ℕ→ℕ := Nat.rec (h 0) (fun i v=>max (h (i+1)) (v+1))
 exact ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (h (i+1)) (g i+1)),fun i=> u i (g i) (by cases i; exact le_refl _; exact le_max_left ..)⟩
variable {K':P.Register}{J:P.Ellis 3 x}(B:P.Experiment K' c r x J)
include B in
lemma panel_sales :∃ n:ℕ→ℕ, P.HandleWith x c r Y n:= by
 let A (i j:ℕ)(k:L): H:= (e i) (E ((w i).toNNReal) (P.shard x k (c j) (r j)))
 let T' (i:ℕ)(k:L): H:= ζ k • (e i) ω
 let W(i j:ℕ):= ∀ k:L,‖A i j k-T' i k‖ ≤ P.macroStep i
 have hp(i:ℕ):∀ᶠ j:ℕ in atTop, W i j:= by
    apply eventually_all.mpr; intro k
    let v:=(w i).toNNReal; have hv:0<v:= Real.toNNReal_pos.mpr ((Y i).real_width_pos P 3)
    have he: Tendsto (fun j:ℕ=> A i j k) atTop (𝓝 (T' i k)):=by
       have he:Tendsto (fun j=> A i j k) atTop (𝓝 ((e i) (ζ k • ω))):=((e i).continuous.tendsto _).comp (thin_front_shard_tendsto k B (fun _=>v) (thin_compare_dew B hv _ (Eventually.of_forall fun _=>le_refl v)))
       rw [map_smul] at he; exact he
    exact ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually (ge_mem_nhds (P.macroStep_pos i)))
 obtain ⟨n,g,q⟩:= choose_handle (fun i=> (B.launch.smaller.tendsto_atTop.eventually (eventually_ge_atTop (Y i).s)).and ((B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and (hp i)))
 exact ⟨n,g,fun i=> (q i).1, fun i=>(q i).2.1, fun i=>(q i).2.2⟩
lemma cradlePositive {j:Axis}{H':Hilbert}(Y':OS.Semigroup H' j)(x:H') : Positive Y' (fun t:ℝ=>Y'.E t.toNNReal x):= by
 intro s t p q; rw [←ContinuousLinearMap.comp_apply,←Y'.time,show (t-s).toNNReal+s.toNNReal=t.toNNReal from ?_]; apply NNReal.eq; rw [NNReal.coe_add]; simp [p.le,sub_nonneg.mpr q,p.le.trans q]
abbrev cradleH (A:P.Apron)(F:P.birthF 3 A.s A.F)(t:ℝ):H:= E t.toNNReal (P.thinOrigin x A F)
abbrev cradleG (A:P.Apron)(F:P.birthF 3 A.s A.F)(t:ℝ):G:= (R).E t.toNNReal (Ξ (P.thinOrigin x A F))
lemma cradle_bank (A:P.Apron)(F:P.birthF 3 A.s A.F)(t:ℝ) : P.cradleG x A F t= Ξ (P.cradleH x A F t):= (P.bankHeat ..).symm
noncomputable def route_before (V:V!) (t:ℝ): H:= ζ Z • V 3 [] t
variable (T':P.HandleWith x c r Y n)
variable {V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}(U:P.Radiates x Y V)
include T'
lemma stitch_clear (i:ℕ) : P.birthF 3 (Q Z i).s (Q Z i).F := (P.stitch_certificate Z (r (n i)) x (T'.already i)).choose
include U
lemma stitch_profile {t:ℝ}(w':0<t) (p:∀ i, P.birthF 3 (Q Z i).s (Q Z i).F): Tendsto (fun i=> P.cradleH x (Q Z i) (p i) t) atTop (𝓝 (P.route_before Z x V t)):=by
 let F(i:ℕ):= P.thinOrigin x (Q Z i) (p i); let Y'(i:ℕ):=(e i) ω
 have ht:Tendsto (fun i=> F i- (ζ Z) • Y' i) atTop (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun _=> norm_nonneg _) (fun i=>?_) (P.macroStep_zero)
    have hx:F i = (e i) (E ((w i).toNNReal) (P.shard x Z (c (n i)) (r (n i)))):= (P.stitch_certificate Z (r (n i)) x (T'.already i)).choose_spec
    rw [hx]; exact T'.price i Z
 let Q':= E (t.toNNReal)
 have he:Tendsto (fun i=> Q' (Y' i)) atTop (𝓝 (V 3 [] t)):=by
    -- even simpler: t is shifted argument of beamRaw, goes slightly *up*!
    let g(i:ℕ):=t+w i; have hg:Tendsto g atTop (𝓝 t):=by simpa only [add_zero] using (U.slender 3).const_add t
    refine (U.vary 3 [] w' hg).congr fun i=> ?_
    change E ((g i - w i).toNNReal) (Y' i)=Q' (Y' i); rw [show g i - w i=t from add_sub_cancel_right ..]
 have hx:Tendsto (fun i=> Q' (F i-ζ Z • Y' i) + ζ Z • Q' (Y' i)) atTop (𝓝 (P.route_before Z x V t)):=by
    have hy:= ((Q'.continuous.tendsto _).comp ht).add (he.const_smul (ζ Z))
    rw [map_zero,zero_add] at hy; exact hy
 exact hx.congr fun i=> (by rw [map_sub,map_smul,sub_add_cancel])
omit T' in
lemma routeBefore_pos : Positive (S) (P.route_before Z x V):= by
 intro s t p q; unfold route_before; rw [map_smul]; exact congrArg (ζ Z • ·) (U.choir 3 [] p q)
omit T' U in
lemma operates_from (L':ℕ→ P.Apron)(V':ℝ→ H)(h:∀ i,P.birthF 3 (L' i).s (L' i).F)
    (u:∀ t:ℝ,t>0→ Tendsto (fun i=> P.cradleH x (L' i) (h i) t) atTop (𝓝 (V' t))) :
    Operates (f:=atTop) (S) V' (fun i=> P.cradleH x (L' i) (h i)) ∧
    Operates (f:=atTop) (R) (fun t=> Ξ (V' t)) (fun i=> P.cradleG x (L' i) (h i)):=by
 exact ⟨⟨u,fun s t p=> Eventually.of_forall fun i=> Positive.moves (S) _ (cradlePositive _ _) p t⟩,
   fun t p=> ((((Ξ).continuous.tendsto _).comp (u t p)).congr (fun i=> (P.cradle_bank x ..).symm)),
   fun s t p=> Eventually.of_forall fun i=> Positive.moves (R) _ (cradlePositive _ _) p t⟩
lemma before_works (z:∀ i,P.birthF 3 (Q Z i).s (Q Z i).F): Operates (f:=atTop) (S) (P.route_before Z x V) (fun i=> P.cradleH x (Q Z i) (z i)) ∧
    Operates (f:=atTop) (R) (P.route_y x V Z) (fun i=> P.cradleG x (Q Z i) (z i)):=by
 rw [show P.route_y x V Z=(fun t=> Ξ (P.route_before Z x V t)) from funext (fun t=> Eq.symm (map_smul (Ξ) (ζ Z) _))]; exact P.operates_from x _ _ z (fun _ p=> P.stitch_profile Z x c r Y n T' U p z)
include B
lemma stitch_thin(j:Axis): Tendsto (fun i=> (Q Z i).realWidth P j) atTop (𝓝 0):=by
 simp_rw [P.stitch_width j Z (r (n _)) (T'.already _)]; have ht:= ((U.slender j).add ((U.slender 3).const_mul 3)).add ((limit_width B.launch j).comp T'.fast.tendsto_atTop)
 rw [mul_zero,zero_add,zero_add] at ht; exact ht
omit B T' U
structure FusionFleet (T':P.HandleWith x c r Y n) (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)): Prop where
    high : StrictMono (fun i=> c (n i))
    paper (Z:Lead.Clan)(i:ℕ): P.Sensor (Q Z i) Z.2
    thin(Z:Lead.Clan)(j:Axis) : Tendsto (fun i=> (Q Z i).realWidth P j) atTop (𝓝 0)
    profile (Z:Lead.Clan): Positive (S) (P.route_before Z x V)
    receipt(Z:Lead.Clan) : Operates (f:=atTop) (S) (P.route_before Z x V) (fun i=> P.cradleH x (Q Z i) (P.stitch_clear Z x c r Y n T' i)) ∧
      Operates (f:=atTop) (R) (P.route_y x V Z) (fun i=> P.cradleG x (Q Z i) (P.stitch_clear Z x c r Y n T' i))
include B T' U
lemma makeFleet (u:∀ i,PureGauge K (Y i).F): P.FusionFleet x c r Y n T' V:=
 ⟨B.launch.smaller.comp T'.fast,fun Z i=> P.stitch_senses Z _ (u i) (T'.distinct i), fun Z j=> P.stitch_thin Z x c r Y n B T' U j, fun Z=> P.routeBefore_pos Z x Y U, fun Z=> P.before_works Z x c r Y n T' U _⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.makeFleet
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.panel_sales
