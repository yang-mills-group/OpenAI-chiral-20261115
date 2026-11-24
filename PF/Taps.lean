import PF.Gating
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

-- Physical gating on a single LP satellite
namespace PureForce
open Lattice
variable {N : Side}
local notation "𝒢" => SU.group
structure Staple (N : Side) (o : Skye.Seat N) where
  face : Lattice.Face (Per (More N))
  path : Lattice.Walk
  endsAt : Lattice.stop o path = face.1

/-- Express the adjoint by actually conjugating the face loop at anchor o. -/
def bud {o : Skye.Seat N}(b: Staple N o)(U:Pane N) := let V:=Lattice.travel U o b.path
                                         (𝒢).curvature (V*Lattice.faceValue U b.face*V⁻¹)
lemma bud_eq {o:Skye.Seat N}(b: Staple N o)(U:Pane N): bud b U =
    (𝒢).adjoint (Lattice.travel U o b.path) ((𝒢).curvature (Lattice.faceValue U b.face)) := Gauge.curvature_conjugate .. -- notation .proj
lemma budNorm {o:Skye.Seat N}(b: Staple N o)(U:Pane N): ‖bud b U‖ ≤ 2:= by
  rw [bud_eq,Gauge.norm_adjoint]; exact (Gauge.curvature_norm ..).trans (Gauge.chord_le_two ..)
lemma budCont {o:Skye.Seat N}(b: Staple N o):Continuous (bud b):= by
  unfold bud faceValue; dsimp
  apply Gauge.continuous_curvature (𝒢) |>.comp
  fun_prop
lemma budCov {o:Skye.Seat N}(b: Staple N o)(U:Pane N)(g:Skye.Seat N → SU.E):
    bud b (Lattice.gauge g U)= (Gauge.adjoint (𝒢) (g o)) (bud b U) := by
  unfold bud; rw [travel_gauge,face_gauge,b.endsAt]; dsimp only
  rw [← Gauge.curvature_conjugate]; apply congrArg (Gauge.curvature (𝒢)); group

def Fits (S:Support (More N)) {o:Skye.Seat N}(b: Staple N o):Prop:=
  (∀ x∈Lattice.visits o b.path,x∈S) ∧ RG.touched b.face ⊆ S
lemma budHere (S:Support (More N)){o:Skye.Seat N}(b: Staple N o)(v:Fits S b): PatchOnly S (bud b):= by
  intro U V h
  have he: Lattice.travel U o b.path=Lattice.travel V o b.path:= travel_local o b.path _ _ (fun i l t=>h i (v.1 _ l) (v.1 _ t))
  unfold bud; rw [he, show Lattice.faceValue U b.face=Lattice.faceValue V b.face from WilsonStartup.face_local b.face _ _ (fun i a t=> h i (v.2 a) (v.2 t))]

abbrev Tap (N:Side)(o:Skye.Seat N):= List (ℝ × Staple N o)
/-- LP.1 hypotheses in finite-stencil form: after kappa normalization removed
by g at its read, any finite cover linear combination, different layouts ok. Can
use concatenated paths from end (at initial vertex of oriented e) to that
centre and then the smoothed face bases; endpoints included in the paint.
Slots with reversed face order represented by negating the weight. -/
def play {o:Skye.Seat N}(f:Tap N o)(U:Pane N): (𝒢).Color:=
    (f.map fun d=>d.1 • bud d.2 U).sum

def tapCost {o:Skye.Seat N}(f:Tap N o):ℝ:= (f.map fun d=>|d.1|).sum
lemma playNorm {o:Skye.Seat N}(f:Tap N o)(U:Pane N): ‖play f U‖≤ tapCost f *2 := by
  induction (show List (ℝ × Staple N o) from f) with
  | nil=>simp [tapCost,play]
  | cons t f ih=>
    simp only [play,tapCost,List.map_cons,List.sum_cons] at *
    have hz : ‖t.1 • bud t.2 U‖ ≤ |t.1| * 2 := by rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (budNorm ..) (abs_nonneg _)
    exact (norm_add_le ..).trans ((add_le_add hz ih).trans_eq (Eq.symm (add_mul ..)))
lemma playCont {o:Skye.Seat N}(f:Tap N o): Continuous (play f) := by
  induction (show List (ℝ × Staple N o) from f) with
  | nil=>exact continuous_const
  | cons t f ih=>
    change Continuous ((t.1 • bud t.2) + play f)
    exact (Continuous.const_smul (budCont _) _).add ih
lemma playCov {o:Skye.Seat N}(f:Tap N o)(U:Pane N)(g:Skye.Seat N → SU.E):
    play f (Lattice.gauge g U)=(Gauge.adjoint (𝒢) (g o)) (play f U) := by
  unfold play; rw [map_list_sum,List.map_map]
  apply congrArg List.sum; congr 1; funext d; simp [budCov]
lemma playHere (S:Support (More N)){o:Skye.Seat N}(f:Tap N o)(p:∀ t∈f,Fits S t.2):
    PatchOnly S (play f):= by
  intro U V h
  exact congrArg List.sum <|List.map_congr_left fun t ht=> (congrArg (t.1 • ·) (budHere S t.2 (p _ ht) U V h))

lemma pingClean {R: Finset (Skye.Seat N)} {U:Pane N} {t:ℝ} :
    clean t R U ↔ Scree.pingS t R U:= by
  constructor
  · rintro v i p; obtain ⟨x,h,q⟩:= Finset.not_disjoint_iff.mp p; exact v i x h q
  exact fun h i x v p=> h i (Finset.not_disjoint_iff.mpr ⟨x,v,p⟩)

/-- LP.2 coefficient at **shifted** U (argument is U_z), with the actual color
metric; χ now the exact pingS from the project. Doesn't include radial odd
weight $w^c_m$. Allows also negating at each root with that weight. -/
def watch {o:Skye.Seat N}(E:ℝ)(f:Tap N o)(χ:Support (More N))(τ:ℝ)(ξ:(𝒢).Color):Pane N→ℂ:=
  {U:Pane N| Scree.pingS τ χ U}.indicator fun U=> (↑((Fintype.card (𝒢).ColorIndex/E) * inner ℝ ξ (play f U)):ℂ)
-- leading bound
lemma watchNorm {o:Skye.Seat N}(E:ℝ)(v:0<E)(f:Tap N o)(χ:Support (More N))(τ:ℝ)(ξ:(𝒢).Color)(p:‖ξ‖≤1)(U:Pane N) :
    ‖watch E f χ τ ξ U‖ ≤ Fintype.card (𝒢).ColorIndex/E * (tapCost f*2):= by
  let B:ℝ:= Fintype.card (𝒢).ColorIndex/E
  have hB: 0 ≤ B:= by dsimp [B]; positivity
  have he: 0 ≤ B*(tapCost f*2):=mul_nonneg hB ((norm_nonneg _).trans (playNorm f U))
  by_cases h:U∈{U:Pane N|Scree.pingS τ χ U}
  · rw [watch,Set.indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_mul,abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm ..).trans ((mul_le_of_le_one_left (norm_nonneg _) p).trans (playNorm ..))) hB
  rw [watch,Set.indicator_of_notMem h,norm_zero]; exact he

lemma watch_env {Θ:Type*}[MeasurableSpace Θ](ξ:Θ→ (𝒢).Color)(m:Measurable ξ)(b:∀ θ, ‖ξ θ‖≤ 1)
    {o:Skye.Seat N}(E:ℝ)(v:0<E)(f:Tap N o)(χ:Support (More N))(τ:ℝ):
    Envelope (fun x:Θ×Pane N=> watch E f χ τ (ξ x.1) x.2) := by
  refine ⟨?_, _,fun x=> watchNorm E v f χ τ (ξ x.1) (b _) x.2⟩
  let X: Set (Θ × Pane N):= Prod.snd ⁻¹' {U | pingS τ χ U}
  let A(x:Θ × Pane N): ℂ:= ↑((Fintype.card (𝒢).ColorIndex/E)*inner ℝ (ξ x.1) (play f x.2))
  have he:(fun x:Θ×Pane N=> watch E f χ τ (ξ x.1) x.2)=X.indicator A := by
    funext x; by_cases t:Scree.pingS τ χ x.2
    · rw [watch,Set.indicator_of_mem (show _ from t), Set.indicator_of_mem (show _ from t)]
    rw [watch,Set.indicator_of_notMem (show _ from t), Set.indicator_of_notMem (show _ from t)]
  rw [he]
  apply Measurable.indicator _ (measurable_snd Scree.ping_o.measurableSet)
  exact Complex.measurable_ofReal.comp (measurable_const.mul (continuous_inner.measurable.comp ((m.comp measurable_fst).prodMk ((playCont f).measurable.comp measurable_snd))))

lemma watch_local {o:Skye.Seat N}(S:Support (More N))(E:ℝ)(f:Tap N o)(a:Skye.Seat N)(r:ℕ)(t:ℝ)(ξ:(𝒢).Color)
    (h:∀ x∈f,Fits S x.2)(tχ:testRegion a r ⊆ S):
    PatchOnly S (watch E f (Lattice.halo r {a}) t ξ):=by
  intro U V v
  have hx:Scree.pingS t (Lattice.halo r {a}) U ↔ Scree.pingS t (Lattice.halo r {a}) V:=
    pingClean.symm.trans ((clean_local (U:=U) (V:=V) (x:=a) (δ:=r) (fun i a b=>v i (tχ a) (tχ b)) _).trans pingClean)
  unfold watch
  by_cases hl: Scree.pingS t (Lattice.halo r {a}) U
  · rw [Set.indicator_of_mem (show _ from hl),Set.indicator_of_mem (show _ from hx.mp hl),show play f U=play f V from playHere S f h _ _ v]
  rw [Set.indicator_of_notMem (show _ from hl),Set.indicator_of_notMem (show _ from mt hx.mpr hl)]

abbrev Angle := Bool × Fin 24
-- true sign means m positive.
def nodes (t:Angle):ℝ := if t.1 then (t.2.val:ℝ)+1 else -((t.2.val:ℝ)+1)
def polarWeight (w:Fin 24→ℝ)(t:Angle):ℂ:= if t.1 then (w t.2:ℝ) else -(w t.2:ℝ)
lemma polar_sum (w:Fin 24→ℝ) : ∑ t:Angle,polarWeight w t=0:=by
  rw [Fintype.sum_prod_type,Fintype.sum_bool]; simp [polarWeight]
lemma bounded_node (t:Angle):|nodes t| ≤ 24:=by
  have he:(t.2.val:ℝ)<24:=by exact_mod_cast t.2.isLt
  have ht:t.2.val+1≤ 24:=by omega
  unfold nodes; split
  · rw [abs_of_nonneg (by positivity)]; exact_mod_cast ht
  rw [abs_neg,abs_of_nonneg (by positivity)]; exact_mod_cast ht

lemma positive_eps {β:ℝ}(h:0<β): 0<rotorEps β:=by unfold rotorEps; positivity

set_option quotPrecheck false
variable (P: Spine)
local notation "Λ" => P.par
local notation "Y" => P.run
local notation "X(" s ")" => hat P.par.R.L P.par.x s
local notation "Θ(" s ")" => ((Y).meter.a s).threshold
local notation "n(" s "," i ")" => side P.run i s
local notation "Cti" => Scree.city
-- receipt for all angular copy integrals at actual epoch with comprehensive h,p cap qualifications. β can be taken beta'_s via subsequent purchase at that s
universe u u'
variable {Q T:Type u}
local notation "Neg" => Bool
include P

theorem tap_epoch : ∀ᶠ s:ℕ in atTop,∀ (i k:ℕ),Pay P.run s i k → ∀ β∈ Set.Icc (X(s)/2) (2*X(s)),
    let n:=side P.run i s;
    ∀ {Q T:Type u} [Fintype Q] [DecidableEq Q] [MeasurableSpace T], ∀ (ν:Measure T) [_p:IsProbabilityMeasure ν],
      ∀ (S:Q→Support (More n))(E:Q → gaugeLink n)(o:Q→Skye.Seat n)(b:Q→ ℕ)
      (neg:Q→Neg)(anchor:Q→Skye.Seat n) (taps:(q:Q)→Tap n (anchor q))
      (dirs:T→Q→ (𝒢).Color) (w:Q→ Fin 24→ℝ)(F:Q→ Evaluation n),
    (∀ q, Measurable (fun θ=>dirs θ q))→ (∀ θ q,‖dirs θ q‖≤1)→(∀ q,∀ x∈taps q,Fits (S q) x.2)→
    (∀ q,testRegion (E q).1 (4*(Λ).J.n+24) ⊆ S q) → (∀ q,testRegion (o q) (b q)⊆ S q)→
    (∀ q,rotorWindow (Λ).J.n (E q)⊆Lattice.halo (b q) {o q}) → Pairwise (Disjoint on S) →
    (∀ q,AtSupport false (S q) (toMark (F q)))→
    -- ask under all the angular directions (e load on each argument).
    let l:=fun θ q j=>rotorLeft (neg q) (nodes j) β (dirs θ q); let r:=fun θ q j=>rotorRight (neg q) (nodes j) β (dirs θ q);
    let watchX:=fun q θ=> watch (rotorEps β) (taps q) (Lattice.halo (b q) {o q}) (Θ(s)/3) (dirs θ q);
    let Y':=fun qs B u=> Function.uncurry (fun θ=> assayShift qs B E (l θ) (r θ) (fun q=>polarWeight (w q)) (fun q U=>watchX q θ U) F (Psi P i k s) u);
    -- any nonempty set of shift options.
    ∀ (layout keep qs:List Q)(q0:Q), q0∈qs→qs.Nodup→ (∀ q∈keep,q∉qs)→
      Integrable (startPrice layout F (Psi P i k s)) (Scree.city n) ∧ (∀ u, Integrable (Y' qs keep u) (ν.prod (Scree.city n))) ∧
      (∀ θ, (∫ x, ∑ u:Q→Angle, Y' qs keep u (θ,x)∂ (Scree.city n))=0) ∧
      denom P i k s ≠ 0 ∧
      Journey.compass P.run i k s (toMark (keptMarks layout F))=
        ((∫ x,startPrice layout F (Psi P i k s) x∂(Scree.city n))+∫ x,(∑ u:Q→Angle,∫ θ,Y' qs keep u (θ,x) ∂ν) ∂(Scree.city n))/denom P i k s ∧
      (∀ q θ U,‖watchX q θ U‖ ≤ Fintype.card (𝒢).ColorIndex/(rotorEps β) * (tapCost (taps q)*2)) ∧
      ∀ θ U key,∀ u:Q→Angle,let a:=fun q=> l θ q (u q);let a':=fun q=> r θ q (u q);
        ∀ L:List Q,L.Nodup→ (∀ q∈L, watchX q θ (oneOffer (E q) (a q) (a' q) U)≠0)→
        let W:=Papal.room P.run s i; let V:=offer L E a a' U;
        W (V,key) = offer L E a a' (W (U,key)) ∧ RG.flags Θ(s) V=RG.flags Θ(s) U ∧ RG.flags (Λ).J.k V=RG.flags (Λ).J.k U ∧
        ∀ (d:Signed)(p:Skye.Seat n), RG.PathData.kept (Λ).K.top.clip Θ(s) p (Lattice.pull d 0 V) ↔ RG.PathData.kept (Λ).K.top.clip Θ(s) p (Lattice.pull d 0 U):=by
  filter_upwards [physical_toggles.{u} P,(turnover (Λ)).eventually_gt_atTop 0] with s he h0 i k hu β hβ n
  intro Q T _ _ _ ν _ S E o b neg m Z δ w F hδ ha h hS hs hr hi hF l r X Y' L ks qs q v H ht
  let φ(q:T):= δ q
  let w0(j:Q):= polarWeight (w j)
  let G':Q→T×Pane n→ℂ:= fun j x=> X j x.1 x.2
  have hβ':0<rotorEps β:= positive_eps ((half_pos h0).trans_le hβ.1)
  have G_loc(j:Q)(θ:T):PatchOnly (S j) (X j θ):= watch_local _ _ _ _ _ _ _ (h j) (hs j)
  have G_env(j:Q): Envelope (G' j):= watch_env (fun θ=>δ θ j) (hδ j) (fun θ=>ha θ j) _ hβ' _ _ _
  have Fq(j:Q): PatchOnly (S j) (F j):=(atSupport_supplies S (hF j)).1
  have FE(j:Q): Envelope (F j):=(atSupport_supplies S (hF j)).2
  have a_here (q:Q): (E q).1 ∈ S q:= hS q (by simp [testRegion,Lattice.halo_spec])
  have hl(q:Q)(u:Angle):Measurable fun θ=>rotorElem (nodes u) β (δ θ q):= (Gauge.lieExp_cont (𝒢)).measurable.comp (Measurable.const_smul (hδ q) (nodes u * rotorEps β))
  have ml(q:Q)(u:Angle): Measurable fun θ=> l θ q u:=by dsimp only [l,rotorLeft]; split_ifs; exact measurable_const; exact hl ..
  have mr(q:Q)(u:Angle): Measurable fun θ=> r θ q u:=by dsimp only [r,rotorRight]; split_ifs; exact (hl ..).inv; exact measurable_const
  have hp:=actualBill P i k s hu ks F FE
  obtain ⟨hW,hw⟩:= angular_cancel S ν qs ks E l r w0 G' F (Psi P i k s) q v H (fun q=>polar_sum (w q)) a_here hi ht Fq G_loc G_env ml mr hp.1
  obtain ⟨hn,hx,hz⟩:=actualBill P i k s hu L F FE
  refine ⟨hn,hW,?_,hx,?_,fun q θ U=>watchNorm _ hβ' _ _ _ _ (ha θ q) _,?_⟩
  · intro θ; obtain ⟨hm,hq⟩:= cancelOffer S qs ks E (l θ) (r θ) w0 (fun q=>X q θ) F (Psi P i k s) q v H (fun q=>polar_sum (w q)) a_here hi ht Fq
      (fun j=> ⟨G_loc j θ, (show Envelope (fun x : Pane n=>G' j (θ,x)) from Env.along (g:=fun x : Pane n=> (θ,x)) (G_env j) (measurable_const.prodMk measurable_id))⟩) hp.1
    refine Eq.trans (integral_finsetSum _ (fun u _=>hm u)) ?_; exact hq
  · refine hz.trans ?_; rw [show (∫ x:Orbit n,(∑ u:Q→Angle,∫ θ,Y' qs ks u (θ,x)∂ν)∂Scree.city n)=(0:ℂ) from hw,add_zero]
  intro θ U key u a a' L hn hχ
  let Q':= {q : Q//q∈L}
  let v' : Q'→ Q:=Subtype.val
  let c:=S ∘ v'; let e:=E ∘ v'; let A:=a ∘ v'; let B:=a' ∘ v'
  have hp': L.attach.Nodup := List.nodup_attach.mpr hn
  have hi': Pairwise (Disjoint on c):= fun x y h=> hi (fun hx:(x:Q)=(y:Q)=>h (Subtype.ext hx))
  have he'(V:Pane n): offer L.attach e A B V=offer L E a a' V:=by
    have hv(f:Q→SU.E)(i:gaugeLink n):offerSide L.attach e (f ∘ v') i =offerSide L E f i:=by
      exact congrArg List.prod (List.attach_map_val (f:=fun q=> atomAt (E q) (f q) i))
    unfold offer; congr 1 <;> exact funext (hv _)
  simp only; simp_rw [←he']
  apply he i β hβ.1 Q' c e (fun q=>nodes (u (v' q))) (δ θ ∘ v') (neg ∘ v') (fun q=>bounded_node _) (fun q=>ha ..) (fun q=>hS _) hi' U key ?_ L.attach hp'
  intro q p x hv
  have τg: oneOffer (E (q:Q)) (a (q:Q)) (a' (q:Q)) U∈ {U|Scree.pingS (Θ(s)/3) (Lattice.halo (b (q:Q)) {o (q:Q)}) U}:= by
    by_contra! hx; exact hχ _ q.property (Set.indicator_of_notMem hx _)
  exact pingClean.mpr τg p x (hr _ hv)

end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

