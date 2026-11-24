import YM.CF.Paxos.Trio
import YM.CF.Fixed.Mantle
/-! Global address retaining every flag. Useful ONLY with paying small.
Guard derivatives on masked fields are not free; here `FleetS` included
pointwise mask, but stationary on `pressQ` directions relevant to that flag set.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson SU Scree Skye Fock Lat Cube MeasureTheory Vow RG
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{x:ℝ}(P:BudgetPoint)(D:Support (More n))
local notation "F" => Pane n
local notation "M" => More n
open Rue Spire
lemma completeV(V W:F)(h:Agrees ((Finset.univ:Support M) : Set (Site M)) V W):V=W:=funext fun i=>h i (mem_univ _) (mem_univ _)
lemma fleetC (V:F)(g:Site (More n) → group.El):FleetS P.threshold (gauge g V)↔ FleetS P.threshold V:=by unfold FleetS; simp_rw [face_gauge,group.chord_conj]
lemma flags_mate (V:F)(g:Site (More n)→ group.El): flags P.threshold (Lattice.gauge g V)= flags P.threshold V:=by ext i; rw [flags_spec,flags_spec]; simp_rw [face_gauge,group.chord_conj]
lemma toyFleet:IsOpen {U:Pane n|FleetS P.threshold U}:=by
  have he:{U:Pane n|FleetS P.threshold U}= ⋂ (i:Face (Per (More n))), {V |group.chord (faceValue V i)≠ P.threshold}:=by ext; simp [FleetS]
  rw [he]; refine isOpen_iInter_of_finite fun i=> isOpen_ne_fun (by unfold faceValue; fun_prop) continuous_const
def deck_F:= {U:F|FleetS P.threshold U}∩{U:F|flags P.threshold U=D}

local notation "A"=> deck_F P D
lemma meas_F:MeasurableSet A:=(toyFleet (n:=n) P).measurableSet.inter (flags_measurable_eq P.threshold D)
lemma deck_gauge (V:F)(g) :gauge g V∈A ↔ V∈A:= and_congr (fleetC P V g) (by change flags _ _=_ ↔ _;rw [flags_mate];rfl)
lemma deck_empty (V:F): V∈deck_F P (∅:Support M) ↔pingS P.threshold Finset.univ V:=by
  constructor
  · intro h; apply (shoreK _ V h.1 Finset.univ).1; unfold Healthy; rw [show flags _ _=∅ from h.2]; simp
  intro h; refine ⟨fun i=>((h i (fun v=>Finset.disjoint_left.mp v (mem_univ _) (WilsonStartup.anchor_visit ..)))).ne,?_ ⟩; change flags _ V=∅; simpa [Healthy,Finset.disjoint_iff_inter_eq_empty] using (ping_le h)
lemma deck_budget (V:F)(v:V∈A) : pingS P.threshold (univ\D) V:= (shoreK _ V v.1 _).1 (by unfold Healthy; rw [show flags _ _ = D from v.2]; exact Finset.disjoint_left.mpr (fun _ p=> (mem_sdiff.mp p).2))
-- Key: either face outside D receives strict tests, or all touched sites are in D, where frozen EXACT, not approximate.
lemma unmoved_F (V:F) (S:Support M)(W:tangD n)(f:WilsonStartup.Cell M)(p:touched f⊆ S): faceValue (pressQ P S V W) f=faceValue V f:=by
  apply WilsonStartup.face_local f; intro i z w; have hp: ¬Disjoint (ends i) (halo (5*P.B) S):=fun h=> Finset.disjoint_left.mp h (mem_insert_self ..) (halo_subset _ _ (p z)); have ht:i∉ Rill.unrest S P.B:= fun p=> hp ((mem_filter.mp p).2); unfold pressQ Forge.gyrate increment Function.comp; dsimp only; rw [Forge.steadyB,if_neg ht]; simp
lemma deck_still (V:F)(S:Support M)(v:pingS P.threshold (univ\D) V)(g:D ⊆ S)(y:tangD n)(u:pingS P.threshold (univ\D) (pressQ P S V y)) : pressQ P S V y ∈ A ↔ V∈A :=by
  let T:=univ\D; let U(x:tangD n):= pressQ P S V x
  have h(i)(h:Disjoint T (touched i)): faceValue (U y) i=faceValue V i:= unmoved_F P V S y _ fun k w=> g (Classical.byContradiction (fun p=> Finset.disjoint_left.mp h (mem_sdiff.mpr ⟨mem_univ _,p⟩) w))
  have ht(i:Face (Per M)):(P.threshold< group.chord (faceValue (U y) i)↔ P.threshold< group.chord (faceValue V i)) ∧ (group.chord (faceValue (U y) i) ≠ P.threshold ↔ group.chord (faceValue V i)≠P.threshold):=by
     by_cases k:Disjoint T (touched i); rw [h i k]; simp
     have hx:=v i k; have hu: group.chord (faceValue (U y) i) < P.threshold:= u i k; exact ⟨iff_of_false hu.asymm hx.asymm, iff_of_true hu.ne hx.ne⟩
  have hv:flags P.threshold (U y)=flags P.threshold V:=by ext k; rw [flags_spec,flags_spec]; simp_rw [(ht _).1]
  change (FleetS P.threshold (U y)∧ flags P.threshold (U y)=D)↔ (FleetS P.threshold V∧ flags P.threshold V=D); rw [hv]; exact and_congr (show FleetS P.threshold (U y) ↔ FleetS P.threshold V from forall_congr' fun i=> (ht i).2) (Iff.rfl)
lemma deck_constant (V:F)(S:Support M)(v:pingS P.threshold (univ\D) V)(g:D ⊆ S) :∀ᶠ y:tangD n in 𝓝 0, pressQ P S V y∈A ↔ V∈A:=by
  let T:= univ\D; let U(x:tangD n):= pressQ P S V x; have hp:ContinuousAt U 0:= ((Forge.stickU (Rill.unrest S P.B) V).comp (continuous_id.const_smul P.threshold)).continuousAt; have he:U 0=V:=by unfold U pressQ; rw [smul_zero]; exact Forge.born ..
  have hK: ∀ᶠ x:tangD n in 𝓝 0, pingS P.threshold T (U x) := by
    apply Filter.Tendsto.eventually (f:=U) hp (p:=fun a=>pingS P.threshold T a); rw [he]
    exact (ping_o (G:=group) (S:=More n)).mem_nhds v
  exact hK.mono fun y u=> deck_still P D V S v g y u
lemma deck_work (s:Sweep n) (U:F): flashA s U∈ deck_F P (Salt.actY s D) ↔ U∈ A:=by
  have hl:FleetS P.threshold (flashA s U) → FleetS P.threshold U := fun v => by
    have hp:= Ione.skew_V s⁻¹ (flashA s U) P.threshold v; rw [Skye.revB] at hp; exact hp
  have hg:FleetS P.threshold U → FleetS P.threshold (flashA s U):= Ione.skew_V s U P.threshold
  refine and_congr ⟨hl,hg⟩ ?_
  change flags P.threshold (flashA s U)= Salt.actY s D ↔ flags P.threshold U=D; rw [flagsA]; exact (Finset.map_injective _).eq_iff
abbrev hours(x:Support M)(f:Copy n)(V:Orbit n):Cipher n:= ((Prod.fst ⁻¹' deck_F P x).indicator f V)
lemma unveil_F (Y:Copy n)(V:Orbit n)(v:V.1∈A): hours P D Y V=Y V:= Set.indicator_of_mem (show V∈_ from v) _
lemma shut_F (Y:Copy n)(V:Orbit n)(v:V.1∉A): hours P D Y V=0:= Set.indicator_of_notMem (show V∉_ from v) _
lemma deck_keep(Q:Copy n)(Z:ℝ)(u:Medal P univ D Q Z x): Medal P univ D (hours P D Q) Z x:=by
  obtain ⟨H,b,hb,v,w⟩:=u; refine ⟨⟨fun U V p l=>?_ ,fun U=>?_ , H.keeps.indicator (measurable_fst (meas_F P D)),fun U g=>?_⟩,b,hb,?_,w⟩
  · rw [Prod.ext (completeV _ _ p) (funext fun i=>l (mem_univ i))]
  · by_cases h:U.1∈ A; rw [unveil_F _ _ _ _ h]; exact H.lit _; rw [shut_F _ _ _ _ h]; exact Pastry.Flour.trivial
  · let W:Orbit n:= (gauge g U.1,threadG g U.2); change hours P D Q W= _; by_cases h: U.1∈ A
    · rw [unveil_F P D Q U h,unveil_F P D Q W ((deck_gauge P D _ g).2 h)]; exact H.gaugeX _ _
    rw [shut_F P D Q U h, shut_F P D Q W (mt (deck_gauge P D _ g).1 h),map_zero]
  intro U k S p
  by_cases h:U.1∈ A
  · apply (v U k p).germ; filter_upwards [deck_constant P D U.1 S k p] with y hy; exact (congrArg Subtype.val (unveil_F P D Q (pressQ P S U.1 y,U.2) (hy.2 h))).symm
  apply Rue.zero_s _ hb; filter_upwards [deck_constant P D U.1 S k p] with y hy; exact shut_F P D Q (pressQ P S U.1 y,U.2) (mt hy.1 h) -- maybe `.val`
lemma deck_sure(Q:Copy n) : Firm P univ D (hours P D Q):=⟨fun h=>False.elim (h (subset_univ _)),fun V v=> (le_of_eq (show flags _ V.1=D from (of_not_not (fun h:V.1∉A=> v (shut_F _ _ _ _ h)) : V.1∈A).2).symm)⟩
end YM.CF.Fixed.Voltage
