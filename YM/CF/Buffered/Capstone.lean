import YM.CF.Buffered.RoostCast
/-!
# Allowed continuations. Allocate the Bᵢ, split a TILE at every direction.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Spire Push.SectorMeasure Ordered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m p v w l B n:Side}

variable (K:Ordered m v p)
local notation "D" => Domain m B
local notation "qM" => GridN m
local notation "I" => Xmind m B
local notation "X" => Pack m B
local notation "S" => Locale v B
local notation "d" => Domain v B
local notation "g" => GridN v

def whole (K:Ordered m v p) (x:Locale v B): Pack m B:= K.coast (Rails.replica _ x)
lemma whole_zero (x:S) : reel 0 (K.fromCube (whole K x))=x := by unfold whole; rw [atCube,reel_zero K.onGrid]
lemma whole_cont : Continuous (whole (B:=B) K) := (coast_cont K).comp (Rails.replica_cont _)

def wholeWater (i:Tor g) (x:X): ℝ:= water m B x.1 (K.pebbles.zone 0 i.val) x.2
def small (i:Tor g)(x:S): ℝ:= wholeWater K i (whole K x)
def permitted (e x:ℝ) : Set (Locale v B) := {u| (∀ i,small (m:=m) K i u ≠ 0) ∧ (∀ i (y:Roost d (Facade.frame i)), tideF (Facade.detail i y u)≤e ∧ SU.group.chord (Facade.detail i y u) ≤ x)}
def secure (e x:ℝ) : Set (Pack m B):= TallyR m B e 0 ∩ Prod.fst ⁻¹' Calm group D x
lemma netv (x:X): net m B 0 x=∏ j:Index m, water m B x.1 j x.2:=by rw [net,top,Wilson.bare]; simp; rfl
lemma whole_s (U:X)(e x:ℝ) : U∈secure e x ↔ ((∀ i,water m B U.1 i U.2≠0) ∧ ∀ i:Face (Per (Domain m B)), tideF (faceValue U.1 i) ≤ e ∧ SU.group.chord (faceValue U.1 i)≤x):=by
 change ((Guard _ _∧ net m B 0 U≠0)∧ U.1∈Calm _ _ _)↔_; rw [flags_s,guard_s,netv,prod_ne_zero_iff]; simp only [mem_univ,true_implies]; rw [forall_and]; tauto
lemma water_continuous (i:Tor g) : Continuous (small (B:=B) K i):= (water_cont m B _).comp (whole_cont K)
lemma water_turn_price {i: Tor g}(x:X)(r t:Rail (Uniform p))(T:Finset Axis):let V:= onPack B (K.ferry r t T) x
 water m B V.1 (K.pebbles.zone r i.val) V.2=water m B x.1 (K.pebbles.zone t (shades T i).val) x.2:=by intro V; unfold V; dsimp only [onPack]; rw [water_turn,ferry_label,flip_empty]
lemma ferry_none (r t:Rail (Uniform p))(u:X): reel r (K.fromCube (onPack B (K.ferry r t ∅) u))=reel t (K.fromCube u) := by rw [ferry_extract,past_empty]
lemma nom_r {i:Tor g}: shades ∅ i=i:=Subtype.ext (funext fun a=>by simp [shades])
lemma water_reads (i: Tor g)(r:Rail (Uniform p))(x:X) : small K i (reel r (K.fromCube x))=water m B x.1 (K.pebbles.zone r i.val) x.2:=by
 let U:= reel r (K.fromCube x); let Z:=onPack B (K.ferry 0 r ∅) x
 have h: reel 0 (K.fromCube Z)=U:=ferry_none ..
 exact (K.same_water _ i ((whole_zero K U).trans h.symm)).trans (by simpa only [nom_r] using water_turn_price K (i:=i) x 0 r ∅)
include K in
lemma price_turn (i:PlaqAxes)(j:Roost d (Facade.frame i)){Y:Type*}(F:E→Y)(p:Sanctum F)(T: Finset Axis)(x:S) : F (Facade.detail i j (past T x))=F (Facade.detail i (shades T j) x):=by
 nth_rw 1 2 [←whole_zero K x]; rw [←ferry_extract B K 0 0 T,Facade.intrinsic,Facade.intrinsic]; exact Facade.shift_price _ _ _ _ _ _ _ p
lemma mist_turn (i: Tor g)(u:S)(T:Finset Axis): small K i (past T u)=small K (shades T i) u:=by
 nth_rw 1 2 [←whole_zero K u]; rw [←ferry_extract B K 0 0 T,water_reads,water_reads]; exact water_turn_price ..
-- permitted stable in any combination of mirrors
lemma turn_permit (e x:ℝ)(u:Locale v B)(T:Finset Axis) : past T u∈permitted K e x↔u∈permitted K e x:=by
 have he {z:Locale v B} (v:z∈permitted K e x): past T z∈permitted K e x:=by
    refine ⟨fun i=>?_,fun i j=>?_⟩
    · rw [mist_turn]; exact v.1 _
    rw [price_turn (K:=K) _ _ _ tide_s, price_turn (K:=K) _ _ _ chord_s]; exact v.2 ..
 constructor; swap; · exact he
 intro q; have hp:= he q; rw [show past T (past T u)=u from ?_] at hp; · exact hp
 apply Prod.ext
 · funext i j; simp only [Rails.past,shades_square]; split_ifs <;> simp
 funext j; simp only [Rails.past,shades_square]
lemma permit_iff (u:X)(e x:ℝ): u∈secure e x ↔ ∀ r:Rail (Uniform p), reel r (K.fromCube u) ∈ permitted K e x:=by
 rw [whole_s]; constructor
 · rintro ⟨l₁,l₂⟩ r; refine ⟨fun i=>?_,fun i j=>?_⟩
   · rw [water_reads]; exact l₁ _
   rw [Facade.intrinsic]; exact l₂ _
 intro h; constructor
 · intro i; obtain ⟨⟨r,z⟩,eq⟩:=K.pebbles.slots.surjective i; change K.pebbles.zone r z.val=i at eq; rw [←eq]; have hp : small K (ofpost ∅ z) (reel r (K.fromCube u))≠0:=(h r).1 _; rw [water_reads] at hp; exact hp
 rintro ⟨y,i⟩; obtain ⟨⟨r,z⟩,eq⟩:=(K.sugar B).slots.surjective y; change (K.sugar B).zone r z.val=y at eq; subst y; have h':= (h r).2 i (ofpost (Facade.frame i) z); rw [Facade.intrinsic] at h'; exact h'
lemma permitted_iff (e x:ℝ)(t:Locale v B) : t∈permitted K e x ↔ whole K t∈secure e x:=by
 rw [permit_iff]; constructor
 · intro p r; unfold whole; rw [atCube,Rails.reeling K.onGrid,turn_permit]; exact p
 intro v; specialize v 0; rwa [whole_zero] at v
lemma allowed_borel (e x:ℝ): MeasurableSet (permitted (B:=B) K e x) := by rw [show permitted (B:=B) K e x=(whole K)⁻¹' secure e x from Set.ext (permitted_iff K e x)]; exact ((tally_meas ..).inter ((calm_m ..).preimage measurable_fst)).preimage (whole_cont K).measurable

section budget
variable {e x d' f f':ℝ} (P:Budget B e d')
include P in
lemma unit_canvas (i:Post (CSide v B))(r:Rail (Uniform p)){y:X}(g':y∈secure e x): ‖K.canvas r i y‖=1:=by
 have hz:= tallyP g'.1; exact grain_unit P.1 hz.1 (show Verified m B margin _ _ {0} from hz.2) (stick_in _ (mem_singleton_self _)) _
variable {c : Phase.Part m B} (Q:Pinning m B) {W: Phase.Scroll m B c}(F:ScaleK f f' W)
def tab (W: Phase.Scroll m B c)(i:Index m)(x:X): ℂ:= ∑ j:Gloss.costG m B, if Q.target j=i then Q.bill W j x else 0
lemma pay_zero (v: Era m): Spire.payZ v 0=0:=by unfold Spire.payZ; cases wageZ v; rfl; exact star_zero _
lemma tab_turn (W:Phase.Scroll m B c)(r t:Rail (Uniform p))(i:Tor g)(u:X)(T:Finset Axis) :let Y:= K.ferry r t T
 tab Q W (K.pebbles.zone r i.val) (onPack B Y u)= Spire.payZ (Gloss.phat Y) (tab Q W (K.pebbles.zone t (shades T i).val) u):=by
 intro Y; let V:= phat Y
 have he(j): ρx V⁻¹ j= Trip.adv Y⁻¹ j:=by rw [← Gloss.κo]; rfl
 have hz z : Trip.adv Y⁻¹ z=K.pebbles.zone r i.val↔ z=K.pebbles.zone t (shades T i).val:=by
    rw [show K.pebbles.zone t (shades T i).val=Trip.adv Y (K.pebbles.zone r i.val) from by unfold Y; rw [ferry_label,flip_empty]]; constructor; · intro h; rw [←h,adv_last]
    intro h; rw [h,adv_back]
 unfold tab; rw [←Equiv.sum_comp (Gloss.eQ B V) (fun i'=> if Q.target i'=_ then Q.bill W i' (onPack _ Y u) else 0),←Gloss.ζ_b, Gloss.pay_m]; apply sum_congr rfl; intro j _; change (if Q.target (Gloss.mot V j)=_ then Q.bill W (Gloss.mot V j) (Gloss.vest B V u) else _)= _
 rw [Q.bill_rotates W V,Q.target_moves,he]; by_cases h:Trip.adv Y⁻¹ (Q.target j)=K.pebbles.zone r i.val
 · rw [if_pos h,if_pos ((hz _).mp h)]
 rw [if_neg h,if_neg (fun p=>h ((hz _).2 p)),pay_zero]
lemma tab_sum (W:Phase.Scroll m B c)(u:X): ∑ i, tab Q W i u= Q.cabin W u:=by unfold tab; rw [sum_comm]; simp [Pinning.cabin]
include F P
lemma pays (i:Index m): ContinuousOn (tab Q W i) (payer m B e):= by refine continuousOn_finsetSum _ fun j _=>?_ ; split <;> first|apply Q.bill_continuousOn F P|apply continuousOn_const
lemma tab_eq (j:Tor g)(r:Rail (Uniform p)){u t:X}(p:u∈payer m B e)(b:t∈payer m B e)(h: reel r (K.fromCube u)=reel r (K.fromCube t)): tab Q W (K.pebbles.zone r j.val) u=tab Q W (K.pebbles.zone r j.val) t:=by
 unfold tab; apply sum_congr rfl; intro i _; split_ifs with e; swap; · rfl
 exact Q.bill_matched F P i u t p b (e.symm ▸ (K.meet r h j).2) (e.symm ▸ (K.meet r h j).1)
lemma tab_bound (i:Index m):∃ v:ℝ, ∀ u∈payer m B e, ‖tab Q W i u‖≤v:=by
 refine ⟨∑ j:Gloss.costG m B, max 0 (Gloss.rip m*W.mint j.2),fun x p=>?_⟩; unfold tab; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_ ; split; · exact (Q.bill_bound F P j p).trans (le_max_right ..)
 rw [norm_zero]; exact le_max_left ..
end budget
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.tab_eq
#print axioms YM.CF.Buffered.Region.permit_iff
