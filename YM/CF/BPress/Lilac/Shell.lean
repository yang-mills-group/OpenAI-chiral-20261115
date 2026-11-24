import YM.CF.BPress.Lilac.Hearth
/-! absolute ($small$) price Π thanks to Pledge.Scope & hum derivative comparison at real $Orbit x0$. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Born Peel.Along
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
variable {H: Sugar.Crew A}{T:GramM N}{X: Sugar.Stage N}{Y:Driver N}{k r:ℕ}{e c d:ℝ}
namespace Stripe
abbrev ClipSize := op_chord.choose
lemma clip_p: 0<ClipSize:= op_chord.choose_spec.1
private abbrev capa (c:ℝ):= sphereRate*c + μH*c+ μH*c*priceTone
abbrev shellQ (c:ℝ):= ClipSize*c
def shadow(r:ℕ)(c:ℝ):= 4*r*c + (r:ℝ)* capa c +shellQ c
lemma caps(c:ℝ)(p:0≤c): 0 ≤ capa c:= by unfold capa μH; positivity [sphereRate_cost.positive]
lemma shadowP {c:ℝ}(b:0≤c)(r:ℕ) : shellQ c ≤ shadow r c:=by unfold shadow; exact le_add_of_nonneg_left (add_nonneg (by positivity) (mul_nonneg (by positivity) (caps _ b))) -- tune
section primary
variable (p:Born A R X Y) (F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)(t:ShortP X H R r) {S:Support (More N)} (U:Grove (Grid.field 4 (More N)) S)(a:S.card≤r)(v:Locale.meets A X.W.M S)(g: Visit A R H)
local notation "κ"=> debts H g.val
local notation "α₀"=> ΓStage F Q (party A R H g)
variable {o: Site (More N)} (w:o∈ S) (h:plan A R o∉ vicinity H g.val)
include t U v a w h
lemma dam (x:Site (More N))(u:x∈ S): Good A R (debts H g.val) 6 (Locale.panel A x) ∧ x∈reachP (Hazel.town A o) (Warm B):=by
 let K:= morning v U a t o w x (halo_subset _ _ u); have hv:=t.μWide; exact ⟨solidarity g h _ K.2, reach_m _ _ (hv.le.trans (by unfold umbra Warm; omega)) K.1⟩ -- tune unfolding
local notation "z"=> chip g.val (plan A R o)
include F in
lemma badge {i:Site (More N)}(b:i∈ S): (H.tape (fU g.val)).color i=chip g.val (plan A R o):=by
 obtain ⟨g0,hp⟩:= dam t U a v g w h i b; let K:= morning v U a t o w i (halo_subset _ _ b); let q:= F.pay _ g.property; let u:=Locale.panel A i; let i0:=Locale.panel A o; let p:=q.licence.grip.settle; have hv: delta u.2 i0.2 ≤ R.L.val:= by
    apply (tail_sep i o).trans; apply (U.lim i b o w).le.trans; have he:=t.μBlock; change X.W.M+(r+fundP X H) ≤ _ at he; omega
 refine (carriedP p (x:=u) (y:=i0) (good_m g0 (by norm_num)) (stem_t (r:=1) (plan A R i) _|>.1 K.2|>.1) hv).trans (steadyP F g h i0 rfl)
include F Q p
lemma climbS (d:0<c): Nougat.Shell S (p.H₁ z).val.X (α₀).val.G (α₀).val.X (shellQ c) ∧ Y.Beta.eval S (α₀) (p.H₁ z) ≤ shadow r c:=by
 let A1:= (α₀); let z0:=z; let B1:=p.H₁ z0; let P:=F.pay _ g.property; let p':= (p.ideal z0).progress; let Q':= P.licence.progress; let x':= fU g.val; let η1:= H.fury R X x'; let η2:= Rosetta z0 A X.W R X.tile
 have hQ(j:Link (More N))(f:j∈ inside S): chord (A1.val.G j) 1≤ c:=by
    let i:= Hazel.town A o; let q:= dam t U a v g w h; obtain ⟨t1,t2⟩:= inside_iff ..|>.1 f; have hp(x:Site (More N))(s:x∈S): x∈ safe A R X.W (debts H g.val):= touched_s.mpr (fun _=> good_m (q x s).1 (by norm_num))
    exact P.licence.grip.uSeat j i ((inside_iff ..).mpr ⟨reach_m _ _ halfway (q _ t1).2, reach_m _ _ halfway (q _ t2).2⟩) ((inside_iff ..).2 ⟨hp _ t1,hp _ t2⟩) (good_m (q _ t1).1 (by norm_num))
 constructor
 · refine ⟨fun i x y=> (op_chord.choose_spec.2 _ _).trans (mul_le_mul_of_nonneg_left (hQ i ((inside_iff ..).2 ⟨x,y⟩)) clip_p.le), fun i l=> ?_⟩ -- Prop hole tune
   obtain ⟨u,v',q,-⟩:= Hazel.Zone.perturbation z Q' p' ((dam t U a v g w h i l).2) (good_m ((dam t U a v g w h i l).1) (by norm_num)) (badge F t U a v g w h l); exact ⟨u,q,(op_chord.choose_spec.2 u 1).trans (mul_le_mul_of_nonneg_left v' clip_p.le)⟩
 change evalC S A1.val B1.val ≤_; have hz:turnTick S A1.val B1.val=0:=by
    refine sum_eq_zero (fun i b=>?_ ); change FateTick (decide (i∈ Picks A R (debts H g.val))) (decide (i∈ Picks A R ∅))= 0; have ht(p:Seal (SiteX A R))(q:Good A R p 6 (Locale.panel A (node i))): i∈Picks A R p ↔ ¬Welkin A (node i):=⟨fun h=>(mem_filter.mp h).2.1,fun h=>mem_filter.mpr ⟨mem_univ _,h,q⟩⟩
                                                                                                                 -- tune
    unfold FateTick; simp only [ht _ (dam t U a v g w h (node i) (mem_filter.mp b).2).1, ht _ (by simp [Good,Hazel.Local] : Good A R ∅ 6 _), ↓reduceIte]
 unfold evalC shadow; rw [hz,add_zero]; refine le_trans (add_le_add ?_ ?_) (le_add_of_nonneg_right (by unfold shellQ; positivity [clip_p] : 0≤ shellQ c)); · refine le_trans (invitation.size d.le (fun i t d=> hQ i ((inside_iff ..).2 ⟨t,d⟩))) ?_; gcongr
 have hv(i:Site (More N))(b:i∈S) : Plain.sun A1.val B1.val i≤capa c:= by
    obtain ⟨u,v⟩:= Hazel.Zone.price z Q' p' ((dam t U a v g w h i b).2) (good_m (dam t U a v g w h i b).1 (by norm_num)) (badge F t U a v g w h b); -- ...
    unfold Plain.sun; -- β decode.Act inherits equal.Tilt
    have ht(x:ℝ)(h:x∈ Set.Icc (0:ℝ) 2) : A1.val.spin false x=η1 x ∧ A1.val.spin true x=primeC η1 x:=sketch_spin _ _ _ _ _ _ P.licence h
    have hf(x:ℝ)(h:x∈ Set.Icc (0:ℝ) 2) : B1.val.spin false x=η2 x ∧ B1.val.spin true x=primeC η2 x:=sketch_spin _ _ _ _ _ _ (p.ideal z0) h
    refine add_le_add (add_le_add u ((supPrice ..).2 fun x t=>?_)) ((supPrice ..).2 fun x t=>?_); · change ‖(A1.val.spin false x i)-(B1.val.spin false x i)‖ ≤ _; rw [(ht x t).1, (hf x t).1]; exact (v x t).1
    change ‖(A1.val.spin true x i)-(B1.val.spin true x i)‖≤_; rw [(ht x t).2,(hf x t).2]; exact (v x t).2
 unfold meetP; rw [add_zero]; refine le_trans (sum_le_sum hv) ?_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr a) (caps c d.le) -- tune
end primary
end Stripe
end YM.CF.BPress.Lilac
