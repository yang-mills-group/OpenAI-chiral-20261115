import YM.SU5.FiniteGaugeData.Dally.Pimento
/-!
 # Ward estimator, freight.
 -/
noncomputable section
open Metric Filter Function WithLp Set
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
open _root_.YM Dally Gem Leal Leal.Breve Celeritas Land Mist OS OS.Semigroup Flute Apso Mink
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space) (A : Tribe G)
variable {n : ℕ} (u : Fin n → ι) (w : Palette G u)
variable (b : SpaceAxis) (x : Points n) (t s : ℝ)
attribute [local instance] ostensible
local notation "ₜ" => timeAxis
abbrev Job (n : ℕ) := Bool ⊕ (Fin n × Bool) -- [inl false normal] [inl true vane] [inr (i,true) time] [inr (i,false) space]
abbrev TimeLeak {n : ℕ} (i : Fin n) : Job n:= Sum.inr (i,true)
abbrev TiltLeak {n : ℕ} (i : Fin n) : Job n:= Sum.inr (i,false)
def room : Job n → Points n
  | .inl _ => x
  | .inr (i,q) => if q then Leak x i timeAxis t else Leak x i b.castSucc t
def quay : Job n → Palette G u
  | .inl true => vane G u w b t
  | _ => w
def beam (f : Job n → ℂ) : ℂ := (∑ i : Fin n,
  ((x i ₜ) • (f (TiltLeak i) - f (.inl false)) - (x i b.castSucc) • (f (TimeLeak i) - f (.inl false)))) +
  (f (.inl true)- f (.inl false))
abbrev Buoy(j : Job n) := ticket W G ω A ₜ (room b x t j) u (quay G u w b t j)
lemma ballast : blush W G ω A u w b x t = beam b x (Buoy W G ω A u w b x t) := rfl
lemma beam_c : Continuous (beam b x) := by unfold beam; fun_prop

/- Iterated sampling (outer first eventual, hence *last* limit when thinking
   iterated limits). At order Each, no synchronization of convergence across slots. -/
section
variable {D σ : Type} [DecidableEq D]
def Raster (L : List D) (u : D→ℕ) : Filter (D→ℕ) := match L with
  | [] => pure u
  | i::L => Filter.bind (atTop : Filter ℕ) fun v => Raster L (update u i v)
lemma Raster.sure (L : List D) (u : D→ℕ) : (Raster L u).NeBot := by
  induction L generalizing u with
  | nil => change (pure u : Filter (D → ℕ)).NeBot; infer_instance
  | cons i L ih =>
    apply (frequently_true_iff_neBot _).mp; rw [Raster, frequently_bind]
    exact (Eventually.of_forall fun n => (frequently_true_iff_neBot _).mpr (ih _)).frequently
attribute [local instance] Raster.sure
/- Invitation across *jobs* with one ℓ setting at a time. -/
structure Greeting (P : (σ→ D→ Shrine K)→ Prop) : Prop where
  h (i : D) (S: ℕ→ σ→D→Shrine K) (F:σ→D→ Shrine K) (p : ∀ a j, Weaves (fun n=> S n a j) (F a j))
    (q : ∀ a j,j≠i→∀ n,S n a j=F a j) (k:P F) : ∀ᶠ n in atTop,P (S n)
lemma seasonality (P : (σ→D→Shrine K)→Prop) (H : Greeting P) (L : List D) (m : D→ℕ)
    (v : L.Nodup) (F : σ → D → Shrine K) (Q : σ → D → ℕ → Shrine K) (p : P F)
    (r : ∀ j ∈ L, ∀ a, Weaves (Q a j) (F a j))
    (t : ∀ j ∉ L, ∀ a, Q a j (m j) = F a j) :
    ∀ᶠ n in Raster L m, P (fun a j => Q a j (n j)) := by
  induction L generalizing m F with
  | nil =>
    rw [Raster,eventually_pure]
    rwa [show (fun a j => Q a j (m j)) = F from funext fun a=> funext fun j=> t j (by simp) a]
  | cons i L ih =>
    rw [Raster,eventually_bind]
    let S (n:ℕ) (a:σ) := update (F a) i (Q a i n)
    have vi := List.nodup_cons.mp v
    have A a j (z : j≠i)(n) : S n a j= F a j := update_of_ne z _ _
    have B n a : S n a i= Q a i n := update_self ..
    have u a j : Weaves (fun n=> S n a j) (F a j) := by
      by_cases h:j=i
      · subst j; simp_rw [B]; exact r i List.mem_cons_self a
      simp_rw [A a j h]; exact weaves_r _
    filter_upwards [H.h _ _ _ u A p] with n g
    refine ih _ vi.2 _ g ?_ ?_
    · intro j k a; rw [A a j (fun w=> vi.1 (w ▸ k)) n]; exact r j (by simp [k]) a
    intro j k a; by_cases h : j=i
    · subst j; rw [B n a,update_self]
    rw [A a j h n,update_of_ne h, t j (by simp [h,k]) a]
#print axioms seasonality
variable [Fintype σ]
def Seated (x : σ→ D→E4) (L : Axis → List D) (F : σ → D→ Shrine K) := ∀ j a, (L a).Pairwise (Seers (F j) (x j) a)
variable (ν : σ → D → ℕ) (x : σ → D → E4) (L : Axis → List D)
abbrev tariff (F : σ→D→ Shrine K)(j : σ)(a : Axis):= chalk W ω a (ν j) (F j) (x j) (L a)
lemma banquet {φ : (σ → ℂ) → ℝ} (H : Continuous φ) (Y : Set ℝ) (hy : IsOpen Y) (a : Axis) (e : (L a).Nodup) :
    Greeting fun (F: σ→ D→ Shrine K)=> Seated x L F ∧ φ (fun j=> tariff W ω ν x L F j a) ∈ Y := by
  constructor; rintro i S F p q ⟨k,v⟩
  have G (j : σ) : Tendsto (fun n=> tariff W ω ν x L (S n) j a) atTop (𝓝 (tariff W ω ν x L F j a)) :=
    Chalk_lim W ω a (L a) (ν j) (F j) (x j) (k j a) (fun n=> S n j) (p j) i (q j) e
  have δ : Tendsto (fun n j=> tariff W ω ν x L (S n) j a) atTop (𝓝 fun j=> tariff W ω ν x L F j a) :=
    tendsto_pi_nhds.mpr G
  exact (show ∀ᶠ n in atTop, Seated x L (S n) from eventually_all.mpr fun j=> eventually_all.mpr fun a=>
    Seers.along (F j) (fun n=> S n j) (x j) (L a) a (k j a) (p j)).and
      ((H.continuousAt.tendsto.comp δ).eventually (hy.mem_nhds v))
#print axioms banquet
end
section
/- instantiate with Cask and leafP. No $one Hilbert polarization shift`. -/
variable {D : Type} (T : D→Shrine K)
structure Fleet where
  book (w:G.Chip) (k:ℕ): D
  back (w : G.Chip) : Weaves (fun n=> armor W (G.grade w) (T (book w n))) (imprint G A w)
lemma treasury (h : Stamp W G A (Set.range T)) : Nonempty (Fleet W G A T) := by
  have H (w : G.Chip) := h.pay w
  choose f p q using H
  have V w i : ∃ x, armor W (G.grade w) (T x) = f w i := by
    obtain ⟨g,⟨x,rfl⟩,e⟩ := p w i; exact ⟨x,e⟩
  choose x r using V
  exact ⟨⟨x,fun w => by simp_rw [r]; exact q w⟩⟩
variable (E : Fleet W G A T) (M : Axis→ List (Fin n))
abbrev Runway (j : Job n) := (room b x t j).ofLp
abbrev race (j : Job n) := sailK G u (quay G u w b t j)
abbrev honesty (j : Job n) := G.credit (race G u w b t j)
abbrev dctr (j : Job n) := imprint G A ∘ (race G u w b t j)
abbrev assembly (v : Fin n → ℕ) (j : Job n) (i : Fin n) := E.book (race G u w b t j i) (v i)
abbrev dressedR (v : Fin n→ℕ) (j : Job n) := T ∘ assembly W G A u w b t T E v j
def harness (v : Fin n→ℕ) : Prop := Seated (Runway b x t) M (dressedR W G A u w b t T E v)
-- read *actual* prisms from purchased housing only. No inverse energy in this price.
abbrev timber (v : Fin n→ℕ) (j : Job n)(a : Axis) := chorus W ω (dressedR W G A u w b t T E v j) (Runway b x t j) (M a) a
def billW (v : Fin n→ℕ) : ℂ := beam b x (fun j=> timber W G ω A u w b x t T E M v j ₜ)

local notation "Ω" => Buoy W G ω A u w b x t
local notation "α" => honesty G u w b t
local notation "Π₀" => dctr G A u w b t
variable (H : ∀ j, room b x t j∈ debut n M) (hs : saucer (W ₜ) (ω ₜ) = ω ₜ)
include H hs
attribute [local instance] Raster.sure
lemma bait (p : Set ℝ) (q : IsOpen p) (δ : ‖blush W G ω A u w b x t‖∈ p) :
    ∀ᶠ v in Raster (Each n) 0, harness W G A u w b x t T E M v ∧ ‖billW W G ω A u w b x t T E M v‖∈ p := by
  let y := Runway b x t
  let f (F : Job n→ Fin n→ Shrine K) := beam b x fun j=> tariff W ω (α) y M F j ₜ
  have fv : Seated y M (Π₀):= fun j a => (mapsIn (room b x t j) G A _ (M a) a).1 (H j a).2
  have V : blush W G ω A u w b x t=f (Π₀) := by
    rw [ballast]; apply congrArg; exact funext fun j=> honor W G ω A _ _ _ u _ (H j ₜ)
  let R (v : Fin n →ℕ)(j : Job n) := dressed W (α j) (dressedR W G A u w b t T E v j)
  let Q (j : Job n) (i : Fin n) (k : ℕ) := R (fun _=> k) j i
  let B (F : Job n→ Fin n→ Shrine K) := Seated y M F ∧ ‖f F‖∈p
  have d : (M ₜ).Nodup := (H (.inl false) ₜ).1.nodup_iff.mpr (List.nodup_finRange _)
  have h : ∀ᶠ v in Raster (Each n) 0, B (R v) :=
    seasonality B (banquet W ω (α) y M (beam_c b x |>.norm) p q ₜ d) (Each n) 0 (List.nodup_finRange _)
      (Π₀) Q ⟨fv, V ▸ δ⟩ (fun i _ j => E.back _) (fun j a => False.elim (a (List.mem_finRange j)))
  filter_upwards [h] with v hv
  let r : harness W G A u w b x t T E M v := hv.1
  refine ⟨r,?_⟩
  have P : f (R v) = billW W G ω A u w b x t T E M v := congrArg (beam b x)
    (funext fun j => index_k W ω ₜ (M ₜ) (α j) (dressedR W G A u w b t T E v j) _ (r j ₜ) hs)
  rw [← P]; exact hv.2
omit H hs
/- Budget, fits each j including shifted positions inside open Spot. -/
def convoy (y : Points n) (r : ℝ) := ∀ j, room b x t j ∈ ball y r
lemma nice (y : Points n) (r : ℝ) (h : x∈ ball y r) : convoy b x t y r ↔ ∀ i : Fin n,
      Leak x i timeAxis t ∈ ball y r ∧ Leak x i b.castSucc t ∈ ball y r := by
  constructor
  · exact fun e i=> ⟨e (TimeLeak i), e (TiltLeak i)⟩
  intro p j
  rcases j with r|⟨r,v⟩; · exact h
  cases v
  · exact (p r).2
  exact (p r).1
variable (Δ η : ℝ) (τ : ℕ → ℝ) (S : ∀ n, Set (Points n))
def BallastCost (T' : Spot n M Δ η) : Prop :=
  ∀ x ∈ ball T'.center T'.radius, x∈ S n→∀ u : Fin n → ι, ∀ w : Palette G u,
    ∀ b : SpaceAxis, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, convoy b x (τ i) T'.center T'.radius ∧
     ∀ᶠ v in Raster (Each n) 0, harness W G A u w b x (τ i) T E M v ∧
      ‖billW W G ω A u w b x (τ i) T E M v‖ ≤ τ i * ε
include hs
lemma moored (t' : Spot n M Δ η) (hx : ∀ᶠ k in atTop,0<τ k) :
    AtJig W G ω A M Δ η τ S t' ↔ BallastCost W G ω A T E M Δ η τ S t' := by
  constructor <;> intro h x p q u w b ε e
  · filter_upwards [h x p q u w b (ε/2) (half_pos e),hx] with i ⟨v,r⟩ y
    have E' := (nice b x (τ i) t'.center t'.radius p).2 r
    have H j := (t'.savings (ball_subset_closedBall (E' j))).1
    refine ⟨E',?_⟩
    filter_upwards [bait W G ω A u w b x (τ i) T E M H hs (Iio (τ i * ε)) isOpen_Iio
      (v.trans_lt (mul_lt_mul_of_pos_left (half_lt_self e) y))] with v q using ⟨q.1, le_of_lt q.2⟩
  filter_upwards [h x p q u w b ε e] with i ⟨H,C⟩
  refine ⟨?_,(nice b x (τ i) t'.center t'.radius p).1 H⟩
  by_contra! l
  obtain ⟨v,⟨_,f⟩,_,b'⟩ := (C.and (bait W G ω A u w b x (τ i) T E M
    (fun j=> (t'.savings (ball_subset_closedBall (H j))).1) hs (Ioi (τ i* ε)) isOpen_Ioi l)).exists
  exact b'.not_ge f -- args f
structure Quarter (Δ η : ℝ) (τ : ℕ→ℝ) (S : ∀ n, Set (Points n)) : Prop where
 point (n : ℕ)(M : Axis→List (Fin n))(h:(debut n M).Nonempty): ∃ T' : Spot n M Δ η, BallastCost W G ω A T E M Δ η τ S T'
lemma Sensor (hx : ∀ᶠ k in atTop,0<τ k) :
    Rookie W G ω A Δ η τ S ↔ Quarter W G ω A T E Δ η τ S := by
  constructor
  · intro h; exact ⟨fun n M e=> (h.purchase n M e).imp fun q p=>(moored W G ω A T E M hs Δ η τ S q hx).1 p⟩
  intro h; exact ⟨fun n M e=> (h.point n M e).imp fun q p=>(moored W G ω A T E M hs Δ η τ S q hx).2 p⟩
#print axioms Sensor
end
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon.Dai
