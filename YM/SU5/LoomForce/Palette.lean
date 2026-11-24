import YM.SU5.Hiro.Platters
import YM.CF.Emu.Fez
import YM.SU5.WakeInvestment.DivideList
import YM.SU5.LoomForce.WickG

/-!
# Multi-staff receipt. Route accounting.

Goals include moment (four-copy and higher) against **exact** sector, no separate
curvature or current comparisons substituted. Here color/Slot expansion and
pair tables API on the two types of Mark calls of this stage: always Staff geometry,
including mixed Staff from EmberWind and the pure matter current of WakeInvestment.
Functional ancestors required to get such prices on the Sector of x will use our
very same layout. In particular loans here are *not* announcing any bills against
Gauge vs Matter prediction from these Wake Wick comparisons already.
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
open Function NormedSpace Metric Filter MeasureTheory ProbabilityTheory Fock Analysis Skye
open SU Lat Lattice Laurent Window Reflect Emu Fir Tulip Phase Scroll Spire Peaks Rush Fock
open Ballad Hiro
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ContDiff Matrix MatrixOrder
  Matrix.Norms.L2Operator Classical List
attribute [local instance] opCStarAlgebra

namespace Chain
variable {I J G H : Type*}

def tally [AddMonoid H] (L : List I) (f : I → H) := (L.map f).sum
@[simp] lemma tally_nil [AddMonoid H] (f : I → H) : tally [] f=0 := rfl
lemma tally_more [AddMonoid H] (L : List I) (i : I) (f : I → H) : tally (i::L) f=f i+tally L f := rfl
lemma tally_join [AddMonoid H] (L V : List I) (f : I → H) : tally (L++V) f=tally L f+tally V f := by simp [tally]
lemma tally_same [AddMonoid H] {L : List I} {f g : I → H} (p : ∀ i∈L,f i=g i) : tally L f=tally L g := by
  induction L with
  | nil => rfl
  | cons i L ih => exact congrArg₂ (·+·) (p _ List.mem_cons_self) (ih fun _ h=>p _ (List.mem_cons_of_mem _ h))
lemma tally_remap [AddMonoid H] (L : List I) (f : I→ J) (g : J→ H) : tally (L.map f) g=tally L (fun i=> g (f i)) := by rw [tally,List.map_map]; rfl
lemma tally_deck [AddMonoid H] (L : List I) (f : I → List J) (g : J → H) : tally (L.flatMap f) g=tally L (fun i=> tally (f i) g) := by induction L with|nil=>rfl|cons i L ih=> rw [List.flatMap_cons,tally_join,tally_more,ih]
lemma tally_shift [Semiring H] (h : H) (L : List I) (f : I → H) :
    tally L (fun i => h*f i)=h*tally L f ∧ tally L (fun i => f i*h)=tally L f*h := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [tally_more,ih.1,ih.2,mul_add,add_mul,and_self]
lemma tally_addMap [AddMonoid G] [AddMonoid H] (L : List I) (f : G →+ H) (A : I → G) :
    f (tally L A)=tally L (fun i=> f (A i)) := by induction L with|nil=> exact map_zero f|cons i L ih=> rw [tally_more,map_add,ih,tally_more]
lemma tally_lim [AddMonoid H] [TopologicalSpace H] [ContinuousAdd H] {f : J→I→H} {d : I→ H} {L : List I} {b : Filter J}
    (w : ∀ i∈L,Tendsto (fun j=> f j i) b (𝓝 (d i))) :
    Tendsto (fun j=> tally L (f j)) b (𝓝 (tally L d)) := by
  induction L with
  | nil => exact tendsto_const_nhds
  | cons i L ih => exact (w i List.mem_cons_self).add (ih (fun i t=> w _ (List.mem_cons_of_mem _ t)))
lemma tally_nest [AddCommMonoid H] (L : List I) (V : List G) (f : I → G → H) :
    tally L (fun i=> tally V (f i))=tally V (fun v=> tally L (fun i=> f i v)) := by
  induction L with
  | nil => simp [tally]
  | cons i L ih =>
    rw [tally_more,ih]; clear ih; induction V with
    | nil=> simp
    | cons j V hw=> rw [tally_more,tally_more,add_add_add_comm, hw,tally_more,tally_more]
end Chain

namespace Palette
open Chain
variable {I J G : Type*}
abbrev clan := Lead.Clan
abbrev kol := SU.group.ColorIndex
abbrev Sewer := Option clan -- .none the mixed probe, Some family the pure matter current
structure Leg (I : Type*) where
  i : I
  a : Slot -- creation
  b : Slot -- removal
  field : Option kol
  charge : ℂ
abbrev Route (I : Type*) := List (Leg I)

/-- expand even in multiplicity: no choosing a non-winding copy in the sum. -/
def enter (i : I) : Sewer → List (Leg I)
  | .some x => ((colors x).toList).map fun p=> ⟨i,p,p,none,1⟩
  | .none => (Finset.univ : Finset kol).toList.flatMap fun b=>
      (Finset.univ : Finset Slot).toList.flatMap fun j=> (Finset.univ : Finset Slot).toList.map
        fun k => ⟨i,j,k,some b,colorEntry j k (mug b)⟩
def booths (tag : I → Sewer) : List I → List (Route I)
  | [] => [[]]
  | i::L => (enter i (tag i)).flatMap fun d=> (booths tag L).map (List.cons d)
def shade (L : Route I) := (L.map (·.charge)).prod
def gPage (i : Leg I) : Option (I × kol) := i.field.map fun k=> (i.i,k)
def sPage (i : Leg I) : List (I × Slot × Bool) := [(i.i,i.b,true),(i.i,i.a,false)]
def paperF (L : Route I) := L.filterMap gPage
def paperS (L : Route I) := L.flatMap sPage
abbrev loomZ (I : Type*) := I × Slot × Bool
abbrev loomG (I : Type*) := I × kol
abbrev Chart (I : Type*) := I → I → ℂ
abbrev quoteSpin (L : Route I) (Z : Chart (loomZ I)) := shade L * runes Z (paperS L)
def quote (L : Route I) (Z : Chart (loomZ I)) (W : Chart (loomG I)) :=
    quoteSpin L Z * WickG.read W (paperF L)
def quoted (tag : I → Sewer) (L : List I) (Z : Chart (loomZ I)) (W : Chart (loomG I)) :=
  tally (booths tag L) (fun r=> quote r Z W)

variable {i : Leg I} {t : Sewer} {a : I}
lemma enter_node (h : i∈ enter a t) : i.i=a := by
  unfold enter at h; split at h
  · obtain ⟨j,h,rfl⟩:=List.mem_map.mp h; rfl
  obtain ⟨l,_,j,v,w⟩ := (show ∃ l:kol, l∈ (Finset.univ : Finset kol).toList ∧ ∃ j:Slot,
      j∈ (Finset.univ: Finset Slot).toList ∧ _ from by
    obtain ⟨l,u,p⟩ := List.mem_flatMap.mp h; obtain ⟨j,v,w⟩:= List.mem_flatMap.mp p; exact ⟨l,u,j,v,w⟩)
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp w; rfl

variable {L : Route I} {V : List I} {tag : I → Sewer}
lemma booth_node (h : L∈ booths tag V) : L.map Leg.i=V := by
  induction V generalizing L with
  | nil=>rw [List.mem_singleton.mp h]; rfl
  | cons i V ih=>
    obtain ⟨d,v,u⟩:= List.mem_flatMap.mp h
    obtain ⟨L,p,rfl⟩:= List.mem_map.mp u
    rw [List.map_cons, ih p, enter_node v]

lemma shade_more (e : Leg I) (L : Route I) : shade (e::L) = e.charge*shade L := rfl
lemma paperF_more (e : Leg I) (L : Route I) :
    paperF (e::L)=(gPage e).toList ++ paperF L := by simp [paperF]; cases h:gPage e <;> simp [h]
lemma paperF_length (L : Route I) : (paperF L).length ≤ L.length := List.length_filterMap_le ..
lemma paperF_roster (L : Route I) : (paperF L).map Prod.fst <+ L.map Leg.i := by
  induction L with
  | nil => simp [paperF]
  | cons i L ih=>
    rw [paperF_more]; cases h:i.field <;> first
      | simpa [gPage,h] using ih.cons (i.i)
      | simpa [gPage,h] using ih.cons_cons (i.i)
lemma paperS_assign (L : Route I) {i : loomZ I} (h : i∈paperS L) : i.1∈ L.map Leg.i := by
  obtain ⟨l,v,q⟩:= List.mem_flatMap.mp h; have ht:= List.mem_map_of_mem (f:=Leg.i) v
  rcases List.mem_cons.mp q with r|r; · rw [r]; exact ht
  rw [List.mem_singleton.mp r]; exact ht

lemma attend_spin {P : Filter J} {Z : Chart (loomZ I)} {Y : J → Chart (loomZ I)}
    (d : ∀ i j,Tendsto (fun n => Y n i j) P (𝓝 (Z i j))) (L : Route I) :
    Tendsto (fun n => quoteSpin L (Y n)) P (𝓝 (quoteSpin L Z)) := by
  -- variation of Emu.offer_v to this filter
  apply Tendsto.const_mul
  let X:= loomZ I
  have he(W: List (X × X)): Tendsto (fun m=> (W.map fun v=> Y m v.1 v.2).prod) P
      (𝓝 ((W.map fun v=> Z v.1 v.2).prod)):=by
    induction W with|nil=> exact tendsto_const_nhds|cons i t ih=> exact (d i.1 i.2).mul ih
  have h (W : Cl X) : Tendsto (fun m=>spinC (Y m) W) P (𝓝 (spinC Z W)) := by
    unfold spinC; split_ifs
    exact (he _).const_mul _
    exact tendsto_const_nhds
  exact tally_lim (L:=claps (paperS L)) (f:=fun n=> spinC (Y n)) (d:=spinC Z) (fun i _=>h i)


-- portable to different I
noncomputable def reLeg (g : I→ J) (i : Leg I) : Leg J := ⟨g i.i,i.a,i.b,i.field,i.charge⟩
abbrev gPose (g : I→ J) : loomG I → loomG J := Prod.map g id
abbrev sPose (g : I→ J) : loomZ I → loomZ J := Prod.map g id
private lemma enter_slide (t : Sewer) (g : I→ J) (i : I) : enter (g i) t=(enter i t).map (reLeg g) := by
  cases t <;> (simp only [enter,List.map_flatMap,List.map_map]; rfl)

lemma booths_map (tag : J → Sewer) (L : List I) (g : I → J) :
    booths tag (L.map g)=(booths (tag ∘ g) L).map (fun r=> r.map (reLeg g)) := by
  induction L with
  | nil=> rfl
  | cons i L ih=> rw [List.map_cons,booths, ih, booths, List.map_flatMap, enter_slide _ g i,
      List.flatMap_map]; congr 1; ext1 u; change List.map _ (List.map _ _) = List.map _ ((booths _ L).map _); rw [List.map_map,List.map_map]; rfl

lemma shapeF (L : Route I) (g : I → J) :
    paperF (L.map (reLeg g)) = (paperF L).map (gPose g) := by
  induction L with
  | nil=>rfl
  | cons u L ih=>
    rw [List.map_cons,paperF_more,paperF_more,List.map_append,ih]; cases h:u.field <;> simp [gPage,reLeg,h,gPose]
lemma shapeS (L : Route I) (g : I → J) :
    paperS (L.map (reLeg g)) = (paperS L).map (sPose g) := by
  induction L with
  | nil=> rfl
  | cons i L ih=>
    change sPage (reLeg g i)++paperS (L.map _)=(sPage i++paperS L).map _
    rw [List.map_append,ih]; rfl
lemma quote_map (L : Route I) (g : I → J) (Z : Chart (loomZ J)) (Y : Chart (loomG J)) :
    quote (L.map (reLeg g)) Z Y=quote L (fun i j=> Z (sPose g i) (sPose g j))
        (fun i j=> Y (gPose g i) (gPose g j)) := by
  unfold quote quoteSpin
  rw [shapeS, shapeF, WakeInvestment.rune_map (fun i j => Z (sPose g i) (sPose g j))
        (paperS L) _ Z (fun _ _=> rfl), WickG.read_map, shade,List.map_map]; rfl
lemma quote_big (tag : J → Sewer) (L : List I) (g : I → J) (Z : Chart (loomZ J)) (Y : Chart (loomG J)) :
    quoted tag (L.map g) Z Y = quoted (tag∘g) L (fun i j=> Z (sPose g i) (sPose g j))
        (fun i j=> Y (gPose g i) (gPose g j)) := by
  unfold quoted; rw [booths_map,tally_remap]; simp_rw [quote_map]

lemma attend_quoted {P : Filter J} {Z : Chart (loomZ I)} {W : Chart (loomG I)}
    {ZT : J → Chart (loomZ I)} {WT : J → Chart (loomG I)}
    (d : ∀ i j,Tendsto (fun n => ZT n i j) P (𝓝 (Z i j)))
    (L : List I) (t : L.Pairwise (fun i j=> ∀ a b,Tendsto (fun n => WT n (i,a) (j,b)) P (𝓝 (W (i,a) (j,b))))) :
    Tendsto (fun n => quoted tag L (ZT n) (WT n)) P (𝓝 (quoted tag L Z W)) := by
  refine tally_lim (L := booths tag L) (f:=fun n r=>quote r (ZT n) (WT n)) ?_
  intro r v
  apply Tendsto.mul (attend_spin d r); apply WickG.attend
  rw [←booth_node v] at t
  have he:= List.pairwise_map.mp (t.sublist (paperF_roster r)); exact he.imp (fun {i j} q=> q i.2 j.2)

lemma booths_tally (P Q : List I) {R : Type*} [AddMonoid R] (tag : I → Sewer) (f : Route I→ R) :
    tally (booths tag (P++Q)) f = tally (booths tag P) (fun r=> tally (booths tag Q) (fun r' => f (r++r'))) := by
  induction P generalizing f with
  | nil => simp [Chain.tally, booths]
  | cons i P ih =>
    rw [List.cons_append,booths,booths,tally_deck,tally_deck]; simp_rw [tally_remap]; apply congrArg (tally _) (funext ?_); intro u; exact ih _
lemma quoted_factor (P Q : List I) (tag : I→ Sewer) (Z : Chart (loomZ I)) (Y : Chart (loomG I))
    (a : ∀ i : loomZ I,i.1∈P→∀ j:loomZ I,j.1∈Q→Z i j=0)
    (b : ∀ i : loomG I,i.1∈P→∀ j:loomG I,j.1∈Q→Y i j=0) :
    quoted tag (P++Q) Z Y = quoted tag P Z Y * quoted tag Q Z Y := by
  have ht(L R : Route I)(p : L∈booths tag P)(q:R∈booths tag Q): quote (L++R) Z Y=
      quote L Z Y*quote R Z Y := by
    have hp: WickG.read Y (paperF (L++R))= WickG.read Y (paperF L)* WickG.read Y (paperF R):=by
      have hv(A:Route I)(i:loomG I)(h:i∈paperF A):i.1∈A.map Leg.i := (paperF_roster A).subset (List.mem_map_of_mem h)
      rw [show paperF (L++R)=paperF L++paperF R from List.filterMap_append]; exact WickG.insulated Y (paperF L) (paperF R) (fun i h j k=> b i (booth_node p ▸ hv L i h) j (booth_node q ▸ hv R j k))
    unfold quote quoteSpin; rw [hp,show paperS (L++R)=paperS L++paperS R from List.flatMap_append, WakeInvestment.rune_divide]
    · unfold shade; rw [List.map_append,List.prod_append]; ring
    intro i u j e; exact a i (booth_node p ▸ paperS_assign _ u) j (booth_node q ▸ paperS_assign _ e)
  unfold quoted; rw [booths_tally,←(tally_shift ..).2]; simp_rw [←(tally_shift ..).1] -- risk simp on wrong direction includes tally outer? `rw` parameters
  apply tally_same; intro i e; exact tally_same (fun j p=> ht i j e p)

#print axioms quote_big
#print axioms attend_quoted
#print axioms quoted_factor
end Palette
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
