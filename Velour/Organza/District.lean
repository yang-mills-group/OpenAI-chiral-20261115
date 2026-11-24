import Velour.Organza.Larva
/-!
# Graph cores on cyclic subrepresentations
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL

local notation "U" => S.unit.translation
local notation "M" => S.liftL



/-- Translation-invariant (liquid district). -/
def Mobile (L :Submodule ℂ D):Prop:= ∀b, ∀v∈ L, M b v∈ L
def Car (N:Submodule ℂ H.space):Prop:= ∀ b, MapsTo (U b) (N : Set H.space) N

/-- Ambient shadow. -/
def district (L:Submodule ℂ D): Submodule ℂ H.space:=
    (L.map S.muslin.subtype).topologicalClosure

/-- At every graph. -/
def estate (L:Submodule ℂ D)(n:ℕ): Submodule ℂ H.space:=
    (L.map (S.muslin.subtype.comp (B n))).topologicalClosure

lemma orthogonal_money (N:Submodule ℂ H.space)(q:IsClosed (N:Set H.space))(x:H.space):
  x∈ N ↔ ∀ y ∈Nᗮ, inner ℂ y x=0:= by
  change _ ↔ x ∈ Nᗮᗮ; rw [Submodule.orthogonal_orthogonal_eq_closure]
  change _ ↔ x∈ closure (N:Set _); rw [q.closure_eq]; rfl

variable {S}
variable {L:Submodule ℂ S.muslin}{N:Submodule ℂ H.space}

lemma Car.turns (q:S.Car N)(g:IsClosed (N:Set H.space))(d:ℝ≥0): MapsTo (S.E d) (N:Set _) N:=by
  intro v pv
  refine (orthogonal_money _ g _).mpr fun u h=>?_
  have e:= Paley.empty (S.altitude 0 u v) (fun i=> (S.veers ..).trans
       ((N.mem_orthogonal' u).mp h _ (q _ pv)))


  have w:= e ⟨0,d⟩ d.coe_nonneg
  change inner ℂ u (U 0 (S.edge 0 (E (d:ℝ).toNNReal v)))=0 at w
  rw [S.unit.origin, S.birth, Real.toNNReal_coe] at w; exact w

lemma Mobile.car (h:S.Mobile L):S.Car (S.district L):=by
  intro b; exact (MapsTo.closure (fun _ ⟨v,y,g⟩=> g ▸
    (show U b v.val∈ L.map S.muslin.subtype from ⟨_,h b _ y,rfl⟩))
    (U b).continuous)

lemma Mobile.buy (h:S.Mobile L)(n:ℕ): S.Car (S.estate L n):= by
 intro b
 refine MapsTo.closure ?_ (U b).continuous
 rintro _ ⟨v,y,rfl⟩
 refine ⟨_,h b _ y,?_⟩
 change (B n (M b v)).val=U b (B n v).val
 simpa only [zero_add] using S.liftL_refines b n v


private lemma Mobile.cream (h:S.Mobile L){v:D}(p:v.val∈S.district L)
    (n:ℕ)(t:ℝ≥0)(q:0<t):
   (B n (G t v)).val ∈ S.estate L n:= by
   obtain ⟨Z,e⟩:=S.heat_scale t q n
   have u (w:D): (B n (G t w)).val=Z w.val:= S.gauze_power_inj n (by
        rw [weight_cancel, S.heatL_coe,←mul_apply_eq_comp,e])
   rw [u]
   change v.val∈closure ((L.map S.muslin.subtype):Set H.space) at p
   refine closure_minimal ?_ (((show IsClosed (S.estate L n:Set H.space) from
          Submodule.isClosed_topologicalClosure _)).preimage Z.continuous) p
   rintro _ ⟨w,y,rfl⟩
   change Z w.val∈ S.estate L n; rw [← u, heat_weight, heatL_coe]
   refine (h.buy n).turns (Submodule.isClosed_topologicalClosure _) t ?_
   exact subset_closure (show (B n w).val∈ L.map (S.muslin.subtype.comp (B n)) from ⟨w,y,rfl⟩)


lemma Mobile.preferred (h:S.Mobile L){v:D}(p:v.val∈S.district L)(n:ℕ):
   (B n v).val∈ S.estate L n:= by
   have e:Tendsto (fun t=> (B n (G t v)).val) (𝓝[>] (0:ℝ≥0)) (𝓝 (B n v).val):=
      ((S.surges_warm (d:=id) (tendsto_id.mono_left nhdsWithin_le_nhds)).at_one v) n
   exact (show IsClosed (S.estate L n:Set H.space) from Submodule.isClosed_topologicalClosure _).mem_of_tendsto e
     (Eventually.mono self_mem_nhdsWithin fun d q=> h.cream p n d q)
/-- Full graph core, even countably many detectors. -/
lemma Mobile.core (h:S.Mobile L){v:D}(p:v.val∈S.district L):
    ∃y:ℕ→D, (∀i,y i∈L) ∧ S.Ruffles atTop y v:= by
    have z (n:ℕ) : ∃y∈L, ‖B n (y-v)‖<(2:ℝ)⁻¹^n:=by
       obtain ⟨_,⟨w,e,rfl⟩,u⟩:= Metric.mem_closure_iff.mp
          (show _ ∈ closure (L.map (S.muslin.subtype.comp (B n)):Set H.space) from
             h.preferred p n) ((2:ℝ)⁻¹^n) (by positivity)
       refine ⟨w,e,?_⟩
       rw [map_sub,←dist_eq_norm,dist_comm]; exact u
    choose y k e using z
    refine ⟨y,k, ?_⟩


    intro n
    rw [←tendsto_sub_nhds_zero_iff]
    exact squeeze_zero_norm' ((eventually_ge_atTop n).mono fun i j=> by
           change ‖(B n _)-(B n _)‖≤_
           rw [←map_sub]
           exact le_trans (S.weight_mono j _) (e i).le)
       (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2:ℝ)⁻¹) (by norm_num))
#print axioms Mobile.core

