import ZecaPosts
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Monument
open Poin Boundary Probe
variable {ι:Type}{H:Hilbert}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)
   (Ω:Bench S)(hΩ:∀x:E4,M S x Ω.val=Ω.val)
local notation "J"=>Grotto S G Ω.val
local notation "T"=>springs S G Ω.val
local notation "φ"=>saint S G Ω hΩ
local notation "N"=>chapel S G Ω.val
local notation "C"=>Cove S G Ω.val
local notation "L"=> (C).subtypeL
local notation "h'"=> crystalline S G Ω.val


open Cirrus Cirrus.PavilionM
local notation "Γ"=>Sachet S G
local notation "⬝"=>side S G Ω
local notation "U"=>(N).Model (T) φ
local notation "Λ"=>(N).lens (T) φ


abbrev mast(t:Sachet S G):Test4→ₗ[ℂ] Effort T φ N:=
 organ (T) (N) φ (posting _ _ _ t.property)
abbrev Door(hΩ:∀x:E4,M S x Ω.val=Ω.val)(x:(N).Model (T) (saint S G Ω hΩ)):Bench S :=
    (h').site x.val
abbrev mastV(hΩ:∀x:E4,M S x Ω.val=Ω.val): (N).Model (T) (saint S G Ω hΩ):=
 (N).focus _ _ []
local notation "ω"=>mastV S G Ω hΩ
local notation "op"=>mast S G Ω hΩ
local notation "door"=>Door S G Ω hΩ
variable (V:Boundary.Action (Grotto S G Ω.val))
-- Relic fields instantiate V in cap directly. capsPortal includes Ward-contingent F1.
structure Relic
  (V:Boundary.Action (Grotto S G Ω.val)):Prop extends Frescoes (springs S G Ω.val) (chapel S G Ω.val) (saint S G Ω hΩ) V where
 anchorTransfer: Anchor S Ω.val→∀x:J,(∀p:E4,V.orbit.translation p x=x)→∃z:ℂ,x=z • (φ).val
 net:NetStory T φ N V toFrescoes.w
 into (x:U): L (Λ x)=(door x).val
 init: door ω=Ω

 sold (D:Γ)(f:Test4)(x:U): door (op D f x)=D.val.field S f (door x)
 field (D:Γ)(f:Test4)(x:U):(op D f x).val=(⬝ D).field T f x.val
 wordEuro (α:Type)(F:α→Γ)(sp:α→Cross timeAxis)(t:α→ℝ)
    (u:List α)(e:u.Pairwise fun i j=>t i<t j):
    quoteL T (φ).val (fun x=>⬝ (F x)) sp t u=quoteL S Ω.val (fun x=>(F x).val) sp t u
 determineR (D:Γ)(A:(J).Op):
   (⬝ D).op=A ↔ ∀(f:Test4)(x:U),
   Λ (op D f x)=(ℑ T A f (D.val.n) x.val).val
 adj (D:Γ)(g:Test4)(x y:U):inner ℂ (Λ (op D g x)) (Λ y)=
    inner ℂ (Λ x) (Λ (op (twin S G D) (bar g) y))
 continuity (D:Γ)(x:U): Continuous fun f=> Λ (op D f x)
 per_local (D E:Γ) (f g:Test4)(c:Fields.causal f g): Commute (op D f) (op E g)
 per_net (D:Γ)(f:Test4)(e:HasCompactSupport (⇑f)): op D f∈ Hull T φ N univ (tsupport f)

-- assemble
lemma mintedField (D:Γ)(f:Test4)(x:U):
  door (op D f x)=D.val.field S f (door x):=by
  unfold Door
  refine (congrArg ((h').site)
     (base_money _ _ _ (posting _ _ _ D.property) f x)).trans ?_
  exact posted_test S G Ω D.property f x.val

theorem relic (e:‖Ω.val‖=1)(p:G.Tile S Ω):
   ∃ V,Relic S G Ω hΩ V:=by
 obtain ⟨V,y⟩:=harvested S G Ω hΩ e p
 refine ⟨V,⟨y,fun h=> y.w.unique (sturdy S G Ω hΩ h),
    berth _ φ (safer S G Ω hΩ) _ V y.w,fun _=>rfl,Subtype.ext rfl,mintedField S G Ω hΩ, ?_,
    fun _=>value2 S G Ω,fun D A=> determine T N φ (safer S G Ω hΩ)
        (posting _ _ _ D.property)
        (climb_all _ _ _ (safer S G Ω hΩ) (pilgrims S G Ω.val)) A,
    ?_,fun D=> closed_field _ _ _ (posting _ _ _ D.property),
    fun D E=> chamber _ _ _ (posting _ _ _ D.property) V y.w (posting _ _ _ E.property),
    fun D=>gen _ _ _ (posting _ _ _ D.property)
  ⟩⟩
 · intro D f x;exact base_money _ _ _ (posting _ _ _ D.property) f x
 intro D g x w
 change inner ℂ (door (op D g x)).val (door w).val=inner ℂ
    (door x).val (door (op (twin S G D) (bar g) w)).val
 rw [mintedField,mintedField];exact (realStamp S).adj D.val g _ _
#print axioms relic
