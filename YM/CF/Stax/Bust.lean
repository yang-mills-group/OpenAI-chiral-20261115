import YM.CF.Stax.Sil
import YM.CF.Sour.Park
import YM.CF.Sour.Tile
import YM.CF.Ione.Tape
import YM.CF.Cadre.Point
import YM.CF.Cadre.Gear
import YM.CF.Vow.Grow
import YM.CF.Bake.Pep
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
open Salt Ione Levier Sour
variable (s:Sweep n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "Pu"=> Palot.robe
local notation "SD"=> Support (More n)
local notation "Πt"=> (boxA s).symm.toEmbedding
local notation "σX'"=> σX (n:=n) P
lemma bayG(L: hook (Seat n)): robe (L.map (Tu).toEmbedding)=Ta (robe L):=by
 ext i; unfold Salt.actY; rw [Finset.mem_map_equiv]; constructor
 · intro p; obtain ⟨j,h,v⟩:= mem_biUnion.mp p; obtain ⟨x,q,rfl⟩:= mem_map.mp h; exact mem_biUnion.mpr ⟨x,q,mem_map_equiv.mp v⟩
 intro p; obtain ⟨x,q,v⟩:=mem_biUnion.mp p; exact mem_biUnion.mpr ⟨Tu x,mem_map_of_mem _ q,mem_map_equiv.mpr v⟩
lemma tide(L:hook (Seat n)): Palot.flow _ (L.map (moldA s).toEmbedding) ↔ Palot.flow _ L:=by
 constructor
 · intro p i g j v w; exact (Finset.disjoint_map _).1 (p (Tu i) (mem_map_of_mem _ g) (Tu j) (mem_map_of_mem _ v) ((moldA s).injective.ne w))
 intro p i g j v w; obtain ⟨i,g0,rfl⟩:= mem_map.mp g; obtain ⟨j,v0,rfl⟩:=mem_map.mp v; exact (Finset.disjoint_map _).2 (p i g0 j v0 (fun h=> w (congrArg _ h)))
abbrev burn(s:Sweep n):Equiv.Perm (Finset (Aura n)):= Equiv.finsetCongr (moldA s)
lemma trum(X Y:Aura n)(D:SD)(G:Hk):burn s G∈ Cadre.drum (Tu X) (Tu Y) (Ta D)↔ G∈Cadre.drum X Y D:=by
 have hx(Y:Aura n): (Tu Y).val=Ta Y.val:=rfl; let K:=G.map (Tu).toEmbedding
 have ht(P:Aura n): (∀ j∈K,¬Disjoint (Ta P.val) j.val)↔(∀ j∈G,¬ Disjoint P.val j.val):=by
    constructor; · intro x i h g; exact x (Tu i) (mem_map_of_mem _ h) ((Finset.disjoint_map _).2 g)
    intro x i h g; obtain ⟨j,p,rfl⟩:= mem_map.mp h; exact x j p ((Finset.disjoint_map _).1 g)
 have hW:K=burn s G:=rfl; rw [←hW,Cadre.drum_p,Cadre.drum_p,show Pu K=_ from bayG s G,tide,hx Y,hx X,ht Y]; unfold actY; rw [map_subset_map,←Finset.map_union]; simp -- tune unfolding abbrev `Ta`
variable {H:Bag n}(D:Support (More n))(V:Orbit n)(F' F₀:Copy n)(c:Bias δ H P h z)(p:Injective (priorP V.2))(hb:∀ i:Orbit n,Injective (priorP i.2)→∀ X:Aura n,H (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (Sour.γS s) (H X i))
local notation "W'"=> yellA s V
lemma optic (X Y:Aura n)(δ:ℕ):Bias.αt (Tu X) (Tu Y) (Ta D) δ↔ Bias.αt X Y D δ:=by
 unfold Bias.αt; change (_∧ Ta D ⊆ Ta Y.val ∧ Lattice.halo δ _ ⊆ Ta Y.val)↔_
 have he : Lattice.halo δ (Ta D)=Ta (Lattice.halo δ D):=by unfold Salt.actY; rw [←sitU,paysT]
 rw [he]; exact and_congr map_subset_map (and_congr map_subset_map map_subset_map)
include hb c p
lemma star_R (X Y:Aura n)(t: Bias.αt Y X D δ):coll_T P (Tu X) (Ta D) (H (Tu Y)) W'=sauce s.charge (detX s.s) (Sour.γS s) (coll_T P X D (H Y) V):=by
 let a:=moldA s X; have hv:= (optic s D Y X δ).mpr t; let Λ:=sauce s.charge (detX s.s) (γS s); let Qv:=σX' X D; let Kv:=c.scope X Y D t.1 t.2.1 t.2.2; let Ku:=c.scope (moldA s X) (moldA s Y) (actY s D) hv.1 hv.2.1 hv.2.2
 by_cases f:Gates Qv X.val V.1; swap
 · unfold coll_T; rw [if_neg ?_,if_neg f,sauce,singT,win_z,map_zero]; exact mt (lights_V ..).mp f -- tune
 obtain ⟨Y',q,v⟩:=f; let Z:Orbit n:=(Y',V.2); let X':= σX' a (Ta D); have he: Agrees _ _ _ ∧ Set.EqOn _ _ _:=yellow s V Z X.val v (fun _ _=>rfl)
 let U:= yellA s Z; rw [Kv.toCrate.latch V Z v (fun _ _=>rfl),Kv.toCrate.pointV Z q,Ku.toCrate.latch _ U he.1 he.2, Ku.toCrate.pointV _ (show U.1 ∈ X' from ((Salt.lights_C ..)).mpr q),hb Z p] -- tune
lemma leap (X Y:VX)(g:F' W'=suit_Y s (F₀ V)):c.payX (Tu X) (Ta D) (Tu Y) F' W'=suit_Y s (c.payX X D Y F₀ V):=by
 by_cases hA:Bias.αt Y X D δ; swap; · unfold Bias.payX; rw [dif_neg hA,dif_neg (fun t=> hA ((optic s D Y X δ).mp t)),Pi.zero_apply, Pi.zero_apply,map_zero]
 apply Subtype.ext; rw [c.truth _ _ _ _ ((optic s D Y X δ).mpr hA) _, g]; change Sault.rind (coll_T _ _ _ _ _ *sauce _ _ _ _) =sauce _ _ _ (c.payX X D Y F₀ V).val; rw [c.truth _ _ _ _ hA _,Sault.plower,star_R z s D V c p hb X Y hA,show (sauce _ _ _) (coll_T P X D (H Y) V*(F₀ V).val)= _ from singm ..]
end YM.CF.Stax
