import YM.CF.Tye.Petal
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "j"=> A.loft
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
abbrev trunk (s:Signed)(b:Site (Domain N B))(w: Palot.leaf (Site (Domain N B))): Palot.leaf (Site (Domain N B)):=⟨w.val.image (affine s b), Finset.image_nonempty.mpr w.property⟩
variable{r:ℕ}(t:Signed)(w: Palot.leaf (Site (Domain N B)))(k:ℕ) -- new parent
local notation "Z"=> Channels.offset s b t
local notation "Z'"=> S.ratio.embed Z
local notation "N'"=> M.sent x T A.trot A.room A.post A.beta
local notation "W"=> trunk (N:=N) (B:=B) s b w
-- compare from rotor recipe to base original
lemma dignify {D: Side}(C:Support D)(s:Signed)(b:Site D)(k:ℕ): halo k (C.image (affine s b))= (halo k C).image (affine s b):=by
 ext i; rw [halo_spec]; simp only [mem_image]; let Q:= affine s b; have h(x y:Site D): separation (Q x) (Q y)=separation x y:=by unfold Q; simp [affine]
 constructor
 · rintro ⟨z0,⟨w,v,rfl⟩,z⟩; obtain ⟨u,rfl⟩:= (StepData.sendSites s b).surjective i; rw [show separation _ ((StepData.sendSites s b) u)= _ from h w u] at z; exact ⟨u,halo_spec.mpr ⟨w,v,z⟩,rfl⟩
 rintro ⟨z0,v,rfl⟩; obtain ⟨w,l,p⟩:= halo_spec.mp v; exact ⟨Q w,⟨w,l,rfl⟩,(h w z0).trans_le p⟩
lemma bright_s(i:Site (Domain N B))(z:RG.Atom SU.group r): trunk s b (shoreS t k i z)=shoreS (s*t) k (i+Z) z:=by
 apply Subtype.ext; change _=Lattice.halo _ _; have he(v:Site d): (s*t).act (v+Z)= affine s b (t.act v):=by simp only [Signed.act_add,Channels.offset,Signed.act_inv,affine]; rw [Signed.act_mul]
 rw [show z.footprint _= _ from tour_s i Z z, show insert (i+Z) (Ah Z _)= Ah Z (insert i (z.footprint i)) from (image_insert ..).symm]; unfold Ah; rw [image_image]; dsimp only [Tye.trunk,shoreS,Lich.Muster.parcel]; rw [← dignify _ _ _ k, image_image]; congr 1; exact image_congr fun i _=> (he i).symm -- tune
lemma bright_f(v:Site d')(z:RG.Atom SU.group r): trunk s b (shoreH (S:=S) t k v z)=shoreH (S:=S) (s*t) k (v+Z') z:=by
 apply Subtype.ext; change _=Lattice.halo _ _; have hp(i:Site d'): (s*t).act (S.ratio.parent (i+Z'))= affine s b (t.act (S.ratio.parent i)):= (Arena.herZ b t s (.inr (.inl i) : Along S)).symm
 rw [show z.footprint _=_ from tour_s v Z' z,show insert (v+Z') (Ah Z' _)= Ah Z' (insert v (z.footprint v)) from (image_insert ..).symm]; unfold Ah; rw [image_image]; dsimp only [Tye.trunk,shoreH,Lich.Muster.parcel]; rw [←dignify _ _ _ k, image_image]; congr 1; exact image_congr fun i _=> (hp i).symm -- tune
lemma bright_inj : Injective (trunk s b (N:=N) (B:=B)):=fun v z p=>Subtype.ext (image_injective (StepData.sendSites s b).injective (congrArg Subtype.val p))
include h hp hv hz
local notation "Q"=> A.phaseUp
local notation "R"=> A.phaseLow
lemma extU_s(v:Site d')(P': ℕ→ RG.Atom SU.group r) : extU A Y t k w v P'= extU A M (s*t) k W (v+Z') P':=by
 unfold extU Lich.Muster.crop; apply tsum_congr; intro u; dsimp only; simp only [← bright_f s b]; have he:=bright_inj s b; simp only [he.eq_iff]; split
 next p=> rw [space_s _ _ _ _ _ _ s b M h hp hz hv,channel_turn,Channels.offset_fine]; exact lush_t _ _ _ _ _ (taxes M.key s t b) _
 rfl
lemma sapU_s(v:Site d'): sapU A Y t k w v= sapU A M (s*t) k W (v+Z'):=by
 unfold sapU Lich.Muster.crop; apply tsum_congr; intro u; dsimp only; simp only [←bright_f s b]; have he:=bright_inj s b; simp only [he.eq_iff]; split
 next p=> rw [space_s _ _ _ _ _ _ s b M h hp hz hv,channel_turn,Channels.offset_fine]; exact path_t _ _ _ _ _ (taxes M.key s t b) _ _
 rfl
omit h hp hz hv
lemma extV_s(v:Site (Domain N B))(P': ℕ→ RG.Atom SU.group r) : extV A Y t k w v P'= extV A M (s*t) k W (v+Z) P':=by
 unfold extV Lich.Muster.crop; apply tsum_congr; intro u; dsimp only; simp only [← bright_s (s:=s)]; have he:=bright_inj s b; simp only [he.eq_iff]; split
 next p=> rw [show (Y).V=pull s b M.V from rfl,channel_turn]; exact peer_t _ _ _ _ _ (toured M.key s t b) _
 rfl
lemma sapC_s(v:Site (Domain N B)): sapC A Y t k w v= sapC A M (s*t) k W (v+Z):=by
 unfold sapC Lich.Muster.crop; apply tsum_congr; intro u; dsimp only; simp only [←bright_s (s:=s)]; have he:=bright_inj s b; simp only [he.eq_iff]; split
 next p=> rw [show (Y).V=pull s b M.V from rfl,channel_turn]; exact path_t _ _ _ _ _ (toured M.key s t b) _ _
 rfl
include h hp hz hv
lemma shard_s: shardy A Y k w=shardy A M k W:=by
 unfold shardy; apply congrArg Neg.neg; apply av_a s; intro t; refine congrArg₂ (·-·) (sum_equiv (Equiv.addRight (S.ratio.embed (Channels.offset s b t))) (by simp) ?_) (sum_equiv (Equiv.addRight (Channels.offset s b t)) (by simp) ?_)
 · intro i _; unfold Lich.Muster.river; rw [extU_s A M s b h hp hv hz t,extU_s A M s b h hp hv hz t,sapU_s A M s b h hp hv hz t,extU_s A M s b h hp hv hz t]; rfl
 intro i _; unfold Lich.Muster.flows; simp_rw [extV_s A M s b t, sapC_s A M s b t]; rfl
end YM.CF.Tye
