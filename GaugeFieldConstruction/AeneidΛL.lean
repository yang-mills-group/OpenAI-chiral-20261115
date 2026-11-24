import GaugeFieldConstruction.NereidΛL
import Mathlib.Data.Fin.Tuple.Sort
/-!
 # Compilation of the physical cut rotation, LAST-BIND. `TotalStarsMars` => Skyline. Requires PathUL for that very χ (supplied in Apollo). W analytic + Eu contour: explicitly value `𝒜(W;word)` via time-ordered-perm near x & any monotonocity fixed; usable & unique. Flux integral charges approximations not generators. Using Ward option NOT spatial charge. Maintain spin-indicator at SeatPro.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset YM.Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "M_ν" => H.TinCanL
local notation "Τh" => TouchMΛ H (N:=N)
variable (k:Fin n)(a:Axis)(i:Fin n)
-- actual determination by interior limits
abbrev EastTΛL (x:Points n)(p:Equiv.Perm (Fin n)) := readings (NSF.Points.rearrange p x)∈ NSF.Boundary.sunrise n
abbrev OfferΛL (x:Points n)(p:Equiv.Perm (Fin n))(u:ℂ):Prop:= Tendsto (ΑΛL H (N:=N) (V ∘ p) ∘ wickSlice n) (𝓝[NSF.Work.C20.ordered n] (NSF.Points.rearrange p x)) (𝓝 u)
include hz hv G
lemma EastPorousΛL (x:Points n)(p:Equiv.Perm (Fin n))(e:x∈conf n) (hp:EastTΛL x p) (u:ℂ): OfferΛL (N:=N) H V x p u ↔ u=Z n x V:= by
 have hx: ContinuousAt (fun x=> Z n x (V ∘ p)) (NSF.Points.rearrange p x) := (G.sm _).continuousOn.continuousAt ((conf_open n).mem_nhds (NSF.Points.rearrange_in _ e))
 have hg: OfferΛL (N:=N) H V x p (Z n x V):= by
    rw [← G.symmetry p V x e]; refine (hx.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with i ht; exact (ΥLiveΛL H G hz hv _ ht).symm
 haveI := ordered_neBot (show readings (NSF.Points.rearrange p x)∈ NSF.Boundary.sunrise n from hp)
 exact ⟨fun a=> tendsto_nhds_unique a hg, fun h=> h.symm ▸ hg⟩
omit hz hv G
noncomputable def PluckΛL (x:Points n):Equiv.Perm (Fin n):= Tuple.sort (readings x)
lemma pluckRiseΛL (x: Points n): EastTΛL x (PluckΛL x):= Tuple.monotone_sort (readings x)
noncomputable def RespiteΛL (x:Points n):ℂ:= open scoped Classical in if hp:∃ u:ℂ,OfferΛL H (N:=N) V x (PluckΛL x) u then hp.choose else 0
include hz hv G
lemma αRespiteΛL (x:Points n)(q:x∈conf n): RespiteΛL (N:=N) H V x=Z n x V :=by
 let I:= OfferΛL H (N:=N) V x (PluckΛL x); have h(t:ℂ):I t ↔ t=Z n x V:= EastPorousΛL H G hz hv _ _ _ q (pluckRiseΛL x) _
 have he:∃ u,I u:=⟨_,(h _).2 rfl⟩
 unfold RespiteΛL; rw [dif_pos he]; exact (h _).1 he.choose_spec
local notation "$ΐ"=> RespiteΛL H (N:=N)
-- stress formula on reconstructed analytic distribution W alone. N used to price. (hz,hv only for proof). Any neighbor. RHS translation Ward survives.As smeared Eu tests in Stern. Ξ.S.R.Proper.
include e
variable {x:Points n}
lemma HonestWardΛL (hc:x∈NSF.Work.C20.ordered n)(b:Fathom.Bulb)(hb:BreatherMars b k x): Τh V k a (wickSlice n x)=∑ i:Axis, (-(MinkΛM a:ℂ)*Wickγ i)*(∫ y:E4, (Analysis.D (basis i) b.f y) • ($ΐ (Fin.cons (SkylineΜΛ p i a) V) (YM.Points.cons y x))) :=by
 rw [ΛGenerateL p H G hz hv e V k a hc b hb]; apply sum_congr rfl; intro i _; congr 1; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_
 dsimp only []; by_cases u:y∈(b.LED i).run
 · rw [αRespiteΛL H G hz hv _ _ (RoomMars _ _ _ hb _ (Bulb.cone _ _ u))]
 rw[show Analysis.D (basis i) b.f y=0 from image_eq_zero_of_notMem_tsupport u,zero_smul,zero_smul]
-- with integrability
lemma SimpleFluxΛL (j:Axis)(b:Fathom.Bulb)(hb:BreatherMars b k x): Integrable (fun y:E4=> (Analysis.D (basis j) b.f y) • ($ΐ (Fin.cons (SkylineΜΛ p j a) V) (YM.Points.cons y x))) :=by
 let U:=SkylineΜΛ p j a; have h(t:ΧiMars)(y:E4)(v:y∈(b.LED j).run):ContinuousAt (fun z=> Z (n+1) (YM.Points.cons z x) (Fin.cons t V)) y:=by
    apply ContinuousAt.comp (g:=fun z=> Z (n+1) z (Fin.cons t V)) (f:=fun z=> YM.Points.cons z x) _ ?_
    · exact (G.sm _).continuousOn.continuousAt ((conf_open _).mem_nhds (RoomMars _ _ _ hb _ (Bulb.cone _ _ v)))
    exact (show ContinuousAt (fun z=> AlumUL (z,x)) y from (AlumUL.continuous.continuousAt).comp (x:=y) (f:=fun z=>(z,x)) (continuousAt_id.prodMk continuousAt_const))
 refine (TaxfulUL (b.LED j) _ (h U)).congr ?_
 filter_upwards with y; change _= Analysis.D _ _ _ • _; by_cases u:y∈(b.LED j).run
 · rw [αRespiteΛL H G hz hv _ _ (RoomMars _ _ _ hb _ (Bulb.cone _ _ u))]; rfl -- tune
 change Analysis.D _ _ _ • _= _; rw[show Analysis.D (basis j) b.f y=0 from image_eq_zero_of_notMem_tsupport u,zero_smul,zero_smul]
-- distribution Mink in this projection
abbrev CoffΜΛ (p:Ticket u C)(a b:Axis): (SurfRimL A).Union:= H.TinCanL (SkylineΜΛ p a b)
-- order of H and p tune
lemma PureConsΛL : MintDΛ (X:=N) (CoffΜΛ H p) :=by
 intro n V i a x u; let U:=H.TinCanL.symm ∘ V
 have h (j:Axis): Function.update V i (CoffΜΛ H p j a)= H.TinCanL ∘ (Function.update U i (SkylineΜΛ p j a)) := by ext1 k; by_cases p:k=i<;>simp [p,U,CoffΜΛ]
 simp_rw[h]; exact CosmicConServeΛL p H G hz hv e U i a u
include hu
lemma WConΛL : ConsWΛL Y (CoffΜΛ H p):= ΛHestiaL hu hv _ (PureConsΛL p H G hz hv e)
omit G hz e
lemma TouchReΜΛL (f: YM.Boundary.Joint n)(p:HasCompactSupport (f:Points n→ℂ)):Tendsto (fun y:NSF.Boundary.Heights n=> (∫ x:Points n, Τh V k a (NSF.Boundary.glow x (NSF.Boundary.dawn y))*f x)) (𝓝[NSF.Boundary.east n] 0) (𝓝 (-(Y.W n (H.TinCanL∘ V) (DriftΛL (NSF.Points.direction k a) f)))):= risePayΛ f _ p _ hu hv
-- interpretation: this RHS on *product tests* is inserting δ. explicit.
omit hu hv
lemma LeafWHereΛL (f:Fin n→ YM.Boundary.Test4): Y.expect (List.ofFn fun i=> ((M_ν (V i)), Function.update f k (-ΦshiftΛ (basis a) (f k)) i)) = -(Y.W n (M_ν ∘ V) (DriftΛL (NSF.Points.direction k a) (Joint.materialize n f))) :=by
 rw [NSF.Work.C29.expectOfFn, spotTestΛL]; let g:= ΦshiftΛ (basis a) (f k)
 have he: Joint.materialize n (Function.update f k (-g))=-Joint.materialize n (Function.update f k g):= (NSF.Work.C29.materialLinear n).map_update_neg ..
 change Y.W n _ (Joint.materialize n (Function.update f k (-g)))=_; rw[he,map_neg]; rfl

variable (R:NSF.Boundary.Wightman (SurfRimL A))(s:(SurfRimL A).RealSpin) (Q:R.Realizes (W:=Y) (SurfCheckL.VesselPL p H) s)
local notation "M_H"=> R.operators
variable (q:R.spin=SurfCheckL.HeightsKL p H)
include Q q
lemma LocalCapeΛL (g:Mink.Poincare)(a b:Axis)(f: YM.Boundary.Test4): DragΛL R Q g (R.operators.field (CoffΜΛ H p a b) f)=∑ i:Axis,∑ j:Axis,(costΛ g.Λ⁻¹ a i*costΛ g.Λ⁻¹ b j) • R.operators.field (CoffΜΛ H p i j) (Joint.push g f):=by
 rw [MeadΛL, q, SurfCheckL.KSpunL, ΛμErosL]; simp_rw [map_sum,map_smul, LinearMap.sum_apply,LinearMap.smul_apply]
omit Q q in
lemma LocalStarsΛL (J:R.J=H.AsterBackL)(a b:Axis):R.J (CoffΜΛ H p a b)=CoffΜΛ H p a b:=by
 rw [J]; change H.TinCanL (asterL (H.TinCanL.symm _))=_; rw [LinearEquiv.symm_apply_apply,ΛShade]
#print axioms HonestWardΛL
#print axioms WConΛL
#print axioms LocalCapeΛL
#print axioms LeafWHereΛL
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
