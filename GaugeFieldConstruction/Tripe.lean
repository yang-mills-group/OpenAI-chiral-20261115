import GaugeFieldConstruction.Tornador
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x:Cover}{d:ℕ}
open TableF Flot
variable (x)
def Pan (x:Cover)(d:ℕ)(k:Cover):Cover:= fun i=>max (x i-d) (min (x i+d) (k i))
lemma pan_v (d:ℕ)(z:Cover): Pan x d z∈cartO x d := by rw [cart_spec]; intro j; unfold Pan; omega
lemma pan_id (k:Cover)(p:k∈cartO x d): Pan x d k=k:=by funext j; have hx:=(cart_spec ..).1 p j; unfold Pan; omega
def upD (x:Cover)(d:ℕ)(k:Cover)(i:Axis):Prop:= x i-d≤ k i∧ k i< x i+d
lemma step_D (k:Cover)(d:ℕ)(i:Axis):Pan x d (k+step i) = if upD x d k i then Pan x d k+step i else Pan x d k:=by
 funext j; by_cases z:upD x d k i <;>simp only [z,ite_true,ite_false]
 all_goals unfold Pan; unfold upD at z; by_cases h:j=i <;> simp only [Pi.add_apply,Lattice.step,Pi.single_apply,h,ite_true,ite_false,add_zero]
 all_goals omega
lemma turn_D (i:Cover)(d:ℕ)(j k:Axis)(p:j≠k): upD x d (i+step j) k ↔ upD x d i k:=by simp [upD,Lattice.step,p, Ne.symm p]
lemma inch_D (k:Cover)(i:Axis)(p:k∈cartO x d)(q:k+step i∈cartO x d): upD x d k i:=by
 have hz:=(cart_spec ..).1 p i; have hp:=(cart_spec ..).1 q i; simp only [Pi.add_apply,Lattice.step,Pi.single_eq_same] at hp; unfold upD; omega
variable {E:Type}[AddCommGroup E]
def slide_D (d:ℕ)(V:Wheel Axis E): Wheel Axis E:=fun i x'=> if upD x d x' i then V i (Pan x d x') else 0
lemma root_B (d:ℕ)(V:Wheel Axis E)(p:∀ i:Cover,∀ p:PlaqAxes,deckQ i p ⊆ cartO x d→CurlMap V p.val.1 p.val.2 i=0): ∀ i j,CurlMap (slide_D x d V) i j=0:=by
 let T':= slide_D x d V; have he(i j:Axis)(u:i<j): CurlMap T' i j=0:=by
    funext k; let t:= Pan x d k; change T' j (k+step i)-T' j k-(T' i (k+step j)-T' i k)=0;
    unfold T' slide_D; rw [step_D,step_D,turn_D x k d i j (ne_of_lt u),turn_D x k d j i (ne_of_gt u)];
    by_cases g:upD x d k i <;> by_cases h:upD x d k j; swap
    all_goals try simp [*, t]
    let R:= pan_v x d k; have hi:∀ (k:Cover)(i:Axis)(h:upD x d k i), Pan x d k+step i∈cartO x d:=by intro k i h; have he:= pan_v x d (k+ step i); rwa [step_D,if_pos h] at he
    -- signs
    have hp: deckQ t ⟨(i,j),u⟩ ⊆ cartO x d:=by
       intro X a; simp [deckQ,square_corners] at a; rcases a with rfl|rfl|rfl|rfl; exact hi _ _ g; rw [show t+step i=Pan x d (k+step i) from (by rw [step_D,if_pos g])]; exact hi _ _ ((turn_D x k d i j (ne_of_lt u)).2 h); exact hi _ _ h; exact R
    exact p t _ hp -- tune simp
 intro i j; rcases lt_trichotomy i j with h|rfl|h; exact he _ _ h; exact sub_self _; exact sub_eq_zero.mpr (sub_eq_zero.mp (he _ _ h)).symm
lemma getprim {d:ℕ}(V:Wheel Axis E)(p:∀ i:Cover,∀ p:PlaqAxes,deckQ i p⊆cartO x d→CurlMap V p.val.1 p.val.2 i=0):∃ f: Cover→E,∀ (i:Cover)(j:Axis), i∈cartO x d→i+step j∈cartO x d→f (i+step j)-f i=V j i:=by
 obtain ⟨T',q⟩:= FlightFlux.grainP (slide_D x d V) (root_B x d V p); refine ⟨T',fun i j h v=>?_⟩; exact (congrFun (q j) i).trans (by rw [slide_D,if_pos (inch_D _ _ _ h v),pan_id x i h]) -- tune
variable {x}
open Exterior Work.F03
abbrev Mount (V:tangD n): Wheel Axis SU.group.Color:=fun i j=>V (wrap (More n) j,i)
def toga(f:Face (Per (More n))): tangD n→L[ℝ] SU.group.Color:= by
 refine LinearMap.toContinuousLinearMap (show tangD n→ₗ[ℝ] SU.group.Color from {toFun:=fun x=> faceCurl f (mapCo x),map_add':=fun x y=>?_,map_smul':=fun r i=>?_})
 · ext a; unfold faceCurl dColor; dsimp only; let Q:= plaquette f.2; change (Exterior.d 1 _ *ᵥ (Exterior.parts _ 1 _ a)) (f.1,Q)=(Exterior.d 1 (More n) *ᵥ _) (f.1,Q)+(Exterior.d 1 (More n) *ᵥ _) (f.1,Q) -- tune
   rw [show Exterior.parts SU.group 1 (mapCo (x+y)) a=Exterior.parts _ 1 (mapCo x) a+Exterior.parts _ 1 (mapCo y) a from rfl,Matrix.mulVec_add]; rfl
 ext j; unfold faceCurl dColor; dsimp only; change (Exterior.d 1 _ *ᵥ (r • Exterior.parts GS 1 (mapCo i) j)) _=r • _; rw [Matrix.mulVec_smul]; rfl -- holes
lemma map_U (V:tangD n)(x:Cover)(p:PlaqAxes): toga (wrap (More n) x,p) V= CurlMap (Mount V) p.val.1 p.val.2 x:=by
 change faceCurl (wrap (More n) x,p) _ =_; ext j; unfold faceCurl dColor; dsimp only; change (Exterior.d 1 (More n)*ᵥ Exterior.parts SU.group 1 (mapCo V) j) _=_; rw [d_plaquettes]; unfold Exterior.parts mapCo; simp only [←coord_map,Equiv.symm_apply_apply]; unfold CurlMap FlightFlux.advance; -- want rw
 simp only [Pi.sub_apply,Mount,map_add, show ∀ i:Axis, Pi.single (M:=fun _=>ℤ) i 1 = step i from fun _=>rfl,wrap_step]; rfl
abbrev platesX (Y:Support (More n)):=univ.filter fun j:Face (Per (More n))=>touched j⊆Y
lemma TornE {Y:Cover}{V:tangD n} (w:d+1<n.val)(p:∀ j∈ platesX (knotX Y d n),toga j V=0): ∃ g:Seat n→ SU.group.Color,Agrees (knotX Y d n) V (AnalyticBridge.VerifiedReset.gradient g):=by
 let Z:=knotX Y d n; have hk:∀ i:Cover,∀ p':PlaqAxes,deckQ i p'⊆cartO Y d→CurlMap (Mount V) p'.val.1 p'.val.2 i=0:=by
    intro i p' h; rw [← map_U]; apply p; apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; rw [touchK,←cart_T (show d<n.val by omega)]; exact image_subset_image h -- rewrite goal tune
 obtain ⟨f,h⟩:=getprim (d:=d) Y (Mount V) hk
 let τs (k: Seat n):=prospect Y k; refine ⟨(f ∘ τs),?_⟩; rintro ⟨i,t⟩ a b; have he:τs (i+step t)=τs i+step t:= prospect_Q w i t a
 change V (i,t)= f (τs (i+step t))- f (τs i); rw [he,h (τs i) t ((prospect_R _).2 a) (he ▸ (prospect_R _).2 b),Mount,show wrap (More n) (τs i)=_ from prospect_eta ..]
end ArtCart
end MastTin
end YM.CF.XGarden
end
