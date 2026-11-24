import GaugeFieldConstruction.CometCell
import GaugeFieldConstruction.VitaVenusMars
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Mink Cell
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
local notation "F_ν"=> (p.path.caller four)
local notation "ΤR"=> ledgerL p.dawn.d

def SpheruleL : Lorentz →* Module.End ℂ ΧiMars where
 toFun g:= (F_ν).c.toLinearMap ∘ₗ (ΤR g) ∘ₗ (F_ν).c.symm.toLinearMap
 map_one':=LinearMap.ext fun x=>by simp
 map_mul' a b:=LinearMap.ext fun x=>by rw [Module.End.mul_apply]; simp
lemma SpheruleTravelL (a:Lorentz)(x): SpheruleL p a ((F_ν).c x)=(F_ν).c (ΤR a x):=by unfold SpheruleL; simp
lemma SpheruleParkL (K:Ortho)(h:Lorentz.spatialTurn K): SpheruleL p (Lorentz.room K h)=compassPiMars p (parkLorL K h):= by
 apply LinearMap.ext; intro x; obtain ⟨x,rfl⟩:= (F_ν).c.surjective x; rw [SpheruleTravelL,LedgerBridgeMars]; dsimp only[]; rw [LinearEquiv.symm_apply_apply, punTurnL]
abbrev scorePathL (Ω: Rotors) := p.path.pi Ω four
abbrev ThriveL (a:SpaceAxis) :Module.End ℂ ΧiMars := (-I) • scorePathL p (pVecΩL a)
lemma glowersL (x:ΧiMars)(k:SpaceAxis): Sends (fun t=> SpheruleL p (γBeamL k t) x) 0 (ThriveL p k x):=by
 obtain ⟨x,rfl⟩:= (F_ν).c.surjective x; simp_rw[SpheruleTravelL]; change Sends (fun t=>_) _ ((-I) • ((p.path.pi _ four) ((F_ν).c x))); rw [p.path.turns,←LinearEquiv.map_smul]; exact Stage.posts (Stage.costL _ k x) (F_ν).c.toLinearMap
lemma keepAL (x:ΧiMars)(T: ΧiMars→ₗ[ℂ]ℂ): Continuous fun g=> T (SpheruleL p g x):=by
 obtain ⟨x,rfl⟩:= (F_ν).c.surjective x; simp_rw[SpheruleTravelL]; exact Stage.continL _ x (T ∘ₗ (F_ν).c.toLinearMap)
-- star: commutes with Lorentz. simple on subgroup; use real-time sent
abbrev asterL : ΧiMars →ₛₗ[starRingEnd ℂ] ΧiMars:= spinFrame four (Signed.mirror timeAxis) ∘ₛₗ (Calibration.shade four)
lemma CenterRL (x:E4): Ortho.move (Signed.reflect timeAxis) x=x-(2*time x) • basis timeAxis:=by
 ext i; by_cases p:i=timeAxis
 · rw[p]; simp [time]; ring
 simp [p]
lemma centBasisL (K:Ortho)(h:Lorentz.spatialTurn K): K.motion (basis timeAxis)=basis timeAxis:=PiLp.ext fun i=>by change M4.move _ _ _=_; rw [M4.move_basis, park_crossL K h,basis_eq]
lemma huesOrbitL (K:Ortho)(h:Lorentz.spatialTurn K): HueTurnsMars (Signed.reflect timeAxis) (parkLorL K h)=parkLorL K h:=by
 apply Subtype.ext; change _*K*_ = K
 rw [mul_inv_eq_iff_eq_mul]; apply Ortho.ext; intro x; rw [Ortho.move_mul,Ortho.move_mul,CenterRL,CenterRL]
 change K.motion x- (2*time (K.move x)) • basis _=K.motion (x- _ • _); rw [map_sub, LinearIsometryEquiv.map_smul,centBasisL K h,h.2]
lemma starsParkL (K:Ortho)(h:Lorentz.spatialTurn K)(x:ΧiMars): asterL (SpheruleL p (Lorentz.room K h) x)= SpheruleL p (Lorentz.room K h) (asterL x):=by
 rw [SpheruleParkL p K h]; let U:=compassPiMars p (parkLorL K h); rw [asterL,LinearMap.comp_apply, ← shadePiMoon, DutyPiiotMars,show (Signed.mirror timeAxis).ortho = _ from (@rfl _ (Signed.reflect timeAxis)), huesOrbitL]; rfl
lemma αιL (a:SpaceAxis):conjS (Signed.reflect timeAxis) (pVecΩL a) = -(pVecΩL a):=by
 apply Subtype.ext; ext i j
 change ((Signed.mirror timeAxis).matrix * (pVecΩL a).val * star ((Signed.mirror timeAxis).matrix) : M4) i j= -((pVecΩL a).val i j) -- adjust
 simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply,Matrix.conjTranspose_apply, star_trivial]
 rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
 · by_cases u:i=timeAxis<;> by_cases v:j=timeAxis<;> simp [Signed.matrix_at,pVecΩL,Ortho.plane,Matrix.single,Signed.mirror,u,v,eq_comm]; split_ifs <;> ring
 · intro b _ h; simp [Signed.matrix_at,Signed.mirror,h, Ne.symm h]
 · simp
 · intro b _ h; simp [Signed.matrix_at,Signed.mirror,h, Ne.symm h]
 · simp

lemma pricesLampL (a:SpaceAxis)(x:ΧiMars): asterL (ThriveL p a x)=ThriveL p a (asterL x):=by
 rw [ThriveL, LinearMap.smul_apply,LinearMap.map_smulₛₗ]; change ((star (-I)) • (spinFrame four (Signed.mirror timeAxis) _))=(-I) • (p.path.pi _ four) (spinFrame four _ _)
 rw [show Calibration.shade _ _ =_ from ((p.path.paid (pVecΩL a)).guard p.clarity.canny).soul four x |>.symm, PiiotLieFeelMars, show (Signed.mirror timeAxis).ortho=(Signed.reflect timeAxis) from rfl, αιL]; simp
lemma antiLamL (f:ℝ→ΧiMars)(t)(X)(h:Sends f t X): Sends (fun x=> asterL (f x)) t (asterL X):=by
 intro B; let L' : ΧiMars →ₗ[ℂ]ℂ:={
    toFun z:= star (B (asterL z))
    map_add' z k:= by rw [map_add,map_add,star_add]
    map_smul' x z:= by rw [LinearMap.map_smulₛₗ,map_smul,star_smul]; simp }
 have he: HasDerivAt (L' ∘ f) (L' X) t:= h L'; have hy: HasDerivAt (fun y=> star (L' (f y))) (star (L' X)) t:= Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t he
 change HasDerivAt (fun y=>B _) _ _; simpa [L',Complex.star_def] using hy
lemma balanceL (g:Lorentz): asterL ∘ₛₗ SpheruleL p g=SpheruleL p g ∘ₛₗ asterL:=by
 let U:=SpheruleL p; change asterL ∘ₛₗ U g=U g ∘ₛₗ _; apply Stage.SeenLorL g
 · rw [map_one]; rfl
 · intro i j a b; apply LinearMap.ext; intro x
   have h i j (w:asterL ∘ₛₗ U i=U i ∘ₛₗ asterL): asterL (U i j)=U i (asterL j):= LinearMap.congr_fun w j
   change asterL (U (i*j) x)= U (i*j) (asterL x); rw[map_mul,Module.End.mul_apply,h _ _ a,h _ _ b]; rfl
 · intro K h; apply LinearMap.ext; intro x; exact starsParkL p K h x
 intro a t; apply LinearMap.ext; intro x; let Y:= ThriveL p a; let V u:= U (γBeamL a u)
 have h (i t): Sends (fun t=> V t i) t (Y (V t i)):= ovalL U (ThriveL p) a (fun i=> glowersL p i a) i t
 have hz(i):Sends (fun i=>asterL (V i x)) i (Y (asterL (V i x))):= by
    have h': Sends _ i (asterL (Y (V i x))):= antiLamL _ _ _ (h x i)
    rw[show asterL (Y (V i x))=Y _ from pricesLampL p a (V i x)] at h'; exact h'
 have hy:asterL (V 0 x)=V 0 (asterL x):=by unfold V γBeamL; rw [Ray.boost_start,map_one]; rfl
 exact congr_fun (Stage.captain Y (fun i=> asterL (V i x)) (fun i=> V i (asterL x)) hz (h _) hy) t
#print axioms SpheruleL
#print axioms balanceL
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
