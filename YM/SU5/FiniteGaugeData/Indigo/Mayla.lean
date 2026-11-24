import YM.SU5.FiniteGaugeData.Indigo.LicenseE
import YM.SU5.FiniteGaugeData.Indigo.Tuvalu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
variable (R:Patch)
open CF.Indigo
namespace SpineV
open YM.SU5.FiniteGaugeData.Lapis Lumi
open LapisS LapisS.Stadium
open Chiffon.Prato
open YM.SU5.FiniteGaugeData.Indigo Taper
open Fock
namespace Licor
namespace Lychee
variable (R:Patch)(x:Cover)(t:ℝ)
open YM.SU5.FiniteGaugeData.LapisQ Nectar
local notation "V"=> SU.group.Color
abbrev XiCore := Option (Fin 4)
local notation "E"=> XiCore→ SU.group.Color -- not in signatures
abbrev Beryl (x: XiCore→ SU.group.Color):= Obl (fun i=> x (some i))
noncomputable abbrev Shekel : (XiCore→SU.group.Color)→L[ℝ] SU.group.Color:= (show (XiCore→SU.group.Color)→ₗ[ℝ] SU.group.Color from { toFun:=Beryl,map_add':=fun x y=>by unfold Beryl Obl; simp only [Pi.add_apply]; abel,map_smul':=fun x y=>by unfold Beryl Obl; simp only [Pi.smul_apply,smul_add]; rfl }).toContinuousLinearMap
noncomputable abbrev August (x:Cover)(i:XiCore):RG.Slot:= i.elim (sprinkle x Nest) lyre
noncomputable abbrev near_p (t:ℝ)(F:XiCore→SU.group.Color):= roseM t (Shekel F)
noncomputable abbrev far_p (t:ℝ)(F:XiCore→SU.group.Color):= roseM t (F none)
variable (h:0<t)
include h
noncomputable def Korn : Lumi.Duct SU.group XiCore where
 beam:= August x
 seen:= near_p t
 registered:= (rose_C t).comp Shekel.contDiff
 c:= (t⁻¹*tease t)*‖Shekel‖
 h:= t⁻¹
 grant:=by unfold tease; positivity
 charge:=by positivity
 enough X:=by rw [Real.norm_of_nonneg (vitaM t h (sq_nonneg _))]; exact vivid t h (sq_nonneg _)
 cheer X Y:=by
    have he:0 ≤ tease t:=Real.sqrt_nonneg _; exact (lips₁ (Shekel X) (Shekel Y) t h).trans ((mul_le_mul_of_nonneg_left (show ‖Shekel X-Shekel Y‖ ≤ ‖Shekel‖*‖X-Y‖ from (by rw [←map_sub]; exact Shekel.le_opNorm _)) (show 0≤t⁻¹*tease t from by positivity)).trans_eq (by ring))
 orbs u X:=by
    let I:= SU.group.adjoint u; unfold near_p; change velum t _ = _; have ht:Shekel (fun i=> I (X i))=I (Shekel X):=by change I _+ (I _+(I _+I _))=I (_+(_+(_+_))); simp only [map_add]
    rw [ht,SU.group.norm_adjoint] -- tune rw I reducible
noncomputable def Kayak : Lumi.Duct SU.group XiCore where
 beam:= August x
 seen:= far_p t
 registered:= (rose_C t).comp (contDiff_apply ℝ _ none)
 c:= t⁻¹ * tease t
 h:= t⁻¹
 charge:=by positivity
 grant:=by unfold tease; positivity
 enough X:=by rw [Real.norm_of_nonneg (vitaM t h (sq_nonneg _))]; exact vivid t h (sq_nonneg _)
 cheer X Y:= (lips₁ _ _ t h).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (X-Y) none) (by unfold tease; positivity))
 orbs u X:=by unfold far_p roseM; rw [SU.group.norm_adjoint]
noncomputable def Karve {ι:Type}[Fintype ι] (A B:Lumi.Duct SU.group ι)(q:A.beam=B.beam): Lumi.Duct SU.group ι where -- unused h.K.
 beam:= A.beam
 seen x:=A.seen x*B.seen x
 registered:= A.registered.mul B.registered
 c:=A.h*B.c+A.c*B.h
 h:=A.h*B.h
 charge:=mul_nonneg A.charge B.charge
 grant:=add_nonneg (mul_nonneg A.charge B.grant) (mul_nonneg A.grant B.charge)
 enough X:= (norm_mul ..).trans_le (mul_le_mul (A.enough X) (B.enough X) (norm_nonneg _) A.charge)
 cheer X Y:=by
    let f:= A.seen; let g:= B.seen; let D:= ‖X-Y‖; have hx:0 ≤ A.c*D:= mul_nonneg A.grant (norm_nonneg _); change |f X*g X-f Y*g Y| ≤ _; rw [show f X*g X-f Y*g Y=f X*(g X-g Y)+(f X-f Y)*g Y from (by ring)]
    apply (abs_add_le ..).trans; rw [abs_mul,abs_mul]; refine (add_le_add (mul_le_mul (show |f X|≤_ from A.enough X) (B.cheer X Y) (abs_nonneg _) A.charge) (mul_le_mul (A.cheer X Y) (B.enough Y) (abs_nonneg _) hx)).trans_eq ?_; ring
 orbs u X:= by rw [A.orbs,B.orbs]
-- h unused likely included only in lemmas; for defs Lean variables ignored! especially Korn.h h used via proof need elaboration? yes h positive from field. Karve h not.
noncomputable abbrev Nirv:= Karve (Korn x t h) (Kayak x t h) rfl
-- radius declarations; far motif raw pure. root η(p). single.
local notation "η"=> nodeC (specialM R.L)
local notation "p★"=> x+η
noncomputable abbrev rail_N (t:ℝ)(A:Fin 4→ SU.group.Color):ℝ:= roseM t (Obl A)
noncomputable abbrev rail_F (t:ℝ)(A:Unit→SU.group.Color):ℝ := roseM t (A ())
lemma rimN:Lariat (Fin 4) (rail_N t):=by
 refine ⟨?_,fun u A=>?_⟩; · unfold rail_N; exact (rose_a t).comp (show Continuous Obl from (by unfold Obl; fun_prop))
 unfold rail_N Obl roseM; simp only [← map_add, SU.group.norm_adjoint]
lemma rimD : Lariat Unit (rail_F t):=⟨(rose_a t).comp (continuous_apply (A:=fun _:Unit=> SU.group.Color) ()), fun u x=>by unfold rail_F roseM; rw [SU.group.norm_adjoint]⟩
abbrev Kilt : RG.Slot:=⟨[],Nest⟩
abbrev Halo := rimS (fun _:Unit=> Kilt) (x+nodeC (specialM R.L))
variable (K:Calibration)(α r:ℝ)
noncomputable abbrev Neo (R:Patch)(t:ℝ)(h:0<t)(K:Calibration)(r:ℝ):= suede lyre (nodeC (specialM R.L)) (rail_N t) (rimN t h) K r
noncomputable abbrev Lum (R:Patch)(x: Cover)(t:ℝ)(h:0<t)(K:Calibration)(r:ℝ):= suede (fun _:Unit=> Kilt) (x+nodeC (specialM R.L)) (rail_F t) (rimD t h) K r
local notation "φ"=> Neo R t h K r
local notation "γ"=> Lum R x t h K r
lemma shek : suede (August x) (η) (near_p t) (unitL (Korn x t h)) K r= Neo R t h K r:=by
 apply Subtype.ext; funext m A; let X:= onC (K.c m) A.1; rw [suede_read,Neo,suede_read]; unfold cladF
 change _=_; congr 2; -- likely defeq rfl
private lemma wallTravel(U:LinksC): ‖(sprinkle x Nest).eval (G:=SU.group) (Lattice.translate (nodeC (specialM R.L)) U)‖= ‖SU.group.curvature (faceValue U (x+η,Nest))‖:=by
 unfold RG.Slot.eval; rw [SU.group.norm_adjoint]; unfold faceValue; rw [translateH,wet]; rfl
lemma eachF(U:LinksC): Shuf (fun _:Unit=> Kilt) (x+nodeC (specialM R.L)) U ()= SU.group.curvature (faceValue U (x+η,Nest)):=by
 unfold Shuf Kilt RG.Slot.eval RG.Slot.offset; simp only [travel,stop,SU.group.adjoint_one]; unfold faceValue; rw [translateH,zero_add]
lemma Loin : suede (August x) (η) (far_p t) (unitL (Kayak x t h)) K r= Lum R x t h K r:=by
 apply Subtype.ext; funext m A; let U:=onC (K.c m) A.1; rw [suede_read,Lum,suede_read]; unfold cladF; congr 2; -- inspect
 unfold far_p rail_F roseM; simp only [Pi.smul_apply,norm_smul]; rw [eachF R x t h]; rw [show ‖Shuf (August x) (η) U none‖= _ from wallTravel R x t h U] -- delta defeq U not rw. 

lemma Karn : suede (August x) (η) (Nirv x t h).seen (unitL (Nirv x t h)) K r= φ*γ:=by
 rw [← show _= Neo R t h K r from shek R x t h K r,←show _=Lum R x t h K r from Loin R x t h K r]; apply Subtype.ext; funext m A; let U:= onC (K.c m) A.1; let z:=r • Shuf (August x) (η) U; change (↑(near_p t z * far_p t z):ℂ) • (1:FC _)= ( ((↑(near_p t z):ℂ)) • (1:FC (Single _))) *(↑(far_p t z):ℂ) • (1:FC _); push_cast; rw [mul_smul,Algebra.smul_mul_assoc,one_mul]
lemma aAura(S:Clip): Stadium.pole (Korn x t h) S r K (nodeC (specialM R.L)) 1= Neo R t h K (r*Real.sqrt S.direct):= Eq.trans (Eq.symm (sheer (August x) (η) (Korn x t h) S K r (by rfl) (unitL _))) (shek R x t h K _)
#print axioms wallTravel
lemma rAura(S:Clip): Stadium.pole (Kayak x t h) S r K (nodeC (specialM R.L)) 1= Lum R x t h K (r*Real.sqrt S.direct):= Eq.trans (Eq.symm (sheer (August x) (η) (Kayak x t h) S K r (by rfl) (unitL _))) (Loin R x t h K _)
lemma pAura(S:Clip): Stadium.pole (Nirv x t h) S r K (nodeC (specialM R.L)) 1= Neo R t h K (r*Real.sqrt S.direct)*Lum R x t h K (r*Real.sqrt S.direct):= Eq.trans (Eq.symm (sheer (August x) (η) (Nirv x t h) S K r (by rfl) (unitL _))) (Karn R x t h K _)
-- explicit meters at all supports.
lemma inkL (m':Side)(y:Fields (K.c m')): (Lum R x t h K r).val m' y=( (↑ (roseM t (r • (SU.group.curvature (faceValue (onC _ y.1) (x+η,Nest))))):ℂ) • 1):=by rw [Lum,suede_read]; unfold cladF rail_F; rw [Pi.smul_apply,eachF R x t h]
lemma inkP (m':Side)(y:Fields (K.c m')): (Neo R t h K r).val m' y=((↑(roseM t (r • (Cy R (onC _ y.1)))):ℂ) • 1):=by rw [Neo,suede_read]; unfold cladF rail_N; rw [rL]
lemma HaloL : Locator K (Lum R x t h K r) (Halo R x):= sup_skin _ _ _ _ _ _
lemma HaloP : Locator K (Neo R t h K r) (rimS lyre (nodeC (specialM R.L))):= sup_skin _ _ _ _ _ _
lemma rareV : RawG K (Lum R x t h K r):= raw_skin (fun _:Unit=> Kilt) _ _ _ _ _
lemma rareR : RawG K (Neo R t h K r):= raw_skin lyre _ _ _ _ _
lemma vaultL : Width K (Lum R x t h K r) t⁻¹:=by intro N x'; rw [inkL,norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_of_nonneg (vitaM t h (sq_nonneg _))]; exact vivid t h (sq_nonneg _)
lemma vaultR : Width K (Neo R t h K r) t⁻¹:=by intro N x'; rw [inkP,norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_of_nonneg (vitaM t h (sq_nonneg _))]; exact vivid t h (sq_nonneg _)
#print axioms pAura
end Lychee
end Licor
end SpineV
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
