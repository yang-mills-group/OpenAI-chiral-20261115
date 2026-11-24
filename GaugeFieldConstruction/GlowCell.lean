import GaugeFieldConstruction.MeridianCell
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Cauchy Row Phys Mink Function Set Filter Matrix Complex
open scoped Matrix Matrix.Norms.Frobenius Kronecker BigOperators Topology ContDiff
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
lemma groundRoundL (A:Ortho)(h:Lorentz.spatialTurn A):Lorentz.spatialTurn A⁻¹:=by
 constructor
 · have hz:= parkAxisL A h; change LinearMap.det (Matrix.toEuclideanLin _)=1; rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]; change Matrix.det (star A.val)=1; rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,hz]; rfl
 intro a; simpa using (h.2 (Ortho.move A⁻¹ a)).symm
lemma GroundRoomBackL (A:Ortho)(h:Lorentz.spatialTurn A): (Lorentz.room A h)⁻¹= Lorentz.room A⁻¹ (groundRoundL A h):=Lorentz.ext _ _ fun _=>rfl
abbrev γBeamL(a:SpaceAxis)(t):=(Ray.fromAxis a).boost t
-- induction over spacetime group. arbitrary boost by closure with spatial transport.
theorem SeenLorL {p:Lorentz→Prop}(i:Lorentz)(e:p 1)(h:∀ i j,p i→p j→p (i*j)) (z:∀ K g,p (Lorentz.room K g)) (g:∀ a b,p (γBeamL a b)): p i := by
 have u:i∈YM.Bid.beamGens:=by rw [YM.Work.A16.answer]; trivial
 refine Subgroup.closure_induction (p:=fun x _=> p x ∧ p x⁻¹) ?_ (by simpa using e) ?_ (fun i _ v=>by simp; exact v.symm) u |>.1
 · rintro _ (⟨A,L,rfl⟩|⟨a,t,rfl⟩)
   · rw[GroundRoomBackL]; exact ⟨z A L,z _ _⟩
   rw[Ray.boost_neg]; exact ⟨g _ _,g a (-t)⟩
 intro i j _ _ x v; rw [_root_.mul_inv_rev]; exact ⟨h _ _ x.1 v.1,h _ _ v.2 x.2⟩
section
variable {H:Type*} [AddCommGroup H][Module ℂ H]
lemma ovalL (A:Lorentz→* Module.End ℂ H) (β:SpaceAxis→ Module.End ℂ H) (a:SpaceAxis)
    (p:∀ x,Sends (fun t=>A (γBeamL a t) x) 0 (β a x)) (x) t: Sends (fun i=> A (γBeamL a i) x) t (β a (A (γBeamL a t) x)):= by
  intro L; let R r:=A (γBeamL a r); let y:= R t x; let G:=fun r=>L (R r y)
  have he s : G (s-t)=L (R s x) := by unfold G y R γBeamL; rw [← Module.End.mul_apply, ← map_mul,← Ray.boost_add,sub_add_cancel]
  suffices T: HasDerivAt (fun s:ℝ=>G (s-t)) (L (β a y)) t by simp_rw [he] at T; exact T
  have H : HasDerivAt G (L (β a y)) (t-t):= by rw [sub_self]; exact p y L
  have he:= H.scomp t (h:=fun z : ℝ=> z-t) ((hasDerivAt_id' t).sub_const t); exact he.congr_deriv (by simp)
end
namespace Cell
variable {P:Cell α}
variable (X: Meridian P)

def codeL(B:C4L α): Module.End ℂ (J α):= jet fun a=>∑ i:α, B i a • ket i
lemma onL (B:C4L α) (i j): codeL B (ket i) j=B j i:=by rw [codeL,on_ket]; simp [Finsupp.finsetSum_apply,ket,Finsupp.single_apply]
lemma code1L : codeL (1:C4L α)=LinearMap.id:= ket_ext fun i=>by ext1 j; rw[onL]; simp [Matrix.one_apply,Finsupp.single_apply,ket,eq_comm]
lemma code2L (A B:C4L α): codeL A*codeL B=codeL (A*B):=by
 apply ket_ext; intro x; rw [Module.End.mul_apply]
 ext1 i; nth_rw 2 [codeL]; rw [on_ket,map_sum]; simp only [map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,onL,smul_eq_mul]; rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
def rideL: Lorentz→* Module.End ℂ (J α) where
 toFun a:= codeL (X.sheet a)
 map_one':=by rw[map_one, code1L]; rfl
 map_mul' a b:=by rw[map_mul]; exact (code2L _ _).symm
lemma IdleRideL (A:Ortho)(p):rideL X (Lorentz.room A p) = P.rotate A:=by
 apply ket_ext; intro i; ext1 k
 change codeL _ _ _=bill _ _ _; rw [onL, entry]; exact X.park A _ _ _
lemma CoatRideL (x)(T:J α→ₗ[ℂ]ℂ) : Continuous fun a:Lorentz=>T (rideL X a x):= by
 have h i : Continuous (fun a:Lorentz=>T (rideL X a (ket i))) := by
    simp only [rideL,MonoidHom.coe_mk,OneHom.coe_mk,codeL,on_ket,map_sum,map_smul,smul_eq_mul]
    exact continuous_finsetSum _ fun j _=> (X.tilts j i).mul continuous_const
 induction x using Finsupp.induction_linear with
 | zero=> simp only [map_zero]; exact continuous_const
 | add x y a b=>simp only [map_add]; exact a.add b
 | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket]]; simp only [map_smul,smul_eq_mul]; exact continuous_const.mul (h i)
abbrev NightL (P:Cell α) (a:SpaceAxis):= (-I) • beta P (pVecΩL a)
lemma sparksL (a:SpaceAxis)(x): Sends (fun t=> rideL X (γBeamL a t) x) 0 (NightL P a x):= by
 intro L
 have h i:HasDerivAt (fun t=>L (rideL X (γBeamL a t) (ket i))) (L (NightL P a (ket i))) 0:=by
     simp only [rideL,MonoidHom.coe_mk,OneHom.coe_mk,NightL,beta,codeL,bill, LinearMap.smul_apply,on_ket, map_smul,map_sum, Finset.smul_sum,smul_smul]
     exact HasDerivAt.fun_sum fun j _=> (X.spark a j i).smul_const _ -- ℂ cont smul ring
 induction x using Finsupp.induction_linear with
 | zero=> simp only [Function.comp_def,map_zero]; exact hasDerivAt_const _ _
 | add x y a b=>simp only [Function.comp_def,map_add]; exact a.add b
 | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket]]; simp only [Function.comp_def,map_smul,smul_eq_mul]; exact (h i).const_mul t
lemma ovalRideL (a: SpaceAxis)(x)(t):Sends (fun u=>rideL X (γBeamL a u) x) t (NightL P a (rideL X (γBeamL a t) x)) :=ovalL _ _ a (sparksL X a) x t
end Cell

namespace Angles
open Cell Calibration RawBank
variable {β ξ:Type*} {R:Record β ξ} {F:Conj.Flip β} {H:Submodule ℂ (J β)} (B:Mint R H F α) (P:Cell α)(X:Meridian P)(p: ∀ x : J α,B.issue x=0 → ∀ Ω,B.issue (P.beta Ω x)=0)
local instance iGGL : AddCommGroup ↥H:= @Submodule.addCommGroup ℂ (J β) _ _ _ _
variable (f : Module.Finite ℂ H)
include p f
abbrev γσL (B: Mint R H F α)(P:Cell α)(a:SpaceAxis): Module.End ℂ H:= (-I) • Mint.spin B P (pVecΩL a)
lemma SunsetL (s:Lorentz)(x)(z:B.issue x=0): B.issue (rideL X s x)=0:= by
 suffices ψ:∀ x, B.issue x=0→B.issue (rideL X s x)=0 from ψ _ z
 apply SeenLorL s
 · intro x v; rw [map_one,Module.End.one_apply,v]
 · intro i j v w x z; rw [map_mul,Module.End.mul_apply]; exact v _ (w _ z)
 · intro A L x z; rw [IdleRideL]; exact grace B P p f A ((parkLorL A L).property) x z
 intro a t x z; let u(i:ℝ):= B.issue (rideL X (γBeamL a i) x)
 have he(i) : Sends u i (γσL B P a (u i)) := by
    have h:=posts (ovalRideL X a x i) B.issue
    simp only [γσL,LinearMap.smul_apply,Mint.click B P p,u]; simp only [NightL,LinearMap.smul_apply,map_smul] at h; exact h
 have hz:u 0=0:=by unfold u γBeamL; rw [Ray.boost_start,map_one,Module.End.one_apply,z]
 exact congr_fun (confined u he hz) t
omit f p in
def boardL (s:Lorentz): Module.End ℂ H:= B.issue ∘ₗ rideL X s ∘ₗ B.protrude
lemma luteL (s:Lorentz) (v): boardL B P X s (B.issue v)= B.issue (rideL X s v):=by
 let c := B.protrude (B.issue v)
 have hc:B.issue (c-v)=0 := by rw [map_sub]; rw [show B.issue c=B.issue v from LinearMap.congr_fun (show B.issue ∘ₗ B.protrude=LinearMap.id from Classical.choose_spec (Mint.bend B)) _,sub_self]
 have H:= SunsetL B P X p f s _ hc; rw [map_sub,map_sub,sub_eq_zero] at H; exact H
def jetMeridianL : Lorentz→* Module.End ℂ H where
 toFun:= boardL B P X
 map_one':=by
    apply LinearMap.ext; intro x; obtain ⟨v,rfl⟩:= B.supply x; rw [luteL B P X p f, map_one, Module.End.one_apply]; rfl
 map_mul' a b:=by
    apply LinearMap.ext; intro x; obtain ⟨v,rfl⟩:= B.supply x; rw [Module.End.mul_apply]; simp_rw [luteL B P X p f,map_mul]; rfl
lemma jewelL (i s): jetMeridianL B P X p f s (B.issue i) = B.issue (rideL X s i):= luteL B P X p f s i
lemma padlockL (A:Ortho)(h:Lorentz.spatialTurn A): jetMeridianL B P X p f (Lorentz.room A h)= repr B P p f (parkLorL A h):=LinearMap.ext fun v=> by obtain ⟨i,rfl⟩:=B.supply v; rw [jewelL,bOut,IdleRideL]
lemma distendL (v : H)(L:H→ₗ[ℂ]ℂ):Continuous fun a:Lorentz=>L (jetMeridianL B P X p f a v):=by obtain ⟨i,rfl⟩:=B.supply v; simp_rw [jewelL]; exact CoatRideL X i (L ∘ₗ B.issue)
lemma spikeL (a:SpaceAxis)(v : H): Sends (fun t=> jetMeridianL B P X p f (γBeamL a t) v) 0 (γσL B P a v):=by
 obtain ⟨i,rfl⟩:= B.supply v; simp_rw [jewelL]; have h:=posts (sparksL X a i) B.issue; simp only [γσL,LinearMap.smul_apply,Mint.click B P p]; simp only [NightL,LinearMap.smul_apply,map_smul] at h; exact h
#print axioms jetMeridianL
#print axioms spikeL
end Angles
end YM.GaugeFieldConstruction.Stage
