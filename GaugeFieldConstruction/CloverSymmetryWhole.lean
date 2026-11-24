import GaugeFieldConstruction.CloverSymmetryVerdict
import GaugeFieldConstruction.CeriseGaugeVU
/-!
 # Full basic obstruction. Gives it on the *whole two-clover tensor sector* and any LowInc,
 already in the strict-E analysis & after reconstruction. Does not assert mark budget for every
 operator in that basis or after these rotations. Main application: at chosen `ΩPureVU` with paid budgets.
 -/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 15000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars.CloverRule
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD YM.CF.XGarden.MastTin.ArtCart.BluffV.Fables
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
open Stage.CloverSymmetry
variable (p:Ticket u C)
variable (U:FreeName four) (V Y:UV four)
abbrev Wed03_st:= Wed.mk 0 3 (by decide)
abbrev Wed12_st:= Wed.mk 1 2 (by decide)
abbrev SecondΩ_st := BathJetVU Wg01VU+BathJetVU Wg23VU-(BathJetVU Wed03_st+BathJetVU Wed12_st)
abbrev axisRollC_st : Signed := ⟨⟨![0,1,3,2],![0,1,3,2],by intro i;fin_cases i<;>rfl,by intro i;fin_cases i<;>rfl⟩, ![false,false,true,false]⟩
lemma hRollC_st : signBit axisRollC_st=false:=by decide
lemma hMoveC_st : signBit move_l=false:=by decide
lemma otherCornerSt : spinFrame four axisRollC_st ΩPureVU=SecondΩ_st:=by
 unfold ΩPureVU SecondΩ_st; rw [map_sub,map_add,map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU,
     show wedAct.move axisRollC_st Wg01VU=Wg01VU from (by decide),show wedAct.move axisRollC_st Wg23VU=Wg23VU from (by decide),show wedAct.move axisRollC_st Wg02VU=Wed03_st from (by decide),show wedAct.move axisRollC_st Wg13VU= Wed12_st from (by decide)]
lemma signedFirstSt : spinFrame four move_l ΩPureVU = - ΩPureVU:=by
    unfold ΩPureVU; rw [map_sub,map_add, map_add,φPassTurnVU,φPassTurnVU,φPassTurnVU,φPassTurnVU,show wedAct.move move_l Wg01VU=Wg02VU from (by decide),show wedAct.move move_l Wg23VU=Wg13VU from (by decide),show wedAct.move move_l Wg02VU=Wg01VU from (by decide),show wedAct.move move_l Wg13VU=Wg23VU from (by decide)]; abel
local notation "v" => ΩPureVU
local notation "u'" => SecondΩ_st
lemma corner_st : feat ΩPureVU=(64:ℕ) • ΩPureVU:= vFieldFeatVU
abbrev tensorC_st := Submodule.span ℂ ({ΩPureVU,SecondΩ_st}:Set (UV four))
lemma postpaid_omega_st (h:V∈tensorC_st): ∃ x∈ orbitSpin2, payFrame p x=U.c V:=by
 obtain ⟨z,hz,k⟩:= origin_cost_st p U corner_st
 let f:= (payFrame p).toLinearMap; let R:= orbitSpin2.map f
 suffices h: U.c V∈ R from h
 apply Submodule.span_induction (p:=fun V _=>U.c V∈ R) _ _ _ _ h
 · rintro w  (y₁|q) -- bad h name
   · rw [y₁]; exact ⟨z,hz,k⟩
   rw [Set.mem_singleton_iff.mp q,← otherCornerSt]
   rw [U.h]
   let s:= signMot axisRollC_st hRollC_st; refine ⟨ledger All four s z,keepRotation s hz,?_⟩
   change (payFrame _) _ = _; rw [←journeyCharge, k,PiProperMoon]
 · rw[map_zero]; exact R.zero_mem
 · intro i j _ _ x y; rw [map_add]; exact R.add_mem x y
 intro u x _ h; rw [map_smul]; exact R.smul_mem _ h
lemma fittedTurn_st (j:Axis)(X:UV three): spinFrame four (Signed.mirror j) (Calibration.shade four (LowIncPV X))= LowIncPV (spinFrame three (Signed.mirror j) (Calibration.shade three X)):= by
 have h(d)(x:UV d): Calibration.lift d (Calibration.shade d x)=Calibration.shade five (Calibration.lift d x):= rfl
 apply Calibration.inject four; rw [spin_lift,LowFivePV,spin_lift,h,h,LowFivePV]
variable {Q B:CloudsL}{Shed:SurfCheckL Q}{Y:Wightman (SurfRimL Q)}(T:SurfCheckL B)
variable {W: NSF.Boundary.Surface (SurfRimL Q)} {j:(SurfRimL Q).RealSpin}{R:(SurfRimL Q).Rotation} {F:NSF.Boundary.Waves (SurfRimL Q)} {N: NSF.Boundary.Surface.Aurora W NSF.LD.drapeL}
variable (X: SurfCheckL.boisterL p B)
local notation "Sl"=> inGloomSt (N:=N) Shed B
include T X
lemma fullLock_st (h:V∈tensorC_st)(Z:UV three)(u:F.Region (SurfRimL B))(a:F.NonTangentialFree W)(q:N.FullBody F): (Sl) (U.c V) (LowIncPV Z) ∧ (Sl) (LowIncPV Z) (U.c V):=by
 obtain ⟨l,b,e⟩:= postpaid_omega_st p U _ h; obtain ⟨x,d⟩:=viaCost_st p Z; rw[←e,d]
 have j(k:Points 2)(c:k∈conf 2): sepCost B k (payFrame p l) (payFrame p (LowIncPV x)) = 0:= strictCost p B T X k c b x
 have p'(A H)(t:∀ k∈conf 2, sepCost B k A H=0): Sl A H:= ⟨t,fun x h=> zeroPad B T Shed u q _ t x h,zeroDistrib B T Shed u a q _ t⟩
 exact ⟨p' _ _ j,p' _ _ (sepExchange B T _ _ j)⟩
private lemma chargeOne_st (A:ΧiMars)(R:Signed)(s:signBit R=false)(x:Points 1)(h:x∈conf 1) : B 1 (motionMoonMars (signMot R s) x) ![spinFrame four R A]=B 1 x ![A]:=by
 have he:= X 1 ![A] x h (signMot R s); rw [show compassPiMars _ _ ∘ ![A] = ![spinFrame four R A] from ?_] at he; exact he; ext1 i; fin_cases i; exact PiProperMoon p _ s A
private noncomputable abbrev soh (B:CloudsL) (p:Points 1) : UV four →ₗ[ℂ] ℂ:= (B 1 p).toLinearMap ![0] 0
omit X T in
private lemma sohCost (p:Points 1) (x:UV four): soh B p x=B 1 p ![x]:=by rw [soh,MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i; simp
lemma fullFirst_st(h:V∈tensorC_st)(x:Points 1): B 1 x ![U.c V]=0:=by
 let L:=soh B (0:Points 1)
 have h₁: (0:Points 1)∈conf 1:= fun i j _=>Subsingleton.elim ..
 have g(z)(R:Signed)(e:signBit R=false): L (U.c (spinFrame four R z))= L (U.c z):=by
    unfold L; rw [U.h,sohCost,sohCost]; have he:=chargeOne_st p T X (U.c z) R e _ h₁; rw [show motionMoonMars _ (0:Points 1) = 0 from by apply PiLp.ext; intro t; exact map_zero ((signMot R e).val.motion)] at he; exact he
 have hv:L (U.c ΩPureVU) =0:=by
    have ht:= g v move_l hMoveC_st; rw [signedFirstSt,map_neg,map_neg] at ht; exact neg_eq_self.mp ht
 have he: B 1 (0:Points 1) ![U.c V]= B 1 x ![U.c V] :=by
    have he : NSF.Points.across (x 0) (0:Points 1)=x:=by
       ext1 i; fin_cases i; exact zero_add _
    have hp:= T.even (x 0) ![U.c V] 0 h₁; rw [he] at hp; exact hp.symm
 rw [← he,← sohCost]
 change L _=0; apply Submodule.span_induction (p:=fun w _=> L (U.c w)=0) _ _ _ _ h
 · intro z hz; rcases Set.mem_insert_iff.mp hz with p|q
   · rw[p,hv]
   rw[Set.mem_singleton_iff.mp q,←otherCornerSt,g _ _ hRollC_st,hv]
 · rw [map_zero,map_zero]
 · intro x y _ _ u z; rw [map_add,map_add,u,z,add_zero]
 intro t x _ p; rw[map_smul,map_smul,p,smul_zero] -- note v token conflict.
#print axioms fullLock_st
#print axioms fullFirst_st
end FirstPackMars.CloverRule
end YM.GaugeFieldConstruction.Ember.Volumetric
end
