import YM.SU5.Relativistic.AllErected
import YM.SU5.Relativistic.RopePlace
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f

namespace Lariat
include t
def scoreCard (T:ℕ→Bool→Family (tent Y H) → Family (tent Y H))(s:ℕ)(z:ℤ)(f g:Lariat (tent Y H) n):ℂ := if hue f=hue g then ψ (s+n) (Reflect.chord (hue f) • rideL Y H T s (glueWord (turned Λ j (gaugeShift Λ.block z) f) g)) else 0 -- add T explicit as just λ implicits Lean
lemma sameBill {f g: Lariat (tent Y H) n} {s z}(a:f.hue=g.hue)(t':f.ordains (Λ:=Λ) l s j (μ z))(p:g.ordains (Λ:=Λ) l s j (μ z)): scoreCard Y H D G d j c x T s z f g= ψ (s+n) (Reflect.chord (hue f) • (mirror K j (planeAt (μ z) Λ.R.L n) (E₀ s f) * (E₀ s g))):=by
 rw [scoreCard,if_pos a,braided Y H V G.history u T t s _ _ (costsOpposed Y H j _ s t' p),drawFlip Y H V G.history u T t s] -- include
include t
lemma uniformFaces {J:Type*}[Fintype J](n s:ℕ)(z:ℤ)(f:J→Lariat (tent Y H) n)(q:∀ i,ordains (Λ:=Λ) l s j (gaugeShift Λ.block z) (f i)): Matrix.PosSemidef (Matrix.of fun i k=> scoreCard Y H D G d j c x T s z (f i) (f k)):=by
 let U:= fun i=> hue (f i)
 let A(i:J):= rideL Y H T s (f i); have Hs(i:J):=aboard Y H u T t s (f i)
 let Ζ:= (Λ.R.L.val:ℤ)^n*z; let Z:= μ z
 have he: planeAt Z Λ.R.L n = μ Ζ := by unfold planeAt Z Heat.gaugeShift Ζ; ring
 have hp(i:J):Tower.region j (μ Ζ) (K).ℓ (box Λ l (f i)):= he ▸ placedRoom Y H s _ (q i) -- check p args
 let C (b:Bool) (i:J) := if U i=b then A i else 0
 let M (b:Bool): Matrix J J ℂ:= Matrix.of fun i k=> ψ (s+n) (Reflect.chord b • (mirror K j (gaugeShift Λ.block Ζ) (C b i) * C b k))
 have hK(v:Bool): (M v).PosSemidef:=by
    refine erected Y H D G u t d j c x (s+n) Ζ _ (fun i=> ⟨box Λ l (f i),?_,hp i⟩)
    change InTest K true _ v (C v i); unfold C; split_ifs with g; · exact g ▸ Hs i
    exact InTest.zero
 let N:= M false+M true
 suffices h:(Matrix.of fun i k=> scoreCard Y H D G d j c x T s z (f i) (f k))=N by rw [h]; exact (hK false).add (hK true)
 have hZ: ψ (s+n) 0=0:= (audition Y H V G d c (SameCharacter.resident Y H V G d false (c d) x) _).map_zero
 have hz: mirror K j (μ Ζ) 0=0:=funext fun _=>funext fun _=> Fock.theta_zero _
 ext i k; simp only [N, Matrix.of_apply, Matrix.add_apply]; by_cases v:U i=U k
 · rw [sameBill Y H D G u t d j c x v (q i) (q k), he]
   change ψ _ (Reflect.chord (U i) • (mirror K j (μ Ζ) (A i)*A k))= _
   dsimp only [M,Matrix.of_apply]
   cases g:U k <;> simp only [C,v,g, hz, mul_zero, ite_true,Bool.false_eq_true, Bool.true_eq_false,ite_false,not_false_eq_true, smul_zero, hZ, zero_add,add_zero]
 unfold scoreCard; rw [if_neg v]
 have hx(b:Bool): M b i k=0:=by
    change ψ _ (Reflect.chord b • _)=_
    by_cases t: U k=b
    · have hP: C b i=0:= if_neg fun h=>v (h.trans t.symm)
      change ψ _ (Reflect.chord b • (mirror _ _ _ (C b i)*_))= _
      rw [hP,hz,zero_mul,smul_zero,hZ]
    have hz:C b k=0:= if_neg t
    change ψ _ (Reflect.chord b • (mirror _ _ _ (C b i)*C b k))= _; rw [hz,mul_zero,smul_zero,hZ]
 rw [hx,hx,zero_add]
end Lariat

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
