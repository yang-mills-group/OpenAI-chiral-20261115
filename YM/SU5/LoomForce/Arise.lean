import YM.SU5.LoomForce.Burst
import YM.SU5.LoomForce.AbsenceA
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
namespace Sundial
open LitCurrent LitCurrent.Surplus
open Pressure Worth Worth.Pays BProof
open Next.Rank.Spindle
-- physical-in-microscope timelike here. choose x at 0 (wrapped to every n).
local notation "Ξ"=>takenVolume P
local notation "Υ"=>takenCutoff P
open ProbabilityTheory MeasureTheory
variable {φ : ℕ→ℕ}{β : ℕ→ℝ}(C:Pooling P.run (takenVolume P) (takenCutoff P) φ β)
variable (A:ℝ)(u:0<A)
local notation "X" s:max=> hat (Λ).R.L (Λ).x s
local notation "U" s:max => sPow Λ s A
local notation "Pp" s:max => radiusB (X s)
local notation "Γσ" s:max=> Sheds (Pp s)
abbrev pulseFee (A:ℝ)(β:ℕ→ℝ)(s n:ℕ):= crossFee Γ s (takenVolume P n) (takenCutoff P n) (radiusB (hat (Λ).R.L (Λ).x s)) (-(shadowR P A s)) 0 (κFix β s) (sPow P.par s A)
abbrev spectrumIdx:= PlaqAxes × group.ColorIndex
abbrev atIdx{B:ℕ} (s:Sheds B):spectrumIdx:= (s.1.val.2,s.2)
def accepted {B:ℕ}(s t:Sheds B):ℂ:= if atIdx s=atIdx t then (unitReceipt:ℂ) else 0
include u C
-- Uniform nested: before period projection take throughout entire credit batch of radius at sPow.
private lemma tagged (f:ℕ→ℕ)(t:StrictMono f)(a b: ∀ s,Sheds (radiusB (hat P.par.R.L P.par.x (f s))))
    (s₀ t₀:spectrumIdx)(hs:∀ n, atIdx (a n)=s₀)(ht:∀ n,atIdx (b n)=t₀):
    Tendsto (fun x:ℕ×ℕ=> pulseFee P A β (f x.1) (φ x.2) (a x.1) (b x.1)) successive (𝓝 (if s₀=t₀ then (unitReceipt:ℂ) else 0)) :=by
 let m(u):= U (f u); let Z(u n):= matterSide P (f u) (φ n); let R(u:ℕ):= -(shadowR P A (f u))
 have h₀:= P.par.K.width; have h₁:= zero_lt_one.trans_le P.par.V.up
 let S(i):= P.par.V.L.H i; let T (i:ℕ×ℕ):= S ((Γ).uv (takenCutoff P (φ i.2))-f i.1)
 let I:=s₀.1; let J:=t₀.1; let F(i:ℕ):=openSeat true (R i) (a i); let G(i:ℕ):= openSeat false (R i) (b i)
 let K(x:ℕ×ℕ):= magnify (T x) (m x.1) (plaquette I) (plaquette J) (F x.1-G x.1) (More (Z x.1 x.2))
 let g:Gaia := τx
 let XG := Fintype.card group.ColorIndex
 have hx(i):0< m i:=BProof.coin_pos ..
 let z:=sPower_pay Λ u|>.comp t.tendsto_atTop
 have hu := booth_cost P A u f t a b
 have hp:Tendsto (fun x:ℕ×ℕ=> (XG:ℂ)*K x) successive (𝓝 ((XG:ℂ)*specter I J g)):=by
    refine Metric.tendsto_nhds.mpr fun ε e=> eventually_curry_iff.mpr ?_
    filter_upwards [manifold I J (Λ).K.top.clip (Λ).V.W.parcel h₀ h₁ hx z hu taucost (ε/2) (half_pos e) group] with s H
    filter_upwards [(matterSide_grows P (f s)|>.comp C.up.tendsto_atTop).eventually H] with n H
    let h':= P.par.V.L.roof ((Γ).uv (takenCutoff P (φ n))-f s)
    exact (H _ h'.1 (h'.2.1 _)).trans_lt (half_lt_self e) -- defeq K
 haveI:Nontrivial SU.group.Color:=Thera.yet_one.nontrivial_color
 have hk: (↑XG:ℂ)≠0:= by
   have ht:0<group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
   change (↑(Fintype.card (Fin group.lieDim)):ℂ)≠0; rw [Fintype.card_fin]; exact Nat.cast_ne_zero.mpr ht.ne'
 have hf:Tendsto K successive (𝓝 (specter I J g)) := by
    have hs:=hp.const_mul ((XG:ℂ)⁻¹); rw [inv_mul_cancel_left₀ hk] at hs; exact hs.congr fun i=> inv_mul_cancel_left₀ hk _
 let E(x:ℕ×ℕ):= reachCost P.run (f x.1) (takenVolume P (φ x.2)) (takenCutoff P (φ x.2)) (κFix β (f x.1))
 have he:Tendsto (fun i:ℕ×ℕ=> (E i:ℂ)^2) successive (𝓝 1):= by
    let W(x:ℕ×ℕ):=(f x.1,x.2)
    have hv:Tendsto W successive successive:= fun s e=> eventually_curry_iff.mpr (t.tendsto_atTop.eventually (eventually_curry_iff.mp e)) -- tune
    have ht := (((reachesSucc P β C).comp hv).pow 2); rw [one_pow] at ht; exact ht
 let D:= sch (G:=group) s₀.2 t₀.2
 have h:= ((he.mul hf).const_mul (realDir I:ℂ)).const_mul (D:ℂ)
 rw [one_mul,show g=τx from rfl,taxing I J] at h -- g fold?
 have hl: ((D:ℂ)* (if I=J then (unitReceipt:ℂ) else 0))=(if s₀=t₀ then (unitReceipt:ℂ) else 0):=by
    by_cases x:s₀=t₀; · subst t₀; simp [D,sch,I,J]
    rw [if_neg x]; split; next h=> rw [show D=0 from if_neg fun e=> x (Prod.ext h e),Complex.ofReal_zero, zero_mul]
    rw [mul_zero]
 rw [hl] at h; refine h.congr fun x=>?_
 let i := x.1; let n:=φ x.2; let M:= T x; let N:= Z i x.2; let B:=More N; let s:= f i; let R':= readingFob (Pp (f i)) (R i) (0:Site N);
 obtain ⟨a₀,b₀⟩:= cost_p (R i) N true (a i); obtain ⟨a₁,b₁⟩:= cost_p (R i) N false (b i)
 let ω:=bodyV P.run s (takenVolume P n) 0 (R i) (Pp s)
 let Ξ₀:= (wrap B (F i),plaquette I); let Ξ₁:= (wrap B (G i),plaquette J)
 have hT:ω (true,a i)= Ξ₀:= Prod.ext a₀ (congrArg plaquette (b₀.trans (congrArg Prod.fst (hs i))))
 have hQ:ω (false,b i)= Ξ₁:= Prod.ext a₁ (congrArg plaquette (b₁.trans (congrArg Prod.fst (ht i))))
 let L:=reachCost Γ s (takenVolume P n) (takenCutoff P n) (κFix β s); have hm:K x=(m i:ℂ)^4 * rimble (More N) M Ξ₀ Ξ₁ := by
    let v:= F i-G i; change (m i:ℂ)^4* rimble _ M (wrap _ v,_) (0,_)=_; unfold Ξ₀ Ξ₁; rw [rimflare B M (wrap B (F i)) (wrap B (G i)) v (map_sub (wrap B) (F i) _).symm, rimflare B M (wrap B v) 0 v (sub_zero ..)]
 change (D:ℂ)* ((realDir I:ℂ)* ((L:ℂ)^2*K x))=((m i:ℂ)^4*↑(sailDir true (a i))* (L:ℂ)^2)* (sch (G:=group) (a i).2 (b i).2:ℂ)* rimble B M (ω (true,a i)) (ω (false,b i))
 rw [hT,hQ, hm, show sailDir true (a i)=realDir I from congrArg realDir (congrArg Prod.fst (hs i)), show sch (G:=group) (a i).2 (b i).2=D from congrArg₂ (sch (G:=group)) (congrArg Prod.snd (hs i)) (congrArg Prod.snd (ht i))]; ring
#print axioms tagged
lemma fare_becomes (ε:ℝ)(p:0<ε): ∀ᶠ s:ℕ in atTop, ∀ᶠ n:ℕ in atTop,∀ k d:Γσ s, ‖pulseFee P A β s (φ n) k d-accepted k d‖ ≤ ε:=by
 let Z(s n:ℕ)(k d:Γσ s) := ε < dist (pulseFee P A β s (φ n) k d) (accepted k d); by_contra h; push Not at h; have ht : ∃ᶠ s:ℕ in atTop, ∃ (x y:spectrumIdx)(a b:Γσ s), atIdx a=x∧atIdx b=y∧ ∃ᶠ n:ℕ in atTop, Z s n a b:= by
    refine h.mono fun i p=>?_; simp_rw [frequently_exists] at p
    obtain ⟨x,y,t⟩:=p; refine ⟨_,_,x,y,rfl,rfl,?_⟩; exact t.mono fun i t=> by simpa only [Z,dist_eq_norm] using t
 simp_rw [frequently_exists] at ht -- hazard sells a,b dependent?
 obtain ⟨x,y,k⟩:=ht; obtain ⟨f,p,q⟩:=extraction_of_frequently_atTop k; choose a b u v Q using q
 let M:= tagged P C A ‹0<A› f p a b x y u v -- shadow
 obtain ⟨n,e⟩:= (eventually_curry_iff.mp (Metric.tendsto_nhds.mp M ε (by assumption))).exists
 obtain ⟨i,g,h⟩:= ((Q n).and_eventually e).exists; unfold Z accepted at g; rw [u,v] at g; exact lt_asymm h g
#print axioms fare_becomes
omit C u
open Finger
open _root_.Zephyr.Chern
open Swell Sault Vow RG Rive Nor Prism
abbrev tip (k:spectrumIdx):ℝ:= marker k.1 k.2
abbrev incidence (c:ℝ):= 2*unitReceipt^2*(c^2/Finger.probe tip)
lemma incidence_pos {c:ℝ}(t:0<c) : 0 < incidence c:=mul_pos (mul_pos two_pos (pow_pos unit_pos _)) (div_pos (pow_pos t _) (probe_pos tip))
variable {N:Side}{B:ℕ} (h:2*(B+1)<(More N).val){Z T:SOp N}{r:ℕ}{d a v c D u:ℝ}{K:Scree.Loom N}{Uφ:BudgetPoint} {m:ℕ}
lemma emit (E:Pattern Z T r d a v)(hz:4*B+1<N.val)(z:Checked Uφ K u d a k m) (t:Stakes (compassLine E 0 K Uφ k) c) (e:0 ≤ c)(q:B=Uφ.B): incidence c ≤ (Finger.Ledger (cashY B h 0 E k) accepted).re:=by
 apply revealed _ atIdx unitReceipt tip _ e _
 exact cashYaw B h _ E k
 have ht:=(show c ≤ _ from (show c≤ _ from t.2)); apply ht.trans (le_of_eq ?_)
 rw [reading_focus B h hz z E q, polynomial]; rfl
#print axioms emit
end Sundial
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
