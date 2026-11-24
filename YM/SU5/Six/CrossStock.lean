import YM.SU5.Cordial.Meridian
/-!
# Zoom-matrix transport: the mixed moving stock reading

Generalize LatticeFieldEstimates (two purchasable stocks), Fountain (Wick evaluation), Meridian
(reflection and rounded positions) to different clans. This is with the ACTUAL
singleState on one axis-3 spectrum point. In particular, the stencil can change!
No use of a fixed-stencil extrapolation. `readyUV` will be supplied, on this same
point and along the same Launch, by `Prototype.summit` in the application.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section

-- As in Fountain, expanding the Wick price in matter Slots.
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze Twah
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
namespace Cordial
open Lead (Clan)
open YM.Stationary (Gaia)
variable {I : Type*} (P : Cellz I → Gaia) (D : I → DirSpin) (c : I → Clan)
local notation "ρ" => germRho P D
private lemma wick_pair_pair {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
 simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

/-- Different clans: all cross-contractions vanish. -/
lemma witness_pair_other {i j : I} (e : c i ≠ c j) :
    witness c [i,j] P D = lyric P D (c i) i * lyric P D (c j) j := by
  let f (p q : Slot) := runes (ρ) (sayHi (sayHi [] i p) j q)
  let A := billX P D
  let W := A i i * A j j
  have hf (p q : Slot) (u : p ∈ colors (c i)) (v : q ∈ colors (c j)) : f p q = W := by
    have hp : family p = c i := (mem_filter.mp u).2
    have hq : family q = c j := (mem_filter.mp v).2
    have h : p ≠ q := fun r => e (hp.symm.trans ((congrArg family r).trans hq))
    unfold f
    change runes _ [(i,p,true),(i,p,false),(j,q,true),(j,q,false)] = _
    rw [wick_pair_pair]
    simp only [funds,funds_neg,dcash,h,h.symm,↓reduceIte,
      neg_zero,mul_zero,sub_zero,add_zero]
    rfl
  unfold witness
  change ∑ p ∈ colors (c i), ∑ q ∈ colors (c j), f p q = _
  have hg (p : Slot) (u : p ∈ colors (c i)) : (∑ q ∈ colors (c j), f p q) = numberX (c j) * W := by
    rw [sum_congr rfl (fun q w => hf p q u w),sum_const,nsmul_eq_mul,colors_card,numberX]
  rw [sum_congr rfl hg, sum_const,nsmul_eq_mul,colors_card]
  unfold W A lyric numberX
  ring
end Cordial
end YM.CF.Buffered.Ballad


namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z W':Lead.Clan)(a:Axis)(s:ℕ)(c r:ℕ→ℕ)
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N₀"=> notch M
local notation "σ" n:max=> P.singleState a (c n) (P.otherSpectrum 3 a x)
local notation "ε" => YM.basis (3:Axis)
local notation "ℓ" => P.calibration.ℓ
local notation "β" => P.otherSpectrum 3 3 x

section
private def pairMixed (A B: Lead q) (Y Z' : Lead.Clan):= plait ![liftS A,liftS B] ![Y,Z'] (Twah.letters 2) q
private lemma pairMixed_val (A B:Lead q): pairMixed A B Z W'=(liftS A).groundWord q Z*(liftS B).groundWord q W':= congrArg ((liftS A).groundWord q Z * ·) (mul_one ((liftS B).groundWord q W'))
variable {c r}{P x} {d:ℕ→ℝ}
variable (S:Launch P c r) (A B:∀ i,Lead (r i)) (h:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
variable (U V:Gaia)(b:Bool)(i:Fin 2)(t:marchesR r A U V)(v:remainsR r A b i)
include S h p t v
lemma mixed_wins (X Y: Gaia)(b': Bool)(j:Fin 2)(T:marchesR r B X Y)(e:remainsR r B b' j)(u:Injective (zephyr U V X Y)):
 Tendsto (fun n=>(σ n) (P.stockS Z (A n)*P.stockS W' (B n))) atTop (𝓝 (Lead.cash b*Lead.cash b' * Twah.witness ![Z,W'] (Twah.letters 2) (zephyr U V X Y) ![(i,i),(j,j)])):=by
 let f(n:ℕ): Fin 2→ Twah:=![liftS (A n),liftS (B n)]; let D: Fin 2→DirSpin:= ![(i,i),(j,j)]
 let χ(n:ℕ):= Gemini.flourish (liftS (A n)) Z (R:=r n) -- proofs unicode
 let W: Fin 2→Lead.Clan :=![Z,W']; let Z' := zephyr U V X Y;
 have h₁:riseUp f r Z':= by rintro ⟨k,z⟩; fin_cases k <;> cases z <;> first| exact t.1| exact t.2| exact T.1|exact T.2
 have h₂(n:ℕ)(i:Fin 2): (f n i).traceV.length=2*r n:=by fin_cases i<;> first | exact (A _).costs| exact (B _).costs
 have h₃(n:ℕ): bodyF (f n)= D:=by funext k; fin_cases k; exact congrArg (fun z:Fin 2=>(z,z)) (v n).2; exact congrArg (fun z:Fin 2=>(z,z)) (e n).2
 have hq:= (Prototype.rightRide S W _ _ _ (Eventually.of_forall h₃) h₁
   (show plateau f Z' from fun i j p=> Eventually.of_forall (fun l=> congrArg _ (u p)))
   (Eventually.of_forall (p:=fun n=> ∀ j:Fin 2,(f n j).traceV.length ≤ 32*((n+2)*r n)) (fun n k=> by
      rw [h₂]; calc _ ≤ 32*((0+2)*r n):=by omega
                    _ ≤ _:=by gcongr; exact Nat.zero_le _)) h p a).const_mul (Lead.cash b*Lead.cash b')
 have he(n:ℕ):
   P.stockS Z (A n)*P.stockS W' (B n) = (Lead.cash b*Lead.cash b') • P.tuneK (lovely (f n) W (Twah.letters 2) (r n)):= by
    simp only [P.liftS_paid,(v n).1,(e n).1,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
    rw [mul_comm (Lead.cash b') (Lead.cash b)]
    exact congrArg (fun t:P.Test=> (Lead.cash b * Lead.cash b') • t) (P.songsAg (lovely (f n) W (Twah.letters 2) _) ((χ n).mul (Gemini.flourish (liftS (B n)) W')) (pairMixed_val Z W' (A n) (B n))).symm
 simp_rw [he,map_smul,smul_eq_mul]; exact hq
end

-- GEN
local notation "U" => P.voyageF 3 (β)
local notation "S" => P.physicalEnergy 3 (β)
variable (J: List Street)
lemma cross_traffic (t ν:ℕ) (n:Street→ℤ): let z:=P.shard x Z s t; let f:= P.flash t; inner ℂ z ((U).raw J (fun i=> N₀ s (n i)) ((S).E (whenly M s ν) (P.shard x W' s t)))= P.singleState 3 s (β) (P.stockS Z (f.mirror 3 0)* P.stockS W' (P.ride J n (P.migrate 3 f ν))):=by
 intro Z₁ f; let W:=P.stockS Z f
 let A:=P.brightC Z s t; let A':=P.brightC W' s t; let v:= P.passesLater 3 s ν A'; let z:= P.viewF 3 (β) s v; let p:= P.certify 3 s J n v; let u:=P.viewF 3 (β) s p
 let Q:=P.luggage 3 J n; let b:=P.singleState 3 s (β);
 have hu:u=(U).raw J (fun i=> N₀ s (n i)) ((S).E (whenly M s ν) (P.shard x W' s t)):= (P.ship_ideal 3 (β) s J n v).trans (congrArg ((U).raw J (fun i=> N₀ s (n i))) (P.releasedLater 3 (β) s ν A'));
 calc _ = inner ℂ Z₁ u := congrArg (inner ℂ Z₁) hu.symm
      _ = b ((P.reflectTest 3 W) * Q (P.shifts 3 ν (P.stockS W' f))):= P.released_gram 3 (β) s A p
      _ = _:= congrArg b (congrArg₂ (· * ·) (P.mirror_stock Z 3 f) ((congrArg Q (P.acrossStocks W' 3 f ν)).trans (P.pal_transfer W' J n (P.migrate 3 f ν))))

variable {P x c r} (A:Launch P c r) {d:ℕ→ℝ} (Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
include A Y p
omit A Y p in
 private lemma reflect_three_basis: inversion 3 ε=-ε:=by ext i; by_cases z:i=3; subst i; simp [inversion]; simp [inversion,z]
local notation "φ" i:max=> P.shard x Z (c i) (r i)
/-- Mixed reflected native heat/space costs in the zoom. -/
lemma cross_penetration (e : Z ≠ W') (q:ℕ→ℕ)(z:ℝ)(v:0 ≤ z)(n:Street→ℕ→ℤ)(t:Street→ℝ) (N:∀ i∈J, P.bargain r (n i) (t i))(Q:P.bargain r (fun i=> (q i:ℤ)) z): Tendsto (fun i:ℕ=> inner ℂ (φ i) ((U).raw J (fun k=>N₀ (c i) (n k i)) ((S).E (whenly M (c i) (q i)) (P.shard x W' (c i) (r i))))) atTop (𝓝 ((purePrice Z:ℂ)*(purePrice W':ℂ))) := by
 let F(i):=P.flash (r i); let x' := palace J t; let G(i):=(F i).mirror 3 0; let kS(i):=P.migrate 3 (F i) (q i); let L(i):=P.ride J (fun k=> n k i) (kS i); let a₁:Gaia:= -ε; let a₀:Gaia:= (-2:ℝ) • ε; let v₀:=layoutFirst z x'; let v₁:=v₀+ε; let D:= zephyr a₀ a₁ v₀ v₁
 have he:= P.heights_here r A.eager A.unitSize; have hg : marchesR r G a₀ a₁:=by
    have hz:= revolve 3 r F _ _ he A.eager; rw [map_smul, reflect_three_basis, smul_neg,←neg_smul] at hz; exact hz
 have hp : marchesR r L v₀ v₁:=by
    have k:= P.rideLegs r J n N (P.marching 3 r F _ _ he _ z Q); 
    let y:E4:=x'.val; have hx:v₀=(ε+ z • ε)+ y:=by unfold v₀ layoutFirst siteOf y; abel
    have hv : v₁=((2:ℝ) • ε+ z • ε)+y:=by unfold v₁; rw [hx]; module
    rw [hx,hv]; exact k
 have hr: remainsR r F false 0:= fun i=>⟨rfl,rfl⟩; have hh: remainsR r G false 0:= turnsZ (3:Axis) r F _ _ hr; have hw: remainsR r L false 0:= P.rider_remain r J _ n (P.passRemain 3 r _ _ _ hr _)
 have hv(i:Gaia)(x:ℝ): i 3=x→(i+ ε) 3=x+1:=fun h=>by simp [h]
 have hV:v₀ 3=z+1:= hv _ _ (tip z _); have hU:v₁ 3=z+1+1:=hv _ _ hV; have hx:D=duo z x':=by funext x; rcases x with ⟨x,y⟩; fin_cases x<;> cases y<;> rfl
 have hb(x y:Gaia)(h:x 3< y 3):x≠y:=fun t=> h.ne (t ▸ rfl)
 have ha: a₁ 3= -1:=by unfold a₁; simp
 have ha0:a₀ 3= -2:=by unfold a₀; simp
 have u: Injective D:=zephyr_non a₀ a₁ v₀ v₁ (hb _ _ (by rw [ha,ha0]; norm_num)) (hb _ _ (by linarith)) ⟨hb _ _ (by linarith), hb _ _ (by linarith),hb _ _ (by linarith), hb _ _ (by linarith) ⟩
 have hz:= mixed_wins Z W' 3 A G L Y p _ _ false 0 hg hh _ _ false 0 hp hw u
 have ht : Lead.cash false*Lead.cash false*Twah.witness ![Z,W'] (Twah.letters 2) D (![(0,0),(0,0)])=(purePrice Z:ℂ)*(purePrice W':ℂ):=by
    rw [show (![ (0,0),(0,0)]:Fin 2→DirSpin)=0 from funext fun k=>by fin_cases k<;> rfl,hx]; rw [show Lead.cash false = (1/5:ℂ) by simp [Lead.cash,phaseF]]
    rw [show Twah.letters 2 = [0,1] from rfl, Cordial.witness_pair_other _ _ _ (by exact e)]
    unfold lyric
    rw [(Cordial.reunion z x').1,(Cordial.reunion z x').2.1]
    change (1/5:ℂ)*(1/5)*(numberX Z * P20 * (numberX W' * P20)) = _
    rw [show (purePrice Z:ℂ)=numberX Z * P20 / 5 from price_as Z,
        show (purePrice W':ℂ)=numberX W' * P20 / 5 from price_as W']
    ring
 refine ?_ -- type annotate
 let fz(i:ℕ):= P.singleState 3 (c i) (β) (P.stockS Z (G i)*P.stockS W' (L i))
 have hx:Tendsto fz atTop (𝓝 ((purePrice Z:ℂ)*(purePrice W':ℂ))):=by rw [←ht]; exact hz
 exact hx.congr fun i=>(P.cross_traffic x Z W' (c i) J (r i) (q i) (fun k=> n k i)).symm -- tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
