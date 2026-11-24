import YM.SU5.Cordial.Rings
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
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
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z:Lead.Clan)(a:Axis)(s:ℕ)(c r:ℕ→ℕ)
local notation "B" => P.par.block
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N₀"=> notch M
local notation "σ" n:max=> P.singleState a (c n) (P.otherSpectrum 3 a x)
local notation "ε" => YM.basis (3:Axis)
local notation "ℓ" => P.calibration.ℓ
local notation "β" => P.otherSpectrum 3 3 x
local notation "V" => P.ColorHil 3 (β)
local notation "U" => P.voyageF 3 (β)
local notation "S" => P.physicalEnergy 3 (β)
lemma brightC (n:ℕ): P.birthF 3 s (P.stockS Z (P.flash n)):= ⟨P.mantra 3 (flourish (P.flash n) Z) (P.flash_here n) s,rfl⟩
def shard (n:ℕ): V := P.viewF 3 (β) s (P.brightC Z s n)
lemma photon (n:ℕ): P.shard x Z s n=P.coinK 3 (flourish (P.flash n) Z) (β) (P.flash_here n) s := P.holdsF 3 (β) s (P.brightC ..) _ rfl
abbrev Street := Trans (3:Axis)
def streak (k:Street): Bank:= ⟨basis k.val, by change (basis k.val: E4) 3=0; simp [Ne.symm k.property]⟩
variable (J: List Street) (t:Street→ℝ)(w:Street→ℤ)
noncomputable def ride (F:Lead q):= J.foldr (fun i L=>P.migrate i.val L (w i)) F
@[simp] lemma ride_one(k:Street)(F:Lead q): P.ride (k::J) w F=P.migrate k.val (P.ride J w F) (w k):=rfl
noncomputable def palace : Bank:= (J.map (fun k=> t k • streak k)).sum
lemma palace_one(k:Street): palace (k::J) t=t k • streak k + palace J t:= rfl
lemma pal_transfer (F:Lead q) : P.luggage 3 J w (P.stockS Z F)=P.stockS Z (P.ride J w F):=by induction J with|nil=>rfl|cons i L ih=>rw [P.ship_started,ih,P.ride_one, P.acrossStocks] -- args
lemma rideLegs {t e:Gaia}{A:∀ i,Lead (r i)}(n:Street→ℕ→ℤ){x:Street→ℝ}(p:∀ i ∈ J,P.bargain r (n i) (x i))(u:marchesR r A t e) : marchesR r (fun i=> P.ride J (fun k=> n k i) (A i)) (t+(palace J x).val) (e+(palace J x).val):=by
 induction J with
 | nil=> change marchesR _ A (t+0) (e+0); simpa using u
 | cons f L ih=>
    simp_rw [P.ride_one,palace_one]; have hx:= P.marching f.val r _ _ _ (ih fun i v=> p i (List.Mem.tail _ v)) _ _ (p f (List.mem_cons_self ..));
    convert hx using 1 <;> (first|(change t+((x f • basis (f.val))+(palace L x).val)=_; abel)| (change e+((x f • basis (f.val))+(palace L x).val)=_; abel))
lemma rider_remain {i:Fin 2} {b:Bool}(F:∀ i,Lead (r i))(n:Street→ℕ→ℤ)(t:remainsR r F b i) : remainsR r (fun i=> P.ride J (fun k=> n k i) (F i)) b i:=by
 induction J with|nil=>exact t|cons u L h=> simp_rw [P.ride_one]; exact P.passRemain u.val r _ b i h (n u)
lemma traffic (t ν:ℕ) (n:Street→ℤ): let z:=P.shard x Z s t; let f:= P.flash t; inner ℂ z ((U).raw J (fun i=> N₀ s (n i)) ((S).E (whenly M s ν) z))= P.singleState 3 s (β) (P.stockS Z (f.mirror 3 0)* P.stockS Z (P.ride J n (P.migrate 3 f ν))):=by
 intro Z₁ f; let W:=P.stockS Z f
 let A:=P.brightC Z s t; let v:= P.passesLater 3 s ν A; let z:= P.viewF 3 (β) s v; let p:= P.certify 3 s J n v; let u:=P.viewF 3 (β) s p
 let Q:=P.luggage 3 J n; let b:=P.singleState 3 s (β);
 have hu:u=(U).raw J (fun i=> N₀ s (n i)) ((S).E (whenly M s ν) Z₁):= (P.ship_ideal 3 (β) s J n v).trans (congrArg ((U).raw J (fun i=> N₀ s (n i))) (P.releasedLater 3 (β) s ν A));
 calc _ = inner ℂ Z₁ u := congrArg (inner ℂ Z₁) hu.symm
      _ = b ((P.reflectTest 3 W) * Q (P.shifts 3 ν W)):= P.released_gram 3 (β) s A p
      _ = _:= congrArg b (congrArg₂ (· * ·) (P.mirror_stock Z 3 f) ((congrArg Q (P.acrossStocks Z 3 f ν)).trans (P.pal_transfer Z J n (P.migrate 3 f ν))))
-- norm cost from k for reflection variations, even if birth only at high n
lemma zephyr_non (T T' V₀ V':Gaia)(v:T≠T')(p:V₀≠V') (q: T≠V₀ ∧ T≠V' ∧ T'≠V₀ ∧ T'≠V') : Function.Injective (zephyr T T' V₀ V'):=by
   rintro ⟨i,b⟩ ⟨j,c⟩; obtain ⟨ha,hb,hc,hd⟩:=q; fin_cases i <;> fin_cases j <;> cases b <;> cases c <;> simp [zephyr,v,p,ha,hb,hc,hd, Ne.symm v, Ne.symm p, Ne.symm ha,Ne.symm hb,Ne.symm hc, Ne.symm hd]
variable {P x c r} (A:Launch P c r) {d:ℕ→ℝ} (Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
include A Y p
local notation "Λ" a:max=> P.otherSpectrum 3 a (β) -- intermediate
lemma other_hint {F:∀ i,Lead (r i)}{b:Bool}{i:Fin 2}{T T': Gaia}(u:marchesR r F T T')(e:remainsR r F b i) (t:0 < T a)(h:0< T' a)(j:T ≠ T') : ∃ Z₀:ℝ,∀ᶠ i:ℕ in atTop,∀ w:P.birthF a (c i) (P.stockS Z (F i)), ‖P.viewF a (Λ a) (c i) w‖ ≤ Z₀:=by
 let g:=inversion a; have hZ(x : Gaia)(t:0<x a): g x a < 0:= by rw [show g=inversion a from rfl,invert_self]; exact neg_lt_zero.mpr t
 have hb(x y : Gaia)(t:0<x a)(h:0<y a): g x≠y:= fun e=>not_lt_of_ge (e.symm ▸ h.le) (hZ x t) -- rewriting occurrence
 let Z'(i):=(F i).mirror a 0
 have H:= duo_wins Z a A Z' F Y p _ _ _ _ (revolve a r F T T' u A.eager) (turnsZ a r F b i e) T T' b i u e (zephyr_non _ _ _ _ (fun u=>j (g.injective u).symm) j ⟨hb _ _ h t, hb _ _ h h,hb _ _ t t,hb _ _ t h⟩)
 let τ(i:ℕ):= (P.stockS Z (Z' i)* P.stockS Z (F i))
 let f(i:ℕ):=P.singleState 3 (c i) x (P.stockS Z (Z' i)* P.stockS Z (F i));
 let A₁:ℂ:=Lead.cash (axis_val a b)*Lead.cash b * Twah.witness (fun _=>Z) (Twah.letters 2) (zephyr ((inversion a) T') ((inversion a) T) T T') ![(Lead.shuffle a i, Lead.shuffle a i), (i, i)]
 have he:Tendsto f atTop (𝓝 A₁) := H.congr fun i=>P.single_agrees 3 a x (c i) (τ i)
 have hz:Tendsto (fun i=> (f i).re) atTop (𝓝 A₁.re):= Complex.continuous_re.continuousAt.tendsto.comp he
 refine ⟨Real.sqrt (A₁.re+1),?_⟩
 filter_upwards [hz.eventually (ge_mem_nhds (lt_add_one A₁.re))] with i e v
 have ht:(f i).re= ‖P.viewF a (Λ a) (c i) v‖^2:= by
    let f₁:=P.singleState a (c i) (Λ a); let z:= P.viewF a (Λ a) (c i) v
    have hv : inner ℂ z z= f₁ (τ i):= (P.released_gram a (Λ a) (c i) v v).trans (congrArg f₁ (congrArg (· * P.stockS Z (F i)) (P.mirror_stock Z a (F i))))
    have hu := hv.trans ((P.single_agrees 3 a (β) (c i) (τ i)).trans (P.single_agrees 3 3 x (c i) (τ i)))
    exact (congrArg Complex.re hu).symm.trans (inner_self_eq_norm_sq (𝕜:=ℂ) z)
 rw [ht] at e; exact Real.le_sqrt_of_sq_le e -- tune
open Ballad (axis_val)
omit A Y p in
 private lemma bend_true: inversion 3 ε=-ε:=by ext i; by_cases z:i=3; subst i; simp [inversion]; simp [inversion,z]
local notation "φ" i:max=> P.shard x Z (c i) (r i)
lemma penetration (q:ℕ→ℕ)(z:ℝ)(v:0 ≤ z)(n:Street→ℕ→ℤ)(t:Street→ℝ) (N:∀ i∈J, P.bargain r (n i) (t i))(Q:P.bargain r (fun i=> (q i:ℤ)) z): Tendsto (fun i:ℕ=> inner ℂ (φ i) ((U).raw J (fun k=>N₀ (c i) (n k i)) ((S).E (whenly M (c i) (q i)) (φ i)))) atTop (𝓝 (ovoid Z z (palace J t))) := by
 let F(i):=P.flash (r i); let x' := palace J t; let G(i):=(F i).mirror 3 0; let kS(i):=P.migrate 3 (F i) (q i); let L(i):=P.ride J (fun k=> n k i) (kS i); let a₁:Gaia:= -ε; let a₀:Gaia:= (-2:ℝ) • ε; let v₀:=layoutFirst z x'; let v₁:=v₀+ε; let D:= zephyr a₀ a₁ v₀ v₁
 have he:= P.heights_here r A.eager A.unitSize; have hg : marchesR r G a₀ a₁:=by
    have hz:= revolve 3 r F _ _ he A.eager; rw [map_smul, bend_true, smul_neg,←neg_smul] at hz; exact hz
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
 have hz:= duo_wins Z 3 A G L Y p _ _ false 0 hg hh _ _ false 0 hp hw u
 have ht : Lead.cash false*Lead.cash false*Twah.witness (fun _=>Z) (Twah.letters 2) D (![(0,0),(0,0)])=ovoid Z z x':=by
    rw [show (![ (0,0),(0,0)]:Fin 2→DirSpin)=0 from funext fun k=>by fin_cases k<;> rfl,hx]; rw [show Lead.cash false = (1/5:ℂ) by simp [Lead.cash,phaseF]]; exact goesO ..
 refine ?_ -- type annotate
 let fz(i:ℕ):= P.singleState 3 (c i) (β) (P.stockS Z (G i)*P.stockS Z (L i))
 have hx:Tendsto fz atTop (𝓝 (ovoid Z z x')):=by rw [←ht]; exact hz
 exact hx.congr fun i=>(P.traffic x Z (c i) J (r i) (q i) (fun k=> n k i)).symm -- tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.penetration
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.other_hint
