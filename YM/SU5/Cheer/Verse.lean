import YM.SU5.Cheer.Chapel
set_option maxHeartbeats 80000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Cheer
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "ψ"=> P.lucid x Z
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "G" i:max=> P.comesFrom x Z (c i) (r i)
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "z" i:max=> P.allowance x Z (c i) (r i)
local notation "φ" i:max=> ψ (c i) (r i)
local notation "η" i:max=> P.birthCloud x Z (c i) (r i)
local notation "M"=> Cheer.FLap
local notation "p"=> P.seasons 3 (ξ)
-- notational ambiguity cast. prefer:
def pairedLight (t:ℂ) (v:Space3):ℂ:= numberX Z/25*(Cheer.plum v (t+2)* Cheer.plum v (t+4))
private lemma party_escort (R:P.Register) (h:P.party 3 R x): P.lodestarHere 3 ξ:= h.2.1.accepted 3
variable {P c r x}(A:Launch P c r){q:ℕ→ℝ}(Y:readyUV P c r x q)(e:Tendsto q atTop (𝓝 0))(u:P.lodestarHere 3 (P.otherSpectrum 3 3 x))
include A Y e
lemma refreshing : Tendsto (fun i:ℕ=> z i) atTop (𝓝 (purePrice Z:ℂ)) := by
 let Ω':=(purePrice Z:ℂ); have hw:Ω' ≠ 0:= Complex.ofReal_ne_zero.mpr (purePrice_p Z).ne'
 let f(i):=P.singleState 3 (c i) (P.otherSpectrum 3 3 x); have he:=(aboutOne Z A Y e).const_mul Ω'; rw [mul_one] at he
 refine he.congr fun i=>?_
 have hv: z i= f i (P.stockS Z (P.flash (r i))):=rfl
 change Ω'* f i (Ω'⁻¹ • P.stockS Z _) = _; rw [map_smul,smul_eq_mul, hv,← mul_assoc,mul_inv_cancel₀ hw,one_mul]
include u
lemma lyricalCloud : Cheer.Lyrical (promenade Z) (fun i:ℕ=> G i):= by
 let X(i):ℝ≥0:= ⟨ρ i,(P.dew_pos _ (A.unitSize i)).le⟩
 refine ⟨fun i=> Cheer.radiant (S) (η i) (ρ i) (X i).property, home_bright Z,fun v t=>?_⟩
 let T (i:ℕ):= X i * t; let U:= cutPulse v; let α (i:ℕ):= ρ i • U; let h (i:ℕ)(f:H):= inner ℂ f ((S).U (α i) ((S).E (T i) f))
 have he:P.dimensionS c r T (t:ℝ):= tendsto_const_nhds.congr fun i=> by rw [show (T i :ℝ)= ρ i*(t:ℝ) from rfl]; field_simp [(P.dew_pos _ (A.unitSize i)).ne']
 have hv:Tendsto (fun i=> (ρ i)⁻¹ • α i) atTop (𝓝 U):= tendsto_const_nhds.congr fun i=> (inv_smul_smul₀ (P.dew_pos _ (A.unitSize i)).ne' U).symm
 have hb:Tendsto (fun i=>h i (φ i)) atTop (𝓝 (ovoid Z (t:ℝ) U)):= EuclidAll Z A Y e U t t.property _ he _ hv
 have ht(i): M (G i) v ↑(t:ℝ)= h i (φ i)- (↑‖z i‖:ℂ)^2:= (Cheer.back S (η i) (X i) t v).trans (P.background_zeroed x Z (c i) (r i) (α i) (T i) u)
 let θ:=(purePrice Z:ℂ); have hp:= (((Complex.continuous_ofReal.continuousAt).tendsto.comp (refreshing Z A Y e).norm).pow 2); rw [Complex.norm_real, Real.norm_of_nonneg (purePrice_p Z).le] at hp -- tune
 have hk : ovoid Z (t:ℝ) U - θ^2=M (promenade Z) v ↑(t:ℝ):= blinded Z v t
 have hy:= hb.sub hp; rw [show _ = _ from hk] at hy; exact hy.congr fun i=> (ht i).symm
lemma priceStream (v:Space3)(t:ℂ)(h:0≤t.re): Tendsto (fun i:ℕ=> M (G i) v t) atTop (𝓝 (pairedLight Z t v)):=by
 let S':= promenade Z; rw [show pairedLight Z t v= M S' v t from (pays_move Z v t h).symm]; exact (lyricalCloud Z A Y e u).val _ _ h
lemma rollingR (v:E4): Tendsto (fun i:ℕ=> inner ℂ (η i) ((S).unit.translation (Cheer.zoom (ρ i) v) (η i))) atTop (𝓝 (pairedLight Z (-(time v:ℂ)*Complex.I) (spatial v))):= by
 let x':ℂ:= -(time v:ℂ)*Complex.I
 have hp : 0≤ x'.re:= by simp [x']
 refine (priceStream Z A Y e u (spatial v) x' hp).congr fun i => ?_
 exact ((Cheer.slogan S (η i) (ρ i) v).trans (Cheer.Lyrical.lays_flat (G i) v)).symm
variable (P x c r)
omit A u e Y
structure Bands : Prop where
   weak : Tendsto (fun i:ℕ=>G i) atTop (𝓝 (promenade Z))
   finite_t (U:E4): Tendsto (fun i:ℕ=> inner ℂ (η i) ((p).unit.translation (Cheer.zoom (ρ i) U) (η i))) atTop (𝓝 (pairedLight Z (-(time U:ℂ)*Complex.I) (spatial U)))
   exhausted : Tendsto (fun i:ℕ=> (η i)-(p).ℚmeasure.region Mink.inside (η i)) atTop (𝓝 0)
   funded (U:Set E4)(hf:IsOpen U)(he:(Mink.inside∩U).Nonempty) (u:ℝ)(h:u<(promenade Z:Measure E4).real U) : ∀ᶠ i:ℕ in atTop,u<‖(p).ℚmeasure.region (Cheer.press (ρ i) U) (η i)‖^2
 -- define
variable {P x c r}
include A u e Y
omit A u e Y in
private lemma beep {G':Hilbert}(f:ℕ→G')(h0:Tendsto (fun i:ℕ=> ‖f i‖^2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0):= by
 have hp:=Real.continuous_sqrt.continuousAt.tendsto.comp h0; rw [Real.sqrt_zero] at hp; exact tendsto_zero_iff_norm_tendsto_zero.mpr (hp.congr fun i=> Real.sqrt_sq (norm_nonneg _))
lemma fertile : P.Bands x Z c r:= by -- grammar
 let V:= lyricalCloud Z A Y e u; let G':=(S).ℚmeasure; refine ⟨V.march (promenade_ne Z),rollingR Z A Y e u,?_,?_⟩
 · let f(i:ℕ):= (η i) - G'.region Mink.inside (η i); have hy(i:ℕ): f i= G'.region Mink.insideᶜ (η i):= sub_eq_of_eq_add' (Cheer.orth_inside (S) (η i)).symm -- sign
   have h0 : Tendsto (fun i:ℕ=> ‖f i‖^2) atTop (𝓝 0):= (Cheer.forgotten V (promenade_ne Z) (promenade_strict Z)).congr fun i=> by exact ((congrArg (fun x:H=>‖x‖^2) (hy i)).trans (Cheer.outside (S) (η i) (P.dew_pos _ (A.unitSize i)))).symm
   exact beep (G':=H) f h0
 intro U t _ a h; exact (Cheer.knock a U V (promenade_ne Z) t h).mono fun i v=>by exact lt_of_lt_of_eq v (Cheer.norm_region (S) (η i) (ρ i) U t.measurableSet).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms refreshing
#print axioms priceStream
#print axioms Bands.exhausted
#print axioms fertile
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
