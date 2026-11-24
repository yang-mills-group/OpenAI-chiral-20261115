import YM.CF.Fixed.Stencil
import YM.CF.Fixed.Fine
import YM.Push.LOCAL_SPLITTING.Transport

/-!
Exact symmetry and normalization, to be applied within each finite-volume
RG horizon. The offset (denoted `E.v` in `GramM`) should not simply be set
to zero in the partition estimates at lower levels. Here we prove what
happens after its exact cancellation. At the top level this is in fact
simpler: there is no offset.

Some identities are algebraic even when both sides vanish due to `integral`
(totalized). These are NOT existence of normalized readings; for that we
supply integrability *and* nonzero `partitionZ` separately.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.Fixed
open Function NormedSpace Filter Metric Finset Lattice Wilson Cube MeasureTheory Spire
open SU Lat Fock Scroll Tulip Skye Scree RG Dial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra

variable {N : Side} (i : Axis)

lemma preserve_reflectOrbit : MeasurePreserving (reflectOrbit (N:=N) i) (city N) (city N):=by
  let s:=reflectSweep N i
  refine (show MeasurePreserving (flashA s) _ _ from ?_).prod (tuft s)
  rw [show flashA s=reflConfig N i from funext (flash_reflect i)]; exact reflConfig_preserves N i

lemma square_reflectOrbit (u:Orbit N) : reflectOrbit i (reflectOrbit i u)=u:=by
  refine Prod.ext ?_ ?_
  · change flashA _ (flashA _ _)=_; rw [flash_reflect, flash_reflect, square_reflConfig]
  change bun _ (bun _ _)=_; nth_rw 1 [←inv_reflectSweep i]; exact tuftT ..

def reflAll : MeasurableEquiv (Orbit N) (Orbit N):=
  ⟨⟨reflectOrbit (N:=N) i, reflectOrbit (N:=N) i, square_reflectOrbit i, square_reflectOrbit i⟩,
   (preserve_reflectOrbit i).measurable, (preserve_reflectOrbit i).measurable⟩

abbrev mirrorWave (x:Phys N):= arum (reflectP N i) false true (mateK N) x

lemma twist_mate : mirrorWave i (mateK N)=mateK N:=by
  exact arum_self (reflectP N i) false true (Tset N) ((touchP N) ▸ (tickB N)) (tickR (reflShape i) inert (pinSpin i) (mirrorX i) N)

lemma mirror_inner (x y:Phys N) : inner ℂ (mirrorWave i x) (mirrorWave i y)=star (inner ℂ x y):= by
  exact arum_globe (reflectP N i) false true (Tset N) ((touchP N) ▸ (tickB N))
    (tickR (reflShape i) inert (pinSpin i) (mirrorX i) N) x y

lemma mirror_apply (A:FC (Single N)) (x:Phys N) : mirrorWave i (acts A x)=
    acts (Reed.reverseW (reflectP N i) false A) (mirrorWave i x) := by
  unfold mirrorWave; rw [arum_act, Reed.reverseW,Reflect.chord]; simp [Spire.tourP,windX]

lemma mirror_scale (c:ℂ) (x:Phys N) : mirrorWave i (c•x)=star c • mirrorWave i x:= by apply arum_scale

abbrev MirrorCompatible (i:Axis) (F : Orbit N → Phys N) : Prop :=
  ∀ᵐ y∂city N, F (reflectOrbit i y)= mirrorWave i (F y)

/-- Test and denominator use the same `city`, including the independent tag
measures of this FiniteGaugeData model. `F` is complex, not norm or squared modulus. -/
def functional (F : Orbit N→ Phys N) (X : Test N):ℂ:=
  ∫ i:Orbit N, beamZ N (acts (X i.1) (F i))∂city N

lemma functional_scale (X : Test N) (F : Orbit N→ Phys N) (c:ℂ) :
    functional (c•F) X=c * functional F X:=by
  unfold functional; simp_rw [Pi.smul_apply,map_smul,beamZ,inner_smul_right]
  exact integral_const_mul ..

lemma functional_reflect (X:Test N) (F:Orbit N→ Phys N) (t:MirrorCompatible i F) :
    functional F (reflectTest i false X)=star (functional F X):=by
  let T:= reflAll (N:=N) i
  let G (V: Test N) (u: Orbit N):= beamZ N (acts (V u.1) (F u))
  change (∫ u,G (reflectTest i false X) u ∂city N)=(starRingEnd ℂ) (∫ u,G X u∂city N)
  rw [← (show MeasurePreserving T _ _ from preserve_reflectOrbit i).integral_comp' (G _),←integral_conj];
  apply integral_congr_ae; filter_upwards [t] with u h
  change inner ℂ (mateK N) (acts (Reed.reverseW (reflectP N i) false (X (reflConfig N i ((reflectOrbit i u).1)))) (F (reflectOrbit i u)))=_
  rw [h,show reflConfig N i ((reflectOrbit i u).1)=u.1 from by unfold reflectOrbit; dsimp only; rw [flash_reflect,square_reflConfig]]
  rw [←mirror_apply];
  -- Don't rewrite mateK inside arum
  nth_rw 1 [← twist_mate (N:=N) i]
  exact mirror_inner ..

abbrev gram (i:Axis) {I:Type*} (W : Test N→ℂ) (F:I→Test N):Matrix I I ℂ:=
  fun a b=> W (reflectTest i false (F a)*F b)

lemma reflectOne : reflectTest (N:=N) i false 1 = 1:=by
  funext U; change Reed.reverseW (reflectP N i) false 1=1; rw [Reed.reverseW, Fock.theta_one]; exact one_smul ..

lemma gram_hermitian {W: Test N →ℂ} {I:Type*} (F:I→Test N) (hf:∀ t,Probe (F t))
    (p:∀ A:Test N, Probe A → W (reflectTest i false A)=star (W A)): (gram i W F).IsHermitian:=by
  ext j k
  let T:Support (More N):= univ
  let x:=F j; let y:=F k; let Y:=reflectTest i false y
  have hp : InRegion T false Y:=probe_reflect i (hf k)
  have ht : Probe (Y*x) := hp.mul (show InRegion T false x from hf j)
  have he:=InRegion.reflect_mul i hp (show InRegion T false x from hf j)
  rw [show reflectTest i false Y=y from InRegion.reflect_involutive i (show InRegion T false y from hf k)] at he
  exact ((p (Y*x) ht).symm.trans (congrArg W he))

section
open Paige Peaks Vault
variable {m B L:Side} {j:ℕ} {ho: Odd L.val} {Y:Pricing j L ho (Thread j)} {d:ℝ}
local notation "N_"=> mid m B

/-- Numerator evaluation in a finite block, with the extensive scalar offset kept (so
it can be called verbatim at the top). -/
def numerator (U:Grasp Y B d) (V:GramM (mid m B)) (F:Loom (mid m B)) : Test (mid m B) → ℂ :=
  functional (denZ V U F)

variable (U:Grasp Y B d) (V:GramM (mid m B)) (F:Loom (mid m B))

def evalNormalized (X: Test (mid m B)):ℂ:= numerator U V F X/ partitionZ V U F

/-- Rescale both by exactly the inverse exponential of the same complex
`X.v`. This is the `recX` density also used in the diagonal estimates. -/
abbrev rescaleOffset : Orbit (mid m B)→Phys (mid m B) := Complex.exp (-V.v) • denZ V U F
abbrev scaledZ := Complex.exp (-V.v) * partitionZ V U F

lemma strip_offset (X: Test (mid m B)) :
    functional (rescaleOffset U V F) X/scaledZ U V F=evalNormalized U V F X:=by
  rw [rescaleOffset,functional_scale,scaledZ,mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
  rfl

lemma numerator_one : numerator U V F 1= partitionZ V U F:=by unfold numerator functional; simp only [Pi.one_apply,act_one]; rfl
lemma scaledZ_one : functional (rescaleOffset U V F) 1=scaledZ U V F:=by
  rw [rescaleOffset, functional_scale]; exact congrArg _ (numerator_one U V F)

lemma stir_reflect (X: Pane N_): stir (xtra false) (reflShape i) X=reflConfig N_ i X:=by
  rw [←flash_reflect, flashA,castX_reflect]

lemma betaL_reflect {t : ℝ} {k : ℕ} (H : Roof _ t d k F) (x: Orbit N_)
    (hp: Injective (priorP x.2)) : V.betaL F (reflectOrbit i x)-V.v=star (V.betaL F x-V.v):=by
  let a:=Signed.mirror i
  have he:F (reflectOrbit i x)= flashA (reflectSweep N_ i) (F x):=H.move _ _ _ hp
  have hx(A:Pane N_) : Pec.pigment V.J.I (flashA (reflectSweep N_ i) A)=star (Pec.pigment V.J.I A):=by
    rw [flash_reflect, ← show Nacre.Yg (Nacre.incX (Signed.mirror i)) A=reflConfig N_ i A from Nacre.Ywin (Signed.mirror i) A]
    unfold Pec.pigment; rw [Pec.prog,Pec.complX,Spire.det_t]; rfl
  unfold GramM.betaL GramM.H0; rw [he,hx]
  rw [show (reflectOrbit i x).1= reflConfig N_ i x.1 from flash_reflect i x.1,
      reflConfig, Push.Local.channels_pull]
  simp only [star_sub, Complex.star_def, Complex.conj_ofReal]; ring

/-- Use with `X` actual (not another reflection model's) reflection relation
on `relV`, proved separately for the Nest operators on exactly this Grasp. -/
lemma rescale_reflect {S:Sweep N_ → Prop} {t h a b c:ℝ} {k:ℕ} (K:Stamped j L ho Y)
    (H : Roof _ t d k F) (n:U.roundZ ≤ (mid m B).val) (x:S (reflectSweep N_ i)) (p:1≤j)
    (A:IncX S V.F V.p h a) (B':IncX S V.slip V.p h b) (C:Dark S V.K V.p h c)
    (X : ∀ y:Pane N_, Guard y d → relV U V.J (flashA (reflectSweep N_ i) y) = mirrorWave i (relV U V.J y)) :
    MirrorCompatible i (rescaleOffset U V F) := by
  refine ((Measure.quasiMeasurePreserving_snd (μ:=prior SU.group (More N_)) (ν:=depot N_)).ae sepT).mono ?_
  intro z hp
  have he:F (reflectOrbit i z)=flashA (reflectSweep N_ i) (F z):=H.move _ _ _ hp
  let f:= reflectOrbit (N:=N_) i; let R:=F z; let Z:= F (f z); let J:=V.J; let T:=spar j J.M Z; let T':=spar j J.M R; let v:= reflectP N_ i
  have hZ:IsStarProjection T:= (U.broadness _ n _).projection _ (H.paid (f z))
  have hT:IsStarProjection T':= (U.broadness _ n _).projection _ (H.paid z)
  have ht : sings false v T'=swapX true T := by
    change sings false v (spar _ _ _)= swapX true (spar j J.M (F (reflectOrbit i z))); rw [he,flash_reflect,←stir_reflect]
    exact funde_f _ _ _ (mirrorX i) _ j p _ _ (K.fields_one _ (U.needed.trans n)) ((H.paid z).shrink U.gem)
  have hg(y) : rescaleOffset U V F y= Complex.exp (V.betaL F y-V.v) • acts (tank (spar j V.J.M (F y)) (V.board y)) (relV U V.J (F y)):=by
    rw [rescaleOffset, Pi.smul_apply]; unfold denZ; rw [smul_smul,←Complex.exp_add]; congr 3; abel
  change rescaleOffset U V F _= _; rw [hg,hg];
  change Complex.exp _ • acts (tank T _) (relV U V.J Z)=_
  rw [mirror_scale,betaL_reflect i V F H _ hp]
  have hP : star (Complex.exp (V.betaL F z-V.v))=Complex.exp (star (V.betaL F z-V.v)):= (Complex.exp_conj _).symm
  rw [hP];
  have hs : relV U V.J Z=mirrorWave i (relV U V.J R):=by unfold Z R f; rw [he]; exact X _ (H.paid z)
  rw [hs]; apply congrArg _
  change acts _ _= arum _ _ _ _ (acts (tank T' (V.board z)) _)
  rw [board_reflect i A B' C x _ hp, tank_eq T _ hZ,tank_eq T' _ hT,arum_act,appleT hT hZ false true v ht]

lemma scaledZ_real (X:MirrorCompatible i (rescaleOffset U V F)): star (scaledZ U V F)= scaledZ U V F:=by
  rw [← scaledZ_one, ← functional_reflect i 1 _ X, reflectOne]
lemma evalNormalized_reflect (X:MirrorCompatible i (rescaleOffset U V F)) (O:Test (mid m B)) :
    evalNormalized U V F (reflectTest i false O)=star (evalNormalized U V F O):=by
  rw [← strip_offset, ← strip_offset,functional_reflect i O _ X,
      star_div₀,scaledZ_real i U V F X]

end
end YM.CF.Fixed
