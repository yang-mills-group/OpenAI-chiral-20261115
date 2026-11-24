import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Undouble
/-!
# Ward for all translations by matter pitch on actual torus
Do NOT assume `h:X.face primeU..` gives covariance of the Gram. Need
circumvent! Use regulator formulas at the top and naturality verified
along each step. Canonically on marked ratios lived in this tower.
Then ordinary equality in E & fixed periods (not claiming heat for movement of
one such pitch). Seam convention; eventually use in seeking further motion.
Keep separate from cap moments (δ geometry matters!). -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K₁"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
open Set MeshClock -- maybe not Theory
open Tapestry Tapestry.Altitude Spark

section prior
variable {N:Side}
variable (z:ℤ)
local notation "R" z:max=>reflMark (n:=N) j z
local notation "Rv" z:max=> reflFields (n:=N) j z
local notation "U₁"=>lagX ((0-z) • step j: Cover)
local notation "Γ"=>prepU (lagX ((0-z) • step j)) 1 inert N

noncomputable def around (N:Side): MeasurableEquiv (Orbit N) (Orbit N) := (reflOrbit j 0 N).trans (reflOrbit j z N)
local notation "C"=>around j z N
lemma round_prior : MeasurePreserving (around j z N) (city N) (city N):= MeasurePreserving.comp (f:=reflOrbit j 0 N) (g:=reflOrbit j z N) (reflOrbit_mp j z) (reflOrbit_mp j 0)
lemma round_actual (v:Orbit N) : ((around j z N) v).1= Yg (U₁) v.1:=by
  change Yg (plane j z) (Yg (plane j 0) v.1)=_
  rw [←kor,plane_join]
lemma drawn_round {X:Scree.Loom N}{r ℓ n}(p:Roof N r ℓ n X):∀ᵐ v:Orbit N ∂city N, drawn X ((around j z N) v)= reflFields j z (reflFields j 0 (drawn X v)):= by
  filter_upwards [(roof_move X j 0 p), (reflOrbit_mp (N:=N) j 0).quasiMeasurePreserving.ae (roof_move X j z p)] with x h t
  exact t.trans (congrArg (reflFields j z) h)
lemma paid_flipped (f:Mark N)(p:AtSupport false univ f) (W:Fields N):
    (R z) ((R 0) f) ((Rv z) ((Rv 0) W))=Spire.tourP Γ false false (f W):=by
  unfold reflMark; rw [reflFields_inv,reflFields_inv]
  exact theta_theta _ _ _ (firm_join j 0 z) ((p.allV W).sector)

-- arbitrary shape at the top; need JetS on χ spin & proper orientation
variable (a: Shape) (b : UNI SpinIdx)
lemma stillMask {v:ℝ} (x:Pane N): RG.flags v (stir (xtra false) a x)=∅ ↔ RG.flags v x=∅:=by
  rw [show stir (xtra false) a x=flashA ⟨a.s,wrap N a.t,false⟩ x from (stir_e a false x).symm,flagsA, Finset.map_eq_empty]
lemma basic_move (X:RG.Clip) (x:Pane N): basicP X (stir (xtra false) a x)=basicP X x:= pull_basic X a.s x (wrap _ (2 • a.t))
-- some check
lemma arum_zero {W:Type*}[LinearOrder W] [Fintype W](U:UNI W)(q:Wave W) : Spire.arum U false false q 0=0:= by
  exact (congrArg (Spire.arum U false false q) (zero_smul ℂ (0:Wave W)).symm).trans ((arum_scale U false false q 0 0).trans (zero_smul ℂ (Spire.arum U false false q 0))) -- target scaled arum zero, not oculus
end prior

section tranche
variable (i' k':ℕ)
local notation "M"=> Y.uv k'
local notation "Yc"=> Y.voyage i'
local notation "L₁" s:max=>side Y i' s
local notation "ν"=>side Y i' M
local notation "X" s:max => ((Y.voyage i').X (Y.uv k')).gram s
local notation "T"=>Y.meter.a M
local notation "YT" s:max=> (Y.voyage i').CapeT s
local notation "PU"=> Λ.U
local notation "Zn"=>capP (K:=Λ.K) PU ((X M).beta) (T) (m:=mesh (Y.ir i') Λ.R.L M)
lemma growFlags {v:Pane ν} (p:flags (T).threshold v=∅) : flags Λ.J.k v= ∅:=by
  have ht: (T).threshold≤ Λ.J.k:= (Y.history i' k').pole M
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i b; obtain ⟨c,t,u⟩ := (flags_spec ..).mp b; exact notMem_empty _ (p ▸ (flags_spec ..).mpr ⟨c,t,ht.trans_lt u⟩) -- need type
lemma guardedTop (x:Pane ν)(p:flags (T).threshold x= ∅): Cube.Guard x Λ.d := by
  let Z:=Papal.roofage Y i' M
  let v:Orbit ν:=⟨x,Classical.arbitrary _⟩
  have h:(YT M) v=x:=funext fun i=> Z.lamp x v.2 i (by simp [growFlags Y i' k' p])
  exact h ▸ Z.paid v
-- shape transformation where charge and det chosen false
lemma tenor (v:Pane ν) (a:Shape)(S:UNI SpinIdx)(t: JetS a.s false false S):
    Spire.arum (prepU a S (xtra false) _) false false (Dial.mateK _) (Zn v)= Zn (stir (xtra false) a v):= by
  let D:=prepU a S (xtra false) ν; let v':=stir (xtra false) a v
  let R : Set (Pane ν):={v|flags (T).threshold v = ∅}
  unfold capP; by_cases p:v∈R
  · rw [Set.indicator_of_mem p, Set.indicator_of_mem (show v'∈R from (stillMask a v).mpr p), arum_scale,
      change_g Λ.W.pearl Λ.V.note (Λ.J.gran.trans ((Y.voyage i').ownership M).size) (show 1 ≤ Λ.K.j by rw [Λ.kJ]; decide) v (guardedTop Y i' k' v p) babyM a false S t, basic_move]; rfl
  rw [Set.indicator_of_notMem p, Set.indicator_of_notMem (show v'∉R from mt (stillMask a v).mp p), arum_zero]
lemma sharpPitch (z:ℤ){f:Mark ν}(p:AtSupport false univ f):
   Journey.compass Y i' k' (Y.uv k') (reflMark j z (reflMark j 0 f))=Journey.compass Y i' k' (Y.uv k') f:=by
  unfold Journey.compass; apply congrArg (· / _); unfold markedRead
  let S:= around j z ν
  let A:=lagX ((0-z) • step j:Cover); let U := prepU A 1 (xtra false) ν
  let Z:=denZ (X M) Λ.U (YT M)
  let D(g:Mark ν) (v:Orbit ν):= letterRead (g (drawn (YT M) v)) (Z v)
  let G:=reflMark j z (reflMark j 0 f)
  change (∫ v,D G v∂city ν)=(∫ v,D f v∂city ν)
  rw [← (round_prior (N:=ν) j z).integral_comp' (D G)]
  apply integral_congr_ae; filter_upwards [drawn_round j z (Papal.roofage Y i' M)] with v p'
  have ht:JetS A.s false false 1 := calmSX
  let U₀:=Spire.arum U false false (Dial.mateK ν)
  have hx:Z (S v)=U₀ (Z v):=by unfold Z; rw [Y.whole,Y.whole,round_actual]; exact (tenor Y i' k' v.1 A 1 ht).symm -- alias
  unfold D; change inner ℂ (Dial.mateK ν) (acts (G (drawn (YT M) _)) _) = inner ℂ (Dial.mateK ν) (acts _ _); unfold G; rw [p',hx,paid_flipped j z f p]
  change inner ℂ (Dial.mateK ν) (acts (Spire.tourP U false false (f (drawn (YT M) v))) (Spire.arum U false false (Dial.mateK ν) (Z v)))=_
  rw [← arum_act U false false]; nth_rw 1 [← arum_self (q:=Dial.mateK ν) U false false (Tset ν) ((touchP ν) ▸ Dial.tickB ν) (tickR A inert 1 ht ν)]; exact arum_globe U false false (Tset ν) ((touchP ν) ▸ Dial.tickB ν) (tickR A inert 1 ht ν) _ _

private lemma moonRise {S:Side} (f:Mark S)(p:AtSupport false univ f)(z:ℤ): AtSupport false univ (reflMark j z f):=(p.refl j z).mono (Finset.subset_univ _)
lemma ascender_paid {s:ℕ}(z:Satin.PairIdx Y s i' k'){f:Mark (side Y i' s)}(q:AtSupport false univ f):AtSupport false univ (ascender Y s i' k' f):=by
 let Z:=music Y s i' k' (frock q); have h:attire Z=ascender Y s i' k' f:=flowing ..; rw [← h]; exact Tapestry.Ward.signs Z

lemma reflects_step {s:ℕ}(z:Satin.PairIdx Y s i' k'){f:Mark (side Y i' s)}(p:AtSupport false univ f) (a:ℤ):
 ascender Y s i' k' (reflMark j a (reflMark j 0 f))=
  reflMark j (Λ.R.L.val * a) (reflMark j 0 (ascender Y s i' k' f)):=by rw [ascendTurn Y s i' k' j a z (moonRise j f p 0),ascendTurn Y s i' k' j 0 z p,mul_zero] -- implicit names
lemma all_rungs {s:ℕ}(z:Tapestry.Pay Y s i' k'){f:Mark (side Y i' s)}(q:AtSupport false univ f) (v:ℤ):
  Journey.compass Y i' k' s (reflMark j v (reflMark j 0 f))=Journey.compass Y i' k' s f:= by
  suffices h:∀ t:ℕ,∀{s:ℕ},∀ (e:t+s=M){f:Mark (side Y i' s)} (q:AtSupport false univ f) (v:ℤ), Journey.compass Y i' k' s (reflMark j v (reflMark j 0 f))=Journey.compass Y i' k' s f from h (M-s) (Nat.sub_add_cancel z.2) q v
  intro t; induction t with
  | zero=>intro s k f p v; rw [Nat.zero_add] at k; subst s; exact sharpPitch Y j i' k' v p
  | succ t ih=>
    intro s g f p v; have ht:Satin.PairIdx Y s i' k':= ⟨z.1,by omega⟩
    rw [partake Y s i' k' ht (moonRise j _ (moonRise j f p 0) v),reflects_step Y j i' k' ht p v]
    exact (ih (show t+(s+1)=M by omega) (ascender_paid Y i' k' ht p) (Λ.R.L.val*v :ℤ)).trans (partake Y s i' k' ht p).symm

lemma shiftSharpFull {s:ℕ} (z:Tapestry.Pay Y s i' k') {F:Family (tent Y H)} (p: TestFamily K₁ true F) (v:ℤ) :
    sharp Y H s i' k' (chime K₁ j v F)= sharp Y H s i' k' F:=by
  unfold chime; rw [actualRead,actualRead]
  have ht(r) (F:Family (tent Y H)): exhibit Y H s i' (mirror K₁ j r F)=reflMark j r (exhibit Y H s i' F):= displayRef ..
  rw [ht,ht]
  exact all_rungs Y j i' k' z (safeNat Y H s i' (⟨F,p⟩: Dome (tent Y H))) v -- rewrite def inspect
include V in
lemma shiftRow {s:ℕ}{F:Family (tent Y H)} (p:TestFamily K₁ true F) (v:ℤ) : I s (chime K₁ j v F) i'= I s F i' := by
  have h:= V.together s F p; have hu:= V.together s (chime K₁ j v F) (aux_test (flow_port K₁ j v p.paid.choose_spec))
  exact tendsto_nhds_unique_of_eventuallyEq (hu.inner i') (h.inner i') ((V.pick.pass Y H s i').mono fun _ q=>shiftSharpFull Y H j i' _ ⟨q.depth,q.enters⟩ p v)
include V in
lemma shift_eFull {s:ℕ}{F:Family (tent Y H)}(p:TestFamily K₁ true F)(v:ℤ): E s (chime K₁ j v F)= E s F:=by
  have h:= V.together s F p; have u:=V.together s (chime K₁ j v F) (aux_test (flow_port K₁ j v p.paid.choose_spec)); exact tendsto_nhds_unique_of_eventuallyEq u.periods h.periods (Eventually.of_forall fun t=> shiftRow Y H V j (i t) p v)

end tranche
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.tenor
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.shiftSharpFull
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.shift_eFull
