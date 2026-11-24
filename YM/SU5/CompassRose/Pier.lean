import YM.SU5.CompassRose.Stems
import YM.SU5.CompassRose.Petals

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open CF.Fir CF.Jill CF.Flare CF.Kea CF.Emu CF.Dial Lamour Lamour.Bridge Cache Glaze Next.Free Laurent
open WakeInvestment Gleam Gleam.Wake Regis.Head.Brecht
variable (P : Spine)(v : ℕ→ℕ)(β : ℕ→ℝ) (T : Pools P v β)
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
local notation "Y" => P.run
local notation "R" s:max A:max => sPow P.par s A
local notation "ζ" s:max A:max => zoomR P.par A s
variable {A:ℝ} (p:0<A)
local notation "Ω" z:max => (Y).uv (cᵥ z) - ((z:ℕ×ℕ).1)
local notation "B₀" z:max => P.par.V.L.mood (Ω z)
local notation "G₀" z:max => P.par.V.L.tied (Ω z)
abbrev grid (z:ℕ×ℕ) := stamen (B₀ z) (G₀ z) (More (O z))
local notation "φ" z:max => grid P v z
local notation "μ" z:max => stdGaussian (φ z)
local notation "χ₀" z:max => reachCost Y ((z:ℕ×ℕ).1) (pᵥ z) (cᵥ z) (κFix β ((z:ℕ×ℕ).1))
variable {I:Type*} (W:I→ℕ→Staff)
abbrev CTag (I:Type*) := I × SU.group.ColorIndex
def originBond (A:ℝ) (z:ℕ×ℕ) (i:CTag I) : grid P v z :=
   ((R z.1 A)^2 * χ₀ z) • trill (B₀ z) (G₀ z) i.2
     (wrap (More (O z)) (W i.1 z.1).face.1,plaquette (W i.1 z.1).face.2)
-- replicate horizon costs at every path period, keep orientation. Stability 
lemma tide (V: I→ℕ→Staff) {x y: Cover}{F G:PlaqAxes} {z : ℕ × ℕ}
    (i j: CTag I) (p: (W i.1 z.1).face=(x,F)) (q:(V j.1 z.1).face=(y,G)) :
    RoseGaussian.cost (originBond P v β W A z i) (originBond P v β V A z j) =
      (χ₀ z:ℂ)^2 * (sch (G:=SU.group) i.2 j.2:ℂ) * magnify
        (P.par.V.L.H (Ω z)) (R z.1 A) (plaquette F) (plaquette G) (x-y) (More (O z)) := by
  let n:= More (O z); let a := wrap n x; let b := wrap n y; let f:Body 2 n := (a,plaquette F); let g:Body 2 n := (b,plaquette G)
  let L:=trill (n:=n) (B₀ z) (G₀ z); let C:=P.par.V.L.H (Ω z)
  obtain ⟨r,V,_⟩ := (P.par.V.L.roof (Ω z))
  have he := chimes (B₀ z) (G₀ z) (V n) r P.par.K.width i.2 j.2 f g (show Even n.val from ⟨(O z).val,Nat.mul_two _⟩)
  simp_rw [←joy,appraisal] at he
  let U := R z.1 A
  have hv:magnify C U (plaquette F) (plaquette G) (x-y) n=(U:ℂ)^4*rimble n C f g:=by
    unfold f g; rw [magnify,rimflare n C _ 0 (x-y) (sub_zero ..),rimflare n C a b (x-y) (map_sub (wrap n) x y).symm]
  unfold RoseGaussian.cost originBond; rw [p,q];
  let T:= U^2 * χ₀ z
  change Complex.ofReal (inner ℝ (T • L i.2 f) (T • L j.2 g))=_
  rw [real_inner_smul_left (L i.2 f) (T • L j.2 g) T,real_inner_smul_right (L i.2 f) (L j.2 g) T,hv]; unfold L T; push_cast; rw [he]; unfold C U; ring

abbrev tideRow (x:I→Gaia) (F:I→PlaqAxes) (i j:CTag I) :ℂ:= (sch (G:=SU.group) i.2 j.2:ℂ)*specter (F i.1) (F j.1) (x i.1-x j.1)
variable {x:I→Gaia}{L:I→DirSpin}{F : I→PlaqAxes}{r w : I→ℕ→ℕ} (t:∀ i, LayoutBudget P A (x i) (W i) (r i) (w i) (F i) (L i))
include T p t
lemma tide_limit (i j: CTag I) (e : x i.1 ≠ x j.1) : Tendsto
    (fun z:ℕ×ℕ => RoseGaussian.cost (originBond P v β W A z i) (originBond P v β W A z j)) bobbin
    (𝓝 (tideRow x F i j)) := by
  let C : ℂ:=Fintype.card SU.group.ColorIndex; have hx:C≠0:=by
    unfold C; haveI : Nontrivial SU.group.Color:= Thera.yet_one.nontrivial_color; have ht:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
    change (Fintype.card (Fin SU.group.lieDim):ℂ) ≠0; rw [Fintype.card_fin]; exact_mod_cast ht.ne'
  let V(i:CTag I)(s:ℕ):= (W i.1 s).face.1
  let K(z:ℕ×ℕ):=P.par.V.L.H (Ω z); let X:=x i.1-x j.1;
  let S:=specter (F i.1) (F j.1) X
  let μ' (z:ℕ×ℕ):=magnify (K z) (R z.1 A) (plaquette (F i.1)) (plaquette (F j.1)) (V i z.1- V j z.1) (More (O z))
  have hh:Tendsto μ' bobbin (𝓝 S):=by
     have hp:Tendsto (fun z=>C*μ' z) bobbin (𝓝 (C*S)):= pair_photons (U:=V i) (V:=V j) P T (F i.1) (F j.1) (rungs_pos P) (sPower_pay P.par p) X (by simp_rw [rise_step]; exact (t _).face_target.sub (t _).face_target) (sub_ne_zero.mpr e)
     simpa [inv_mul_cancel_left₀ hx] using hp.const_mul C⁻¹
  let s (z:ℕ×ℕ):ℝ:= χ₀ z; have he := (((Complex.continuous_ofReal.continuousAt.tendsto.comp (reach_normalized (f:=v) P T)).pow 2).mul_const (↑(sch (G:=SU.group) i.2 j.2):ℂ)).mul hh
  rw [Complex.ofReal_one,one_pow,one_mul] at he
  apply he.congr; intro z; exact (tide (A:=A) (x:=V i z.1) (y:=V j z.1) (z:=z) (F:=F i.1) (G:=F j.1) P v β W W i j (Prod.ext rfl ((t i.1).plane z.1)) (Prod.ext rfl ((t j.1).plane z.1))).symm
omit T p t
local notation "Ξ" z:max => cargoShip P v W z
variable [Fintype I]
lemma actual_tilt (z:ℕ×ℕ) (Z:grid P v z) (i:CTag I) : inner ℝ (originBond P v β W A z i) Z=
    (R z.1 A)^2 * (Ξ z).siphon (χ₀ z) 1 0 P.par.K.top.clip i Z.val := by
  obtain ⟨X,uX⟩:= song (B₀ z) (G₀ z) Z
  have he:= congrArg Subtype.val uX
  let S:=Ξ z; let t:=χ₀ z
  let a:= W i.1 z.1; let q:=P.par.K.top.clip
  have ht:= S.belly (B₀ z) (G₀ z) t (fun x=> (x i:ℂ)) X
  change (↑(S.siphon t 1 0 q i (tiler (B₀ z) (G₀ z) X)):ℂ) = ↑(t* Work.F03.faceCurl (S.ua i) X (S.lens i)) at ht
  have hw:= Complex.ofReal_injective ht
  change tiler (B₀ z) (G₀ z) X = Z.val at he
  rw [he] at hw
  let L:=trill (B₀ z) (G₀ z) i.2 (wrap (More (O z)) a.face.1,plaquette a.face.2); let V0 := (R z.1 A)^2*t
  change inner ℝ (V0 • L) Z=_
  rw [real_inner_smul_left L Z V0]; unfold L; rw [joy,inspire]; rw [show _= _ from hw]
  rw [←he, Etch.river_now]; change _=_*( _ * Work.F03.faceCurl _ X i.2); change V0*_ = _; unfold V0; rw [mul_assoc]; rfl
--#print axioms tide_limit
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
