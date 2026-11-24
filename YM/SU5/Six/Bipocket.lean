import YM.SU5.FiniteGaugeData.Tapestry.Equivariant
import YM.SU5.FiniteGaugeData.Tower.Diagram
import YM.CF.Matter.Mass
/-! # Endpoint footprints of the two chiral letters

A property at ONE resolution, WITHOUT requiring generation diagonal
refinement. We use the exact pushMark implementation and modeGauge (merely
for a **constant central** SU gauge). Tests charge an actual pocket on the
lattice; next files in this series will descend this through the large
Tivoli sizes to the cover and the advancing marks of `Spine`. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 400000
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow.Tapestry Tower
variable (W:Bool)
def phaseName (W:Bool):ℂ:=SU.z^(if W then 2 else 4:ℕ)
lemma pname_unit : ‖phaseName W‖=1:=by unfold phaseName; rw [norm_pow,SU.z_n]; simp
lemma pname_ne (W:Bool):phaseName W≠1:= by
  intro t
  have hv:= SU.z_prim.dvd_of_pow_eq_one _ t
  cases W <;> norm_num at hv
lemma charge_identity (i:SU.Slot) : phaseName (Window.family i).2=SU.z^SU.charge i:= by
  rcases i with ⟨j,u|u⟩<;> rfl
lemma phase_injective : Function.Injective phaseName:= by
  have he: phaseName true≠phaseName false:=by
    intro h; exact (by decide:¬2=4) (SU.z_prim.pow_inj (by decide) (by decide) h)
  rintro (_|_) (_|_) <;> simp [he,Ne.symm he]
lemma center_commutes (x:SU.E): SU.central * x = x * SU.central := by
  apply Subtype.ext; apply Subtype.ext
  change Matrix.diagonal (fun _:SU.F=>SU.z) * SU.fund x = SU.fund x * Matrix.diagonal (fun _:SU.F=>SU.z)
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal,mul_comm]

def speciesSet (N:Side) (W:Bool): Finset (Single N):= univ.filter (fun i=>(Window.family i.2).2=W)

section finite
variable (N:Side) (S T: Support (More N))
lemma species_center (v:Ket (Single N))(i:Single N) : (acts (tradew N (fun _=>SU.central)).val v).ofLp i=
    phaseName (Window.family i.2).2*v.ofLp i:=by
  let A:=(tradew N (fun _=>SU.central)).val
  have he(x y:Single N): A x y=(Matrix.diagonal (fun j:Single N=> phaseName (Window.family j.2).2)) x y:= by
    rcases x with ⟨x,i⟩; rcases y with ⟨y,j⟩
    change jump (Equiv.refl (Site N × SpinIdx)) (fun i=> (SU.matter SU.central).val) (x,i) (y,j)= _
    rw [jump_apply]; simp only [Equiv.refl_apply]; split
    · next h=> subst y; rw [SU.by_charge]; by_cases w:i=j
               · subst j; rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]; exact (charge_identity _).symm
               rw [Matrix.diagonal_apply_ne _ w, Matrix.diagonal_apply_ne _ (by simp [w])]
    next e=> rw [Matrix.diagonal_apply_ne _ (by simp [e])]
  rw [act_at]; change (A *ᵥ _ ) i= _; rw [ Matrix.ext he, Matrix.mulVec_diagonal]
lemma species_iff {v:Ket (Single N)}:
    withinM (speciesSet N W) v ↔ acts (tradew N (fun _=>SU.central)).val v= phaseName W • v:= by
  constructor
  · intro h; apply PiLp.ext; intro i; rw [species_center]; change _= phaseName W*v.ofLp i
    by_cases t:i∈speciesSet N W
    · rw [(mem_filter.mp t).2]
    rw [(within_test ..).mp h i t,mul_zero,mul_zero]
  intro p; apply (within_test ..).mpr
  intro i hi
  by_contra q
  have hp: (Window.family i.2).2 = W:= by
    apply phase_injective; apply mul_right_cancel₀ q
    have hv:= congrArg (fun x:Ket _=> x.ofLp i) p
    exact (species_center N v i).symm.trans hv -- argument order
  exact hi (mem_filter.mpr ⟨mem_univ _,hp⟩)

/-- Single creation in S, single removal in T. When charged as a product
 word put the removal first. Exterior signs use the actual Fock convention. -/
def bipocket (N:Side)(W:Bool)(S T:Support (More N)):Submodule ℂ (FC (Single N)) :=
  Submodule.span ℂ {x | ∃ a b:Ket (Single N), withinM (Tset N) a ∧ withinM (speciesSet N W) a ∧ withinM (modesIn N S) a ∧
    withinM (Tset N)ᶜ b ∧ withinM (speciesSet N W) b ∧ withinM (modesIn N T) b ∧ x = Fock.remove b * create a}
lemma bipocket_mono {S S' T T':Support (More N)}(p:S⊆S')(t:T⊆T') : bipocket N W S T≤bipocket N W S' T':= by
  refine Submodule.span_mono ?_
  rintro x ⟨a,b,u,v,r,w,q,h,c⟩
  exact ⟨a,b,u,v,(within_test ..).2 (fun i y=> (within_test ..).1 r i fun k=>y (modes_monotone p k)),
    w,q,(within_test ..).2 (fun i y=>(within_test ..).1 h i fun k=> y (modes_monotone t k)),c⟩
lemma generator {a b:Ket (Single N)} (u:withinM (Tset N) a) (v:withinM (speciesSet N W) a) (r:withinM (modesIn N S) a)
    (w:withinM (Tset N)ᶜ b) (q:withinM (speciesSet N W) b) (t: withinM (modesIn N T) b) : Fock.remove b * create a ∈ bipocket N W S T :=
  Submodule.subset_span (show _ ∈ _ from ⟨a,b,u,v,r,w,q,t,rfl⟩)
end finite
lemma center_nom {N P:Side} (G:Ratio N P) (x:Nom N P) : july G (fun _=>SU.central) x=x:= by
  have he {N:Side}(v:Pane N) : Lattice.gauge (fun _=> SU.central) v=v:= by
    funext i; rw [Lattice.gauge,center_commutes,mul_inv_cancel_right]
  exact Prod.ext (he _) (he _)
section push
variable {N P:Side}(G:Ratio N P)(j:ℕ)(Q:Haro.SpaceM)(M:Male)(ho:Odd G.count.val)
  {R:ℕ}(p:LaurentRadius j G.count R)
local notation "S₊" S:max => Advance.padded G S (clothRadius G.count R)
include p ho
lemma byMode_species {x:Nom N P}{v:Ket (Single N)} (h:withinM (speciesSet N W) v) (c:Bool) :
    withinM (speciesSet P W) (byMode G j Q.val M x c v):= by
  apply (species_iff ..).mpr
  rw [modeGauge G (fun _ => SU.central) j p ho M Q,center_nom]; exact
    (congrArg (byMode G j Q.val M x c) ((species_iff ..).mp h)).trans (map_smul ..)
lemma sub_bipocket (S T:Support (More N))(x:Nom N P){a:FC (Single N)}(h:a∈bipocket N W S T) :
    subF G j Q.val M ho x a∈ bipocket P W (S₊ S) (S₊ T) := by
  let B:=bipocket P W (S₊ S) (S₊ T)
  refine Submodule.span_induction (p:=fun z _=> subF G j Q.val M ho x z∈B) (fun z r=>?_) ?_ ?_ ?_ h
  · obtain ⟨a,b,u,v,r,w,q,t,e⟩:=r; rw [e, sub_mul G j Q.val M ho _ (fine_remove _ w (within_univ _)) (fine_create _ u (within_univ _)), sub_remove G j Q.val M ho _ w,sub_create G j Q.val M ho _ u]
    exact generator W P (S₊ S) (S₊ T)
      (carried_up G j Q.val M ho x true u) (byMode_species W G j Q M ho p v _)
      (mode_support G j Q.val M ho S p r _) (carried_down G j Q.val M ho x false w)
      (byMode_species W G j Q M ho p q _) (mode_support G j Q.val M ho T p t _)
  · rw [map_zero]; exact B.zero_mem
  · intro a b _ _ e h; rw [map_add]; exact B.add_mem e h
  intro c a _ e; rw [map_smul]; exact B.smul_mem _ e

variable (A:StepData (More N) (More P))(q:Chi)(d β:ℝ)(l:Loom N)
lemma pushMark_bipocket (S T:Support (More N))(t:Measurable l)
    (u:A.patch.Branches A.kernel SU.group)(a:0<d)(b:2*d<firstRadius SU.group)
    (f:Mark N)(he:Envelope f)(h:∀ x,f x∈bipocket N W S T)(v:Fields P):
    pushMark G A j Q.val M ho q d β l f v∈bipocket P W (S₊ S) (S₊ T):=by
  rw [outright G A j Q.val M ho q d β l p t u a b _ he]
  let X:=(bipocket P W (S₊ S) (S₊ T)).restrictScalars ℝ
  apply X.convex.integral_mem X.closed_of_finiteDimensional _ (pushIntegrable G A j Q.val M ho q d β l f p t u a b he v v.1)
  apply Eventually.of_forall; intro i
  apply X.smul_mem
  unfold gathered avgF
  apply X.smul_mem
  apply X.sum_mem
  intro j' _
  exact sub_bipocket W G j Q M ho p S T _ (h _)
end push
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ)
local notation "N" => side Y i s
local notation "P" => side Y i (s+1)
local notation "G"=> (Vale.apt (Y.ir i) Λ.block Λ.R.L s)
local notation "R"=> aliasLaw Λ
local notation "Z"=> ((Y.voyage i).X (Y.uv k))
lemma footprint_step (S:Finset Cover) : Advance.padded G (Satin.region S N) (clothRadius Λ.R.L R) ⊆ Satin.region (wingspan Λ l S) P:= by
  have u : beforePad R ≤ Advance.gross R (distanceLaw l) Λ.R.J:=by unfold Advance.gross; omega
  let D:=Λ.R.L.val* Advance.gross R (distanceLaw l) Λ.R.J
  have he: Advance.padded G (Satin.region S N) D ⊆ Satin.region (wingspan Λ l S) P :=
    next_contains S D N G
  have hp: halo (4* Λ.R.L.val) (Advance.padded G (Satin.region S N) (clothRadius Λ.R.L R)) ⊆
      Advance.padded G (Satin.region S N) (Λ.R.L.val * beforePad R):= before_zone G (Satin.region S N) R
  have ht: Advance.padded G (Satin.region S N) (Λ.R.L.val * beforePad R) ⊆ Advance.padded G (Satin.region S N) D:= Corona.halo_mono (Nat.mul_le_mul_left _ u) (by rfl)
  exact (halo_subset _ (Advance.padded G (Satin.region S N) (clothRadius Λ.R.L R))).trans ((hp.trans ht).trans he)
lemma ascend_bipocket (S T:Finset Cover) (f:Mark (side Y i s))(he:Envelope f)
    (v:∀ x,f x∈bipocket (side Y i s) W (Satin.region S N) (Satin.region T N))
    (p: Satin.PairIdx Y s i k)(x:Fields P):
    Tapestry.ascender Y s i k f x ∈ bipocket P W (Satin.region (Tower.wingspan Λ l S) P) (Satin.region (Tower.wingspan Λ l T) P):=by
  have a:= (fullness Y i k p.1).cap_grant
  obtain ⟨L⟩:= a.grant s p.2
  apply bipocket_mono W _ (footprint_step Y s i S) (footprint_step Y s i T)
  exact pushMark_bipocket W G Λ.K.j (patternQ Y s i k) ((Z).gram (s+1)).J.M
    Λ.R.odd_side (Journey.legal Λ) (steps Λ.V (Y.ir i) Λ.block (Y.uv k) s) Chi.canonical Λ.J.d
    ((Z).gram (s+1)).beta ((Y.voyage i).CapeT s) _ _ ((Y.voyage i).ownership s).paid.bill (a.branch s p.2)
    L.legal.1 L.legal.2 f he v x
end YM.CF.Buffered.Afterglow.Six
