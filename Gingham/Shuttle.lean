import Gingham.TopperWord
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration YM.Velour

lemma hitting {F:SampleDose}(h:F.Normalized): (tsupport F.val).Nonempty := by
  by_contra g
  have e:F.val=fun _=>0:= funext fun x=>by by_contra q; exact g ⟨x,subset_closure q⟩
  have t:=h.2
  simp [e] at t

lemma room_nonempty {F:SampleDose}(h:F.Normalized) {d:ℝ≥0}(u:0<d){l r:ℝ}
    (c:Corners 3 l r F d):l<r:=by
  obtain ⟨p,hp⟩:=hitting h
  obtain ⟨b,t⟩:=c p hp
  linarith only [show (0:ℝ)<d from u,b,t]

/-- Two-index trick. Bool true = G (earlier). -/
abbrev rise {X:Type} (g m:X) : Bool→X
  | true=>g
  | false=>m
local notation "N" => [true,false]
variable (a:Weave)

lemma byside : Umbrella N (rise a.blot a.well) a.gap:=by
  intro p t i
  have b:=a.stagger _ (a.ta (t true List.mem_cons_self)) _ (a.tb
     (t false (List.mem_cons_of_mem _ List.mem_cons_self)))|>.1 i
  rcases lt_or_ge (p true i) (p false i) with h|h
  · rw [abs_of_pos (sub_pos.mpr h)] at b
    exact ⟨N,.refl _,by simp; linarith only [b]⟩
  rw [abs_of_nonpos (sub_nonpos.mpr h)] at b
  exact ⟨[false,true],.swap ..,by simp; linarith only [b]⟩


lemma groove : EuOrder N (rise a.l (0:ℝ)) (rise (0:ℝ) a.r) := by
  refine ⟨?_,?_,?_⟩
  · exact fun i _=>by cases i
                      · exact room_nonempty a.well_one a.topay a.room_b
                      · exact room_nonempty a.blot_one a.topay a.room_a
  · simp [rise]
  · intro g m t u e
    have h := congrArg List.length e
    simp at h
    have g':List.length t=0:=by omega
    rw [List.length_eq_zero_iff.mp g'] at e
    simp at e
    rcases e with ⟨rfl,rfl,_⟩; rfl

variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


lemma single_grid_tends (J:P.Ellis 3 x)
    {l r:ℝ}{F:SampleDose}{d:ℝ≥0}(z:0<d)(u:F.Normalized)(q:Corners 3 l r F d)
    (g:Hook P x){s t:ℕ→ℕ}(n:Tendsto s atTop atTop) (b:Tendsto t atTop atTop)
    (r₀:∀ᶠ i in atTop, (g.arms.fieldA (s i)).s ≤ t i):
    Tendsto (fun i=>P.singleState 3 (t i) x (tile_read P g.arms F (s i) (t i))) atTop
      (𝓝 (cup ω₁ (P.flounce 3 ξ d l r (toll P x g d) F))):=by
  let f:=fun _:Bool=>l
  let w:=fun _:Bool=>r
  have h:EuOrder [true] f w:= by
    refine ⟨fun _ _=>room_nonempty u z q,by simp,?_⟩
    intro _ _ _ _ e; have t:=congrArg List.length e; simp at t; omega
  have he:Umbrella [true] (fun _=>F) (1:ℝ):=by
    intro p t i; exact ⟨_,.refl _,by simp⟩
  have e:= mirrorball P x 3 [true] f w (fun _=>d) (fun _=>F) (fun _=>g.arms)
    (fun _=>g.earns) J h (fun i _=> ⟨z,q⟩) zero_lt_one he
    (σ:=fun i _=>s i) (fun _ _=> n)
    b (r₀.mono fun _ h _ _=> h)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at e
  exact e

variable (g m:Hook P x)

abbrev Parts := ℂ × ℂ × ℂ
def discrepancy (r:Parts):ℂ:= r.1 - r.2.1*r.2.2

def tux {H:Hilbert} (u:H)(b c:H.Op) : Parts :=
   (coupled u b c, cup u b, cup u c)

abbrev AudEu : Parts :=
   tux ω₁ (EuLeft P x a (toll P x g)) (EuRight P x a (toll P x m))

abbrev BlotAt (i t:ℕ) := tile_read P g.arms a.blot i t
abbrev WellAt (j t:ℕ) := tile_read P m.arms a.well j t

/-- Height t elected mean on literal ordered pair and each marginal,
common ground and stamped data; with refinement, not necessarily pure. -/
def GridEu (i j t:ℕ):Parts :=
  let L:=BlotAt a P x g i t
  let R:=WellAt a P x m j t
  let E:=P.singleState 3 t x
  (E (L*R),E L,E R)
abbrev Height (i j t:ℕ):Prop :=
   (g.arms.fieldA i).s  ≤  t ∧ (m.arms.fieldA j).s  ≤  t


theorem shuttle (J:P.Ellis 3 x)
    {s m' t:ℕ→ℕ}(h:Tendsto s atTop atTop)
    (p:Tendsto m' atTop atTop)(b:Tendsto t atTop atTop)
    (r₀:∀ᶠ i in atTop, Height P x g m (s i) (m' i) (t i)):
    Tendsto (fun i=> GridEu a P x g m (s i) (m' i) (t i)) atTop
        (𝓝 (AudEu a P x g m)):=by
  let Z:=rise g m
  have e:=mirrorball P x 3 N (rise a.l 0) (rise 0 a.r) (fun _=>a.wound)
    (rise a.blot a.well) (fun i=>(Z i).arms) (fun i=>(Z i).earns)
    J (groove a) (fun i _=> ⟨a.topay,by cases i;exact a.room_b; exact a.room_a⟩)
    a.strict (byside a) (σ:=fun i=> rise (s i) (m' i))
    (fun i _=>by cases i;exact p; exact h) b (r₀.mono fun _ h i _=>by cases i;exact h.2;exact h.1)
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at e
  exact e.prodMk_nhds
    ((single_grid_tends P x J a.topay a.blot_one a.room_a g h b
        (r₀.mono fun _ t=>t.1)).prodMk_nhds
       (single_grid_tends P x J a.topay a.well_one a.room_b m p b (r₀.mono fun _ t=>t.2)))



structure InFoot (F:SampleDose) (b:Hook P x) (U:Set Vantage) (i t:ℕ):Prop where
  yes : (b.arms.fieldA i).s ≤ t
  physical : P.spacePrice (b.arms.fieldA i) F ⊆ U
  raw : P.asked_at t (tile_read P b.arms F i t) (P.spacePrice (b.arms.fieldA i) F)
  singlet : tile_read P b.arms F i t ∈ enclave P.calibration

/-- From the Shrink.lives calculation of Wicks in project (not
imported). Physical footprints paid inside the same neighborhood
of the compact test at **any** reading t covering the printed widths.
So `a.stagger` prices them TOO. -/
lemma foothold (b:Hook P x)(F:SampleDose) (U:Set Vantage)(o:IsOpen U)
    (h:tsupport F.val⊆U):
    ∀ᶠ i in atTop,∀t,(b.arms.fieldA i).s  ≤  t→ InFoot P x F b U i t:=by
  obtain ⟨δ,p,d⟩:= (show IsCompact (tsupport F.val) from F.budget).exists_thickening_subset_open o h
  have e(j:Axis): Tendsto (fun i=>(b.arms.fieldA i).realWidth P j) atTop (𝓝 0):=by
    simp_rw [Apron.width_real]; exact NNReal.tendsto_coe.mpr (b.earns.thin j)
  filter_upwards [eventually_all.mpr (fun j=>(e j).eventually (gt_mem_nhds p))] with i t₀ t hi
  obtain ⟨A,y,z⟩:= P.prepared_at t _ F hi
  refine ⟨hi,?_,⟨A,(bay P.calibration A true).smul_mem y _,z⟩,
    (enclave P.calibration).smul_mem (P.prepared_color t _ F) _⟩
  intro y f
  obtain ⟨k,v,f⟩:= Set.mem_iUnion₂.mp f
  refine d (mem_thickening_iff.mpr ⟨k,v,?_⟩)
  rw [dist_pi_lt_iff p]
  exact fun j=> (Real.dist_eq ..).trans_lt ((f j).trans_lt (t₀ j))


abbrev InBuoy (i k t:ℕ):Prop :=
     InFoot P x a.blot g a.ra i t ∧ InFoot P x a.well m a.rb k t

theorem wide_travel (J:P.Ellis 3 x)(W:Set Parts)(p:W∈𝓝 (AudEu a P x g m)):
     ∃ n,∀ i k t:ℕ, n ≤ i → n ≤ k → n ≤ t → Height P x g m i k t →
       InBuoy a P x g m i k t ∧ GridEu a P x g m i k t∈W:=by
   by_contra! h
   choose s₁ s₂ t u v w y z using h
   have q := tendsto_atTop_mono u tendsto_id
   have e := tendsto_atTop_mono v tendsto_id
   have b:= shuttle a P x g m J q e (tendsto_atTop_mono w tendsto_id) (Eventually.of_forall y)
   have m': ∀ᶠ _n:ℕ in atTop, False:=by
     filter_upwards [b.eventually p, q.eventually (foothold P x g a.blot a.ra a.oa a.ta),
           e.eventually (foothold P x m a.well a.rb a.ob a.tb)] with i h f g
     exact z i ⟨f _ (y i).1,g _ (y i).2⟩ h
   obtain ⟨i,h⟩:=m'.exists
   contradiction

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

