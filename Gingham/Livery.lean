import Gingham.Linsey
import Gingham.Relief
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
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


open SatinRegistration
variable {ι:Type}[Fintype ι][DecidableEq ι]
lemma arrow_rank {A B : ι→ Quote P x}
    (w :∀i,(𝓢).Covetails (A i)) (c :∀i,(𝓢).Covetails (B i))
    {s t : ℝ≥0} (a:0<s) (b:0<t)
    (z:Vantage)(v:∀ j,z j ≠ 0)
    (n: ProofRank (Matrix.of fun i j=>inner ℂ (jut ω₁ (A i s))
              (V z (jut ω₁ (B j t)))) ≠ 0):
    ∃ r : ℝ≥0, ∃ p q:Vantage, 0<r ∧
      p 3= -(r:ℝ) ∧ q 3=r ∧ (∀ j, j ≠ 3→p j≠q j) ∧ 2*(r:ℝ)< |q 0 - p 0| ∧
      ProofRank (Matrix.of fun i j=>inner ℂ (stood P x (A i r) p)
        (stood P x (B j r) q)) ≠ 0 := by
  let d : ℝ≥0 := ⟨|z 0|/2,(half_pos (abs_pos.mpr (v 0))).le⟩
  simp_rw [P.uses_cart] at n
  obtain ⟨r,h,g,m⟩ := downward_rank 𝓢 ω₁ _ _ (home_basis P x) w c a b
      _ n d (show (0:ℝ) < d from half_pos (abs_pos.mpr (v 0)))
  let p(i:Axis) := if i=3 then -(r:ℝ) else 0
  let q(i:Axis) := if i=3 then (r:ℝ) else z i
  refine ⟨r,p,q,h,if_pos rfl,if_pos rfl,fun j t => ?_,?_,?_⟩
  · simp only [p,q,t,ite_false]; exact (v _).symm
  · change (r:ℝ) < |z 0|/2 at g
    simp only [p,q,show (0:Axis) ≠ 3 by decide,ite_false,sub_zero]; linarith -- fin simp neq
  simp_rw [V_stood]
  have ep : V p = ContinuousLinearMap.id ℂ (G).space := by
    rw [P.uses_cart]
    have ef : transverse 3 (fun i=>p i.val)=0 := by
      ext i
      by_cases g:i=3
      · subst i; rfl
      change _=(0:ℝ)
      simpa! only [p,g,ite_false] using
           transverse_eyes 3 (fun j=>p j.val) ⟨i,g⟩ --?
    rw [ef,(𝓢).uZero]
  simp_rw [ep,ContinuousLinearMap.id_apply,P.uses_cart]
  have ef : (fun i:Trans 3=> q i.val) = fun i=> z i.val := funext fun i=> if_neg i.property
  simp_rw [ef]; exact m



lemma red_alert {f:ι→ι→ℕ→ℂ}{z:ι→ι→ℂ}
    (p:∀i j,Tendsto (f i j) atTop (𝓝 (z i j)))
    (e:ProofRank (Matrix.of z)≠0):
    ∀ᶠ k in atTop, ProofRank (Matrix.of fun i j=> f i j k) ≠ 0 :=
  ((rank_warm.tendsto _).comp
      (show Tendsto (fun k=>Matrix.of fun i j=> f i j k) atTop (𝓝 (Matrix.of z)) from
       tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr (p i)))).eventually_ne e

def Comes (a:Weave) (L M:ι→Quote P x) (l m:ι→(𝓢).Detector):Prop :=
  Scrive a ∧
  ProofRank (Matrix.of fun i j=>
    fault ω₁ (EuLeft P x a (L i)) (EuRight P x a (M j))) ≠ 0 ∧
  ProofRank (Matrix.of fun i j=>
    rfault 𝓢 Ω (RealLeft P x a (l i)) (RealRight P x a (m j))) ≠ 0

theorem colored {A B L:ι→Quote P x}
    (w :∀i,(𝓢).Covetails (A i)) (c :∀j,(𝓢).Covetails (B j))
    {s t : ℝ≥0} (a:0<s) (b:0<t)
    (y:Vantage)(v:∀j,y j ≠ 0)
    (u:ProofRank (Matrix.of fun i j=>inner ℂ (jut ω₁ (A i s))
           (V y (jut ω₁ (B j t)))) ≠ 0)
    {f ℓ g:ι→(𝓢).Detector}
    (F :∀i, (𝓢).Instates (A i) (f i)) (J :∀i,(𝓢).Instates (L i) (ℓ i))
    (hs:∀ i, ∀d:ℝ≥0, 0<d → star (A i d)=L i d)
    (M :∀j,(𝓢).Instates (B j) (g j)) :
    ∃ i:Weave, Comes P x i L B ℓ g := by
  obtain ⟨h,p,q,z,pp,qq,span,spac,e⟩ := arrow_rank P x w c a b y v u
  let X := nib p
  let Y := nib q
  let px := nib_to p
  let qy := nib_to q
  have rx (u:Vantage) (v) (m:ℕ→SampleDose)(k:Condenses u m) :
    Tendsto (fun i=>age 𝓢 (-(u 3))
         (jut ω₁ ((𝓢).rasp v (sachet_LocalFieldBounds (m i)))))
       atTop (𝓝 (stood P x v u)) := realBeam P x k v

  have active := red_alert (fun i j=>(rx p (A i h) X px).inner
       (rx q (B j h) Y qy)) e
  let Yu (i:ℕ) (t:ℝ) := trim (Y i) (foldSpace (t • basis 3))
  let fires (i:ℕ) (t:ℝ) :=
    |t| < (1/2:ℝ)^i ∧
    ProofRank (Matrix.of fun k j=>rfault 𝓢 Ω
         (ℓ k (sachet_LocalFieldBounds (X i))) (g j (sachet_LocalFieldBounds (Yu i t)))) ≠ 0
  have moves : ∀ᶠ i in atTop, ∃ t, fires i t := by
    filter_upwards [active] with i ep
    have mt := fun k=>(F k).mirror (J k) ((eventually_mem_nhdsWithin).mono fun d ht=>hs k d ht)
       (sachet_LocalFieldBounds (X i))
    rw [sachet_bar] at mt
    simpa only [fires,Yu,trim_ahead] using
       sunup_rank 𝓢 Ω (home_basis P x) (home_norm P x)
         F M (sachet_LocalFieldBounds (X i)) (sachet_LocalFieldBounds (Y i)) mt z z
         (-(p 3)) (-(q 3)) ep ((1/2:ℝ)^i) (pow_pos (by norm_num) _)
  let jog (i:ℕ) : ℝ := if k:∃ t, fires i t then k.choose else 0
  have hp : ∀ᶠ i in atTop, fires i (jog i) := moves.mono fun i k=>by
    unfold jog; rw[dif_pos k]; exact k.choose_spec

  let U (i:ℕ) := Yu i (jog i)
  have k : Condenses q U :=
    condenses_after qy (convergeJog jog (hp.mono fun i h=>h.1))
  have eu := red_alert (fun i j=>Eu_imag P x z pp qq _ _ (w i) (c j) px k) e
  have pv : ∀ᶠ _a:ℕ in atTop, ∃ i:Weave, Comes P x i L B ℓ g := by
    filter_upwards [weaves_late h p q z px k pp qq span spac,eu,hp] with n he f y
    obtain ⟨i,bl,wl,wo,l,r⟩ := he
    refine ⟨i,⟨n,p,q,_,y.1,bl,wl⟩,?_,?_⟩
    · unfold EuLeft EuRight
      simp_rw [bl, wl,wo,l,r, ← hs _ _ (half_pos z)]
      push_cast -- coe part
      exact f
    · simp_rw [RealLeft,RealRight,bl,wl]
      exact y.2
  obtain ⟨i,z⟩ := pv.exists; exact z


variable (L M:ι→Hook P x)
local notation "𝒮"=> toll P x
local notation "𝒫"=> pelisse P x
local notation "west'" => fun (i : ι)=> (L i).west P x

abbrev Knife (v:Vantage) (s t:ℝ≥0):Matrix ι ι ℂ :=
   Matrix.of fun i j=> inner ℂ (jut ω₁ (𝒮 (L i) s))
                  (V v (jut ω₁ (𝒮 (M j) t)))

theorem stir (v:Vantage)(p:∀i,v i≠0) {s t:ℝ≥0}
    (h:0<s)(e:0<t)
    (z:ProofRank (Knife P x L M v s t)≠0):
    ∃ a:Weave, Comes P x a (𝒮 ∘ (west')) (𝒮 ∘ M)
       (𝒫 ∘ (west')) (𝒫 ∘ M):=
   colored P x (A:=𝒮 ∘ L) (fun i=>(paid_on_G ..).1)
      (fun i=> (paid_on_G ..).1) h e v p z
      (f:=𝒫 ∘ L) (fun i=>collects P x _)
      (fun i=> collects P x _) (fun i s _=>toll_adj P x (L i) s)
      (fun i=> collects P x _)


def Spike (A:Matrix ι ι Parts) (δ:ℝ):Prop :=
    8 * δ < ‖Matrix.det (Matrix.of fun i j=> discrepancy (A i j))‖ ∧
    ∀i,Jubilation (A i i) δ

def Inflow (A:Matrix ι ι Parts) (δ:ℝ):Prop :=
    ∀B:Matrix ι ι Parts,(∀i j, Topaz (B i j) (A i j) δ)→ Spike B δ

lemma ticket_rank {A:Matrix ι ι Parts}
    (h:ProofRank (Matrix.of fun i j=>discrepancy (A i j))≠0):
    ∀ᶠ δ in 𝓝[>] (0:ℝ), Inflow A δ:=by
  let p := 𝓝[>] (0:ℝ)
  let z(B:Matrix ι ι Parts):Matrix ι ι ℂ:=
    Matrix.of fun i j=> discrepancy (B i j)
  have e := (rank_iff _).mp h
  -- a failing B for each δ if exists, else A
  let B (d:ℝ) := if q:∃b:Matrix ι ι Parts,(∀i j, Topaz (b i j) (A i j) d) ∧ ¬Spike b d
      then q.choose else A
  have pays:∀ᶠ d in p,∀i j,Topaz (B d i j) (A i j) d:=by
    filter_upwards [eventually_mem_nhdsWithin] with d (hd:0<d)
    unfold B
    split
    · rename_i k; exact k.choose_spec.1
    exact fun i j=>Topaz.refl _ hd
  have t₀:Tendsto id p (𝓝 0):=tendsto_id.mono_left nhdsWithin_le_nhds
  have t:Tendsto (fun d=>z (B d)) p (𝓝 (z A)):=by
    apply tendsto_pi_nhds.mpr; intro i
    apply tendsto_pi_nhds.mpr; intro j
    have t : Tendsto (fun d=>(B d i j).1) p (𝓝 (A i j).1) :=
       tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg)
            (pays.mono fun d u=> (u i j).1.le) t₀)
    have s : Tendsto (fun d=>guess (B d i j)) p (𝓝 (guess (A i j))) :=
       tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg)
            (pays.mono fun d u=> (u i j).2.1.le) t₀)
    exact t.sub s
  have d₀:Tendsto (fun d=> 8*d) p (𝓝 0):= by simpa using t₀.const_mul 8
  have a':∀ᶠ d in p,Spike (B d) d:=by
    have v:Tendsto (fun d=> ‖(z (B d)).det‖) p (𝓝 ‖(z A).det‖):=
       ((continuous_id.matrix_det.tendsto _).comp t).norm
    have b:=d₀.eventually_lt v (norm_pos_iff.mpr e.1)
    have q :∀ᶠ d in p,∀i,Jubilation (B d i i) d:=eventually_all.mpr fun i=>
       d₀.eventually_lt (((continuous_id.matrix_elem i i).continuousAt.tendsto.comp t).norm) (norm_pos_iff.mpr (e.2 i))
    exact b.and q
  refine a'.mono (fun d y B' u=>by
     by_contra q
     have hv:∃b:Matrix ι ι Parts,(∀i j, Topaz (b i j) (A i j) d) ∧ ¬Spike b d:=
        ⟨B',u,q⟩
     unfold B at y;rw [dif_pos hv] at y
     exact hv.choose_spec.2 y)



abbrev EUCard (a:Weave):Matrix ι ι Parts :=
   Matrix.of fun i j=> AudEu a P x (L i) (M j)
abbrev RealCard (a:Weave):Matrix ι ι Parts :=
   Matrix.of fun i j=> AudReal a P x (L i) (M j)

/-- simultaneous paid strict budget for width pricing -- both Eu and real prices. -/
structure Force (a:Weave)(δ:ℝ):Prop where
   normalized:Scrive a
   can_pay:0<δ
   eg:Inflow (EUCard P x L M a) δ
   rg:Inflow (RealCard P x L M a) δ
   el:∀i j,∃ n,∀ u v t:ℕ, n ≤ u→n ≤ v→n ≤ t→Height P x (L i) (M j) u v t →
      InBuoy a P x (L i) (M j) u v t ∧
      Topaz (GridEu a P x (L i) (M j) u v t) (AudEu a P x (L i) (M j)) δ
   rl:∀i j,
    ∀ᶠ e in 𝓝[>] (0:ℝ≥0),
       Topaz (StageReal a P x (L i) (M j) e) (AudReal a P x (L i) (M j)) δ ∧
       ∃ n:ℕ,∀ u v:ℕ,n ≤ u→ n ≤ v→
        HeatPaid P x (L i) (M j) e u v ∧
        Topaz (WidthReal a P x (L i) (M j) e u v) (AudReal a P x (L i) (M j)) δ


lemma refuses (A:Matrix ι ι Parts){δ:ℝ} (e:0<δ) (h:Inflow A δ): Spike A δ :=
  h A (fun i j=>Topaz.refl _ e)

lemma Force.glows {a:Weave}{δ:ℝ}(h:Force P x L M a δ) (i:ι):
    Glory a P x (L i) (M i) δ :=
   ⟨h.can_pay,(refuses _ h.can_pay h.eg).2 i,(refuses _ h.can_pay h.rg).2 i,
     h.el i i,h.rl i i⟩

lemma abreast (e:P.Ellis 3 x){a:Weave}
    (h:Comes P x a (𝒮 ∘ L) (𝒮 ∘ M) (𝒫 ∘ L) (𝒫 ∘ M)):
    ∃ δ,Force P x L M a δ:=by
   have i:= ticket_rank (A:=EUCard P x L M a) h.2.1
   have j:= ticket_rank (A:=RealCard P x L M a) h.2.2
   obtain ⟨δ, p,q,r⟩:=(eventually_mem_nhdsWithin.and (i.and j)).exists
   refine ⟨δ,h.1,p,q,r,fun i j=>
      wide_travel a P x _ _ e _ (likelier _ _ (Topaz.refl _ p)), ?_⟩
   intro i j
   have n:=(rt_without a P x (L i) (M j)).eventually
       (likelier _ _ (Topaz.refl _ p))
   filter_upwards [n,eventually_mem_nhdsWithin] with e he b
   exact ⟨he,resists a P x _ _ _ b _ (likelier _ _ he)⟩

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
