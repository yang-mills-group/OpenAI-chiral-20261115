import GaugeFieldConstruction.StencilProjection
import GaugeFieldConstruction.Porches
import GaugeFieldConstruction.SoulBreadNX
import YM.SU5.Assay.RawLag
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
open SelectionAnalysis Heat
namespace Discipline
variable (P:Spine) (i:Axis)(x:P.Spectrum0 3)
local notation "ν" => P.advocate 3 x i
local notation "H"=> P.ColorHil i ν
local notation "B"=> P.ManyF i ν
local notation "J"=> P.gnsIn i ν
local notation "C"=> P.privateH x i
local notation "V"=> P.voyageF i ν
local notation "D"=> (C).DegreeHab
local notation "S"=> P.seasons i ν
local notation "T"=> (C).BrightHab
local notation "Κ"=> (C).canopy.track
local notation "μ"=> marks (timeMesh P.par)
abbrev ladderFrameSt (k:P.Slabs i): (D).Op:=((C).canopy.track.aviator (C).canopy.list).orthogonalProjectionOnto ∘L (C).ρ k ∘L ((C).canopy.track.aviator (C).canopy.list).subtypeL
-- GNS profiles
lemma gnsEvents (j:Trans i)(a: μ) : (J).toContinuousLinearMap.comp (((V).crew j).play a) = (((Κ).crew j).play a).comp (J).toContinuousLinearMap:=by
 obtain ⟨t,p,rfl⟩:= notch_exists _ a
 rw [P.meets i ν j t p,(C).canopy_plays]; exact P.restrict_flight i ν (P.walksColor i (t,p,j))
noncomputable def passFrame : B →ₗᵢ[ℂ] D := Alliance.mapLevels (V) (Κ) (look i) (J) (gnsEvents P i x)
local notation "Λ_"=> passFrame P i x
lemma pocketGns(x':B) : ((Λ_) x').val= (J) ((P.enter i ν) x'):= rfl
lemma frameHeavenL : (Λ_) (P.heaven i ν) = (C).groundHab := Subtype.ext (P.present0 i ν)
lemma frameHeat (t:ℝ≥0) : (Λ_).toContinuousLinearMap.comp ((S).E t)= ((T).E t).comp (Λ_).toContinuousLinearMap:=by ext1 y; exact Subtype.ext (P.warmTransit i ν t y.val)
lemma frameSpace (t:OS.Cross i) : (Λ_).toContinuousLinearMap.comp ((S).U t)= ((T).U t).comp (Λ_).toContinuousLinearMap:=by ext1 y; exact Alliance.flightLevels (V) (Κ) (daylight _) (look i) (J) (gnsEvents P i x) (fun m=> t.val m.val) y
local notation "Πz"=> (Λ_).toContinuousLinearMap
noncomputable def projectPrice (U:P.Slabs i): (B).Op := (Πz).adjoint.comp ((ladderFrameSt P i x U).comp Πz)
local notation "Π"=> projectPrice P i x
lemma projected_symSt (A:P.Physical i)(u:B) : (Λ_) (P.reprise i ν (P.colorSpace i ν A) u) = ladderFrameSt P i x A.val (Λ_ u) := by
 have h: P.wealth i ν = ((V).aviator (look i)).orthogonalProjectionOnto :=by
    ext1 y; apply Subtype.ext; exact DFunLike.congr_fun (P.visitors_op i ν) y
 change (Λ_) ((P.wealth i ν) (P.colorSpace i ν A u.val))= _; rw[h]; exact Alliance.mapFrameL (V) (Κ) (look i) (J) (gnsEvents P i x) _ _ (P.restrict_flight i ν A) u
lemma notLoss (A:P.Physical i) : projectPrice P i x A.val=P.reprise i ν (P.colorSpace i ν A):=by
 ext1 y; change (Πz).adjoint (ladderFrameSt P i x A.val (Λ_ y))= _; rw [← projected_symSt]; exact DFunLike.congr_fun (Λ_).adjoint_comp_self _
-- estimates
noncomputable def projectLine : (P.Slabs i) →ₗ[ℂ] (B).Op where
 toFun := (Π)
 map_add' a b := by simp [projectPrice,ladderFrameSt]
 map_smul' a b := by simp [projectPrice,ladderFrameSt]

private lemma nestPrice (A:P.Physical i) : ‖(Π) A.val‖ ≤ ‖A.val‖:=by rw [notLoss]; exact (P.reprise_pay _ _ _).trans (NonUnitalStarAlgHom.norm_apply_le (P.colorSpace i ν) A)
lemma shadowCost (p q:P.Slabs i)(u:p∈P.neutralSlabs i)(v:q∈P.neutralSlabs i): ‖(Π) p-(Π) q‖≤ ‖p-q‖:=by
 let L:=projectLine P i x; change ‖L p-L q‖≤ _; rw [←map_sub]; exact nestPrice P i x (⟨_, sub_mem u v⟩:P.Physical i)
local notation "d"=> P.neutralSlabs i
lemma lamp_shadow {t s:ℕ}{f:P.Test}(g:f∈enclave P.calibration)(v:P.BEntry i t f): P.HabBox i s t f =(P.doorBox i s t f).val := Subtype.ext ((heard_box s v).trans (doorBox_val s v g).symm)
lemma tintShadow (A B': P.meshPin)(Z:P.Slabs i)(F:P.Test)(g:F∈enclave P.calibration)(s:ℕ)(h:P.Habitable i F s A B' Z): Z∈ P.neutralSlabs i:=by
 obtain ⟨t,hp,j,b,u,a,H0,rfl⟩:=h
 rw [lamp_shadow P i (P.shifts_keep i _ (P.refine_keeps _ _ g _)) H0]; exact Subtype.property _
#print axioms passFrame
#print axioms frameHeat
#print axioms frameSpace
#print axioms notLoss
#print axioms tintShadow


-- framed cost. Actual Apron at declared width, preserve for ALL pads. Does not
-- claim a Venue of fixed sky units, just level. Telescope notation with real mesh units.
lemma costHeatSt (A: P.Slabs i)(h:A∈ P.neutralSlabs i)(l r:ℝ): projectLine P i x (P.hearthNX i l * A * P.hearthNX i r)=(S).sand ((Π) A) l r:=by
 let t:=P.risesColor i l.toNNReal; let u:=P.risesColor i r.toNNReal; let Z:P.Physical i:=⟨_,h⟩
 change (Π) (t*Z*u).val=(S).sand ((Π) Z.val) l r
 rw [notLoss P i x (t*Z*u),notLoss P i x Z,map_mul,map_mul]; exact P.reprise_sand i ν _ l r

lemma regionHeatSt (A:P.Apron)(u w:P.meshPin)(l:A.realWidth P i ≤ (u:ℝ))(r:A.realWidth P i≤ (w:ℝ)):
    let z:=P.grantGapNX i A.s (A.u i) A.F (u:ℝ) (w:ℝ); P.Habitable i A.F A.s (-u) w z ∧ projectPrice P i x z=P.base i ν A (u:ℝ) (w:ℝ):=by
 intro z; let F:= A.F; let m:=A.s; let h:=A.u i; let K:=P.shifts i h F; let X:=P.HabBox i m (h+h) K
 have hm : A.realWidth P i=P.tock A.s (A.u i):=rfl
 have hz:P.Habitable i F m (-u) w z:= hearthPayNX i m h (A.admit i) (hm ▸ l) (hm ▸ r)
 refine ⟨hz,?_⟩; let S':= P.physicalEnergy i ν; let L:=(u:ℝ)-A.realWidth P i; let R:=(w:ℝ)-A.realWidth P i
 have hk: X=(P.doorBox i m (h+h) K).val:= lamp_shadow P i (A.color P i) (A.admit i)
 change projectLine P i x (P.hearthNX i L * X * P.hearthNX i R)=_
 rw [hk,costHeatSt P i x _ (P.doorBox ..).property,notLoss,Spine.base,P.engine_seen]; rfl

lemma shadowOwnSt (A:P.Apron) {l r:ℤ}(h:(-(l:ℤ))≤ -((A.u i):ℤ))(q:((A.u i):ℤ)≤r): P.HabitLevel i A.F A.s (-P.stampPin A.s l) (P.stampPin A.s r) (P.grantGapNX i A.s (A.u i) A.F (P.stampPin A.s l:ℝ) (P.stampPin A.s r:ℝ)) A.s:=by
    have hu:P.Marrow i A.s ((P.stampPin A.s (-((A.u i):ℤ))):ℝ) ((P.stampPin A.s (A.u i)):ℝ) A.S:=by apply (Marrow.at_size A.S).2; rw [← neg_mul_eq_mul_neg]; simpa [neg_mul] using A.shelter i
    let n:=(l+r).toNat; have hv0:0<(A.u i):=A.pos i; have he:(n:ℤ)=l+r:=Int.toNat_of_nonneg (by omega); have hs:-l+(n:ℤ)=r:=by omega
    have hx:= BEntry.mesh_frame A.bay (s:=A.s) (j:=i) (a:=-l) (w:=n) (by omega) fun x k=> And.intro (le_trans ((minted_le ..).mpr h) ((hu x k).1)) ((hu x k).2.trans (by rw [hs]; exact (minted_le ..).mpr q))
    let X:=P.HabBox i A.s n (P.shifts i (- -l) (P.conveying A.s (A.s-A.s) A.F)); let U₀:=P.grantGapNX i A.s (A.u i) A.F (P.stampPin A.s l:ℝ) (P.stampPin A.s r:ℝ)
    have hp:P.HabitLevel i A.F A.s (-P.stampPin A.s l) (P.stampPin A.s r) X A.s:=⟨le_rfl,-l,n,minted_neg P A.s l,by rw [←minted_neg,←minted_sub];congr 1; omega,by rw [convey_start]; exact hx,rfl⟩
    have ht:P.tock A.s (A.u i) ≤ (P.stampPin A.s l:ℝ):= (minted_le ..).mpr (by omega : ((A.u i):ℤ) ≤ l); have hk:P.tock A.s (A.u i) ≤ (P.stampPin A.s r:ℝ):=(minted_le ..).mpr q
    have h₀:X=U₀:= Habitable.same (show P.Habitable i _ _ _ _ _ from ⟨A.s,hp⟩) (hearthPayNX i A.s (A.u i) (A.admit i) ht hk)
    rwa [h₀] at hp

lemma shadowStallSt (U:ℕ→P.Apron)(a b:P.meshPin)(ha:0<(a:ℝ))(hb:0<(b:ℝ))(t:Tendsto (fun i':ℕ=> (U i').s) atTop atTop)(h:Tendsto (fun i'=> (U i').realWidth P i) atTop (𝓝 0)): ∀ᶠ s in atTop,P.HabitLevel i (U s).F (U s).s (-a) b (P.grantGapNX i (U s).s ((U s).u i) (U s).F (a:ℝ) (b:ℝ)) (U s).s:=by
 filter_upwards [t.eventually (minted_tall a), t.eventually (minted_tall b), h.eventually (gt_mem_nhds ha),h.eventually (gt_mem_nhds hb)] with s u v e q
 obtain ⟨l,r⟩:=u; obtain ⟨t',w⟩:=v; subst a b; exact shadowOwnSt P i (U s) (neg_le_neg ((minted_le ..).mp e.le)) ((minted_le ..).mp q.le)
#print axioms regionHeatSt
#print axioms shadowOwnSt
#print axioms shadowStallSt

end Discipline
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
