import WakeRoad.Xylem
/-! # Oriented comparisons and deck legality. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Buffered Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Skye Precision Tree Fock
attribute [local instance] opCStarAlgebra
open PhysicalNext.JointLoad.Heir
open YM.WakeRoad CF.Pannier.Chancel Rous Pressure Papal EmberWind Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open CF.Gingham.Ruff
local notation "G₅"=> SU.group
open CF.Gingham.Ruff
namespace ArborJet
variable {N:Side}{m d s:ℕ}{S:Support (More N)}
local notation "M"=> Signed.mirror (3:Axis)
open CF.Gingham.Ruff CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Gingham.VoyageB
variable (w:ℤ)(b:Bool){u:Side}{a δ v c e E:ℝ}{k r:ℕ}{p:BudgetPoint}{Z:Scree.Loom N}
   {f h:Chin N→OP N} (X:Rialto 6 e δ v)(B:GarlandBook u a c e f h)
   (U:Briefly p r e Z)(Y:Arioso X B.pump U)(T:Tagbill a E u k r p.B)(D:Web SU.group)(P:Parasols p δ (p.B/10+1))
local notation "β"=> p.B
local notation "τ"=>p.threshold
local notation "χ"=>p.B/10
local notation "o₀"=> (0:Seat N)
-- NB don't subtract musicA 0, pay constant
local notation "V'"=>elector (N:=N) (χ) w b
abbrev twice (Y:Web SU.group)(u:Side)(a cw r s δ la0 _z:ℝ)(n:ℕ):ℝ := -- cw=pepCharge,p=n,z threshold? notation
 let C:=Lion u (a/4) cw; let m:=n/10
 -- score rotate expense, plus centered removal
 la0^2 * ((tributeFog Y m cw a r δ s u + δ^2*(r^3*cw))+2*C*r*(2* SU.group.colorScale*s*r))
include X P Y T D
lemma scored (la0 z:ℝ)(V:Pane N)
   (ℓ:going (N:=N) w b (β+2) ⊆ S) (h':Tiny S V z)(zp:0≤z)
   (y:ordinary (possession (n:=N) S) ((1/2)*p.threshold) V)
   (calm:keynote (χ) p.threshold δ ≤ D.radius)(j:2*((χ)+2)< (More N).val):
   let t:=atoms X B.pump p.B
   ‖paletron w b B U la0 δ V-WakeRoad.Score (portrait b t) ((V').material la0 V)‖ ≤ twice D u a (pepCharge u a c) τ z δ la0 0 p.B:=by
 intro C
 have t : (χ)+2 ≤ β+2:=by omega
 have hb: encasing w b (BlockP (β+10) (0: Seat N)) ⊆ S:=by rw [centered]; exact (Corona.halo_mono (show β+10 ≤ β+2+debt+12 by omega) le_rfl).trans ℓ
 have hS: ordinary (possession (n:=N) (encasing w b (BlockP (β+10) (0:Seat N)))) ((1/2)*p.threshold) V := fun i h=> y i (mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp h).2: touched i⊆_).trans hb ⟩)
 obtain ⟨ht,hs⟩:= outfit (S:= BlockP (β+10) (0:Seat N)) w b (U:=V) (tiny_mono h' hb) hS
 let v:=attire w b V
 have hv: bouton (0:Site N)=0:=by unfold bouton; rw [←Ratio.root_embed,map_zero]
 have hp:pingS p.threshold (hoop (0:Site N) p.B) v:=by
    apply passage ?_ hs (by have :=p.threshold_pos;linarith); unfold hoop; rw [hv]; exact halo_spread (fun i h=> (blocks_test.mp h)) (by omega) -- not infer.
 let X' := fault (χ) (0:Seat N) v
 let G:=elector (N:=N) (χ) w b
 let v₀:= G.material 1 V
 let Φ:Postcard (χ) →ℝ:= fun j=>stamp b j * v₀ j
 let c':= pepCharge u a c; let b₀:=Lion u (a/4) c'
 have hz: WakeRoad.coin C≤ b₀:=atoms_fee X B.pump (show Tagbill (4*(a/4)) E u k r β from by rw [show (4:ℝ)*(a/4)=a from by ring]; exact T)
 let φ:=Matrix.trace (coinF U B.pump true (pitchK (v,v)))
 let H:= (musicA X B.pump p) 0; have h₀:0≤c':=Shells.carrot_c B.pump; have hp0:=p.threshold_pos
 have hh : ‖H‖ ≤ p.threshold^3*c':= Y.fixed.trans (mul_le_mul_of_nonneg_right Y.press h₀)
 have y': Tiny (shore (bouton (0:Site N)) (χ+1)) v z:= tiny_mono ht (by rw [hv]; exact Corona.halo_mono (show χ+1 ≤ β+10 by omega) le_rfl)
 let F':= tributeFog D (χ) c' a (τ) δ z u
 have hm: ‖δ^2 • (φ - H) - WakeRoad.Score C X'‖ ≤ F':= by
    have he:= profit X B.pump T U Y D P calm j (pitchK (v,v)) hp y' zp
    rw [hv] at he; exact he
 have hg : ‖δ^2 • φ-WakeRoad.Score C X'‖≤ F'+δ^2 *((τ)^3*c') := by
    rw [show δ^2 • φ-WakeRoad.Score C X'=(δ^2 • (φ-H)-WakeRoad.Score C X')+δ^2 • H from by rw [smul_sub]; abel]
    exact (norm_add_le ..).trans (add_le_add hm (by rw [norm_smul,Real.norm_of_nonneg (sq_nonneg δ)]; gcongr))
 have hu (i:Postcard (χ)):= attiring w b h' y ℓ t i
 have hq(i:Postcard (χ)):|Φ i| ≤ τ :=by
    unfold Φ v₀; rw [abs_mul,stamp_abs,one_mul]; unfold Vessel.material; rw [one_mul]; have h:= (PiLp.norm_apply_le (p:=2) _ (G.lens i)).trans (hu i).1; refine h.trans (by linarith only [hp0])
 have hq'(i:Postcard (χ)): |X' i| ≤ τ:=by
    let o:= Boom.port (0: Seat N) i.1.1.val
    let A:=i.1.2
    have h: o∈ hoop (0:Site N) p.B:=by unfold hoop; rw [hv]; exact (shoreq ..).mpr ((separation_box_add _ i.1.1.property).trans (by omega))
    exact (PiLp.norm_apply_le (p:=2) _ i.2).trans ((SU.group.curvature_norm _).trans ((hp (o,A) (not_disjoint_iff.mpr ⟨o,h,Work.E01.base_touched _⟩)).le))
 have e':=(score_equate C X' Φ hq' hq hp0.le (d:=2* SU.group.colorScale*z*τ) (fun i=> ?_))
 swap; · have h:|X' i-Φ i|≤ 2* SU.group.colorScale*z*((1/2)*p.threshold):=by simpa only [Φ,v₀,Vessel.material,one_mul] using (hu i).2
         exact h.trans (by have hv:=SU.group.colorScale_pos; gcongr; linarith only [hp0])
 let s' := 2 * b₀*τ*(2* SU.group.colorScale*z*τ)
 have he : ‖ δ^2 • φ - WakeRoad.Score C Φ‖ ≤ (F'+δ^2*(τ^3 *c'))+s':=by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (WakeRoad.Score C X') _).trans
    apply add_le_add hg (e'.trans (by unfold s'; have hv:=SU.group.colorScale_pos; gcongr))
 rw [portrait_rec,paletron,show (fun i=> stamp b i*(V').material la0 V i)= la0 • Φ from funext fun i=>by
    unfold Φ v₀ Vessel.material; rw [Pi.smul_apply,smul_eq_mul,one_mul,mul_left_comm], score_scale,medley_scale, (show (la0*δ)^2=la0^2*δ^2 from mul_pow ..), ←smul_smul,medley_scale,←smul_sub,←medley_scale b (δ^2),←medley_diff,norm_smul,Real.norm_of_nonneg (sq_nonneg la0),medley_fee]
 exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
#print axioms scored
