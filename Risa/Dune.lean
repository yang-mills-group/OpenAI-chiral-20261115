import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import Risa.Helm
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
local notation "D1" => CF.Compass.decor
variable (Xh:Hike)(G)(p':BudgetPoint)(o:Site n)(σ:Signed)(u:ℝ)
local notation "χ"=> Xh.cost
local notation "Γ"=> (ridges:ℝ)
local notation "𝕥"=>p'.threshold
-- how rotation applied to guard? simplest wrap call via pull. See forWind. anchor arbitrary n. physical size Lens= Γ.
noncomputable abbrev party(t:Signed)(b:Site n)(V:Config G n):PlaqAxes→G.Color:=fun i=>u • AnalyticBridge.VerifiedReset.petals (pull t b V) 0 i
def guardian (t:Signed)(b:Site n)(V:Config G n):Prop:= CF.Scree.pingS (G:=G) (c:=n) p'.threshold (Lattice.halo 10 {(0: Site n)}) (pull t b V) -- check namespace
noncomputable abbrev solicit (t:Signed)(b:Site n)(V:Config G n):ℝ:= if guardian G p' t b V then naked G (party G u t b V) else 0
local notation "£"=> |u| *𝕥
lemma cast_part (t:Signed)(b:Site n)(V:Config G n)(h:guardian G p' t b V)(i:PlaqAxes): ‖party G u t b V i‖ ≤£:=by
 let X:=pull t b V
 have hv: Healthy p'.threshold {(0:Site n)} X:=by
    apply disjoint_left.mpr; intro y p r; obtain ⟨d,w,r⟩:=(flags_spec ..).mp r
    have hp:=h d ((not_disjoint_iff.mpr ⟨y, halo_spec.mpr ⟨0,mem_singleton_self _,by simpa [mem_singleton.mp p]⟩,w⟩))
    exact (not_lt_of_ge hp.le) r
 have ht(a b:Lattice.Step)(d:a.dir < b.dir): ‖plate X 0 a b‖ ≤ p'.threshold:= (G.curvature_norm _).trans (Square.small a b d hv)
 unfold party petals clover stencil
 rw [norm_smul,Real.norm_eq_abs]; gcongr
 let a:=i.val.1; let b:=i.val.2
 have h'(a':Lattice.Step)(ha:a'.dir=a): ‖plate X 0 a' (posDir b)-plate X 0 a' (negDir b)‖ ≤ 𝕥+𝕥:= (norm_sub_le ..).trans (add_le_add (ht _ _ (ha.symm ▸ i.property)) (ht _ _ (ha.symm ▸ i.property)))
 rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (show 0 ≤(4:ℝ) by norm_num))]
 exact (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (h' (posDir a) rfl) (h' (negDir a) rfl))) (by norm_num : (0:ℝ) ≤ 4⁻¹)).trans (le_of_eq (show _* ((𝕥+𝕥)+(𝕥+𝕥))=𝕥 from by ring)) -- types
noncomputable abbrev gradM:= Γ*(|u| *𝕥)^2
lemma launchQ (t:Signed)(b:Site n)(V:Config G n): |solicit G p' u t b V|≤ gradM p' u:=by
 unfold solicit; split; next h=> exact thrill _ (cast_part G p' u _ _ _ h) -- h
 next h=> rw [abs_zero]; unfold gradM ridges; positivity
lemma launch_meas: Measurable (solicit G p' u σ o):=by
 let f:=fun V:Config G n=> pull σ o V
 unfold solicit; have ht:= prior_pull (G:=G) (n:=n) σ o
 have he:MeasurableSet {V:Config G n|guardian G p' σ o V}:= ht.measurable ((CF.Scree.ping_o ..).measurableSet)
 refine Measurable.ite he (?_) measurable_const; unfold naked party; let a:= (G.Color); fun_prop (disch:=exact ht.measurable)
lemma launch_env:RG.Envelope (solicit G p' u σ o):= ⟨launch_meas G p' o σ u,gradM p' u, fun i=>by rw [Real.norm_eq_abs]; exact launchQ G p' u ..⟩
lemma green_Φ : GaugeInvariant (solicit G p' u σ o):=by
 intro i U; unfold solicit party naked guardian; -- pull gauge rotate. need commute `pull_gauge`
 rw [ProjectorNext.Equivariance.pull_gauge]
 simp_rw [CF.Scree.pingB, AnalyticBridge.VerifiedReset.petals_gauge,norm_smul,G.norm_adjoint]
-- roto
lemma solic_pull (k:Signed)(b:Site n)(V:Config G n): solicit G p' u σ o (pull k b V)=solicit G p' u (k*σ) (affine k b o) V:=by
 unfold solicit guardian party; simp_rw [pull_pull]
-- used as possible variant orientation.P Lease weak detection uses alert at x.Criterion m≥20.
variable {G o σ u}
abbrev stint(r:Ratio c n)(m:ℕ)(A:Support c)(D:Finset (Cell n))(o:Site n):Prop:=Safe r A (hallBill m) o ∧ vigilant D (hallBill m) o
private lemma sent_near (f:Cell n)(i:Site n)(s:Signed)(b:Site n): separation (Face.send s b f).1 (affine s b i) ≤ 2+separation f.1 i:=by
 have he:= Work.H03.touched_send s b f
 have ht:affine s b f.1 ∈ touched (Face.send s b f):=he.symm ▸ mem_image_of_mem _ (Work.E01.base_touched f)
 have hg:= Work.E01.sep_touched _ _ ht; have hk:=separation_triangle (Face.send s b f).1 (affine s b f.1) (affine s b i)
 have h(i j:Site n): separation (affine s b i) (affine s b j)=separation i j:=by simp [affine]
 linarith only [hk,hg,h f.1 i] -- rewrite
lemma echo (h:stint r m A (weak p'.threshold U) o)(k:20  ≤ m): guardian G p' σ o U :=by
 intro i hv
 obtain ⟨y,p,w⟩:=Finset.not_disjoint_iff.mp hv; have hi:=Work.E01.sep_touched i y w; obtain ⟨a,g,he⟩:= halo_spec.mp p; rw [mem_singleton.mp g,separation_comm] at he; have hx:= separation_triangle i.1 y 0; have hs:= sent_near i 0 σ o
 have hf:= Face.send_price U i σ o G.chord G.chord_inv (fun _ u=> G.chord_conj u _)
 rw [hf]
 by_contra! t; have hl:=h.2 (Face.send σ o i) ((weak_mem _).mpr t)
 rw [affine,Signed.act_zero,zero_add] at hs; unfold hallBill Sequest at hl; omega
#print axioms echo
end Risa
end YM.Gleam.Luster
