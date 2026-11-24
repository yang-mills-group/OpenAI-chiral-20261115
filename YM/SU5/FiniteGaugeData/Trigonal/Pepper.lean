import YM.SU5.FiniteGaugeData.Trigonal.Doupe
/-! # Color-specific tilted contract. Arbitrary many-body. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
variable (f:Fin n→Trigo.Chamber true)(g':Fin n→Trigo.Chamber false)
open Fock Tint -- auth
open MeasureTheory Stationary
local notation "δ"=> Fin (projCard n)
-- AP conversion.Remind.
def modelG (u:X)(y:Y₀): Grit:= ⟨(0,true),u.1,y.1,Lattice.route (nodeC u.1) (nodeC y.1) 1,Lattice.route_end ..,u.2.val,y.2.val,u.2.property,mem_compl.mp y.2.property⟩ -- zero card def? switch dummy choose
private lemma pension : (MeasureTheory.volume (α:= Gaia)).restrict boundsEarth= ArchiveK.μF:=by
 apply Measure.restrict_congr_set; let U(a:Axis):Set ℝ:=Set.Ico (-Real.pi) (-Real.pi+2*Real.pi); let V(a:Axis):Set ℝ:= Set.Ioc (-Real.pi) Real.pi; have he(a:Axis): U a=ᵐ[MeasureTheory.volume] V a:=by unfold U V; rw [show -Real.pi+2*Real.pi=Real.pi from by ring]; exact Ico_ae_eq_Icc.trans Ioc_ae_eq_Icc.symm
 let p: Set (Axis→ℝ):=Set.univ.pi U; let q:= Set.univ.pi V; have hp:p=ᵐ[volume] q:= Measure.ae_eq_set_pi (fun i _=>he i); have hz(x:Gaia): x∈ boundsEarth↔x.ofLp ∈ q:= (Set.mem_univ_pi).symm; -- tune
 filter_upwards [(PiLp.volume_preserving_ofLp Axis).quasiMeasurePreserving.ae hp] with i z; apply propext; change i∈ boundsEarth↔ i∈ ArchiveK.stair; rw [hz]; exact Eq.to_iff z.symm -- tune z holds props eq?
lemma Income (u:X)(y:Y₀) : Trigo.levy u y=(modelG u y).finalIncome:=by
 unfold Trigo.levy Trigo.rotor ArchiveK.scout finalIncome; rw [pension,Complex.real_smul]; rfl -- maps equal calendar ℝ units
-- entry.P
abbrev gate(N:Side)(M:Male)(i j:Fin n):= (modelG (f i) (g' j)).stage N M
def sceneM (A:Op (Fin n)): Op (Fin (projCard n)):= ( (1:Op SU.Slot)⊗ₖ A ).submatrix (collar n) (collar n)
local notation "Ω"=> Trigo.TaxR Trigo.levy f g'
local notation "ϕ" x:max=> collar n x
local notation "ℱ" z:max=> f (collar n z).2
local notation "𝒢" z:max=> g' (collar n z).2
lemma rentMo (N:Side)(M:Male)(p:Standing (tickA N) (spar 4 M (1:Pane N)))(i j:δ) : Lycan.cupE (tickA N) (spar 4 M (1:Pane N)) (quantum N (ℱ i) (collar n i).1) (quantum N (𝒢 j) (collar n j).1)=sceneM (Matrix.of (gate f g' N M)) i j:=by
 let X₁:= modelG (ℱ i) (𝒢 j); let a:= (ϕ i).1; let b:= (ϕ j).1; have H:= livPrice id N M p (X₁,a) (X₁,b); unfold Otter at H; -- tune
 simp only [sceneM,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,ite_mul,one_mul,zero_mul]; exact H
local notation "W0"=> (sceneM Ω).det
lemma finance(N:Side)(M:Male)(p:Standing (tickA N) (spar 4 M (1:Pane N))): slopeI (paper f g') 4 N M=(sceneM (Matrix.of (gate f g' N M))).det:=by
 let u(x:δ):= quantum N (ℱ x) (ϕ x).1; let v(x:δ):= quantum N (𝒢 x) (ϕ x).1; let Q':=tickA N; let P':= spar 4 M (1:Pane N); change Volt Q' P' (TextK f g' N)=_
 let x(i:δ):=(i,i); let A:= List.ofFn x; change _=_; rw [show TextK f g' N=Lycan.studio u v A from (by unfold Lycan.studio A; rw [List.map_ofFn]; rfl), Lycan.adjust p u v (fun i j=> crossz ..), Lycan.sweet (s:=x)]; refine congrArg Matrix.det ?_; ext i j; exact rentMo f g' N M p i j
abbrev WealthQ := (Trigo.TaxR Trigo.levy f g').det ^ (45:ℕ)
lemma scene_me (A:Op (Fin n)):(sceneM A).det=A.det^ (45:ℕ):=by unfold sceneM; rw [Matrix.det_submatrix_equiv_self,Matrix.det_kronecker,Matrix.det_one,one_pow,one_mul]; rw [SU.slots]
-- before pricing monotone.Sph asserts eventually bound.Vecast.
private lemma landing (N:ℕ→Side)(M:ℕ→Male)(t:Tendsto (fun i=>(N i).val) atTop atTop)(q:Tendsto (fun i=>(M i).val.val) atTop atTop)(e:∀ i:ℕ,Even (N i).val)(p:∀ i:ℕ,Standing (tickA (N i)) (spar 4 (M i) (1:Pane (N i)))) : Tendsto (fun i=>slopeI (paper f g') 4 (N i) (M i)) atTop (𝓝 (WealthQ f g')):=by
 simp_rw [finance f g' _ _ (p _),scene_me]; let f₀(i:ℕ):= Matrix.of (gate f g' (N i) (M i)); have he:Tendsto f₀ atTop (𝓝 Ω):=tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr (fun j=>by change Tendsto (fun z:ℕ=> _) atTop (𝓝 (Trigo.levy _ _)); rw [Income]; exact ((modelG (f i) (g' j)).authorized q t e).2)); exact ((continuous_id.matrix_det.continuousAt (x:=Ω)).tendsto.comp he).pow _
#print axioms finance
#print axioms landing
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ){ε:ℝ}
local notation "Kₜ"=> tent Y h
local notation "M0" i:max s:max=> side Y i s
local notation "ΛF"=> W Kₜ
local notation "Ox" s:max i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram s
private lemma chalet (e:0<ε): ∃ T:ℕ,∀ (M:Male)(L:Side), Even L.val→ T≤ M.val.val→ T≤ L.val →Standing (tickA L) (spar Λ.K.j M (1:Pane L)) → ‖slopeI (paper f g') Λ.K.j L M - WealthQ f g'‖ ≤ ε:=by
 rw [Λ.kJ]; by_contra! p; choose m n a b v F' t' using p; obtain ⟨w,u₀⟩:= ((landing f g' n m (tendsto_atTop_mono v tendsto_id) (tendsto_atTop_mono b tendsto_id) a F').eventually (closedBall_mem_nhds _ e)).exists; apply (t' w).not_ge; rw [←dist_eq_norm]; exact mem_closedBall.mp u₀
include K R A S' P'
lemma punctum (e:0<ε): ∀ᶠ s in atTop, forall Φ: ℕ→ W Kₜ→ₗ[ℂ]ℂ,Sphere Y h K R A Φ→ ‖Φ s (Base f g' Kₜ) - WealthQ f g'‖ ≤ ε:=by
 let j:= (footprint f)∪ footprint g'; let S:= insert (0:Cover) j; have hp:= veteran f g' Kₜ (S:=S) (fun i u=>mem_insert_of_mem (mem_union_left _ u)) (fun i u=>mem_insert_of_mem (mem_union_right _ u)) (insert_nonempty ..)
 obtain ⟨T,t⟩:= chalet (Λ:=Λ) f g' (half_pos e)
 filter_upwards [lanterne Y,lantern Y h hp K R A S' P' (half_pos e)] with s p v₀
 obtain ⟨i,H0,a⟩:= (((side_grows Y s h K.pick.grow_i T).and v₀)).exists; obtain ⟨k,U,b,c⟩:= (a.and ((K.pick.pass Y h s (u i)).and (heightZoom Y s T K.pick.grow_k))).exists; let N:= M0 (u i) s; let M:= (Ox s (u i) (v k)).J.M; have hP:= t M N (electionLive (u:=u) Y s i) (c (u i)) H0 (p (u i) (v k) b.enters M).1.tender; intro Φ H; exact (norm_sub_le_norm_sub_add_norm_sub _ (slopeI (paper f g') Λ.K.j N M) _).trans ((add_le_add (U Φ H) hP).trans_eq (by ring))
lemma motionQ(p:(TaxR Trigo.levy f g').det ≠0): ∀ᶠ s in atTop, forall Φ: ℕ→ W Kₜ→ₗ[ℂ]ℂ,Sphere Y h K R A Φ → Φ s (Base f g' Kₜ) ≠ 0:=by
 let W:= WealthQ f g'; have hp:0<‖W‖:= norm_pos_iff.mpr (pow_ne_zero _ p); filter_upwards [punctum Y f g' h K R A S' P' (half_pos hp)] with i t Φ H z; have he:=t Φ H; rw [z,zero_sub,norm_neg] at he; exact he.not_gt (half_lt_self hp)
#print axioms motionQ
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
