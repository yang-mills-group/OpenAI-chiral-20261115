import YM.SU5.FiniteGaugeData.Mist.Outfit
import YM.SU5.FiniteGaugeData.Mist.AtlasX
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
open scoped NNReal ENNReal
variable (X:Engine Y h W' R a H)(b:Axis)
local notation "Q"=> Anteroom X.val
local notation "G"=> regular Y h W' R a H X
local notation "M"=> TipH Y h W' R a H X
local notation "C"=> casin Y h W' R A S' a H X
local notation "Σ" => time_aux Y h W' R A S' a H X
local notation "ΩA"=> omegaV Y h W' R a H
variable (w:TipH Y h W' R a H X)
include S'
lemma home_acts (t:ℝ) : (Revolve Y h W' R A S' a H X t).comp (cpo (Anteroom X.val))=(cpo (Anteroom X.val)).comp ((casin Y h W' R A S' a H X).edge t) := (Utah.intervenes C Σ (cpo (Anteroom X.val)) (fun x=> (Cot.cpo_fun (home_base Y h W' R a H X Terrace.scheduleL x)).symm) t).symm
lemma home_dip (t:ℝ) : ((casin Y h W' R A S' a H X).edge t).comp (dip Q)= (dip Q).comp (Revolve Y h W' R A S' a H X t):= (Utah.intervenes Σ C _ (fun v=> Cot.dip_fun (home_base Y h W' R a H X Terrace.scheduleL v)) t).symm
lemma home_equiv : (∀ t:E4,(casin Y h W' R A S' a H X).unit.translation t w=w) ↔ cpo (Anteroom X.val) w∈ X.val.Unity:= by
 have hv : (∀ (b:Axis)(p:b≠ a)(z:ℝ), (C).U (Utah.Vac z b p) w=w) ↔ ∀ (j:Axis)(s:j≠a)(u:ℕ)(i:ℤ)(p:Allows a j i), X.val.stepT u j i p (cpo Q w)=cpo Q w:= by
    apply forall_congr'; intro j; apply forall_congr'; intro k
    have ht(x:ℝ): (C).U (Utah.Vac x j k)=_:= Kodiak.comb_one (whimsy Y h W' R a H X) x j -- v
    refine Iff.trans ?_ (Kodiak.planted _ X.val (Mist.liveL Λ) j (Terrace.scheduleV j) w k); apply forall_congr'; intro x; refine Eq.to_iff ?_; exact congrArg (fun phi:(TipH Y h W' R a H X).Op=> phi w=w) (ht x)
 apply (Utah.unique (C) w).trans; refine Iff.trans ?_ (core_real Y h W' R A S' a H X _).symm
 apply and_comm.trans; apply and_congr hv; apply forall_congr'; intro t
 have he (v:TipH Y h W' R a H X): (Revolve Y h W' R A S' a H X t) (cpo Q v) = cpo Q ((C).edge t v):= DFunLike.congr_fun (home_acts Y h W' R A S' a H X t) v
 constructor; intro u; exact (he w).trans (congrArg (cpo Q) u)
 intro h'; exact Subtype.ext ((he w).symm.trans h')
def Dew : TipH Y h W' R a H X:= dip Q ΩA
local notation "Ω"=>Dew Y h W' R a H X
#check gold_fixed
lemma stem : (cpo (Anteroom X.val)) (Dew Y h W' R a H X)=omegaV Y h W' R a H:= inlet (include_unity X.val _ (gold_fixed Y h W' R a H X))
theorem dew_pays : ‖Dew Y h W' R a H X‖=1 ∧ ∀ z:E4, (casin Y h W' R A S' a H X).unit.translation z (Ω)=(Ω):=by
 have he:= stem Y h W' R A S' a H X; refine ⟨(Hills.yen _).symm.trans ((congrArg norm he).trans (omegaBudget Y h W' R A S' a H)),?_⟩; apply (home_equiv Y h W' R A S' a H X (Ω)).2; exact he.symm ▸ gold_fixed Y h W' R a H X
lemma soloDew (p:Unique Y h W' R a H X)(q:∀ z:E4,(casin Y h W' R A S' a H X).unit.translation z w=w) :∃ z:ℂ,w=z • (Ω):=by
 obtain ⟨b,t⟩:= p ⟨_,(home_equiv Y h W' R A S' a H X w).1 q⟩; refine ⟨b,Subtype.ext ?_⟩; exact t.trans ((congrArg (b • ·) (stem Y h W' R A S' a H X)).symm) -- defeq
-- PVM support and Laplace
open _root_.YM Boundary
abbrev lensV:= (casin Y h W' R A S' a H X).ℚmeasure
theorem backed : (casin Y h W' R A S' a H X).unit.Spectrum (lensV Y h W' R A S' a H X) ∧ ((lensV Y h W' R A S' a H X).diagonal w).support ⊆ {p : E4 | 0 ≤ p a} := ⟨(C).joint,(C).nonneg w⟩
theorem prismLook (z:ℂ)(p:0≤z.im)(b:E4): inner ℂ w ((C).unit.translation b ((C).edge z.re ((coneT Y h W' R a H X z.im.toNNReal) w))) = ∫ x, _root_.YM.Boundary.Probe.plane x b * Complex.exp ((↑(x a):ℂ)*z*Complex.I) ∂ (lensV Y h W' R A S' a H X).diagonal w:= (C).heat b w p
#print axioms backed
#print axioms dew_pays
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
