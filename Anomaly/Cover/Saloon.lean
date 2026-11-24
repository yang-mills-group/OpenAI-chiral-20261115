import Anomaly.Cover.Locket
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock Preparation.Yoke
open Swell Sonar StageQ Ione Vow Tapestry.StageW
namespace Spine
universe u
variable (P:Spine)
local notation "L"=>P.par.R.L
local notation "F" s:max=>hat L P.par.x s
local notation "N" s:max i:max=>side P.run i s
set_option maxHeartbeats 1100000
set_option synthInstance.maxHeartbeats 85000
variable {p:ℕ→ℕ}{A:ℕ→Family P.calibration}{x:Family P.calibration}{S:Finset Cover}
open Proscenium
-- sharp convergence (adapt Sect library).
lemma deckF (s:ℕ)(v:Tendsto p atTop atTop)(t:BQueue S A x): Tendsto (fun j=>Journey.compass P.run (P.nomadic (p j)) (P.engine (p j)) s (exhibit P.run P.large s (P.nomadic (p j)) (A j))) atTop (𝓝 (P.E s x)):=by
 simp_rw [← actualRead]
 have M:=P.history; obtain ⟨C₀,b₀,V'⟩:=P.history.implements s S; let D:= toll P.run P.large s S; obtain ⟨D',h'⟩:= toll_pays P.run P.large s S; obtain ⟨C,h,uX,u⟩:= t.bdd; have hd:0 ≤ D:=D'; refine Metric.tendsto_nhds.mpr fun ε e=>?_ ; let d:= ε/(D+C+1); have he:0<d:=by unfold d; positivity
 filter_upwards [v.eventually (V' d he),v.eventually (P.history.finance s), t.saved d he,v.eventually ((P.law.pick.grow_k.comp P.history.growsB).tendsto_atTop.eventually h')] with n h g w h'; rw [dist_eq_norm]; let X:= Journey.sharp P.run P.large s (P.nomadic (p n)) (P.engine (p n)); refine lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub (X (A n)) (X x) _) ((add_le_add (b:=D*d) (d:=d*C) ?_ (h x t.landing C uX).2.2.2.2.1).trans_lt ?_)
 · unfold X nomadic engine; simp only [Function.comp_apply]; rw [←sharp_sub P.run P.large _ (aux_test (t.whereTo _)) (aux_test t.landing) g]; exact h' _ g.depth _ (Tower.InTest.subOp (t.whereTo _) t.landing) _ (w _)
 have hp:d*(D+C+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith
variable (s m:ℕ){B t:ℕ→ℕ}
local notation "S'"=> roomFox P s m
local notation "τ"=>Tapestry.Swatch S'
local notation "q"=> render S' P.calibration
abbrev preVote {S:Finset Cover}(A:Proscenium→ Tapestry.Swatch S):Tapestry.Swatch S:= ∑ i:Signed,(dollar i:ℂ) • A (Proscenium.gauge i)
abbrev XO (A:Proscenium→Tapestry.Swatch (P.roomFox s m)):= ((hat P.par.R.L P.par.x s:ℝ):ℂ) • preVote A
variable {X:(j:ℕ)→SOp (age P.run (P.nomadic (B j)) s)}{J:(j:ℕ)→Axis→ SOp (age P.run (P.nomadic (B j)) s)} {U:ℕ→Proscenium→ Tapestry.Swatch (P.roomFox s m)} {G:Proscenium→Tapestry.Swatch (P.roomFox s m)} (u:OnTape P s m B X J t U G)
include u
lemma convoyP (j:ℕ)(h:s<P.run.uv (P.engine (B (t j)))):Tapestry.present P.run P.large s (P.nomadic (B (t j))) S' (XO P s m (U j))=chartS P s _ (P.engine (B (t j))) (X (t j)):=by
 unfold XO preVote chartS; rw [map_smul,map_sum,show (RootBook P.run _ _ _).p=_ from (Papal.prices_plot P.run s (P.nomadic (B (t j))) _ h.le).1]; simp_rw [map_smul,u.issued]; funext x; simp only [Pi.smul_apply]; unfold patronF seaX po; let f:=showroom (P.run.meter.a s) ((P.run.voyage (P.nomadic (B (t j)))).CapeT s) (X (t j)) (J (t j)) m 0; have hw:=StageW.weighP (P.run.meter.a s) ((P.run.voyage (P.nomadic (B (t j)))).CapeT s) (X (t j)) (J (t j)) m 0 x
 rw [show ∑ i:Signed, (dollar i:ℂ) • f (Proscenium.gauge i)=StageW.votingN f from ?_]; swap; · apply sum_congr rfl; intro i _; exact Complex.coe_smul ..
 rw [show StageW.votingN f x=_ from hw]; simp only [Lamour.Bridge.Celeste.Clock.Hookah.chalkOp,Pi.smul_apply,Complex.real_smul,←smul_smul]; -- tune
lemma queueX : BQueue (roomFox P s m) (fun j=> render S' P.calibration (XO P s m (U j))) (render (P.roomFox s m) P.calibration (XO P s m G)):=by
 refine queue_V _ (Tendsto.const_smul (?_) _); apply tendsto_finsetSum; intro i _; exact (u.distance _).const_smul _
lemma bullion {a b:ℝ}(B':PinnedW P.run s (P.nomadic∘B) (P.engine∘B) m a b X J) (v:Tendsto B atTop atTop)(h:ℤ):
 let W':= render (P.roomFox s m) P.calibration (P.XO s m G); let Z:=fun j=> B (t j); let χ:= fun j=>chartS P s (P.nomadic (Z j)) (P.engine (Z j)) (X (t j))
 Tendsto (fun j=> Journey.compass P.run (P.nomadic (Z j)) (P.engine (Z j)) s (reflMark 3 h (χ j)*χ j)) atTop (𝓝 (P.E s (mirror P.calibration 3 h W'*W'))):=by
 intro W Z χ; have hp:= queueX P s m u
 have hv:=deckF P s (v.comp u.advance.tendsto_atTop) ((hp.revolve 3 h).multiply hp)
 refine hv.congr fun i=>?_ ; apply congrArg; rw [actual_product]; rw [mirror_time,actual_reflect]; rw [←present_exhibit]; exact congrArg (fun x=>reflMark 3 h x *x) (convoyP P s m u i (B' (t i)).1) -- tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
