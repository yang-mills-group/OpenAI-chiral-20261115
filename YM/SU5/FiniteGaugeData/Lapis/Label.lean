import YM.SU5.FiniteGaugeData.Lapis.Luray
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LapisS
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
open YM.SU5.FiniteGaugeData.Lapis Lumi Eight
open Next.Rank Spindle Push.Local Rhythm LightK
namespace Stadium
variable {ι:Type}[Fintype ι][DecidableEq ι]
variable (T:Duct SU.group ι)(K:Clip)(r x α:ℝ){N:Side}
variable (Q:Calibration)(p:Cover)(a: Signed)
local notation "I₁"=> Lumi.macroK ι T
local notation "S₁"=> scape p (macroK ι T)
-- any normalized response over all inputs. Work in cover units.
abbrev chart7 (x:LinksC)(i:ι):= ((Γ T a i).2) • ((Γ T a i).1).eval (G:=SU.group) (Lattice.translate p x)
abbrev stencil7 (x: LinksC):ℂ:= (((T.seen ((r*Real.sqrt K.direct) • chart7 T p a x)) :ℝ):ℂ)
def rod := scalar Q (stencil7 T K r p a ∘ Prod.fst)
local notation "Z"=> rod T K r Q p a
lemma rod_tomb : InTest Q false (scape p (macroK ι T)) false (rod T K r Q p a):=by
 apply InTest.seed; apply Coeff.fromC
 · have he(i:ι):Continuous (fun X:LinksC=>chart7 T p a X i):= Continuous.smul (continuous_const (y:=(Γ T a i).2)) ((RG.Slot.cont _).comp (show Continuous (fun X:LinksC=>Lattice.translate p X) by unfold Lattice.translate; fun_prop))
   exact Complex.continuous_ofReal.comp (T.registered.continuous.comp (Continuous.smul (continuous_const (y:=r*Real.sqrt K.direct)) (continuous_pi he))) -- named arg
 intro X Y h; unfold stencil7; apply congrArg ((↑):ℝ→ℂ); apply congrArg T.seen; apply congrArg; funext i; unfold chart7; apply congrArg; apply (Γ T a i).1.covered; intro z w u; apply h (z.1+p,z.2) (mem_image_of_mem _ (resident T a i _ w)); apply Eq.subst _ (mem_image_of_mem (fun i:Cover=>i+p) (resident T a i _ u)); dsimp only; abel
lemma rod_book (i:Side)(x: Fields (Q.c i)): rod T K r Q p a i x = ((Lumi.live T K r a (wrap _ p) x.1:ℂ) • (1:FC _)):=by
 unfold rod scalar; dsimp only [Function.comp_apply]; congr 3; unfold stencil7 Lumi.live; apply congrArg ((↑):ℝ→ℂ); apply congrArg; apply congrArg; funext j
 have hp(N:Side)(X:Pane N): Lattice.translate p (onC N X)=expandAt (wrap (More N) p) X:=by funext i; unfold onC Lattice.translate expandAt; rw [map_add,add_zero]
 rw [looks T j,chart7,RG.Slot.atSite,hp]
open Tint
lemma rod_tangible : Durable Q (rod T K r Q p a) :=by
 intro i u x; simp_rw [rod_book, twist_scalar,map_one]; change (↑(Lumi.live T K r a _ (gauge u x.1)):ℂ) • (1:FC _) = _; rw [lived_g] -- tune
abbrev pole : W Q:= ⟨rod T K r Q p a,⟨⟨S₁,(rod_tomb ..).widen⟩,by simp⟩,(show Durable _ _ from rod_tangible T K r Q p a)⟩
lemma paneBolt : Locator Q (pole T K r Q p a) S₁:= (rod_tomb ..).widen
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
variable (s i k:ℕ)
local notation "Kₜ" =>tent Y h
local notation "N₁"=> side Y i s
private def beamAt (N:Side):Mark N:= fun x=> (↑(Lumi.live T K r a (wrap _ p) x.1):ℂ) • 1
lemma sold_rod : sold Y h s i (pole T K r (tent Y h) p a).val=(fun x=> (↑(Lumi.live T K r a (wrap _ p) x.1):ℂ) • 1) := by
 rw [sold_v]; unfold send; rw [show (pole T K r Kₜ p a).val (momentm Y i s)=beamAt T K r p a _ from funext (fun x=> rod_book ..)]; exact castL (terrain Y h (Y.ir i) s)
where castL {M N:Side}(e:M=N): (show Mark N from e ▸ beamAt T K r p a M)= beamAt T K r p a N:=by subst M; rfl
end Stadium
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Stadium.pole
