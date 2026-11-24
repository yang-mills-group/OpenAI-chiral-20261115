import YM.CF.DPress.Chess.Sermon.Boot
import YM.CF.BPress.Test
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon Dial
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
-- Borel top, or through a packed epoch.Lifting. Keep definitions actual Test; no support duplicated
open BPress
variable {A:Fixed.Test n}
def peer (A:Fixed.Test n) : Fixed.Test n:= fun x=> W.θ _ (A (W.shine _ x))
lemma penny {S:Support (More n)}(p:BPress.IsMark S A u): IsMark (W.negZ S) (peer W A) u:=by
 refine ⟨fun x y i=> congrArg (W.θ n) (p.reads _ _ (W.read i)),fun i=> W.θwalk (p.even _), (W.θ_c n).measurable.comp (p.borel.comp (W.trail n).measurable),fun x=>?_⟩; rw [peer,W.θ_cost]; exact p.cost _
lemma truly_{D:Support (More n)}(p:IsMark D A u):peer W (peer W A)=A:=by funext x; unfold peer; rw [W.twice]; exact W.θsec (p.even _)
lemma peer_env (p:Envelope A) : Envelope (peer W A) := Env.along (Girt.pole_w A _ (W.θ_c _) p) (W.trail _).measurable
abbrev payload (A: Fixed.Test n):HT n:= fun x=> A x.1
abbrev Boss (n: Side)(S:Support (More n))(F: Fixed.Test n): Prop := ∃ u:ℝ, IsMark S F u
lemma Boss.window (S:Support (More n))(p:Boss n S A):Envelope A:=by obtain ⟨c,p⟩:=p; exact ⟨p.borel,c,p.cost⟩
namespace Porch
lemma stake (P:Loom n)(A B: Fixed.Test n)(E:Orbit n→Phys n): Fixed.functional E (peer W A* B)= Sermon.gram P E (peer_H W (payload A) (payload B)):= rfl
open Print
private lemma prime {N:Type*}[Fintype N][LinearOrder N]{A B X Y: FC N}{g:Wave N}(p:Equal g A B)(h:Equal g X Y)(t: X*B=B*X)(v:Y*B=B*Y) : Equal g (A*X) (B*Y) := Eq.trans (deeper p X) (by rw [← t,← v]; exact deeper h _)
open Fixed in
lemma base (p: Wall.rail ≤ 2*ℓ)(t:0<ℓ) (P:Loom n) (E:Orbit n→Phys n):∃ Ξ:Fixed.Test n→HT n,(∀ A:Fixed.Test n,Boss n (W.crop n (2*ℓ)) A→ Learn W ℓ (Ξ A)) ∧ ∀ A B,Boss n (W.crop n (2*ℓ)) A→Boss n (W.crop n (2*ℓ)) B → Fixed.functional E (peer W A*B)= Sermon.gram P E (peer_H W (Ξ A) (Ξ B)):=by
 let Z:= W.crop n (2*ℓ); let L:= W.negZ Z; let H:=matterRegion n Z; let V:=matterRegion n L; let J:= W.night (n:=n) (a:=2*ℓ) (b:=2*ℓ) (by omega); have hj: Disjoint H V:= disjoint_left.mpr fun i x y=>disjoint_left.mp J ((mem_matterRegion ..).1 x) ((mem_matterRegion ..).1 y)
 obtain ⟨A,v,h⟩:= lack (upperIndices n) H false; let F(f: Fixed.Test n):HT n:= A ∘ payload f; let r: Sea (cutM (upperIndices n)) (mateK n):= (Fixed.tickA_upper _ ▸ tickB _); refine ⟨F,?_,?_⟩
 · rintro B ⟨u,k⟩; exact ⟨fun x y t=> congrArg A (k.reads _ _ (agrees_mono t.1 (Finset.coe_subset.mpr (W.grade p n)))), Env.along (Girt.pole_w B A A.continuous (Boss.window _ ⟨u,k⟩)) measurable_fst, fun x=> v _⟩ -- pole_w arg? t.1 and name etc tune
 rintro B C ⟨_,b⟩ ⟨_,c⟩; rw [stake W P]; unfold Sermon.gram; refine integral_congr_ae (Eventually.of_forall fun i=>?_); let x:= μC P i; let p₁:= wake W x; let k:= mateK n; let X:= mirror W (payload B) x; let Y:= mirror W (F B) x; let u:= payload C x; let v':= F C x; let H₁:Equal k X Y:= Print.Θ_member W.shape (pinSpin W.i) W.Ξjet (all_up k r (h _ (b.even _))); have Hv:Equal k u v':= all_up k r (h _ (c.even _)); have vh:Sector H false v':=(v _).sector; have hk:Sector V false Y:= W.θwalk ((v _).sector); have hg:= prime H₁ Hv ((c.even x.1|>.apart hk hj).trans (one_smul _ _)) ((vh.apart hk hj).trans (one_smul _ _))
 change inner ℂ k (acts (X*u) (E i))= inner ℂ k (acts (Y*v') (E i)); rw [←act_inner,←act_inner (A:=Y*v'), hg] -- tune binder param? `prime` ambiguous
end Porch
end YM.CF.DPress.Chess
