import YM.CF.DPress.FD.Warp.Cons
/-! Locally symmetric selection of transports. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Cube Lat Scroll Tw Finset
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m:ℕ}{u:ℝ}
namespace Con
local notation "L"=> Seat n
local notation "rΩ"=> Reign n
private lemma directR (s:Sweep n)(F:rΩ)(X:Pane n)(x:L)(p:Must l u (flashA s X) ((boxA s).symm x) F):Must l u X x ((gate n).mv s⁻¹ F):=by
 rw [←revB s X]; exact direct x p -- p defeq?
lemma movex (X Y:Pane n)(s:Sweep n)(z:L)(p: Agrees (brim z r) X Y): Agrees (brim ((boxA s).symm z) r) (flashA s X) (flashA s Y):=by
 apply flashD; rw [show (brim ((boxA s).symm z) r).map _=brim z r from ?_]; exact p
 exact (cellV s r _).trans (by rw [Equiv.apply_symm_apply])
structure Trophy(n:Side)(l:ℕ)(u:ℝ) where
 G(η:Cotton n)(x:Seat n):Pane n→ Reign n
 knows(c x):Measurable (G c x)
 bill(η x X):Sound l u X x → Must l u X x (G η x X)
 turn(s i η X): G (act s η) i (flashA s X)=(gate n).mv s (G η (boxA s i) X)
 port(i X Y η η'):η {i}=η' {i}→Agrees (Space i l) X Y→ G η i X=G η' i Y
lemma gate_y (s:Sweep n): Continuous ((gate n).mv s):= by rw [show (gate n).mv s=(fun x:Reign n=> fun i=> polarT s.charge (x (boxA s i))) from funext (fun x=>funext fun y=>gate_e s x y)]; exact continuous_pi (fun i=> (rev_C _).comp (continuous_apply _)) -- fix typo
lemma cabinet (t:0≤u)(p:2*(globe l+1)<(More n).val):Nonempty (Trophy n l u):=by
 choose g h v e using fun i:L=> promise i l u t p; let T(η:Cotton n)(x:L):= tune (pane n) (gate n) g (pos n) (η {x}) x
 refine ⟨{G:=T,knows:=?_,bill:= ?_,turn:= ?_,port:=?_}⟩
 · intro η x; let s:= η {x}; exact (gate_y s⁻¹).measurable.comp ((h _).comp (revM s).measurable)
 · intro η x X v'; let s:=η {x}; apply directR s (g ((boxA s).symm x) (flashA s X)); apply v; apply (sounds _ _).2; rwa [Equiv.apply_symm_apply]
 · intro s i η X; let x:=boxA s i; have hv(i:L) : ({(pos n).mv s i} :Support (More n))= ζ s⁻¹ {i}:=by rw [ζ,map_singleton,sitU]; rfl
   let V(x:L):Support (More n):={x}; have hx:= tune_v (pane n) (gate n) s η (pos n) x V hv X g; have hz:(pos n).mv s x=i:= (boxA s).symm_apply_apply _; rw [hz] at hx; exact hx
 intro i X Y η η' t v; unfold T tune; rw [t,e]; apply movex X Y _ i v
-- uses of halo budgets all finite.Idea program.Any input α.Tell.Version.Pl.
end Con
end YM.CF.DPress.FD
