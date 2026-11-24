import YM.CF.Continuum.CanalTwo
import YM.CF.Continuum.Square
import YM.CF.Bloom.Flux
import YM.CF.Song.Beat
import YM.CF.Py.Tides
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m C B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
variable {R:GramM (Scree.mid m B)}{P:Grasp Y B e}{A:Loom (Scree.mid m B)} {R':GramM (Scree.mid C B)}{A':Loom (Scree.mid C B)}{G:Ratio (Scree.mid m B) (Scree.mid C B)}{T:RG.StepData (More (Scree.mid m B)) (More (Scree.mid C B))}{q:Chi}{d:ℝ}(E:Girt.BaseL P G R' A A' q d)(p:T.ratio=ratio G)(v:T.patch.Branches T.kernel group)
variable {N:Side} (X8:Haro.SpaceM)
open Window
lemma boseMoment (F:Orbit N → Phys N)(f:Pane N →ℂ) : Window.moment F (bosonic N f) = ∫ i, beamL N (F i)* f i.1 ∂city N:=by
 unfold Window.moment; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_; change inner ℂ _ (acts (f i.1 • 1) (F i))=_; rw [act_smul, act_one,inner_smul_right]; exact mul_comm (f i.1) (beamZ N (F i))
open Push.GridApprox
include E p v
lemma fly_QM (f:Pane (mid m B)→ℂ)(he:RG.Envelope f) (g: Rue.IsleB group R.p.threshold)(u:∀ z:Orbit (Scree.mid m B),Rue.FleetS R.p.threshold z.1→Scree.stove P A R' A' G T q d X8.val z=denZ R P A z): Window.moment (denZ R P A) (bosonic _ f)= Window.moment (denZ R' P A') (bosonic _ (back T R'.beta f)):=by
 let U:= Orbit (Scree.mid m B); let V:=Orbit (Scree.mid C B); let K:=beamL (Scree.mid m B); let Λ:=beamL (Scree.mid C B); let F(X:U×V):= integrated P A R' A' G T q d X8.val X.1 X.2; let D(x:U)(y:V):=K (F (x,y))*f x.1; let S(y:V)(x:U):=Λ (denZ R' P A' y)* ((T.density R'.beta y.1 x.1:ℂ)*f x.1)
 have ht: Integrable F ((city _).prod (city _)):= Env.integrableX (Girt.buoy E T p v X8.val) _; have hp: Integrable (fun x=>K (F x)) _ :=K.integrable_comp ht
 have hz(i:U)(j:V):D i j = S j i:=by
    unfold D S F K Λ; rw [relay_F E X8]; simp only [Complex.real_smul]; ring
 obtain ⟨C',H⟩:= he.cost
 have hD:Integrable (Function.uncurry D) ((city _).prod (city _)):=hp.mul_bdd (he.meas.comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable (Eventually.of_forall (fun i:U×V=>H i.1.1))
 rw [boseMoment,boseMoment];
 calc
   _=∫ x,(∫ y,D x y ∂city _) ∂city _:=by
       apply integral_congr_ae; filter_upwards [((Measure.quasiMeasurePreserving_fst (μ:=prior group (More (Scree.mid m B))) (ν:=depot (Scree.mid m B))).ae (g (More _))), ht.prod_right_ae] with i pX s
       change K _*_= _; rw [← u i pX]; change K (∫ y,F (i,y)∂city _)*_= _; rw [←K.integral_comp_comm s]; exact (integral_mul_const _ _).symm
   _= ∫ y,(∫ x,D x y ∂city _) ∂city _:= integral_integral_swap hD
   _= _:=by
       simp_rw [hz]; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_ ; dsimp only [S]; rw [integral_const_mul]; congr 1; have hp := (back_slice (T.isKernel v R'.beta) he i.1).integrableC (prior group (More (Scree.mid m B)));
       change (∫ z:U,_∂(prior group (More (Scree.mid m B))).prod (depot (Scree.mid m B)))=_; rw [integral_prod _ (hp.comp_fst _)]; simp only [back, integral_const, probReal_univ,one_smul]
end YM.CF.Scree
