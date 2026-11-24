import YM.CF.Py.Tides
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m C B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
variable {R:GramM (Scree.mid m B)}{P:Grasp Y B e}{A:Loom (Scree.mid m B)} {R':GramM (Scree.mid C B)}{A':Loom (Scree.mid C B)}{G:Ratio (Scree.mid m B) (Scree.mid C B)}{T:RG.StepData (More (Scree.mid m B)) (More (Scree.mid C B))}{q:Chi}{d:ℝ}(E:Girt.BaseL P G R' A A' q d)(p:T.ratio=ratio G)(v:T.patch.Branches T.kernel group)
include E
lemma relayQ (X:Orbit (Scree.mid m B))(W:Orbit (Scree.mid C B)): beamL (Scree.mid m B) (integrated P A R' A' G T q d 0 X W)= T.density R'.beta W.1 X.1 • beamL (Scree.mid C B) (denZ R' P A' W):=by
 let L' :=ratio G; letI :Nonempty (Forest L'):= Tree.select L' (show Odd G.count.val from E.power.symm ▸ ho)
 let v:=denZ R' P A' W
 have hp:Fintype.card (Forest L')≠0:= Fintype.card_ne_zero
 have ht(F: Forest L'):beamL (Scree.mid m B) (carrier P A R' A' G T q d 0 F X W)= T.density R'.beta W.1 X.1 • beamL _ v:=by
    rw [carrier,map_smul]; apply congrArg (fun z:ℂ=> T.density _ W.1 X.1 • z); rw [show beamL _ (scaleZ _ _)= _ from by change beamL _ (Girt.scaleW _ 0 _) = _; rw [Jade.thin_k]]; change inner ℂ (mateK _) _= beamZ _ v; have hQ:= Spire.shuttle G E.power E.size _ (E.trial F (A' W) X) E.pe R'.J.M; rw [show inner ℂ _ _= _ from hQ.2 (cartsL (switchG G).symm v)] -- tune
    exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
 unfold integrated; rw [map_smul,map_sum]; rw [sum_congr rfl (fun i _=>ht i),sum_const,card_univ]
 simp only [nsmul_eq_mul,Complex.real_smul,Complex.ofReal_natCast,Complex.ofReal_inv]; rw [←mul_assoc, inv_mul_cancel₀,one_mul]; exact_mod_cast hp
include p v
lemma balanceBa (g: Rue.IsleB group R.p.threshold)(u:∀ z:Orbit (Scree.mid m B),Rue.FleetS R.p.threshold z.1→Scree.stove P A R' A' G T q d 0 z=denZ R P A z) : partitionZ R P A=partitionZ R' P A':=by
 let U:=Orbit (Scree.mid m B); let V:=Orbit (Scree.mid C B); let K:=beamL (Scree.mid m B); let Λ:=beamL (Scree.mid C B); let F(X:U×V):= integrated P A R' A' G T q d 0 X.1 X.2
 have ht: Integrable F ((city _).prod (city _)):= Env.integrableX (Girt.buoy E T p v 0) _; have hp: Integrable (fun x=>K (F x)) _ :=K.integrable_comp ht
 calc
   _= ∫ x, K (∫ y, F (x,y) ∂city _) ∂city _:= by unfold partitionZ; apply integral_congr_ae; refine ((Measure.quasiMeasurePreserving_fst (μ:=prior group (More (Scree.mid m B))) (ν:=depot (Scree.mid m B))).ae (g (More _))).mono fun i p=>?_ ; dsimp only; rw [← u i p]; rfl
   _= K (∫ x, (∫ y,F (x,y) ∂city _) ∂city _):=K.integral_comp_comm ht.integral_prod_left -- tune implicit order
   _= ∫ z, K (F z) ∂(city _).prod (city _):=by rw [K.integral_comp_comm ht,integral_prod F ht]
   _= ∫ y,(∫ x, K (F (x,y)) ∂city _) ∂city _:= integral_prod_symm _ hp
   _= _:=by
     unfold partitionZ; apply integral_congr_ae; apply Eventually.of_forall; intro y; dsimp only [F]; change (∫ x, beamL (Scree.mid m B) _ ∂city _)=beamZ (Scree.mid C B) (denZ R' P A' y); simp_rw [relayQ E]; rw [integral_smul_const]; have hk:= (T.isKernel v R'.beta).integrable y.1; rw [city]; rw [integral_prod]; simp only [integral_const, probReal_univ,one_smul,(T.isKernel v R'.beta).total,one_smul]; rfl
     exact hk.comp_fst _
include E
end YM.CF.Scree
